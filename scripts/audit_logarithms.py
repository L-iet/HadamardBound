"""Compile the relevant arXiv supplement in isolation, using the current Lean.

Run with `lake env python scripts/audit_logarithms.py`. Downloaded sources and
artifacts stay in ignored directories. The dependency is reconstructed by prepare_logarithms.py. Historical audit
reports do not certify changed sources until this verifier is run again.
"""

from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import urllib.request


PROJECT = Path(__file__).resolve().parents[1]
ARCHIVE_SHA256 = "2b37bfa6f04a1316eead45f1b6ba2ad660eef6a02f00b31476d603a7e55de69e"
ARCHIVE = PROJECT / "sources/logarithms-2610.28079v1.tar"
SOURCE = PROJECT / "vendor/logarithms"
BUILD = PROJECT / ".lake/logarithms-audit"
TARGET = "QuadraticPi.RationalLogRatioTheorem"
FULL_TARGET = TARGET


def source_path(module):
    return SOURCE / (module.replace(".", "/") + ".lean")


def main():
    global BUILD, TARGET
    # Windows console defaults cannot encode Lean's Unicode diagnostics.
    sys.stdout.reconfigure(encoding="utf-8", errors="backslashreplace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--threads", type=int, default=2)
    parser.add_argument("--target", default=TARGET)
    parser.add_argument("--build-dir", type=Path, default=BUILD)
    parser.add_argument("--prepare-only", action="store_true",
                        help="verify, extract and patch sources without compiling")
    args = parser.parse_args()
    if args.jobs < 1 or args.threads < 1:
        parser.error("jobs and threads must be positive")
    BUILD = args.build_dir.resolve()
    TARGET = args.target
    if not BUILD.is_relative_to(PROJECT) or not re.fullmatch(r"[A-Za-z0-9_.]+", TARGET):
        parser.error("build-dir must be within the project and target must be a module name")
    subprocess.run([sys.executable, str(PROJECT / "scripts/prepare_logarithms.py")],
                   cwd=PROJECT, check=True)

    if args.prepare_only:
        print(f"Prepared {SOURCE}; archive SHA256={ARCHIVE_SHA256}", flush=True)
        return 0

    deps = {}
    contents = {}

    def visit(module):
        if module in deps:
            return
        path = source_path(module)
        text = path.read_text(encoding="utf-8")
        contents[module] = text
        imports = re.findall(r"^(?:public )?import\s+(\S+)", text, re.M)
        local = {name for name in imports if source_path(name).exists()}
        deps[module] = local
        for name in sorted(local):
            visit(name)

    visit(TARGET)
    if TARGET == FULL_TARGET:
        # The paper's theorem does not need this elementary converse, but
        # our adapter does. Build it here rather than relying on another cache.
        visit("QuadraticPi.ExponentConverse")
    BUILD.mkdir(parents=True, exist_ok=True)
    lib = BUILD / "lib/lean"
    lib.mkdir(parents=True, exist_ok=True)
    logs = BUILD / "logs"
    logs.mkdir(parents=True, exist_ok=True)
    lean = shutil.which("lean")
    if not lean:
        raise RuntimeError("Lean is missing; run through lake env")
    version = subprocess.check_output([lean, "--githash"], text=True).strip()
    manifest = (PROJECT / "lake-manifest.json").read_bytes()
    environment = hashlib.sha256(version.encode() + manifest).hexdigest()
    fingerprints = {}

    def fingerprint(module):
        if module not in fingerprints:
            data = environment + contents[module] + "".join(
                name + fingerprint(name) for name in sorted(deps[module])
            )
            fingerprints[module] = hashlib.sha256(data.encode()).hexdigest()
        return fingerprints[module]

    for module in deps:
        fingerprint(module)
    state_path = BUILD / "state.json"
    state = json.loads(state_path.read_text()) if state_path.exists() else {}

    def output_path(module):
        return lib / (module.replace(".", "/") + ".olean")

    done = {
        module for module in deps
        if state.get(module) == fingerprints[module] and output_path(module).exists()
    }
    pending = set(deps) - done
    active = {}
    failed = []
    env = os.environ.copy()
    env["LEAN_PATH"] = str(lib) + os.pathsep + env.get("LEAN_PATH", "")

    def compile_module(module):
        output = output_path(module)
        output.parent.mkdir(parents=True, exist_ok=True)
        result = subprocess.run(
            [lean, f"-j{args.threads}", "-R", str(SOURCE), str(source_path(module)),
             "-o", str(output)],
            cwd=PROJECT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, encoding="utf-8", errors="replace",
        )
        (logs / (module + ".log")).write_text(result.stdout, encoding="utf-8")
        return result.returncode, result.stdout

    print(f"Lean {version}; {len(deps)} modules; {len(done)} verified cached; jobs={args.jobs}", flush=True)
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        while pending or active:
            if not failed:
                ready = sorted(m for m in pending if deps[m] <= done)
                for module in ready[: args.jobs - len(active)]:
                    pending.remove(module)
                    active[executor.submit(compile_module, module)] = module
            if not active:
                if pending and not failed:
                    raise RuntimeError("The import graph has an unresolved cycle")
                break
            finished, _ = wait(active, return_when=FIRST_COMPLETED)
            for future in finished:
                module = active.pop(future)
                code, output = future.result()
                if code == 0:
                    done.add(module)
                    state[module] = fingerprints[module]
                    print(f"PASS {len(done)}/{len(deps)} {module}", flush=True)
                else:
                    failed.append(module)
                    print(f"FAIL {module}\n{output}", flush=True)
                state_path.write_text(json.dumps(state, indent=2), encoding="utf-8")
    report = {"target": TARGET, "leanCommit": version, "archiveSHA256": ARCHIVE_SHA256,
              "total": len(deps), "passed": len(done), "failed": failed,
              "remaining": sorted(pending)}
    if not failed and not pending and TARGET == FULL_TARGET:
        allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}

        def run_check(label, arguments, audited_count=None):
            result = subprocess.run(
                [lean, f"-j{args.threads}", *arguments], cwd=PROJECT, env=env,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, encoding="utf-8", errors="replace",
            )
            (logs / (label + ".log")).write_text(result.stdout, encoding="utf-8")
            ok = result.returncode == 0
            if audited_count is not None and ok:
                profiles = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", result.stdout)
                axioms = {name.strip() for p in profiles for name in p.split(",") if name.strip()}
                report[label + "Axioms"] = sorted(axioms)
                ok = len(profiles) == audited_count and axioms <= allowed_axioms
            report[label + "Passed"] = ok
            print(f"{'PASS' if ok else 'FAIL'} {label}", flush=True)
            if not ok:
                print(result.stdout, flush=True)
            return ok

        external_ok = run_check("external-endpoint-audit",
            [str(PROJECT / "integration/AuditExternalLogarithms.lean")], audited_count=2)
        finite_output = lib / "integration/FiniteApproximationAdapter.olean"
        finite_output.parent.mkdir(parents=True, exist_ok=True)
        finite_ok = external_ok and run_check("finite-approximation-adapter",
            ["-R", str(PROJECT), str(PROJECT / "integration/FiniteApproximationAdapter.lean"),
             "-o", str(finite_output)])
        adapter_output = lib / "integration/LogarithmRatioInput.olean"
        adapter_output.parent.mkdir(parents=True, exist_ok=True)
        adapter_ok = finite_ok and run_check("hadamard-adapter",
            ["-R", str(PROJECT), str(PROJECT / "integration/LogarithmRatioInput.lean"),
             "-o", str(adapter_output)])
        audit_ok = adapter_ok and run_check("hadamard-adapter-audit",
            [str(PROJECT / "integration/AuditLogarithmRatioInput.lean")], audited_count=5)
        complete_output = lib / "integration/CompleteResults.olean"
        complete_ok = audit_ok and run_check("complete-results",
            ["-R", str(PROJECT), str(PROJECT / "integration/CompleteResults.lean"),
             "-o", str(complete_output)])
        complete_audit_ok = complete_ok and run_check("complete-results-audit",
            [str(PROJECT / "integration/AuditCompleteResults.lean")], audited_count=9)
        report["integrationPassed"] = bool(complete_audit_ok)
    (BUILD / "report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items() if k != "remaining"}), flush=True)
    return int(bool(failed or pending or
        (TARGET == FULL_TARGET and not report.get("integrationPassed", False))))


if __name__ == "__main__":
    raise SystemExit(main())
