"""Audit the independently written quantitative logarithm proof.

First build HadamardMultibaseClassical. This checks the project-source import
closure, every declaration in AuditClassical.lean, and the pinned permissive
Mathlib package licences.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

from audit_mathlib_licenses import inventory
from check_submission import code_only

ROOT = Path(__file__).resolve().parents[1]


def source_closure():
    files = {}

    def visit(module):
        if module == "Mathlib" or module.startswith(("Mathlib.", "Lean.", "Std.", "Init.")):
            return
        if not (module == "HadamardMultibaseClassical" or module.startswith("HadamardMultibase.")):
            raise ValueError(f"Non-approved proof import: {module}")
        relative = module.replace(".", "/") + ".lean"
        if relative in files:
            return
        data = (ROOT / relative).read_bytes()
        code = code_only(data.decode("utf-8"))
        if re.search(r"\b(?:sorry|admit|axiom|native_decide|ofReduceBool)\b", code):
            raise ValueError(f"Unproved/trust shortcut in rework closure: {relative}")
        files[relative] = hashlib.sha256(data).hexdigest()
        for imported in re.findall(r"^(?:public )?import\s+(\S+)", code, re.M):
            visit(imported)

    visit("HadamardMultibaseClassical")
    return dict(sorted(files.items()))


def main():
    closure = source_closure()
    licences = inventory()
    recorded = json.loads((ROOT / "submission/mathlib-licenses.json").read_text(encoding="utf-8"))
    if licences != recorded:
        raise ValueError("The reviewed permissive package inventory changed")
    source = (ROOT / "AuditClassical.lean").read_text(encoding="utf-8")
    expected = set(re.findall(r"^#print axioms (\S+)", source, re.M))
    theorem_modules = [p for p in (ROOT / "HadamardMultibase").glob("*.lean")
                       if p.stem.startswith(("Baker", "ExponentialPolynomial")) or p.stem in {
                           "ClassicalLogarithmForms", "ElementaryLogarithmBounds",
                           "BoundedIntegerKernel", "SmallRationalValues", "RationalAuxiliaryKernel", "LogarithmSeparation"}]
    declared = {"HadamardMultibase." + name for path in theorem_modules
                for name in re.findall(r"\btheorem\s+([A-Za-z_][A-Za-z0-9_.]*)",
                                       code_only(path.read_text(encoding="utf-8")))}
    if declared != expected:
        raise ValueError(f"Foundation theorem coverage differs: missing={sorted(declared - expected)}, "
                         f"extra={sorted(expected - declared)}")
    run = subprocess.run(["lake", "env", "lean", "AuditClassical.lean"], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                         text=True, encoding="utf-8", errors="replace")
    (ROOT / ".lake/classical-rework-axioms.log").write_text(run.stdout, encoding="utf-8")
    if run.returncode:
        raise RuntimeError("Classical axiom audit did not compile; see .lake/classical-rework-axioms.log")
    profiles = {name: [a.strip() for a in axioms.split(",") if a.strip()]
                for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", run.stdout)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", run.stdout):
        profiles[name] = []
    if set(profiles) != expected:
        raise ValueError(f"Audit coverage mismatch: {sorted(expected - set(profiles))}")
    axioms = sorted({a for profile in profiles.values() for a in profile})
    if set(axioms) - {"propext", "Classical.choice", "Quot.sound"}:
        raise ValueError(f"Nonstandard axiom dependencies: {axioms}")
    report = {"foundationsChecked": True, "logarithmSeparationProofComplete": True,
              "polynomialRotationSeparationProved": True,
              "entryPoint": "HadamardMultibaseClassical", "auditedDeclarations": len(profiles),
              "axioms": axioms, "projectSourceClosure": closure,
              "additionalProofDependencies": [], "permissiveLakePackages": len(licences["packages"]),
              "checkedAtUTC": datetime.now(timezone.utc).isoformat()}
    (ROOT / ".lake/classical-rework-audit.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({k: v for k, v in report.items() if k != "projectSourceClosure"}, indent=2))


if __name__ == "__main__":
    main()
