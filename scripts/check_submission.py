"""Check the repository's statement surface, proof sources and provenance.

This is a structural preflight, not a substitute for Lean or Comparator.
--ready also fails on the explicitly recorded publication blockers.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
EXCLUDED = {".git", ".lake", ".proof-tools", "sources", "__pycache__"}


def code_only(text):
    """Mask nested Lean comments and strings while preserving line breaks."""
    result = list(text)
    depth = 0
    string = False
    i = 0
    while i < len(text):
        pair = text[i:i + 2]
        width = 1
        if depth:
            if pair == "/-":
                depth += 1
                width = 2
            elif pair == "-/":
                depth -= 1
                width = 2
        elif string:
            if text[i] == "\\":
                width = min(2, len(text) - i)
            elif text[i] == '"':
                string = False
        elif pair == "/-":
            depth = 1
            width = 2
        elif pair == "--":
            end = text.find("\n", i)
            width = (len(text) if end < 0 else end) - i
        elif text[i] == '"':
            string = True
        else:
            i += 1
            continue
        for j in range(i, i + width):
            if result[j] not in "\r\n":
                result[j] = " "
        i += width
    if depth or string:
        raise ValueError("Unterminated comment/string")
    return "".join(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ready", action="store_true")
    args = parser.parse_args()
    errors = []
    files = []
    for directory, children, names in os.walk(ROOT):
        children[:] = [name for name in children if name not in EXCLUDED]
        files.extend(Path(directory) / name for name in names if name.endswith(".lean"))
    files.sort()
    holes = 0
    for path in files:
        rel = path.relative_to(ROOT).as_posix()
        if path.is_symlink():
            errors.append(f"{rel}: source symlink")
            continue
        text = path.read_text(encoding="utf-8")
        code = code_only(text)
        if path.name != "lakefile.lean" and not re.match(r"\s*module\b", code):
            errors.append(f"{rel}: module header missing")
        if len(text.splitlines()) > 10000:
            errors.append(f"{rel}: exceeds 10000 physical lines")
        forbidden = re.findall(r"\b(?:sorry|admit|axiom|native_decide)\b", code)
        if rel == "Challenge.lean":
            holes = forbidden.count("sorry")
            if set(forbidden) - {"sorry"}:
                errors.append("Challenge has an unexpected trust shortcut")
            if len(text.splitlines()) > 1000 or len(text.encode()) > 102400:
                errors.append("Challenge exceeds Palomar's size limit")
            for imp in re.findall(r"^(?:public )?import\s+(\S+)", code, re.M):
                if not imp.startswith("Mathlib."):
                    errors.append(f"Challenge imports non-mathlib module: {imp}")
        elif forbidden:
            errors.append(f"{rel}: forbidden proof tokens {forbidden}")
    config = json.loads((ROOT / "comparator.json").read_text())
    if config.get("permitted_axioms") != ["propext", "Quot.sound", "Classical.choice"]:
        errors.append("Comparator axiom list differs from the standard three")
    if "external_kernels" in config:
        errors.append("External kernels must be supplied by the verifier, not submitted config")
    if holes != len(config["theorem_names"]):
        errors.append("Challenge hole count differs from the compared theorem count")
    if "Challenge" in re.findall(r"^(?:public )?import\s+(\S+)",
                                  code_only((ROOT / "Solution.lean").read_text()), re.M):
        errors.append("Solution imports Challenge")
    metadata = json.loads((ROOT / "formalization.yaml").read_text(encoding="utf-8"))
    if metadata["project"]["license"] != "Apache-2.0":
        errors.append("Own-project licence metadata must match LICENSE")
    if metadata["status"]["sorry_count"] != 0 or metadata["status"]["axioms"]:
        errors.append("Metadata reports proof holes or custom axioms")
    provenance = json.loads((ROOT / "vendor/logarithms/provenance.json").read_text())
    recorded = json.loads((ROOT / "submission/logarithms-source-manifest.json").read_text())
    if provenance != recorded:
        errors.append("Prepared and recorded dependency inventories differ")
    for entry in provenance["files"]:
        path = ROOT / "vendor/logarithms" / entry["path"]
        if hashlib.sha256(path.read_bytes()).hexdigest() != entry["moduleSHA256"]:
            errors.append(f"Dependency hash mismatch: {entry['path']}")
    blockers = json.loads((ROOT / "submission/readiness.json").read_text())
    pending = [item["description"] for item in blockers["gates"] if not item["passed"]]
    report = {"leanFiles": len(files), "dependencyModules": provenance["moduleCount"],
              "comparedTheorems": len(config["theorem_names"]), "challengeHoles": holes,
              "errors": errors, "pendingGates": pending}
    print(json.dumps(report, indent=2))
    return 1 if errors or (args.ready and pending) else 0


if __name__ == "__main__":
    raise SystemExit(main())
