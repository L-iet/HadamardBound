"""Check proof-source structure; --ready also requires completed target proofs."""
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
    errors, files = [], []
    holes = 0
    for directory, children, names in os.walk(ROOT):
        children[:] = [name for name in children if name not in EXCLUDED]
        files.extend(Path(directory) / name for name in names if name.endswith(".lean"))
    for path in sorted(files):
        rel = path.relative_to(ROOT).as_posix()
        if path.is_symlink():
            errors.append(f"{rel}: source symlink")
            continue
        code = code_only(path.read_text(encoding="utf-8"))
        if not re.match(r"\s*module\b", code):
            errors.append(f"{rel}: module header missing")
        tokens = re.findall(r"\b(?:sorry|admit|axiom|native_decide|ofReduceBool)\b", code)
        imports = re.findall(r"^(?:public )?import\s+(\S+)", code, re.M)
        if rel == "Challenge.lean":
            holes = tokens.count("sorry")
            if set(tokens) - {"sorry"}:
                errors.append("Target specifications contain an unexpected trust shortcut")
            if any(not name.startswith("Mathlib.") for name in imports):
                errors.append("Target specifications must import only mathlib")
        else:
            if tokens:
                errors.append(f"{rel}: forbidden proof tokens {tokens}")
            if "Challenge" in imports:
                errors.append(f"{rel}: proof code imports target specifications")
        for name in imports:
            if name.startswith(("Mathlib.", "Lean.", "Std.", "Init.")):
                continue
            if not (ROOT / (name.replace(".", "/") + ".lean")).is_file():
                errors.append(f"{rel}: missing local import {name}")
    metadata = json.loads((ROOT / "formalization.yaml").read_text(encoding="utf-8"))
    if metadata["project"]["license"] != "Apache-2.0":
        errors.append("Project licence metadata differs from LICENSE")
    if metadata["status"]["sorry_count"] != 0 or metadata["status"]["axioms"]:
        errors.append("Metadata differs from the proof-hole/custom-axiom inventory")
    gates = json.loads((ROOT / "submission/readiness.json").read_text(encoding="utf-8"))["gates"]
    pending = [g["description"] for g in gates if not g["passed"]]
    config_path = ROOT / "comparator.json"
    if not config_path.is_file():
        errors.append("Comparator configuration missing")
    else:
        config = json.loads(config_path.read_text())
        if holes != len(config["theorem_names"]):
            errors.append("Specification placeholder count differs from comparison targets")
        audit = (ROOT / "Audit.lean").read_text(encoding="utf-8")
        for name in config["theorem_names"]:
            if f"#print axioms {name}\n" not in audit:
                errors.append(f"Final endpoint omitted from axiom audit: {name}")
    if args.ready:
        evidence = json.loads((ROOT / "submission/verification.json").read_text())
        if not evidence.get("unconditionalFinalBoundsVerified") or not evidence.get("independentComparisonComplete"):
            errors.append("Completed proof/comparison evidence missing")
        comparison = evidence.get("comparison", {})
        for field, relative in [("challengeSourceSHA256", "Challenge.lean"),
                                ("configSHA256", "comparator.json"),
                                ("proofSourceManifestSHA256", "submission/proof-sources.json")]:
            if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != comparison.get(field):
                errors.append(f"Verification evidence changed: {relative}")
        manifest = json.loads((ROOT / "submission/proof-sources.json").read_text())
        for relative, digest in manifest["projectSourceSHA256"].items():
            path = ROOT / relative
            if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != digest:
                errors.append(f"Verified proof source changed: {relative}")
    print(json.dumps({"leanFiles": len(files), "proofHoles": 0, "targetSpecificationPlaceholders": holes,
                      "errors": errors, "pendingGates": pending}, indent=2))
    return int(bool(errors or (args.ready and pending)))

if __name__ == "__main__":
    raise SystemExit(main())
