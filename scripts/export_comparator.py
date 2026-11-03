"""Export a compiled environment for cross-platform Comparator checking.

Includes the toolchain's mandatory primitive declarations, not only the named
theorems. Export-only checking does not rebuild these sources in a sandbox.
The canonical Linux source-build check remains verify-comparator.sh with no
--*-from-export arguments.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("module", choices=["Challenge", "Solution"])
args = parser.parse_args()
prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
implementation = prefix / "src/lean/lake/Lake/CLI/Check.lean"
source = implementation.read_text(encoding="utf-8")
primitive_source = source.split("def primitiveTargets", 1)[1].split("def builtinTargets", 1)[0]
primitive_source = re.sub(r"--[^\n]*", "", primitive_source)
primitives = re.findall(r"``([A-Za-z][A-Za-z0-9_.]*)", primitive_source)
if not primitives or "String.mk" not in primitives:
    raise RuntimeError("Cannot recover this toolchain's primitive export contract")
config = json.loads((root / "comparator.json").read_text())
targets = list(dict.fromkeys(["Quot", "Quot.mk", "Quot.lift", "Quot.ind",
                             *config["theorem_names"], *config["permitted_axioms"],
                             *primitives, *config.get("definition_names", [])]))
destination = root / ".lake/palomar-exports"
destination.mkdir(parents=True, exist_ok=True)
path = destination / (args.module.lower() + ".ndjson")
with path.open("wb") as out, path.with_suffix(".stderr").open("wb") as err:
    result = subprocess.run(["lake", "env", "leanexport", args.module, "--", *targets],
                            cwd=root, stdout=out, stderr=err)
if result.returncode:
    raise SystemExit(result.returncode)
report = {"module": args.module, "targets": targets, "bytes": path.stat().st_size,
          "leanGithash": subprocess.check_output(["lean", "--githash"], text=True).strip(),
          "primitiveContractSHA256": hashlib.sha256(implementation.read_bytes()).hexdigest(),
          "sourceBuildSandboxedByThisExport": False}
sha = hashlib.sha256()
with path.open("rb") as handle:
    for chunk in iter(lambda: handle.read(1024 * 1024), b""):
        sha.update(chunk)
report["sha256"] = sha.hexdigest()
path.with_suffix(".json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({key: report[key] for key in ["module", "bytes", "sha256", "leanGithash"]}))
