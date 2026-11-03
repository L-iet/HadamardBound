"""Run the complete principal-declaration audit and the documented import test."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parents[1]
audit = (root / "Audit.lean").read_text(encoding="utf-8")
expected = set(re.findall(r"^#print axioms (\S+)", audit, re.M))
result = subprocess.run(["lake", "env", "lean", "Audit.lean"], cwd=root,
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                        text=True, encoding="utf-8", errors="replace")
(root / ".lake/palomar-axiom-audit.log").write_text(result.stdout, encoding="utf-8")
if result.returncode:
    raise SystemExit(result.returncode)
profiles = {name: [a.strip() for a in axioms.split(",") if a.strip()]
            for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",
                                          result.stdout)}
for name in re.findall(r"'([^']+)' does not depend on any axioms", result.stdout):
    profiles[name] = []
if set(profiles) != expected:
    raise RuntimeError(f"Audit coverage differs: missing={sorted(expected-set(profiles))}")
axioms = sorted({a for profile in profiles.values() for a in profile})
if set(axioms) - {"propext", "Quot.sound", "Classical.choice"}:
    raise RuntimeError(f"Nonstandard proof axioms: {axioms}")
client = '''module
import HadamardMultibaseComplete
#check HadamardMultibase.sparseRepresentationBound
#check HadamardMultibase.Complete.main_bound
#check HadamardMultibase.Complete.covering_bounds
#check HadamardMultibase.Complete.optimalConditionNumber_bound
'''
test = subprocess.run(["lake", "env", "lean", "--stdin"], cwd=root, input=client,
                      stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                      text=True, encoding="utf-8", errors="replace")
(root / ".lake/palomar-readme-client.log").write_text(test.stdout, encoding="utf-8")
if test.returncode:
    raise SystemExit(test.returncode)
report = {"auditedDeclarations": len(profiles), "axioms": axioms,
          "auditExit": result.returncode, "modernClientExit": test.returncode,
          "auditSourceSHA256": hashlib.sha256(audit.encode()).hexdigest(),
          "verifiedAtUTC": datetime.now(timezone.utc).isoformat()}
(root / ".lake/palomar-axiom-audit.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
