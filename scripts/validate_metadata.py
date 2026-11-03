"""Validate formalization.yaml against the pinned upstream v0.4 schema."""
import json
from pathlib import Path
import urllib.request

from jsonschema import Draft7Validator

root = Path(__file__).resolve().parents[1]
reference = json.loads((root / "submission/upstream-references.json").read_text())["metadata"]
url = (f"https://raw.githubusercontent.com/{reference['repository']}/"
       f"{reference['revision']}/schema/v0.4.schema.json")
schema = json.load(urllib.request.urlopen(url))
metadata = json.loads((root / "formalization.yaml").read_text(encoding="utf-8"))
errors = sorted(Draft7Validator(schema).iter_errors(metadata), key=lambda e: str(e.path))
for error in errors:
    print("/".join(map(str, error.absolute_path)), error.message)
if errors:
    raise SystemExit(1)
print(f"Metadata schema passed at {reference['revision']}")
