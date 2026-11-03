"""Record and verify permissive licences for the pinned Mathlib package closure.

This covers the Lake packages in lake-manifest.json. It is not a licence grant
for unrelated local source trees or a mathematical proof audit.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
RECORD = ROOT / "submission/mathlib-licenses.json"
ALLOWED = {"mathlib", "plausible", "LeanSearchClient", "importGraph", "proofwidgets",
           "aesop", "Qq", "batteries", "Cli"}


def inventory():
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = []
    if {p["name"] for p in manifest["packages"]} != ALLOWED:
        raise ValueError("Package set changed; review every new dependency and its licence")
    for package in manifest["packages"]:
        name = package["name"]
        if package["type"] != "git" or len(package["rev"]) != 40:
            raise ValueError(f"Dependency is not pinned to a full Git commit: {name}")
        directory = ROOT / manifest["packagesDir"] / name
        licence = directory / "LICENSE"
        data = licence.read_bytes()
        text = data.decode("utf-8").strip()
        if text.startswith("Apache License") and "Version 2.0, January 2004" in text:
            spdx = "Apache-2.0"
        elif text.startswith("MIT License") and "Permission is hereby granted, free of charge" in text:
            spdx = "MIT"
        else:
            raise ValueError(f"Unrecognized licence; human review required: {name}")
        git = subprocess.run(["git", "-C", str(directory), "rev-parse", "HEAD"],
                             check=True, capture_output=True, text=True)
        if git.stdout.strip() != package["rev"]:
            raise ValueError(f"Local package is not at its pinned revision: {name}")
        packages.append({"name": name, "repository": package["url"], "revision": package["rev"],
                         "license": spdx, "licensePath": "LICENSE",
                         "licenseSHA256": hashlib.sha256(data).hexdigest()})
    return {"scope": "Pinned Mathlib and its Lake package closure",
            "permittedLicenses": ["Apache-2.0", "MIT"], "packages": packages}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--record", action="store_true", help="record the reviewed package inventory")
    args = parser.parse_args()
    report = inventory()
    if args.record:
        RECORD.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    elif json.loads(RECORD.read_text(encoding="utf-8")) != report:
        raise ValueError("Pinned package/licence inventory changed; review before updating")
    print(f"Verified {len(report['packages'])} pinned package licences: Apache-2.0 or MIT")


if __name__ == "__main__":
    main()
