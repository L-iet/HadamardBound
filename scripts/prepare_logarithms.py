"""Reconstruct the exact proof dependency, retaining upstream terms and hashes.

This prepares local source files. It does not grant redistribution permission.
The original arXiv archive stays in ignored sources/; only the required import
closure is materialized under vendor/logarithms/.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import tarfile
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
SHA256 = "2b37bfa6f04a1316eead45f1b6ba2ad660eef6a02f00b31476d603a7e55de69e"
URL = "https://arxiv.org/src/2610.28079v1"
TARGETS = ["QuadraticPi.RationalLogRatioTheorem", "QuadraticPi.ExponentConverse"]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def modernize(text):
    """Publish legacy interfaces explicitly; preserve all mathematical bodies."""
    if re.search(r"^module\s*$", text, re.M):
        return text
    # Legacy files could use private abbreviations and local instance bodies in
    # public statement types. Publish those interfaces explicitly in the port.
    text = re.sub(r"^(\s*(?:@\[[^\n]*\]\s*)*)private (?=(?:noncomputable )?(?:def|abbrev|instance|local instance)\b)",
                  r"\1", text, flags=re.M)
    text = re.sub(r"^import ", "public import ", text, flags=re.M)
    imports = list(re.finditer(r"^public import[^\n]*\n", text, re.M))
    if not imports:
        raise ValueError("Expected an import header")
    end = imports[-1].end()
    return "module\n\n" + text[:end] + "\n@[expose] public section\n" + text[end:]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true", help="reconstruct and compare without writing source")
    parser.add_argument("--update-manifest", action="store_true",
                        help="record a reviewed new source inventory under submission/")
    args = parser.parse_args()
    if args.verify and args.update_manifest:
        parser.error("--verify cannot update the recorded inventory")
    archive = ROOT / "sources/logarithms-2610.28079v1.tar"
    archive.parent.mkdir(parents=True, exist_ok=True)
    if not archive.exists():
        urllib.request.urlretrieve(URL, archive)
    if digest(archive.read_bytes()) != SHA256:
        raise RuntimeError("Archive checksum mismatch")
    with tarfile.open(archive) as tar:
        raw = {m.name.removeprefix("anc/lean/"): tar.extractfile(m).read()
               for m in tar.getmembers()
               if m.isfile() and m.name.startswith("anc/lean/")}
    patches = json.loads((ROOT / "integration/logarithms-4.35-patches.json").read_text(encoding="utf-8"))
    selected = set()

    def visit(module):
        rel = module.replace(".", "/") + ".lean"
        if rel not in raw or rel in selected:
            return
        selected.add(rel)
        for imp in re.findall(r"^(?:public )?import\s+(\S+)", raw[rel].decode(), re.M):
            visit(imp)

    for target in TARGETS:
        visit(target)
    destination = ROOT / "vendor/logarithms"
    destination.mkdir(parents=True, exist_ok=True)
    entries = []
    for rel in sorted(selected):
        text = raw[rel].decode("utf-8").replace("\r\n", "\n")
        for patch in patches:
            if patch["path"] != rel:
                continue
            count = patch.get("expectedOccurrences", 1)
            if text.count(patch["old"]) != count:
                raise RuntimeError(f"Patch mismatch: {rel}")
            text = text.replace(patch["old"], patch["new"], count)
        modern = modernize(text).encode("utf-8")
        port_patches = ROOT / "integration/logarithms-module-patches.json"
        if port_patches.exists():
            for patch in json.loads(port_patches.read_text(encoding="utf-8")):
                if patch["path"] != rel:
                    continue
                current = modern.decode("utf-8")
                count = patch.get("expectedOccurrences", 1)
                found = (len(re.findall(patch["old"], current)) if patch.get("regex")
                         else current.count(patch["old"]))
                if found != count:
                    raise RuntimeError(f"Module patch mismatch: {rel}")
                changed = (re.sub(patch["old"], patch["new"], current, count=count)
                           if patch.get("regex") else current.replace(patch["old"], patch["new"], count))
                modern = changed.encode("utf-8")
        path = destination / rel
        if not path.resolve().is_relative_to(destination.resolve()):
            raise RuntimeError(f"Unsafe source path: {rel}")
        path.parent.mkdir(parents=True, exist_ok=True)
        if not path.exists() or path.read_bytes() != modern:
            if args.verify:
                raise RuntimeError(f"Prepared source mismatch: {rel}")
            path.write_bytes(modern)
        entries.append({"path": rel, "archiveSHA256": digest(raw[rel]),
                        "compatibleSHA256": digest(text.encode()), "moduleSHA256": digest(modern)})
    for notice in ["SOURCE-NOTICE.txt", "LICENSE-OAI-APACHE-2.0.txt"]:
        if notice not in raw:
            raise RuntimeError(f"Missing upstream notice: {notice}")
        path = destination / notice
        if args.verify:
            if not path.exists() or path.read_bytes() != raw[notice]:
                raise RuntimeError(f"Notice mismatch: {notice}")
        else:
            path.write_bytes(raw[notice])
    module_patches = ROOT / "integration/logarithms-module-patches.json"
    report = {"source": URL, "archiveSHA256": SHA256, "targets": TARGETS,
              "portScriptSHA256": digest(Path(__file__).read_bytes()),
              "arxivDistributionLicense": "http://arxiv.org/licenses/nonexclusive-distrib/1.0/",
              "noticeSHA256": {name: digest(raw[name]) for name in
                               ["SOURCE-NOTICE.txt", "LICENSE-OAI-APACHE-2.0.txt"]},
              "moduleCount": len(entries), "compatibilityPatches": len(patches),
              "modulePort": "module; public imports; exposed public interfaces; recorded proof/import port fixes; no changed mathematical assumptions",
              "modulePatches": len(json.loads(module_patches.read_text(encoding="utf-8"))) if module_patches.exists() else 0,
              "redistributionPermission": "Unresolved for original additions; see SOURCE-NOTICE.txt",
              "files": entries}
    recorded = ROOT / "submission/logarithms-source-manifest.json"
    if args.update_manifest:
        recorded.write_text(json.dumps(report, indent=2) + "\n")
    elif not recorded.exists() or json.loads(recorded.read_text()) != report:
        raise RuntimeError("Recorded source inventory differs; review the changes and use --update-manifest")
    manifest = destination / "provenance.json"
    if args.verify:
        if json.loads(manifest.read_text()) != report:
            raise RuntimeError("Provenance manifest differs from reconstruction")
    else:
        manifest.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Prepared {len(entries)} modules; retained upstream notices; redistribution unresolved")


if __name__ == "__main__":
    main()
