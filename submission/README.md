# Palomar preparation

The repository root is this Lean directory. The outer paper directory is not
part of the repository. No remote repository, public commit, submission or
registration has been created by these preparations.

## Local sequence

1. `python scripts/prepare_logarithms.py` reconstructs the dependency closure.
2. `python scripts/check_submission.py` checks module headers, file sizes,
   source trust tokens, the Challenge boundary and dependency hashes.
3. `lake exe cache get` retrieves the pinned mathlib cache if needed.
4. `lake --rehash build Challenge Solution` builds the independent statement
   environment and the substantive proved environment.
5. `python scripts/audit_axioms.py` runs `lake env lean Audit.lean`, checks every
   expected principal axiom profile, and compiles the modern README client.
6. On Linux with bubblewrap, `bash scripts/verify-comparator.sh` runs the
   toolchain's Comparator with its bundled NanoDa and con-ron kernels.
7. `python scripts/check_submission.py --ready` also checks outstanding
   publication gates, recorded explicitly in `readiness.json`.

Challenge's six intentional `sorry` statements are isolated from Solution.
All proof-source scans and metadata hole counts exclude those deliberate
statement holes. Definitions in Challenge are complete, not holes.

The project metadata uses JSON syntax, which is valid YAML, to allow standard
library tools to read `formalization.yaml`. It has been checked against the
published v0.4 schema at the revision recorded in `upstream-references.json`.
Joshua Mark's ORCID is recorded in the manuscript and metadata credits; the
standard schema's author lists use name strings.

## Publication gates

The logarithm dependency's original additions have no elected blanket software
licence in their supplied notice. The local reconstructed source tree must not
be represented as relicensed under our root Apache licence. Resolving this is
required before publishing the tree or selecting an appropriately licensed,
pinned Git dependency. See `../DEPENDENCIES.md`.

The reconstructed vendor tree is Git-ignored until that is resolved. A final
vendoring decision must remove that ignore rule and include the permitted
source; a dependency decision must pin a public source repository instead.

Palomar rebuilds a pushed immutable commit in a sandbox without build-time
network access. Ignored downloads, local caches and uncommitted vendor files
are not a deployable dependency strategy. A final snapshot must include the
permitted source or resolve it through a supported pinned dependency. The
preparation script alone is not a claim that Palomar's worker will fetch an
arXiv archive during the proof build.

The current evidence is maintained here after each validation run. A pre-port
build or ordinary Lean acceptance is not a Comparator result. Export-only
checks, if performed, must explicitly record that they do not independently
rebuild the source inside the Comparator sandbox.

## Current local evidence

| Check | Result |
| --- | --- |
| Module-system Challenge/Solution build | Passed, 5,811 Lake jobs |
| Principal axiom audit | Passed, 156 declarations; only the standard three axioms |
| Modern import example | Passed |
| Source preflight | Passed, 1,089 Lean files; six statement-only holes, no proof holes or custom axioms |
| Recorded dependency reconstruction | Passed, 1,001 source files matching the pinned archive and recorded port |
| Metadata v0.4 schema | Passed at the pinned schema revision |
| Repository-local corrected paper | PDF compiled with Tectonic 0.17.0 |
| Sandboxed Comparator | Passed all six claims, exit 0; con-ron, NanoDa and Lean default kernels accepted |

`verification.json` records local evidence; `readiness.json` records the
outstanding gates. Neither file is a registry certificate. Build logs and
detailed runtime reports are under ignored `.lake/`.

Once all gates pass, follow the current
[Palomar submission guide](https://palomar-registry.org/how-to-submit), and submit the exact public commit
through https://submit.palomar-registry.org/. Registration is a separate public
action; these preparations do not authorize it.

## Lax compatibility

The small statement surface, complete proof development and repository-local
paper support later Lax packaging. Lax has its own concept/proof separation,
annotations, build environments and submission tooling. No Lax compatibility
check has yet passed. Palomar is the first target.
