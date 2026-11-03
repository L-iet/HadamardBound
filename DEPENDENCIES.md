# Dependencies and licences

The sole direct Lake dependency is mathlib v4.35.0, resolved to commit
56a005855ea17e0b0958f73ec801ae140b0a1679. `lake-manifest.json` pins its
transitive package closure to full Git revisions. Lean 4.35.0 is pinned in
`lean-toolchain`.

Mathlib, batteries, Qq, aesop, proofwidgets, importGraph, LeanSearchClient and
plausible use Apache-2.0. Cli uses MIT. The reviewed root licence texts and
SHA-256 hashes are recorded in `submission/mathlib-licenses.json`.
Run `python scripts/audit_mathlib_licenses.py` to verify the local package
revisions and licence inventory. Dependency notices retain their own terms.
Project-owned Lean code is Apache-2.0 under LICENSE.

The formal proof imports only mathlib, Lean's standard libraries and
project-owned modules. No additional proof-source download is required.
The proof-source closure and axiom checks are reproducible through
`scripts/audit_classical_rework.py` and `scripts/audit_axioms.py`.

Mathematical citations in the manuscript are research references, not source
code dependencies or claims that their full theorems have been formalized.
