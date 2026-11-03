# Dependency provenance

This repository contains the substantive Hadamard development. It is not a
thin wrapper around an external proof of the Hadamard bound.

## Lean and mathlib

`lean-toolchain` pins Lean 4.35.0. `lake-manifest.json` pins mathlib and its
transitive packages; mathlib resolves to
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Mathlib supplies
`Matrix.IsHadamard`, ordinary real analysis, finite-dimensional linear algebra
and probability infrastructure. Its source retains its own Apache-2.0 terms.

## Logarithm-ratio proof

The decisive additional formal input is Gregory V. Chudnovsky's Lean
supplement to *Irrationality exponents of logarithmic numbers: Values,
quotients, and graded approximation*, arXiv:2610.28079v1 (20 October 2026).

* Exact archive: https://arxiv.org/src/2610.28079v1
* SHA-256: `2b37bfa6f04a1316eead45f1b6ba2ad660eef6a02f00b31476d603a7e55de69e`
* Source roots inside the archive: `anc/lean/QuadraticPi` and `anc/lean/OAI`.
* Endpoint: `QuadraticPi.rationalLogRatio_finite_good` in
  `QuadraticPi/RationalLogRatioTheorem.lean`.
* Additional elementary adapter dependency: `QuadraticPi.ExponentConverse`.
* Combined external import closure: 1,001 modules.

The endpoint says that, for positive rational a,b with nonzero log b and no
nontrivial power relation, the reduced rational approximants to log a/log b
with exponent nu > 3 form a finite set. The relevant definitions are
`QuadraticPi.GoodRationalApproximations` and
`QuadraticPi.TwoLogCharacterCenters.NoPowerRelation`. Our proof uses finiteness,
not merely an upper bound on a real-valued supremum of approximation exponents.

`scripts/prepare_logarithms.py` reconstructs the exact closure from the
checksum-verified archive. It applies the 34 explicit changes in
`integration/logarithms-4.35-patches.json`, then adds module headers, public
imports and exposed public sections. It publishes private abbreviations and
instances where public statement types need them. Additional proof/import
fixes are recorded in `integration/logarithms-module-patches.json`, including
explicit formerly transitive imports and removal of redundant tactic steps.
These changes do not add mathematical assumptions or weaken conclusions.
`submission/logarithms-source-manifest.json` records the generator hash and the
archive, compatible-source and module-source hashes for every selected file.
This inventory is versioned even while third-party source remains ignored.
`vendor/logarithms/provenance.json` is its local prepared copy. The ignored `sources/` directory
is a download cache, not a source to commit.

Ordinary preparation and `--verify` require agreement with the recorded
inventory. After reviewing a changed recipe or patches, use
`python scripts/prepare_logarithms.py --update-manifest` to record that change.

The supplement itself records an earlier OpenAI proof-source origin at
`https://github.com/openai/math`, revision
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. That is provenance of part of the
supplement, **not** a claim that our snapshot is byte-identical to that Git
revision. OAI upstream portions are Apache-2.0. The original
`SOURCE-NOTICE.txt` and `LICENSE-OAI-APACHE-2.0.txt` are retained verbatim.

## Redistribution is not yet cleared

The arXiv v1 record links to the
[arXiv nonexclusive distribution licence](http://arxiv.org/licenses/nonexclusive-distrib/1.0/).
The supplement's notice explicitly elects no new blanket software licence for
the author's original additions. This repository's Apache-2.0 licence applies
to its own contributions; it does not relicense those additions. Their public
availability on arXiv is not recorded here as a grant of an Apache licence.

The local `vendor/logarithms` tree is prepared for reproducible checking.
It remains Git-ignored pending clearance, so `git add .` does not include it.
Publishing that tree requires clarification/permission from the relevant
rights holder or an appropriately licensed upstream release. Until then,
submission readiness must remain false. No request has been sent on the
maintainer's behalf. A future pinned public Git dependency may replace this
local tree, but only after its exact source and terms have been reviewed.

## Trust and validation

No external theorem is introduced as a project axiom. The original legacy
closure and all final endpoints previously compiled and used only `propext`,
`Classical.choice`, and `Quot.sound`. The module-system port is a new validation
event and must pass a fresh build, axiom audit and Comparator check; earlier
results do not certify the changed artifacts. See `submission/README.md` for
the current evidence and pending gates.
