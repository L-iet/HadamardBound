# Verification and submission

The default build includes the completed unconditional proof entry points.
The six mathlib-only Challenge placeholders are independent specifications;
no proof imports them. Solution supplies actual proofs without additional
quantitative hypotheses. Local Comparator and NanoDa replay have passed.
See verification.json for hashes, exact scope and checker evidence.

Run the checks in the root README. `python scripts/check_submission.py --ready`
checks the completed local preparation gates. `lake comparator --config
comparator.json` on Linux performs a sandboxed source-build comparison when
bubblewrap is usable. The export-based diagnostic script explicitly does not
sandbox the source build. Palomar repeats verification in its own sandbox;
no remote registry acceptance is claimed.

The responsible author and maintainer is Joshua Mark, ORCID
https://orcid.org/0009-0003-5905-2382. Project code is Apache-2.0; all pinned
Lake packages have Apache-2.0 or MIT licences (mathlib-licenses.json).
The repository root is this Lean directory. No commit was made by this work;
any future submission must identify a public immutable commit containing
all project source files and comparator.json.
