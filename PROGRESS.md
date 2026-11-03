# Proof status

The unconditional results are proved in HadamardMultibase/CompleteResults.lean.
The entire default build passes on Lean/mathlib 4.35.0. No new Git commits.

The independent logarithm-ratio proof is complete: not_liouville_log_ratio,
then polynomialRotationSeparation_log_ratio, sparse representations, and the
Hadamard construction transfer. All 204 logarithm proof lemmas and 357
principal project declarations pass the standard three-axiom audit.

The exact six target statements remain independently specified in Challenge,
whose placeholders are excluded from every proof entry point. Solution has
actual proofs and no additional Diophantine hypotheses. Comparator results,
provenance checks and any external-verification limits are recorded in
submission/verification.json. No registry acceptance or human review is claimed.
