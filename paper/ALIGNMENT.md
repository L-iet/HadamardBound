# Manuscript and proof alignment

The six independently specified targets in Challenge.lean are proved in
HadamardMultibase/CompleteResults.lean and exported by Solution.lean:
sparse representations, Hadamard existence, least exponent, quantitative
gaps, subpolynomial gaps and flat orthogonal matrices. The latter five are
in HadamardMultibase.Complete; the sparse theorem is
HadamardMultibase.sparseRepresentationBound. These proofs have no additional
sparse-representation or quantitative-separation hypotheses.

The project also proves unconditional sign-matrix conditioning and general
independent multi-base sparse/covering bounds when a generator is two.
HadamardOrder uses mathlib's integer Matrix.IsHadamard; logScale is
log n / log(log n). Gap starting points are natural numbers, and the
flatness theorem requires 0 < epsilon < 1/2, ensuring a positive denominator.
Finite initial sparse cases are included. The arbitrary-digit theorem cited
in the manuscript is background, not a separately formalized result.

The formal sparse route proves that irrational ratios of logarithms of
natural integers >= 2 are not Liouville. Polynomial rotation separation,
mesh approximation and a greedy sum argument then supply the required
uniform sparse bound. The logarithm proof is independently written from
mathlib using auxiliary functions and stable interpolation; no additional
proof code is imported. See submission/CLASSICAL-REWORK.md.

Challenge is a mathlib-only specification with six intentional placeholder
proofs. It is excluded from all proof imports; Comparator compares its
statements against the completed Solution proof terms. Local verification
is recorded in submission/verification.json. Registry acceptance, novelty,
practical constants and independent human review are not asserted.
