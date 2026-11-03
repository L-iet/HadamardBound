# Hadamard multi-base formalization

Lean formalization of `paper/hadamard_multibase_note.tex` (2 November 2026
formalization-aligned revision of the 10 September research draft). Uses Lean **4.35.0** and mathlib **v4.35.0**, the latest
stable mathlib release checked on 27 October 2026. `lake-manifest.json` locks
the dependency revisions; mathlib resolves to
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Palomar preparation

Joshua Mark is the author and responsible maintainer (ORCID
[0009-0003-5905-2382](https://orcid.org/0009-0003-5905-2382)). This directory is
the Git repository root; no files in its parent directory are required.
`Challenge.lean`, `Solution.lean` and `comparator.json` package six principal
claims for independent comparison. See [submission/README.md](submission/README.md),
[DEPENDENCIES.md](DEPENDENCIES.md), [paper/ALIGNMENT.md](paper/ALIGNMENT.md) and
`formalization.yaml` for exact scope, provenance, automation and limitations.

The module-system port passed a fresh 5,811-job build and the 156-declaration
axiom audit on 2 November 2026. The full sandboxed Comparator passed all six packaged claims with con-ron,
NanoDa and Lean default kernels, exit 0. The exact scope and evidence are
recorded in submission/verification.json. Redistribution permission for original additions in the external
logarithm proof remains unresolved. The root Apache licence does not relicense
those sources. No Palomar or Lax submission or registration is claimed.

## Build

Install [elan](https://lean-lang.org/install/) and Python 3.9+, then run from this directory:

```sh
python scripts/prepare_logarithms.py  # reconstruct the checksum-pinned module-system source
python scripts/check_submission.py   # structural preflight; not a kernel check
lake update                 # first setup; downloads dependencies and mathlib cache
lake exe cache get          # if cache fetching needs to be retried
lake build
lake env lean Audit.lean     # inspect the axioms used by the principal proofs
```

For an existing checkout, prepare the external sources if missing, fetch the
mathlib cache, then build. Open this directory in VS Code with the Lean 4 extension.
The final Windows build used `$env:LEAN_NUM_THREADS = '4'`; supplement modules use
two compiler threads each.

All seven milestone proofs passed pre-port verification. On Windows on 28 October 2026,
`lake --rehash build` passed (5,809 jobs), `lake env lean Audit.lean` audited
156 declarations using only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` axioms, and the import example below compiled in the normal Lake
environment. Source scans found no `sorry`, `admit`, custom `axiom`, or
`native_decide` in the 86 project Lean files or 1,001 external dependency files.

## Use

Start a Lean client file with:

```lean
module

import HadamardMultibaseComplete

#check HadamardMultibase.sparseRepresentationBound
#check HadamardMultibase.Complete.main_bound
#check HadamardMultibase.Complete.covering_bounds
#check HadamardMultibase.Complete.optimalConditionNumber_bound
```

The complete entry point and the prepared supplement now use Lean's module
system. Fresh validation of that port is recorded separately from the older
legacy-mode evidence.

## Current scope and trust boundary

The project uses mathlib's existing `Matrix.IsHadamard`, specialized to integer
matrices. This ensures entries are ±1, rather than allowing complex unit entries.
`HadamardOrder` additionally requires positive order. Mathlib already supplies
Kronecker products, reindexing, and the divisibility-by-four obstruction.

* `Basic.lean`: Hadamard orders one and two; closure under products, doubling,
  and powers of two; the obstruction for orders above two; the
  minimum exponent `tau` with an existence witness; the two Golay monoids;
  representations with repeated or distinct summands; the specialized sparse
  representation bound as a proposition.
* `Golay.lean`: binary sequences, aperiodic autocorrelation, Golay pairs and
  lengths; the trivial pair of length one; correlation cancellation at all
  positive shifts.
* `GolaySeeds.lean`: explicit pairs of lengths 2, 10, and 26, checked at every
  shift by kernel reduction with `decide`.
* `GolayAlgebra.lean`, `GolayPolynomial.lean`, `GolayOperations.lean`: Laurent
  energy identities; the autocorrelation characterization in both directions;
  encoding of addition, subtraction, reversal, dilation, and tensor products.
* `Turyn.lean`: the binary product construction, preservation of complementarity,
  closure of Golay lengths under products and powers, and the unconditional
  theorem `golayLength_monoid₃`. The input `GolayFamily` is discharged by
  the proved theorem `golayFamily`.
* `Arithmetic.lean`: multiplicative independence of 2,10 and 2,10,26 with
  arbitrary integer exponents, unique exponent tuples, and binary representability.
* `LogIndependence.lean`: irrationality of `log(10)/log(2)` from that independence.
* `SparseGreedy.lean`, `GreedyLogScale.lean`, `ClippedLogScale.lean`,
  `SparseApproximation.lean`, `LogarithmicApproximation.lean`: the greedy
  representation proof from a quantitative logarithmic approximation estimate.
  A remainder at most `C*n/(log n)^κ` eventually decreases the logarithmic
  budget by at least `κ/4`. The proof handles distinctness and all finite initial
  cases, and applies to any positive alphabet representing every natural number.
  `integration/LogarithmRatioInput.lean` discharges the approximation input.
* `RotationMesh.lean`, `QuantitativeRotation.lean`, `LogMeshAsymptotics.lean`,
  `ApproximationFromSeparation.lean`: Dirichlet approximation, a direct
  one-sided rotation mesh, lifting to natural exponents, and the polynomial
  logarithmic approximation rate. Together these reduce the sparse theorem
  to `PolynomialRotationSeparation (log 10 / log 2)`. The construction avoids
  the paper's discrepancy theorem. The verified external logarithm-ratio
  result supplies polynomial separation; qualitative irrationality alone
  would not establish it.
* `CoveringFromSeparation.lean`: the corresponding general covering lower
  deduction for any positive, representable alphabet containing two generators,
  under their polynomial separation hypothesis.
* `NonLiouvilleSeparation.lean`: polynomial rotation separation is equivalent
  to irrationality together with failure of mathlib's `Liouville` predicate.
  The proof includes denominator one and the uniform constant.
* `PowerMonoidRepresentation.lean`: monoid closure, binary representability
  whenever a generator is two, and the general sparse and covering lower
  deductions from separation for a second generator.
* `GeneralIndependence.lean`: the integer-exponent definition of independence
  for arbitrary generator families; independence of every pair and irrationality
  of its logarithm ratio; the proved 2/10 and 2/10/26 instances.
* `CraigenBlock.lean`: the normalized block-merge energy identity that begins
  Craigen's construction.
* `SignedPermutation.lean`, `CraigenCirculant.lean`, `CraigenShuffle.lean`,
  `CraigenSupport.lean`, `CraigenScalar.lean`, `CoefficientSpace.lean`,
  `CraigenInduction.lean`, `CraigenHadamard.lean`: the recursive construction
  from supplementary quasisymmetric ternary sequences to Hadamard matrices.
  This proves `hadamardOrder_of_supplementary_sequences`, the direct-matrix
  version of Corollary 3.8 of Livinskyi's thesis, including the exact dimension.
* `PeriodicAlgebra.lean`, `PeriodicGolay.lean`: finite-group convolution,
  its circulant matrix representation, transport of Golay energy, and the
  reflected-pair construction with total periodic energy 4n.
* `PackedPositions.lean`, `PeriodPositions.lean`, `PartitionedFamily.lean`,
  `GolayPlacement.lean`, `CraigenTransfer.lean`: disjoint symmetric placement
  of arbitrary Golay pairs, full support, supplementary energy, and the proved
  theorem `craigenTransfer` with order `4^(r+1)*(2*L+1)`.
* `Transfer.lean`: the Golay-pair specialization of Craigen's theorem as an
  explicit proposition; proofs that a finite sparse decomposition gives order
  `2^(2*card + 2) * (2*q + 1)` and bounds `tau`; the quantitative conditional
  transfer `t ≤ 2*K*logScale(q) + 2`. Existence for every `2*q+1`, including
  the small cases, follows from the Craigen input alone using q trivial pairs.
  All larger exponents are then available using Sylvester doubling.
* `Asymptotics.lean`: eventual monotonicity of the logarithmic scale,
  its sublogarithmic limit, and the analytic transfer to the main bound in p.
* `Gaps.lean`: the common-exponent grid argument, finite-exception uniformization,
  the quantitative exponential gap estimate, and its subpolynomial consequence.
* `Covering.lean`: the exact binomial bound for finite-alphabet sums, the
  pigeonhole step for missing integers, and the minimum covering number with
  an existence witness.
* `MultiBase.lean`: general finite-base monoids, finite truncations, bounds on
  each exponent, and the bound `T(N) ≤ (Nat.log 2 N + 1)^r`.
* `CoveringExistence.lean`: exponential domination of fixed polynomials and
  existence of a missing positive integer for every fixed summand count,
  for any finite family of bases at least two. Livinskyi's covering function
  for `S(2,10,26)` is defined with this proved existence witness.
* `CoveringEstimates.lean`, `CoveringUpper.lean`: real logarithmic truncation
  counts, the factorial saving in stars-and-bars, vanishing lower order terms,
  and the unconditional upper bound
  `coveringNumber ≤ exp((r-1+η)*m*log(m))` eventually for every `η > 0`.
  The specialization to `S(2,10,26)` has leading coefficient 2.
* `CoveringLower.lean`: inversion of an eventual logarithmic representation
  estimate, with finite initial cases handled by ones. The covering lower bound
  for `S(2,10,26)` is proved conditional on `SparseRepresentationBound`.
* `SubmatrixOrthogonalization.lean`, `SubmatrixFlatness.lean`: block
  orthogonalization and the exact entry bound `1/(s-k)` for an orthogonal
  block matrix whose entries are bounded by `1/s`, when `0 < k < s`.
* `NormalizedHadamard.lean`, `HadamardFlatness.lean`: normalization and
  truncation of integer Hadamard matrices; the eventual flat orthogonal matrix
  corollary for `0 < ε < 1/2`, conditional only on the sparse input.
* `SpectralPerturbation.lean`, `ConditionNumber.lean`,
  `MatrixSpectralPerturbation.lean`: bounds on singular values near a scaled
  isometry; an extended-real condition number that is infinite for singular
  maps; the Euclidean operator-norm perturbation estimate and relative bound
  `conditionNumber ≤ 1 + 4δ` for `0 ≤ δ ≤ 1/2`.
* `FiniteRounding.lean`, `RoundingVariance.lean`, `RoundingMoments.lean`:
  independent rounding as a finite probability distribution, exact means and
  variances, row/column variance `n-1/u²`, cancellation of singleton centered
  coordinates, and higher-moment bounds retaining the variance factor.
* `MatrixTraceMoments.lean`, `MatrixWalkExpansion.lean`,
  `RoundingWordMoments.lean`, `RoundingWalkMoments.lean`: Euclidean operator
  norm bounded by Gram trace moments, exact walk expansions, grouping by random
  coordinates, and reduction of rounding to a deterministic weighted walk sum.
  Singleton coordinates vanish; a surviving word uses at most half as many
  distinct coordinates as factors.
* `WeightedTrees.lean`, `WalkPatterns.lean`, `WalkEdgeCounting.lean`,
  `WalkTreeLabels.lean`, `WalkVarianceProducts.lean`, `WalkSumBound.lean`:
  discovery-tree encoding, faithful unordered-edge counting, and the quantitative
  weighted-walk bound from a variance row-sum estimate.
* `MomentConcentration.lean`, `MomentNormBound.lean`: independent symmetric
  rounding has a sample with operator norm at most
  `4*(2*max(1, Nat.clog 4 N)+1)*sqrt(v)` in dimension N when v≥1 bounds the
  variance row sums. This is proved by trace moments, with a logarithmic loss
  sufficient for the strict exponent in the application.
* `SymmetricDilation.lean`, `DilationRounding.lean`: compression of the symmetric
  dilation in the Euclidean norm; independent rounding of a flat orthogonal
  matrix to a sign matrix, with an explicit operator-norm error bound.
* `RoundingScale.lean`, `RoundingAsymptotics.lean`, `ApproximateHadamard.lean`,
  `OptimalConditionNumber.lean`: absorb the logarithmic concentration loss,
  prove the approximate-Hadamard condition-number corollary, and define the
  optimal sign-matrix condition number with an attained minimum. The theorem
  `optimalConditionNumber_bound` proves `κ(n) ≤ 1+n^(-1/4+δ)` eventually for
  every `δ > 0`, conditional only on the sparse representation input.
* `Results.lean`: unconditional existence for every odd multiplier after scaling
  by a power of two; reusable main and gap deductions from a sparse bound.
* `integration/LogarithmRatioInput.lean`: the proved theorem
  `sparseRepresentationBound` and separation for every independent generator
  pair. `integration/CompleteResults.lean` supplies all closed final endpoints.

There are no project axioms or `sorry` placeholders in the proof development.
Challenge's six deliberate statement holes are isolated from Solution and are
excluded from that assertion. The closed final theorems
are in `HadamardMultibase.Complete`; all Golay, Craigen and sparse inputs are
discharged. Lower-level modules retain their reusable conditional interfaces.

The quantitative logarithm-ratio theorem comes from the Lean supplement to
[arXiv:2610.28079v1](https://arxiv.org/abs/2610.28079). Its exact endpoint and
approximation definitions were inspected; its 1,000-file theorem closure and
one additional elementary adapter dependency compiled under our pinned Lean.
The external theorem, five adapters and nine final endpoints all passed axiom
audits with only the standard three axioms. `scripts/audit_logarithms.py`
reproduces this isolated verification. It pins the source archive by SHA-256
and applies the recorded Lean 4.35 compatibility patches in
`integration/logarithms-4.35-patches.json`. The cached sources retain their
upstream notices. The isolated verifier now uses the same module-system source;
`scripts/prepare_logarithms.py` reconstructs that tree in
`vendor/logarithms` and records all source hashes. See DEPENDENCIES.md for the
unresolved redistribution terms. The Craigen interface proves
the exact consequence used by this manuscript.

`tau p h` requires a proof that some exponent exists. This prevents `Nat.find`
from silently assigning zero when existence is unavailable. It is defined for
any multiplier with such a proof; oddness is needed by the paper's application,
not by the minimum operation itself.

## Milestone status

1. **Complete:** explicit seeds, Turyn multiplication, `GolayFamily`, and the
   full family with the factor 26.
2. **Complete:** the full supplementary-sequence-to-Hadamard construction is
   proved directly with matrix-valued coefficients, avoiding a separate abstract
   signed-group library. Golay pairs are placed with disjoint symmetric supports
   covering a finite group of order `4*L+2`. The energy and exact dimension
   give the unconditional theorem `craigenTransfer`.
3. **Complete:** independence, binary representability, logarithmic
   estimates, distinct greedy sums and finite-case absorption are proved.
   The verified logarithm-ratio theorem discharges the separation input and
   gives the unconditional theorem `sparseRepresentationBound`.
4. **Complete:** the analytic transfer and
   constant absorption are proved with explicit eventual thresholds. Small odd
   multipliers are handled in the uniform envelope.
5. **Complete:** doubling, uniformization,
   the grid construction, the quantitative gap bound, and the subpolynomial
   bound are proved. The pointwise gap formulation implies consecutive-order
   gap bounds via `consecutive_gap_le`.
6. **Complete:** finite multiset counting, the missing-integer pigeonhole step,
   general monoid truncation counts, existence for every fixed m, and the
   witness-based minimum are proved. The upper covering bound, including the
   sharp leading coefficient r−1, is proved. The sparse theorem supplies the
   lower bound for every independent base family containing two, and its Golay
   specialization. `Complete.covering_bounds` gives both sides together.
7. **Complete:** submatrix orthogonalization and its exact entry estimate are
   proved. Normalization, truncation, and transfer from the gap bound give
   eventual flat orthogonal matrices.
   Spectral perturbation and the finite-dimensional condition-number estimate
   are proved. Independent rounding, variance formulas and basic centered
   moments are proved. A generic symmetric operator-norm concentration bound
   with logarithmic loss is proved, and applied to the symmetric dilation of
   entrywise rounding. Spectral perturbation and absorption of the logarithmic
   factor give the final condition-number consequence. The optimal condition
   number is a genuine attained minimum over the finite set of sign matrices.

All seven milestone proofs, the final default Lake build, and the combined
axiom audit have passed.

## Draft issues to resolve during formalization

The flat-orthogonal-matrix corollary is stated for every ε > 0. Its displayed
right-hand side `1/(sqrt(n) - n^ε)` is negative when ε > 1/2 and undefined at
ε = 1/2 in ordinary real notation. The meaningful range of that statement is
`0 < ε < 1/2`; larger ε do not give a weaker version of the same inequality.
The repository-local manuscript corrects this range; the outer draft is untouched.

The formal covering proof handles the finite initial interval separately.
The gap statements quantify over natural-number orders, resolving the
manuscript's issue with unrestricted negative real y.

## Upstream references

* [Mathlib Hadamard matrices](https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/LinearAlgebra/Matrix/HadamardMatrix.lean)
* [Mathlib v4.35.0](https://github.com/leanprover-community/mathlib4/releases/tag/v4.35.0)
* [Alexeev--Jasper--Mixon, arXiv:2511.14653v1](https://arxiv.org/html/2511.14653v1),
  Lemmas 3 and 4 and the random-rounding argument in Section 2.
* The manuscript contains the bibliography for Golay, Turyn, Craigen,
  Livinskyi, Krenn--Suppakitpaisarn--Wagner, and Alexeev--Jasper--Mixon.
