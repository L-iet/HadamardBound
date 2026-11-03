# Informal and formal statement alignment

The repository-local manuscript is `paper/hadamard_multibase_note.tex`.
It is based on the 10 September 2026 research draft and has an explicit
2 November 2026 revision date. `source-origin.json` identifies the original
bytes. The outer directory's manuscript and PDF were not modified and are not
required to build or understand this repository.

## Compared declarations

`Challenge.lean` contains six deliberate proof holes and imports only mathlib.
`Solution.lean` imports the actual proof development and never imports Challenge.
All constants below are uniform in the variables quantified after them.

| Manuscript claim | Compared Lean declaration | Correspondence |
| --- | --- | --- |
| Sparse Golay decomposition | `HadamardMultibase.sparseRepresentationBound` | Every q > 2 is a sum of distinct 2^a*10^b, with at most K log q/log log q terms. Finite initial q are included. |
| Main Hadamard bound | `HadamardMultibase.Complete.main_bound` | For every sufficiently large odd natural p, an actual positive integer Hadamard order 2^t*p exists with t <= C log p/log log p. p need not be prime. |
| Least-exponent version | `HadamardMultibase.Complete.tau_bound` | The least admissible exponent obeys the bound. Existence is proved separately, and no empty-set default is used. |
| Quantitative gaps | `HadamardMultibase.Complete.quantitative_gap_bound` | Every natural y <= x has a strictly larger Hadamard order within exp(D log x/log log x). |
| Subpolynomial consequence | `HadamardMultibase.Complete.subpolynomial_gap_bound` | The same uniform gap is <= x^epsilon eventually, for every epsilon > 0. |
| Flat orthogonal matrices | `HadamardMultibase.Complete.flat_orthogonal_bound` | An n-by-n real M with M.transpose*M = 1 and entries bounded by 1/(sqrt n - n^epsilon), for 0 < epsilon < 1/2. |

`HadamardOrder` uses mathlib's `Matrix.IsHadamard` over integers. Hence its
unitary entries are exactly ±1; this is not a complex-Hadamard relaxation.
`logScale` uses natural logarithms. Eventual thresholds avoid small arguments
where log log is zero or negative. Sparse representations use a `Finset`, so
distinctness is part of the definition.

## Further proved results outside this Comparator surface

The nine unconditional endpoints in `integration/CompleteResults.lean` also
include general and Golay covering bounds and approximate-Hadamard conditioning.
For r independent natural bases >= 2 containing 2, the covering theorem gives
exp(c*m*log m) <= ell_m <= exp((r-1+eta)*m*log m) eventually for every eta > 0.
The minimum missing positive integer allows repeated summands. Its existence
is proved, and finite initial cases are handled explicitly.

For every delta > 0, the conditioning results give actual sign matrices and
the attained optimum with condition number <= 1+n^(-1/4+delta) eventually.
The condition number is the largest/smallest Euclidean singular-value ratio,
with infinity for singular matrices. These results receive the project axiom
audit, but this first Comparator configuration does not independently compare
their definitions. A successful six-claim Comparator report must not be
advertised as a Comparator certification of all nine endpoints.

## Proof route and scope

The construction proves explicit binary seeds, Turyn multiplication, and the
Craigen consequence with exact order 4^(r+1)*(2L+1). It does not formalize all
of Craigen's abstract signed-group theory.

The paper cites Krenn--Suppakitpaisarn--Wagner's general multi-base theorem.
The formal proof instead uses the pinned logarithm-ratio proof described in
DEPENDENCIES.md, obtains polynomial Diophantine separation, constructs a
one-sided rotation mesh, and proves the greedy estimate and finite cases.
The full arbitrary-digit theorem and its worst-case Hamming-weight lower
bound remain cited background, not separately formalized results.

For conditioning, the formal proof supplies a trace-moment concentration
estimate with logarithmic loss. That loss is absorbed for the strict exponent
claimed. It does not import the full general random-matrix result cited by the
informal paper.

## Corrections and qualifications

* The old flatness range "every epsilon > 0" was false for the displayed
  reciprocal. The local paper and Challenge require 0 < epsilon < 1/2.
* Gap predicates use nonnegative natural starting points. An unrestricted
  quantifier over negative reals is not claimed. The local grid proof reflects
  this restriction; real-variable interpolation is not a separate Lean theorem.
* The general covering proof handles the finite initial interval separately.
* The background multi-base statement now specifies nonnegative digits containing
  zero, and its 0/1 specialization is asserted only after verifying 0/1
  representability. No arbitrary-digit-to-binary conversion is claimed.
* No practical numerical C, K or crossover threshold is extracted.
* The manuscript is a research draft. No independent human mathematical review,
  proof of novelty, journal acceptance or registry endorsement is claimed.
* Qualitative subpolynomial Hadamard gaps were already reported by Brent,
  Osborn and Smith in connection with W. D. Smith's unpublished work. The
  quantitative rate and the uniform odd-multiplier bound need a separate
  priority assessment. Search-engine absence is not evidence of first discovery.

## Reuse for Lax

The small statement surface, separate proof environment and local paper are
also useful for Lax. Lax additionally requires its own concept/proof package
layout, annotations and supported environment. No Lax package or validation
is claimed here; Palomar preparation takes priority.
