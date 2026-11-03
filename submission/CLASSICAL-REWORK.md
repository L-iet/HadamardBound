# Independently written logarithm-ratio proof

The proof is complete in `HadamardMultibase/LogarithmSeparation.lean`:

- `not_liouville_log_ratio`: if a,b >= 2 are natural integers and
  log b/log a is irrational, that ratio is not Liouville.
- `polynomialRotationSeparation_log_ratio`: the polynomial separation
  condition needed by the rotation and greedy sparse-representation argument.

All 204 declarations in the logarithm proof are axiom-audited. They use only
mathlib and project-owned Apache-2.0 code, with the standard Lean axioms.
No further proof-source dependency is needed.

## Argument

Assume the ratio is Liouville. `BakerLiouvilleReduction` produces arbitrarily
large integer heights h and rational slopes p/q with q <= exp h, bounded
slope, and logarithmic defect smaller than exp(-A*h) for any fixed A.

Fix a large natural multiplier v, width L=v^6, and derivative budgets
k_j=4^(20-j)*v^8. The auxiliary unknowns have block-degree indices below
h*(L+1), and two frequency indices at most L. The bounded integer kernel
construction in `BakerInitialAuxiliary` gives a nonzero integer vector of
exponentially bounded height, with exact rational comparison equations on
the initial h integer nodes and mixed indices below k_0. There are
h*(L+1)^3 unknowns versus h*k_0^2 equations.

`BakerDenominators` and `BakerDenominatorGrowth` give denominators dividing
lcm(1,...,h)^u*q^r, independent of the evaluation node. `BakerUniformGrowth`
and `BakerUniformPerturbation` keep exponential rates explicit and absorb
fixed polynomial factors into a lower threshold on h.

`BakerInterpolation` through `BakerGridExtrapolation` prove stable Hermite
interpolation using Cauchy divided differences on repeated integer nodes.
The coefficient majorant is eps*(2*k)^n/(n+1-k)!, avoiding a spurious
h*log h loss. The derivative recurrence in `BakerMixedDerivatives` turns
small mixed values into derivative data; `BakerRectangularJets` and
`BakerGridStep` carry out an analytic extrapolation step.

`BakerArithmeticStep` converts this analytic smallness into exact rational
zeros using the denominator bound. At stage j the grid has h*v^j nodes;
the rectangle budget shrinks by four while the grid grows by v. The outer
circle has radius h*v^(j+2). `BakerParameters` and `BakerRateInequalities`
prove that a sufficiently large fixed v makes contour decay dominate the
coefficient height, boundary growth and arithmetic threshold at every stage.
`BakerFiniteExtrapolation` performs all twenty stages with one uniform
height threshold and accuracy rate.

The final grid has at least h*(L+1)^3 nodes. `BakerZeroGridContradiction`
reindexes the zeroth comparison sum into the true distinct frequencies
lambda*log a+mu*log b. The fully proved real exponential-polynomial zero
count and block-polynomial linear independence contradict the nonzero
coefficient vector. Thus the assumed Liouville approximation is impossible.

`CompleteResults` then discharges the sparse input of every final Hadamard
endpoint, plus the general independent multi-base sparse/covering results
with a generator equal to two. Comparator uses the separate mathlib-only
Challenge statements; no proof imports Challenge.

## Mathematical provenance

Michel Waldschmidt, *Linear Independence Measures for Logarithms of Algebraic
Numbers* (2003), especially quantitative interpolation and Lemma 1.12:
https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/LN1819-2003.pdf.
This is a mathematical reference. The Lean code, parameter choices and
assembly above are independently written from mathlib; no external proof
supplement code is imported. Reading a mathematical paper is distinct from
copying its implementation.
