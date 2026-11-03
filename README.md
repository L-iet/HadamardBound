# Hadamard multi-base formalization

Unconditional Lean proofs of sparse multi-base representations and asymptotic
Hadamard existence, gaps, flatness and conditioning, maintained by Joshua Mark
([ORCID](https://orcid.org/0009-0003-5905-2382)).

Lean 4.35.0 and mathlib v4.35.0 are pinned. Project code is Apache-2.0;
the nine Lake packages use Apache-2.0 or MIT. See [DEPENDENCIES.md](DEPENDENCIES.md).
No additional proof-source download is required.

## Build and verification

```sh
lake exe cache get
lake build
python scripts/check_submission.py
python scripts/audit_mathlib_licenses.py
python scripts/audit_classical_rework.py
python scripts/audit_axioms.py
python scripts/export_comparator.py
```

On Linux, `bash scripts/verify-comparator.sh` compares those exports and checks
proof terms with Lean's kernel. This diagnostic does not sandbox the source
build. For a sandboxed run use `lake comparator --config comparator.json` on
Linux, or submit the repository to Palomar. Local checks are not registry acceptance.

## Results

Import `HadamardMultibaseComplete` (or `Solution`). The main theorem is
`HadamardMultibase.Complete.main_bound`: for every sufficiently large odd p,
there is a Hadamard matrix of order 2^t*p with t = O(log p / log log p).
The same namespace proves the least-exponent bound, quantitative and
subpolynomial gaps, flat orthogonal matrices for 0 < epsilon < 1/2,
approximate Hadamard conditioning, and general independent multi-base
sparse representation and covering lower bounds when one generator is two.

`HadamardMultibase.not_liouville_log_ratio` proves that an irrational ratio
log b/log a, for natural a,b >= 2, is not Liouville. The proof uses integer
auxiliary coefficients, block binomial polynomials, denominator estimates,
stable complex interpolation, twenty extrapolation stages and a real
exponential-polynomial zero count. All its code is independently written
from mathlib; see [proof details](submission/CLASSICAL-REWORK.md).

The local axiom audit checks 357 principal declarations, including 204
quantitative logarithm lemmas and all final endpoints. Only propext,
Classical.choice and Quot.sound occur. The proof import closure contains no
holes or custom axioms. `Challenge.lean` deliberately contains six placeholder
proofs for independent statement comparison; no proof imports it.

[Verification evidence](submission/verification.json) records the actual checks.
[Manuscript alignment](paper/ALIGNMENT.md) explains the precise scope.
No novelty determination, independent human review or registry acceptance is claimed.
