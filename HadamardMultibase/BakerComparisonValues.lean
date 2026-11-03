/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerDenominatorGrowth

@[expose] public section

/-!
# Rational comparison values and their common denominators

These are the arithmetic comparison values used when a rational slope p/q
approximates log b / log a. Their common denominator is independent of the
evaluation node and the polynomial degree index. Analytic estimates comparing
these expressions with exponential derivatives are a separate obligation.
-/

namespace HadamardMultibase

noncomputable def bakerComparisonValue (h d u v l lam mu : ℕ) (p : ℤ) (q a b : ℕ) : ℚ :=
  ((Polynomial.hasseDeriv u (bakerBlock h d)).eval (l : ℚ)) *
    ((lam : ℚ) + (mu : ℚ) * p / q) ^ v *
    (a : ℚ) ^ (lam * l) * (b : ℚ) ^ (mu * l)

theorem bakerComparison_integer_multiple {h q : ℕ} (hh : 0 < h) (hq : 0 < q)
    (d u v l lam mu : ℕ) (p : ℤ) (a b : ℕ) :
    HasIntegerMultiple (Nat.lcmUpto h ^ u * q ^ v)
      (bakerComparisonValue h d u v l lam mu p q a b) := by
  have hp := bakerBlock_hasse_common_denominator hh d u (l : ℤ)
  have hs := (rational_slope_integer_multiple q hq p (lam : ℤ) (mu : ℤ)).pow v
  have hm := (hp.mul hs).mul_int ((a : ℤ) ^ (lam * l) * (b : ℤ) ^ (mu * l))
  simpa [bakerComparisonValue, mul_comm, mul_left_comm, mul_assoc] using hm

theorem bakerComparison_sum_integer_multiple {ι : Type*} {h q : ℕ}
    (hh : 0 < h) (hq : 0 < q) (s : Finset ι) (c : ι → ℤ)
    (d lam mu : ι → ℕ) (u v l : ℕ) (p : ℤ) (a b : ℕ) :
    HasIntegerMultiple (Nat.lcmUpto h ^ u * q ^ v)
      (∑ i ∈ s, (c i : ℚ) * bakerComparisonValue h (d i) u v l (lam i) (mu i) p q a b) := by
  apply HasIntegerMultiple.sum
  intro i _
  exact (bakerComparison_integer_multiple hh hq (d i) u v l (lam i) (mu i) p a b).mul_int (c i)

theorem bakerComparison_sum_eq_zero_of_small {ι : Type*} {h q : ℕ}
    (hh : 0 < h) (hq : 0 < q) (s : Finset ι) (c : ι → ℤ)
    (d lam mu : ι → ℕ) (u v l : ℕ) (p : ℤ) (a b : ℕ)
    (hsmall : |((∑ i ∈ s, (c i : ℚ) *
      bakerComparisonValue h (d i) u v l (lam i) (mu i) p q a b : ℚ) : ℝ)| <
        1 / ((Nat.lcmUpto h ^ u * q ^ v : ℕ) : ℝ)) :
    (∑ i ∈ s, (c i : ℚ) *
      bakerComparisonValue h (d i) u v l (lam i) (mu i) p q a b) = 0 := by
  exact rat_eq_zero_of_small_abs (mul_pos (pow_pos (Nat.lcmUpto_pos h) u) (pow_pos hq v))
    (bakerComparison_sum_integer_multiple hh hq s c d lam mu u v l p a b) hsmall

end HadamardMultibase
