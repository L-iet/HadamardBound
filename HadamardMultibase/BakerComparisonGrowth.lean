/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerComparisonValues
public import HadamardMultibase.BakerDerivativeGrowth

@[expose] public section

/-! # Explicit arithmetic size of the comparison entries

The bound keeps every dependence on the block size, derivative orders,
integer node and rational slope visible. Clearing the row denominators
therefore supplies an explicit coefficient-height estimate for the finite
integer system, without a new Diophantine hypothesis.
-/

namespace HadamardMultibase

open Polynomial

theorem bakerBlock_hasse_real_abs_le_two_pow (h d u l : ℕ) :
    |(((hasseDeriv u (bakerBlock h d)).eval (l : ℚ) : ℚ) : ℝ)| ≤
      (2 : ℝ) ^ ((l + 1 + h) * (d / h) + (l + 1 + d % h)) := by
  have hz : ‖(l : ℂ)‖ ≤ (l : ℝ) := by simp
  have he := bakerBlock_hasse_norm_le_two_pow h d u l (l : ℂ) hz
  have hcast : (hasseDeriv u (bakerBlock h d)).eval₂ (Rat.castHom ℂ) (l : ℂ) =
      (((hasseDeriv u (bakerBlock h d)).eval (l : ℚ) : ℚ) : ℂ) := by
    simp
  rw [hcast, Complex.norm_ratCast] at he
  exact he

theorem rational_slope_abs_bound (q lam mu : ℕ) (hq : 0 < q) (p : ℤ) :
    |(lam : ℝ) + (mu : ℝ) * p / q| ≤
      (lam : ℝ) + (mu : ℝ) * |(p : ℝ)| / q := by
  calc |(lam : ℝ) + (mu : ℝ) * p / q|
      ≤ |(lam : ℝ)| + |(mu : ℝ) * p / q| := abs_add_le _ _
    _ = _ := by
      rw [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg lam),
        abs_of_nonneg (Nat.cast_nonneg mu),
        abs_of_pos (show (0 : ℝ) < q by exact_mod_cast hq)]

theorem bakerComparison_real_abs_bound {q : ℕ} (hq : 0 < q)
    (h d u v l lam mu : ℕ) (p : ℤ) (a b : ℕ) :
    |((bakerComparisonValue h d u v l lam mu p q a b : ℚ) : ℝ)| ≤
      (2 : ℝ) ^ ((l + 1 + h) * (d / h) + (l + 1 + d % h)) *
        ((lam : ℝ) + (mu : ℝ) * |(p : ℝ)| / q) ^ v *
        (a : ℝ) ^ (lam * l) * (b : ℝ) ^ (mu * l) := by
  simp only [bakerComparisonValue, Rat.cast_mul, Rat.cast_pow, Rat.cast_add,
    Rat.cast_div, Rat.cast_natCast, Rat.cast_intCast]
  have ha : |(a : ℝ) ^ (lam * l)| = (a : ℝ) ^ (lam * l) := abs_of_nonneg (by positivity)
  have hb : |(b : ℝ) ^ (mu * l)| = (b : ℝ) ^ (mu * l) := abs_of_nonneg (by positivity)
  rw [abs_mul, abs_mul, abs_mul, ha, hb, abs_pow]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg b) _)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (Nat.cast_nonneg a) _)
  apply mul_le_mul (bakerBlock_hasse_real_abs_le_two_pow h d u l)
    (pow_le_pow_left₀ (abs_nonneg _) (rational_slope_abs_bound q lam mu hq p) v)
    (by positivity) (by positivity)

end HadamardMultibase
