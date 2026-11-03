/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerMixedGrowth

@[expose] public section

/-! # Initial arithmetic height bounds

On the first integer grid l<=h, block degree d<h(L+1) gives exponential
growth in h. Row denominators have the same dependence, uniformly in the
varying rational slope as long as q<=exp(h) and its frequencies are bounded.
-/

namespace HadamardMultibase

theorem bakerBlock_hasse_real_abs_le_uniform {h d L T l : ℕ} (hh : 0 < h)
    (hd : d < h * (L + 1)) (u : ℕ) (hl : l ≤ T * h) :
    |(((Polynomial.hasseDeriv u (bakerBlock h d)).eval (l : ℚ) : ℚ) : ℝ)| ≤
      (2 : ℝ) ^ (h * (T + 2) * (L + 1)) := by
  have hz : ‖(l : ℂ)‖ ≤ ((T * h : ℕ) : ℝ) := by
    rw [Complex.norm_natCast]
    exact_mod_cast hl
  have he := bakerBlock_hasse_norm_le_uniform hh hd u (l : ℂ) hz
  have hcast : (Polynomial.hasseDeriv u (bakerBlock h d)).eval₂ (Rat.castHom ℂ) (l : ℂ) =
      (((Polynomial.hasseDeriv u (bakerBlock h d)).eval (l : ℚ) : ℚ) : ℂ) := by simp
  rw [hcast, Complex.norm_ratCast] at he
  exact he

theorem bakerComparison_grid_abs_bound {h d L T l q a b : ℕ} (hh : 0 < h)
    (hd : d < h * (L + 1)) (hl : l ≤ T * h) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (u v lam mu : ℕ) (hlam : lam ≤ L) (hmu : mu ≤ L) (p : ℤ)
    {Γ : ℝ} (hΓ : 0 ≤ Γ) (hgamma : |(lam : ℝ) + (mu : ℝ) * p / q| ≤ Γ) :
    |((bakerComparisonValue h d u v l lam mu p q a b : ℚ) : ℝ)| ≤
      (2 : ℝ) ^ (h * (T + 2) * (L + 1)) * Γ ^ v * ((a * b : ℕ) : ℝ) ^ (L * (T * h)) := by
  have hp := bakerBlock_hasse_real_abs_le_uniform (T := T) hh hd u hl
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hpa : (a : ℝ) ^ (lam * l) ≤ (a : ℝ) ^ (L * (T * h)) :=
    pow_le_pow_right₀ haR (Nat.mul_le_mul hlam hl)
  have hpb : (b : ℝ) ^ (mu * l) ≤ (b : ℝ) ^ (L * (T * h)) :=
    pow_le_pow_right₀ hbR (Nat.mul_le_mul hmu hl)
  have haAbs : |(a : ℝ) ^ (lam * l)| = (a : ℝ) ^ (lam * l) := abs_of_nonneg (by positivity)
  have hbAbs : |(b : ℝ) ^ (mu * l)| = (b : ℝ) ^ (mu * l) := abs_of_nonneg (by positivity)
  simp only [bakerComparisonValue, Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_intCast]
  rw [abs_mul, abs_mul, abs_mul, haAbs, hbAbs, abs_pow, Nat.cast_mul, mul_pow]
  have hpoly : |(((Polynomial.hasseDeriv u (bakerBlock h d)).eval (l : ℚ) : ℚ) : ℝ)| *
      |(lam : ℝ) + (mu : ℝ) * p / q| ^ v ≤
      (2 : ℝ) ^ (h * (T + 2) * (L + 1)) * Γ ^ v :=
    mul_le_mul hp (pow_le_pow_left₀ (abs_nonneg _) hgamma v) (by positivity) (by positivity)
  calc _ ≤ ((2 : ℝ) ^ (h * (T + 2) * (L + 1)) * Γ ^ v) *
      (a : ℝ) ^ (L * (T * h)) * (b : ℝ) ^ (L * (T * h)) := by gcongr
    _ = _ := by ring

theorem bakerComparison_initial_abs_bound {h d L l q a b : ℕ} (hh : 0 < h)
    (hd : d < h * (L + 1)) (hl : l ≤ h) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (u v lam mu : ℕ) (hlam : lam ≤ L) (hmu : mu ≤ L) (p : ℤ)
    {Γ : ℝ} (hΓ : 0 ≤ Γ) (hgamma : |(lam : ℝ) + (mu : ℝ) * p / q| ≤ Γ) :
    |((bakerComparisonValue h d u v l lam mu p q a b : ℚ) : ℝ)| ≤
      (2 : ℝ) ^ (h * 3 * (L + 1)) * Γ ^ v * ((a * b : ℕ) : ℝ) ^ (L * h) := by
  simpa using bakerComparison_grid_abs_bound (T := 1) hh hd (by simpa using hl)
    ha hb u v lam mu hlam hmu p hΓ hgamma

theorem baker_comparison_denominator_exp_bound {h q K u v : ℕ}
    (hq : (q : ℝ) ≤ Real.exp h) (hu : u ≤ K) (hv : v ≤ K) :
    ((Nat.lcmUpto h ^ u * q ^ v : ℕ) : ℝ) ≤
      Real.exp ((Real.log 4 + 5) * (K : ℝ) * (h : ℝ)) := by
  have hpow : (q : ℝ) ^ v ≤ Real.exp ((v : ℝ) * h) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hq v
  have hc : 0 ≤ Real.log 4 + 4 := by have := Real.log_pos (show (1 : ℝ) < 4 by norm_num); linarith
  have huR : (u : ℝ) ≤ K := by exact_mod_cast hu
  have hvR : (v : ℝ) ≤ K := by exact_mod_cast hv
  calc ((Nat.lcmUpto h ^ u * q ^ v : ℕ) : ℝ)
      = (Nat.lcmUpto h : ℝ) ^ u * (q : ℝ) ^ v := by push_cast; rfl
    _ ≤ Real.exp ((Real.log 4 + 4) * (h : ℝ) * u) * Real.exp ((v : ℝ) * h) :=
      mul_le_mul (baker_lcm_power_bound h u) hpow (by positivity) (by positivity)
    _ = Real.exp (((Real.log 4 + 4) * (u : ℝ) + v) * h) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have huScaled := mul_le_mul_of_nonneg_left huR hc
      have hm := mul_le_mul_of_nonneg_right (add_le_add huScaled hvR) (Nat.cast_nonneg h : (0 : ℝ) ≤ h)
      nlinarith [hm]

end HadamardMultibase
