/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerMixedDerivatives

@[expose] public section

/-! # Uniform growth for the mixed auxiliary family

The polynomial bound is independent of the Hasse derivative order. The
remaining index dependence is the explicit slope power Gamma^v.
-/

namespace HadamardMultibase

theorem bounded_slope_frequency {L lam mu : ℕ} {β K : ℝ}
    (_hK : 0 ≤ K) (hβ : |β| ≤ K) (hlam : lam ≤ L) (hmu : mu ≤ L) :
    |(lam : ℝ) + (mu : ℝ) * β| ≤ (L : ℝ) * (1 + K) := by
  calc |(lam : ℝ) + (mu : ℝ) * β| ≤ |(lam : ℝ)| + |(mu : ℝ) * β| := abs_add_le _ _
    _ = (lam : ℝ) + (mu : ℝ) * |β| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg lam), abs_of_nonneg (Nat.cast_nonneg mu)]
    _ ≤ (L : ℝ) + (L : ℝ) * K := by
      have h1 : (lam : ℝ) ≤ L := by exact_mod_cast hlam
      have h2 : (mu : ℝ) ≤ L := by exact_mod_cast hmu
      exact add_le_add h1 (mul_le_mul h2 hβ (abs_nonneg _) (Nat.cast_nonneg _))
    _ = _ := by ring

theorem bakerMixedComplex_norm_bound {n h L T : ℕ} (hh : 0 < h)
    (d lam mu : Fin n → ℕ) (hd : ∀ j, d j < h * (L + 1))
    (u v : ℕ) (β : ℝ) (a : ℕ) (c : Fin n → ℤ)
    (H Γ : ℝ) (hH : 0 ≤ H) (hΓ : 0 ≤ Γ)
    (hc : ∀ j, |(c j : ℝ)| ≤ H)
    (hgamma : ∀ j, |(lam j : ℝ) + (mu j : ℝ) * β| ≤ Γ)
    (z : ℂ) (hz : ‖z‖ ≤ (T * h : ℕ)) :
    ‖bakerMixedComplexValue h u v β a c d lam mu z‖ ≤
      (n : ℝ) * H * (2 : ℝ) ^ (h * (T + 2) * (L + 1)) * Γ ^ v *
        Real.exp (Γ * |Real.log a| * ((T * h : ℕ) : ℝ)) := by
  classical
  let B := (2 : ℝ) ^ (h * (T + 2) * (L + 1))
  let E := Real.exp (Γ * |Real.log a| * ((T * h : ℕ) : ℝ))
  have hterm (j : Fin n) :
      ‖(c j : ℂ) * (Polynomial.hasseDeriv u (bakerBlock h (d j))).eval₂ (Rat.castHom ℂ) z *
        (((lam j : ℝ) + (mu j : ℝ) * β : ℝ) : ℂ) ^ v *
        Complex.exp (((((lam j : ℝ) + (mu j : ℝ) * β) * Real.log a : ℝ) : ℂ) * z)‖ ≤
      H * B * Γ ^ v * E := by
    have hp := bakerBlock_hasse_norm_le_uniform hh (hd j) u z hz
    have hfreq : |((lam j : ℝ) + (mu j : ℝ) * β) * Real.log a| ≤ Γ * |Real.log a| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hgamma j) (abs_nonneg _)
    have he := complex_exp_frequency_norm_bound
      (((lam j : ℝ) + (mu j : ℝ) * β) * Real.log a)
      (Γ * |Real.log a|) ((T * h : ℕ) : ℝ) (by positivity) hfreq z hz
    have hcNorm : ‖(c j : ℂ)‖ ≤ H := by simpa using hc j
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul _ he (norm_nonneg _) (by dsimp [B]; positivity)
    apply mul_le_mul _ (pow_le_pow_left₀ (abs_nonneg _) (hgamma j) v) (by positivity)
      (mul_nonneg hH (by dsimp [B]; positivity))
    exact mul_le_mul hcNorm hp (norm_nonneg _) hH
  calc ‖bakerMixedComplexValue h u v β a c d lam mu z‖
      ≤ ∑ j, ‖(c j : ℂ) * (Polynomial.hasseDeriv u (bakerBlock h (d j))).eval₂ (Rat.castHom ℂ) z *
          (((lam j : ℝ) + (mu j : ℝ) * β : ℝ) : ℂ) ^ v *
          Complex.exp (((((lam j : ℝ) + (mu j : ℝ) * β) * Real.log a : ℝ) : ℂ) * z)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, H * B * Γ ^ v * E := Finset.sum_le_sum (fun j _ => hterm j)
    _ = _ := by simp [B, E]; ring

end HadamardMultibase
