/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerIndexing
public import HadamardMultibase.BakerPerturbation
public import HadamardMultibase.BakerExponentialEstimates

@[expose] public section

/-! # Uniform perturbation on a fixed multiple of the height grid

The threshold is uniform in the rational slope and coefficient vector.
Only the approximation defect varies after the fixed parameters are chosen.
-/
namespace HadamardMultibase
open Filter

noncomputable def bakerGridEntryRate (L S a b : ℕ) : ℝ :=
  ((S : ℝ) + 2) * ((L : ℝ) + 1) * Real.log 2 +
    (L : ℝ) * S * Real.log ((a * b : ℕ) : ℝ)

theorem bakerComparison_grid_exp_bound {h d L S l q a b K : ℕ}
    (hh : 0 < h) (hd : d < h * (L + 1)) (hl : l ≤ S * h)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (u v lam mu : ℕ) (hv : v ≤ K)
    (hlam : lam ≤ L) (hmu : mu ≤ L) (p : ℤ)
    {Γ : ℝ} (hΓ : 1 ≤ Γ) (hgamma : |(lam : ℝ) + (mu : ℝ) * p / q| ≤ Γ) :
    |((bakerComparisonValue h d u v l lam mu p q a b : ℚ) : ℝ)| ≤
      Γ ^ K * Real.exp (bakerGridEntryRate L S a b * h) := by
  have hbnd := bakerComparison_grid_abs_bound hh hd hl ha hb u v lam mu hlam hmu p
    (by linarith : 0 ≤ Γ) hgamma
  apply hbnd.trans
  have hp : Γ ^ v ≤ Γ ^ K := pow_le_pow_right₀ hΓ hv
  have hab : (0 : ℝ) < ((a * b : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (show 0 < a by omega) (show 0 < b by omega)
  calc (2 : ℝ) ^ (h * (S + 2) * (L + 1)) * Γ ^ v *
        ((a * b : ℕ) : ℝ) ^ (L * (S * h))
      ≤ (2 : ℝ) ^ (h * (S + 2) * (L + 1)) * Γ ^ K *
        ((a * b : ℕ) : ℝ) ^ (L * (S * h)) := by gcongr
    _ = _ := by
      have htwo : (2 : ℝ) ^ (h * (S + 2) * (L + 1)) =
          Real.exp (((h * (S + 2) * (L + 1) : ℕ) : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      have habpow : ((a * b : ℕ) : ℝ) ^ (L * (S * h)) =
          Real.exp (((L * (S * h) : ℕ) : ℝ) * Real.log ((a * b : ℕ) : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hab]
      rw [htwo, habpow]
      calc _ = Γ ^ K * (Real.exp (((h * (S + 2) * (L + 1) : ℕ) : ℝ) * Real.log 2) *
          Real.exp (((L * (S * h) : ℕ) : ℝ) * Real.log ((a * b : ℕ) : ℝ))) := by ring
        _ = _ := by
          rw [← Real.exp_add]
          congr 2
          unfold bakerGridEntryRate
          push_cast
          ring

theorem eventually_baker_grid_perturbation {L S K J a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) {Γ : ℝ} (hΓ : 1 ≤ Γ) (C : ℝ) :
    ∀ᶠ h : ℕ in atTop, ∀ n : ℕ, n ≤ J * h →
      ∀ d lam mu : Fin n → ℕ, (∀ j, d j < h * (L + 1)) →
      (∀ j, lam j ≤ L) → (∀ j, mu j ≤ L) →
      ∀ u v l : ℕ, v ≤ K → l ≤ S * h → ∀ p : ℤ, ∀ q : ℕ,
      ∀ c : Fin n → ℤ, (∀ j, |(c j : ℝ)| ≤ Real.exp (C * h)) →
      (∀ j, |(lam j : ℝ) + (mu j : ℝ) * p / q| ≤ Γ) →
      ∀ A : ℝ, 1 ≤ A →
      |((p : ℝ) / q) * Real.log a - Real.log b| ≤ Real.exp (-A * h) →
      |bakerMixedRealValue h u v ((p : ℝ) / q) a c d lam mu l -
        ∑ j, (c j : ℝ) * ((bakerComparisonValue h (d j) u v l (lam j) (mu j) p q a b : ℚ) : ℝ)| ≤
        Real.exp ((C + bakerGridEntryRate L S a b + 1 - A) * h) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_nat_const_mul_pow_le_exp ((L : ℝ) * S) 1 (show (0 : ℝ) < 1 by norm_num),
    eventually_nat_const_mul_pow_le_exp (2 * (J : ℝ) * Γ ^ K * L * S) 2
      (show (0 : ℝ) < 1 by norm_num)] with h hh hsmallGrid hpref
  intro n hn d lam mu hd hlam hmu u v l hv hl p q c hc hgamma A hA hdef
  have hh0 : 0 < h := by omega
  have hnR : (n : ℝ) ≤ (J : ℝ) * h := by exact_mod_cast hn
  have hlR : (l : ℝ) ≤ (S : ℝ) * h := by exact_mod_cast hl
  let η : ℝ := ((p : ℝ) / q) * Real.log a - Real.log b
  have hdef' : |η| ≤ Real.exp (-(h : ℝ)) := hdef.trans (Real.exp_le_exp.mpr (by nlinarith))
  have hLl : ((L * l : ℕ) : ℝ) ≤ Real.exp (h : ℝ) := by
    calc ((L * l : ℕ) : ℝ) ≤ (L : ℝ) * ((S : ℝ) * h) := by push_cast; gcongr
      _ ≤ Real.exp (h : ℝ) := by simpa [pow_one, mul_assoc] using hsmallGrid
  have hsmall : ((L * l : ℕ) : ℝ) * |η| ≤ 1 := by
    calc _ ≤ Real.exp (h : ℝ) * Real.exp (-(h : ℝ)) :=
        mul_le_mul hLl hdef' (abs_nonneg _) (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have herr := bakerMixedRealValue_comparison_error
    (show 0 < a by omega) (show 0 < b by omega) h u v l q L p c d lam mu
    (Real.exp (C * h)) (Γ ^ K * Real.exp (bakerGridEntryRate L S a b * h))
    (Real.exp_pos _).le (by positivity)
    hc (fun j => bakerComparison_grid_exp_bound hh0 (hd j) hl ha hb u v (lam j) (mu j)
      hv (hlam j) (hmu j) p hΓ (hgamma j)) hmu hsmall
  apply herr.trans
  have hpoly : 2 * (n : ℝ) * Γ ^ K * ((L * l : ℕ) : ℝ) ≤ Real.exp (h : ℝ) := by
    have hnl := mul_le_mul hnR hlR (Nat.cast_nonneg l)
      (by positivity : (0 : ℝ) ≤ (J : ℝ) * h)
    have hm := mul_le_mul_of_nonneg_left hnl
      (by positivity : (0 : ℝ) ≤ 2 * Γ ^ K * L)
    calc
      _ ≤ (2 * (J : ℝ) * Γ ^ K * L * S) * (h : ℝ) ^ 2 := by
        push_cast
        nlinarith [hm]
      _ ≤ _ := by simpa using hpref
  calc 2 * (n : ℝ) * Real.exp (C * h) *
        (Γ ^ K * Real.exp (bakerGridEntryRate L S a b * h)) * ((L * l : ℕ) : ℝ) * |η|
      = (2 * (n : ℝ) * Γ ^ K * ((L * l : ℕ) : ℝ)) *
        Real.exp (C * h) * Real.exp (bakerGridEntryRate L S a b * h) * |η| := by ring
    _ ≤ Real.exp (h : ℝ) * Real.exp (C * h) *
        Real.exp (bakerGridEntryRate L S a b * h) * Real.exp (-A * h) := by gcongr
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end HadamardMultibase
