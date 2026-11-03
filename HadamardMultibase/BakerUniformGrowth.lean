/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerInitialHeight
public import HadamardMultibase.BakerExponentialEstimates

@[expose] public section

/-! # Uniform exponential growth rates

Thresholds may depend on the fixed derivative budget and frequency width.
Rates multiplying h remain explicit and uniform in the rational slope,
coefficient vector, grid multiplier and block derivative indices.
-/

namespace HadamardMultibase

open Filter

theorem eventually_bakerMixed_growth {L K J : ℕ} {Γ : ℝ} (hΓ : 1 ≤ Γ)
    (a : ℕ) (C : ℝ) :
    ∀ᶠ h : ℕ in atTop, ∀ n : ℕ, n ≤ J * h →
      ∀ d lam mu : Fin n → ℕ, (∀ j, d j < h * (L + 1)) →
      ∀ u v : ℕ, v ≤ K → ∀ β : ℝ, ∀ c : Fin n → ℤ,
      (∀ j, |(c j : ℝ)| ≤ Real.exp (C * h)) →
      (∀ j, |(lam j : ℝ) + (mu j : ℝ) * β| ≤ Γ) →
      ∀ T : ℕ, ∀ z : ℂ, ‖z‖ ≤ ((T * h : ℕ) : ℝ) →
      ‖bakerMixedComplexValue h u v β a c d lam mu z‖ ≤
        Real.exp ((C + 2 * ((L : ℝ) + 1) * Real.log 2 + 1) * h +
          (((L : ℝ) + 1) * Real.log 2 + Γ * |Real.log a|) * ((T * h : ℕ) : ℝ)) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_nat_const_mul_pow_le_exp ((J : ℝ) * Γ ^ K) 1
      (show (0 : ℝ) < 1 by norm_num)] with h hh he
  intro n hn d lam mu hd u v hv β c hc hgamma T z hz
  have hhpos : 0 < h := by omega
  have hnR : (n : ℝ) ≤ (J : ℝ) * h := by exact_mod_cast hn
  have hΓ0 : 0 ≤ Γ := by linarith
  have hvΓ : Γ ^ v ≤ Γ ^ K := pow_le_pow_right₀ hΓ hv
  have hnΓ : (n : ℝ) * Γ ^ v ≤ Real.exp (h : ℝ) := by
    calc (n : ℝ) * Γ ^ v ≤ ((J : ℝ) * h) * Γ ^ K :=
        mul_le_mul hnR hvΓ (by positivity) (by positivity)
      _ ≤ Real.exp (h : ℝ) := by simpa only [pow_one, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using he
  have hb := bakerMixedComplex_norm_bound hhpos d lam mu hd u v β a c
    (Real.exp (C * h)) Γ (Real.exp_pos _).le hΓ0 hc hgamma z hz
  apply hb.trans
  have htwo : (2 : ℝ) ^ (h * (T + 2) * (L + 1)) =
      Real.exp (((h * (T + 2) * (L + 1) : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  calc (n : ℝ) * Real.exp (C * h) * (2 : ℝ) ^ (h * (T + 2) * (L + 1)) * Γ ^ v *
        Real.exp (Γ * |Real.log a| * ((T * h : ℕ) : ℝ))
      = ((n : ℝ) * Γ ^ v) * Real.exp (C * h) *
        (2 : ℝ) ^ (h * (T + 2) * (L + 1)) * Real.exp (Γ * |Real.log a| * ((T * h : ℕ) : ℝ)) := by ring
    _ ≤ Real.exp (h : ℝ) * Real.exp (C * h) *
        (2 : ℝ) ^ (h * (T + 2) * (L + 1)) * Real.exp (Γ * |Real.log a| * ((T * h : ℕ) : ℝ)) := by gcongr
    _ = _ := by
      rw [htwo, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      ring

noncomputable def bakerInitialHeightRate (K L a b : ℕ) : ℝ :=
  (Real.log 4 + 5) * (K : ℝ) + 3 * ((L : ℝ) + 1) * Real.log 2 +
    (L : ℝ) * Real.log ((a * b : ℕ) : ℝ) + 1

theorem eventually_bakerComparison_cleared_height {K L a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) {Γ : ℝ} (hΓ : 1 ≤ Γ) :
    ∀ᶠ h : ℕ in atTop, ∀ q : ℕ, (q : ℝ) ≤ Real.exp h →
      ∀ d l u v lam mu : ℕ, d < h * (L + 1) → l ≤ h →
      u ≤ K → v ≤ K → lam ≤ L → mu ≤ L → ∀ p : ℤ,
      |(lam : ℝ) + (mu : ℝ) * p / q| ≤ Γ →
      |((Nat.lcmUpto h ^ u * q ^ v : ℕ) : ℝ) *
        ((bakerComparisonValue h d u v l lam mu p q a b : ℚ) : ℝ)| ≤
      Real.exp (bakerInitialHeightRate K L a b * h) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_nat_const_mul_pow_le_exp (Γ ^ K) 0
      (show (0 : ℝ) < 1 by norm_num)] with h hh he
  intro q hq d l u v lam mu hd hl hu hv hlam hmu p hgamma
  have hhpos : 0 < h := by omega
  have hΓ0 : 0 ≤ Γ := by linarith
  have hentry := bakerComparison_initial_abs_bound hhpos hd hl ha hb u v lam mu hlam hmu p hΓ0 hgamma
  have hden := baker_comparison_denominator_exp_bound hq hu hv
  have hgpow : Γ ^ v ≤ Γ ^ K := pow_le_pow_right₀ hΓ hv
  have hΓK : Γ ^ K ≤ Real.exp (h : ℝ) := by simpa using he
  have hab : (0 : ℝ) < ((a * b : ℕ) : ℝ) := by
    have ha0 : 0 < a := by omega
    have hb0 : 0 < b := by omega
    exact_mod_cast Nat.mul_pos ha0 hb0
  rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (Nat.lcmUpto h ^ u * q ^ v : ℕ) by positivity)]
  have hp := mul_le_mul hden hentry (abs_nonneg _) (Real.exp_pos _).le
  apply hp.trans
  calc Real.exp ((Real.log 4 + 5) * (K : ℝ) * h) *
        ((2 : ℝ) ^ (h * 3 * (L + 1)) * Γ ^ v * ((a * b : ℕ) : ℝ) ^ (L * h))
      ≤ Real.exp ((Real.log 4 + 5) * (K : ℝ) * h) *
        ((2 : ℝ) ^ (h * 3 * (L + 1)) * Real.exp (h : ℝ) * ((a * b : ℕ) : ℝ) ^ (L * h)) := by
          gcongr
          exact hgpow.trans hΓK
    _ = _ := by
      have htwo : (2 : ℝ) ^ (h * 3 * (L + 1)) =
          Real.exp (((h * 3 * (L + 1) : ℕ) : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      have hpowers : ((a * b : ℕ) : ℝ) ^ (L * h) =
          Real.exp (((L * h : ℕ) : ℝ) * Real.log ((a * b : ℕ) : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hab]
      rw [htwo, hpowers, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [bakerInitialHeightRate]
      push_cast
      ring

end HadamardMultibase
