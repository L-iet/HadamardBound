module

public import HadamardMultibase.SparseApproximation

@[expose] public section

namespace HadamardMultibase

open Filter

/-- A one-sided logarithmic mesh estimate, the Diophantine part of KSW's
approximation lemma. No existence assertion is built into this definition. -/
def LogarithmicApproximation (S : Set ℕ) : Prop :=
  ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
    ∃ b ∈ S, 0 < b ∧ b ≤ n ∧
      Real.log (n : ℝ) - C / (Real.log n) ^ κ ≤ Real.log (b : ℝ)

theorem remainder_le_of_log_approximation {n b : ℕ} {C κ : ℝ}
    (hb : 0 < b) (hbn : b ≤ n)
    (hlog : Real.log (n : ℝ) - C / (Real.log n) ^ κ ≤ Real.log (b : ℝ)) :
    ((n - b : ℕ) : ℝ) ≤ shrinkingRemainder C κ n := by
  have hn : 0 < n := lt_of_lt_of_le hb hbn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_sub, Real.exp_log hnR, Real.exp_log hbR] at he
  have hexp : 1 - C / (Real.log n) ^ κ ≤
      (Real.exp (C / (Real.log n) ^ κ))⁻¹ := by
    simpa only [Real.exp_neg] using Real.one_sub_le_exp_neg (C / (Real.log n) ^ κ)
  have hmul := mul_le_mul_of_nonneg_left hexp hnR.le
  have hsub : ((n - b : ℕ) : ℝ) = (n : ℝ) - (b : ℝ) := Nat.cast_sub hbn
  rw [hsub]
  dsimp [shrinkingRemainder]
  rw [div_eq_mul_inv] at he
  have h := hmul.trans he
  calc
    (n : ℝ) - (b : ℝ) ≤ (n : ℝ) * (C / (Real.log n) ^ κ) := by nlinarith
    _ = C * (n : ℝ) / (Real.log n) ^ κ := by ring

theorem LogarithmicApproximation.polynomialRemainder {S : Set ℕ}
    (h : LogarithmicApproximation S) : PolynomialRemainderApproximation S := by
  obtain ⟨C, κ, hC, hκ, hevent⟩ := h
  refine ⟨C, κ, hC, hκ, ?_⟩
  filter_upwards [hevent] with n hn
  obtain ⟨b, hbS, hb, hbn, hlog⟩ := hn
  exact ⟨b, hbS, hbn, remainder_le_of_log_approximation hb hbn hlog⟩

theorem sparseRepresentationBound_of_logarithmicApproximation
    (h : LogarithmicApproximation golayMonoid₂) : SparseRepresentationBound :=
  sparseRepresentationBound_of_approximation h.polynomialRemainder

end HadamardMultibase
