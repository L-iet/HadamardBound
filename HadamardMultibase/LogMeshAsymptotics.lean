module

public import HadamardMultibase.QuantitativeRotation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

namespace HadamardMultibase

open Filter

/-- Polynomial separation gives a polynomially shrinking logarithmic mesh. -/
theorem eventual_nonnegative_log_mesh {α : ℝ} (hα : 0 < α)
    (hsep : PolynomialRotationSeparation α) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ t : ℝ in atTop,
      ∃ l m : ℕ, t - 1 / t ^ κ ≤ (l : ℝ) + (m : ℝ) * α ∧
        (l : ℝ) + (m : ℝ) * α ≤ t := by
  obtain ⟨c, hc, ν, hsep⟩ := hsep
  let d : ℝ := (ν : ℝ) + 1
  have hd : 0 < d := by dsimp [d]; positivity
  let κ : ℝ := 1 / (2 * d)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκd : κ * (ν + 1 : ℕ) = (1 / 2 : ℝ) := by
    push_cast
    dsimp [κ, d]
    field_simp
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop
      (max 2 (2 * α / c))] with t ht hu
  have htpos : 0 < t := by linarith
  let u : ℝ := t ^ (1 / 2 : ℝ)
  have hu₂ : 2 ≤ u := (le_max_left _ _).trans hu
  have huα : 2 * α / c ≤ u := (le_max_right _ _).trans hu
  have hu0 : 0 ≤ u := by linarith
  have hu_sq : u * u = t := by
    dsimp [u]
    rw [← Real.rpow_add htpos]
    norm_num
  let Q : ℕ := ⌊t ^ κ⌋₊
  have hpowone : 1 ≤ t ^ κ := Real.one_le_rpow ht hκ.le
  have hQ : 0 < Q := by
    have : 1 ≤ Q := (Nat.le_floor_iff (Real.rpow_nonneg htpos.le κ)).mpr (by simpa using hpowone)
    omega
  have hQle : (Q : ℝ) ≤ t ^ κ := Nat.floor_le (Real.rpow_nonneg htpos.le κ)
  have hQpow : (Q : ℝ) ^ (ν + 1) ≤ u := by
    calc
      (Q : ℝ) ^ (ν + 1) ≤ (t ^ κ) ^ (ν + 1) := by gcongr
      _ = t ^ (κ * (ν + 1 : ℕ)) := (Real.rpow_mul_natCast htpos.le κ (ν + 1)).symm
      _ = u := by rw [hκd]
  have hαu : 2 * α ≤ u * c := (div_le_iff₀ hc).mp huα
  have hmul := mul_le_mul_of_nonneg_right hαu hu0
  have ht₂ : 2 ≤ t := by nlinarith
  have hbudget : 1 + α * ((Q : ℝ) ^ (ν + 1) / c) ≤ t := by
    have hqu := mul_le_mul_of_nonneg_left hQpow hα.le
    have hqdiv : α * ((Q : ℝ) ^ (ν + 1) / c) ≤ α * u / c := by
      simpa only [mul_div_assoc] using (div_le_div_of_nonneg_right hqu hc.le)
    have hhalf : α * u / c ≤ t / 2 := by
      apply (div_le_iff₀ hc).mpr
      nlinarith [hu_sq]
    linarith
  obtain ⟨l, m, hl, hupp⟩ := nonnegative_log_mesh hα hc hsep hQ hbudget
  have hQupper : t ^ κ < (Q : ℝ) + 1 := Nat.lt_floor_add_one _
  have hrecip : 1 / ((Q : ℝ) + 1) ≤ 1 / t ^ κ :=
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos htpos κ) hQupper.le
  exact ⟨l, m, by linarith, hupp⟩

end HadamardMultibase
