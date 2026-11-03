module

public import HadamardMultibase.RoundingScale

@[expose] public section

namespace HadamardMultibase

open Filter

theorem roundingErrorBound_nonneg (n : ℕ) (u : ℝ) : 0 ≤ roundingErrorBound n u := by
  unfold roundingErrorBound
  positivity

/-- The logarithmic loss in moment concentration is absorbed by any strict
power margin below 1/4−ε/2. -/
theorem eventually_scaled_rounding_error {ε α : ℝ}
    (hε : 0 ≤ ε) (hεhalf : ε < 1 / 2) (hα : α < 1 / 4 - ε / 2) :
    ∀ᶠ n : ℕ in atTop, 0 < flatRoundingScale n ε ∧
      4 * flatRoundingScale n ε * roundingErrorBound n (flatRoundingScale n ε) ≤ (n : ℝ) ^ (-α) := by
  let C : ℝ := 5 + 2 / Real.log 4
  have hC : 0 < C := by dsimp [C]; positivity
  have hγ : 0 < 1 / 4 - ε / 2 - α := by linarith
  filter_upwards [eventually_flatRoundingScale_bound hεhalf,
    eventually_log_plus_one_bound hγ (64 * C), eventually_ge_atTop (1 : ℕ)] with n hscale habsorb hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlN : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  let u := flatRoundingScale n ε
  have hcoef := concentration_coefficient_le hn
  have hsqrt := rounding_sqrt_variance_le hnR hε
  have he : roundingErrorBound n u ≤
      8 * C * (Real.log n + 1) * (n : ℝ) ^ (1 / 4 + ε / 2) := by
    unfold roundingErrorBound
    calc
      _ ≤ (4 * (C * (Real.log n + 1))) * (2 * (n : ℝ) ^ (1 / 4 + ε / 2)) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hcoef (by norm_num)
        · exact hsqrt
        · exact Real.sqrt_nonneg _
        · positivity
      _ = _ := by ring
  have hquot : (n : ℝ) ^ (1 / 4 + ε / 2) / Real.sqrt n =
      (n : ℝ) ^ (-(1 / 4 - ε / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hnpos]
    congr 1
    ring
  refine ⟨hscale.1, ?_⟩
  calc
    _ ≤ 4 * (2 / Real.sqrt n) * roundingErrorBound n u :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale.2 (by norm_num))
        (roundingErrorBound_nonneg n u)
    _ ≤ 4 * (2 / Real.sqrt n) *
        (8 * C * (Real.log n + 1) * (n : ℝ) ^ (1 / 4 + ε / 2)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (64 * C * (Real.log n + 1)) * ((n : ℝ) ^ (1 / 4 + ε / 2) / Real.sqrt n) := by ring
    _ = (64 * C * (Real.log n + 1)) * (n : ℝ) ^ (-(1 / 4 - ε / 2)) := by rw [hquot]
    _ ≤ (n : ℝ) ^ (1 / 4 - ε / 2 - α) * (n : ℝ) ^ (-(1 / 4 - ε / 2)) :=
      mul_le_mul_of_nonneg_right habsorb (by positivity)
    _ = _ := by
      rw [← Real.rpow_add hnpos]
      congr 1
      ring

end HadamardMultibase
