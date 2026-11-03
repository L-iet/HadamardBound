module

public import HadamardMultibase.SpectralPerturbation
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Basic.ENNReal.Real

@[expose] public section

namespace HadamardMultibase

open Module
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Spectral condition number, with infinity when the least singular value
vanishes. The zero-dimensional domain is assigned infinity as well; all
asymptotic applications have positive dimension. -/
noncomputable def linearConditionNumber (T : E →ₗ[ℝ] F) : ℝ≥0∞ :=
  if T.singularValues (finrank ℝ E - 1) = 0 then ⊤
  else ENNReal.ofReal (T.singularValues 0 / T.singularValues (finrank ℝ E - 1))

noncomputable def matrixConditionNumber {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ≥0∞ :=
  linearConditionNumber (Matrix.toEuclideanLin A)

theorem linearConditionNumber_ne_top_iff {T : E →ₗ[ℝ] F} :
    linearConditionNumber T ≠ ⊤ ↔ T.singularValues (finrank ℝ E - 1) ≠ 0 := by
  simp [linearConditionNumber]

/-- Positive dimension makes the last singular value detect injectivity. -/
theorem least_singularValue_pos_iff_injective (T : E →ₗ[ℝ] F)
    (hn : 0 < finrank ℝ E) :
    0 < T.singularValues (finrank ℝ E - 1) ↔ Function.Injective T := by
  rw [T.injective_iff_forall_lt_finrank_singularValues_pos]
  constructor
  · intro h i hi
    exact h.trans_le (T.singularValues_antitone (by omega))
  · intro h
    exact h _ (by omega)

theorem linearConditionNumber_finite_iff_injective (T : E →ₗ[ℝ] F)
    (hn : 0 < finrank ℝ E) : linearConditionNumber T ≠ ⊤ ↔ Function.Injective T := by
  rw [linearConditionNumber_ne_top_iff, ← T.singularValues_pos_iff_ne_zero,
    least_singularValue_pos_iff_injective T hn]

/-- The finite perturbation estimate used after random rounding. -/
theorem linearConditionNumber_perturbation (T Q : E →ₗ[ℝ] F)
    (hn : 0 < finrank ℝ E) {r e : ℝ} (he : 0 ≤ e) (her : e < r)
    (hQ : ∀ v, ‖Q v‖ = ‖v‖)
    (herror : ∀ v, ‖(T - r • Q) v‖ ≤ e * ‖v‖) :
    linearConditionNumber T ≤ ENNReal.ofReal ((r + e) / (r - e)) := by
  have hr : 0 ≤ r := he.trans her.le
  have hmax := singularValues_perturbation T Q hr hQ herror (show 0 < finrank ℝ E from hn)
  have hmin := singularValues_perturbation T Q hr hQ herror
    (show finrank ℝ E - 1 < finrank ℝ E by omega)
  have hminpos : 0 < T.singularValues (finrank ℝ E - 1) := by linarith
  rw [linearConditionNumber, ite_eq_right hminpos.ne']
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (r + e) / T.singularValues (finrank ℝ E - 1) :=
      div_le_div_of_nonneg_right hmax.2 hminpos.le
    _ ≤ (r + e) / (r - e) :=
      div_le_div_of_nonneg_left (by linarith) (by linarith) hmin.1

theorem perturbation_ratio_le {δ : ℝ} (hδ : 0 ≤ δ) (hhalf : δ ≤ 1 / 2) :
    (1 + δ) / (1 - δ) ≤ 1 + 4 * δ := by
  apply (div_le_iff₀ (by linarith : 0 < 1 - δ)).mpr
  nlinarith [mul_nonneg hδ (show 0 ≤ 1 / 2 - δ by linarith)]

/-- A relative operator error δ gives condition number at most 1+4δ while
δ≤1/2. This quantitative form is convenient for the eventual power bound. -/
theorem linearConditionNumber_relative_perturbation (T Q : E →ₗ[ℝ] F)
    (hn : 0 < finrank ℝ E) {r δ : ℝ} (hr : 0 < r)
    (hδ : 0 ≤ δ) (hhalf : δ ≤ 1 / 2) (hQ : ∀ v, ‖Q v‖ = ‖v‖)
    (herror : ∀ v, ‖(T - r • Q) v‖ ≤ (r * δ) * ‖v‖) :
    linearConditionNumber T ≤ ENNReal.ofReal (1 + 4 * δ) := by
  have her : r * δ < r := by nlinarith
  have h := linearConditionNumber_perturbation T Q hn (mul_nonneg hr.le hδ) her hQ herror
  apply h.trans
  apply ENNReal.ofReal_le_ofReal
  have heq : (r + r * δ) / (r - r * δ) = (1 + δ) / (1 - δ) := by
    field_simp
  rw [heq]
  exact perturbation_ratio_le hδ hhalf

end HadamardMultibase
