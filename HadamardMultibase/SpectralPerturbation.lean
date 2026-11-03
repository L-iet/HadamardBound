module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Tactic

@[expose] public section

namespace HadamardMultibase

open Module

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Every singular value within the domain dimension is attained as the norm
of the image of a unit vector. -/
theorem singularValue_eq_norm_unit (T : E →ₗ[ℝ] F) (i : Fin (finrank ℝ E)) :
    ∃ v : E, ‖v‖ = 1 ∧ ‖T v‖ = T.singularValues i := by
  let v := T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i
  have hv : ‖v‖ = 1 := OrthonormalBasis.norm_eq_one _ i
  refine ⟨v, hv, ?_⟩
  have heig := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
  have hi := inner_product_apply_eigenvector heig
  change inner ℝ v ((T.adjoint ∘ₗ T) v) = _ at hi
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
    real_inner_self_eq_norm_sq, hv] at hi
  norm_num at hi
  have hsq := T.sq_singularValues_fin rfl i
  have hnonneg := T.singularValues_nonneg i
  have hnorm := norm_nonneg (T v)
  nlinarith

theorem singularValues_bounds_of_norm_bounds (T : E →ₗ[ℝ] F) {a b : ℝ}
    (hlower : ∀ v, a * ‖v‖ ≤ ‖T v‖) (hupper : ∀ v, ‖T v‖ ≤ b * ‖v‖)
    {i : ℕ} (hi : i < finrank ℝ E) : a ≤ T.singularValues i ∧ T.singularValues i ≤ b := by
  obtain ⟨v, hv, hTv⟩ := singularValue_eq_norm_unit T ⟨i, hi⟩
  have hlo := hlower v
  have hup := hupper v
  simpa [hv, hTv] using And.intro hlo hup

/-- Spectral perturbation around a scaled isometry. The error hypothesis is
the defining action bound of the Euclidean operator norm. -/
theorem singularValues_perturbation (T Q : E →ₗ[ℝ] F) {r e : ℝ}
    (hr : 0 ≤ r) (hQ : ∀ v, ‖Q v‖ = ‖v‖)
    (herror : ∀ v, ‖(T - r • Q) v‖ ≤ e * ‖v‖)
    {i : ℕ} (hi : i < finrank ℝ E) :
    r - e ≤ T.singularValues i ∧ T.singularValues i ≤ r + e := by
  apply singularValues_bounds_of_norm_bounds T _ _ hi
  · intro v
    have h := norm_sub_norm_le (r • Q v) (T v)
    rw [norm_sub_rev] at h
    have he := herror v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply] at he
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hQ] at h
    nlinarith
  · intro v
    have h := norm_sub_norm_le (T v) (r • Q v)
    have he := herror v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply] at he
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, hQ] at h
    nlinarith

end HadamardMultibase
