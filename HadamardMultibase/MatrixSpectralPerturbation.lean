module

public import HadamardMultibase.ConditionNumber
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

namespace HadamardMultibase

open Matrix
open scoped ENNReal Matrix.Norms.L2Operator

theorem orthogonal_matrix_norm_map {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Qᵀ * Q = 1) (v : EuclideanSpace ℝ (Fin n)) :
    ‖Matrix.toEuclideanLin Q v‖ = ‖v‖ := by
  have h : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q).adjoint ∘L Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q = 1 := by
    change star (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q) * Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q = 1
    rw [← map_star, ← map_mul]
    have hs : star Q = Qᵀ := by ext i j; simp
    rw [hs, hQ, map_one]
  exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q).norm_map_iff_adjoint_comp_self.mpr h v

/-- Matrix version with the genuine Euclidean operator norm on the error. -/
theorem matrixConditionNumber_perturbation {n : ℕ} (hn : 0 < n)
    (A Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ * Q = 1)
    {r e : ℝ} (he : 0 ≤ e) (her : e < r) (herror : ‖A - r • Q‖ ≤ e) :
    matrixConditionNumber A ≤ ENNReal.ofReal ((r + e) / (r - e)) := by
  apply linearConditionNumber_perturbation (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin Q)
    (by simpa using hn) he her (orthogonal_matrix_norm_map hQ)
  intro v
  have h := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (A - r • Q)).le_opNorm v
  have hnerror : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (A - r • Q)‖ ≤ e := herror
  have hbound := h.trans (mul_le_mul_of_nonneg_right hnerror (norm_nonneg v))
  have hA : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A) v = Matrix.toEuclideanLin A v :=
    congrArg (fun f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) => f v)
      (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin A)
  have hQ' : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) Q) v = Matrix.toEuclideanLin Q v :=
    congrArg (fun f : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) => f v)
      (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin Q)
  simpa only [map_sub, map_smul, _root_.sub_apply, _root_.smul_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, hA, hQ'] using hbound

end HadamardMultibase

