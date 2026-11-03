module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic

@[expose] public section

namespace HadamardMultibase

open Matrix
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hermitian_norm_eq_norm_eigenvalues {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    ‖A‖ = ‖hA.eigenvalues‖ := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  congr 1

theorem hermitian_trace_pow_eq_sum {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (k : ℕ) :
    Matrix.trace (A ^ k) = ∑ i, hA.eigenvalues i ^ k := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp only [Unitary.coe_star_mul_self, Matrix.one_mul]
  rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  simp

/-- The largest eigenvalue moment is bounded by the sum of the nonnegative
eigenvalue moments. -/
theorem posSemidef_norm_pow_le_trace [Nonempty ι] {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (k : ℕ) : ‖A‖ ^ k ≤ Matrix.trace (A ^ k) := by
  classical
  obtain ⟨i, _, hmax⟩ := (Finset.univ : Finset ι).exists_max_image hA.isHermitian.eigenvalues (by simp)
  have hnorm : ‖hA.isHermitian.eigenvalues‖ = hA.isHermitian.eigenvalues i := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (hA.eigenvalues_nonneg i)).mpr
      intro j
      rw [Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg j)]
      exact hmax j (Finset.mem_univ j)
    · have h := norm_le_pi_norm hA.isHermitian.eigenvalues i
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)] using h
  rw [hermitian_norm_eq_norm_eigenvalues hA.isHermitian, hnorm,
    hermitian_trace_pow_eq_sum hA.isHermitian]
  exact Finset.single_le_sum (fun j _ => pow_nonneg (hA.eigenvalues_nonneg j) _) (Finset.mem_univ i)

/-- Trace moments control the genuine Euclidean operator norm of any real
square matrix. This is the deterministic step in the moment method. -/
theorem norm_pow_le_trace_gram_pow [Nonempty ι] (A : Matrix ι ι ℝ) (k : ℕ) :
    ‖A‖ ^ (2 * k) ≤ Matrix.trace ((Aᵀ * A) ^ k) := by
  have hgram : (Aᵀ * A).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self A
  have hnorm : ‖Aᵀ * A‖ = ‖A‖ ^ 2 := by
    simpa only [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial, pow_two] using
      (CStarRing.norm_star_mul_self (x := A))
  rw [pow_mul, ← hnorm]
  exact posSemidef_norm_pow_le_trace hgram k

theorem symmetric_norm_even_pow_le_trace [Nonempty ι] {A : Matrix ι ι ℝ}
    (hA : Aᵀ = A) (k : ℕ) : ‖A‖ ^ (2 * k) ≤ Matrix.trace (A ^ (2 * k)) := by
  simpa only [hA, ← pow_two, ← pow_mul] using norm_pow_le_trace_gram_pow A k

end HadamardMultibase
