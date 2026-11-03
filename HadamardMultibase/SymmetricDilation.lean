module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Data.Matrix.Block
public import Mathlib.Tactic

@[expose] public section

namespace HadamardMultibase

open Matrix
open scoped Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def blockLeftInclusion : Matrix (ι ⊕ ι) ι ℝ :=
  fun i j => Sum.elim (fun k => if k = j then 1 else 0) (fun _ => 0) i

noncomputable def blockRightInclusion : Matrix (ι ⊕ ι) ι ℝ :=
  fun i j => Sum.elim (fun _ => 0) (fun k => if k = j then 1 else 0) i

theorem blockLeftInclusion_gram :
    (blockLeftInclusion (ι := ι))ᵀ * blockLeftInclusion (ι := ι) = (1 : Matrix ι ι ℝ) := by
  ext i j
  simp [blockLeftInclusion, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.transpose_apply, Matrix.one_apply, eq_comm]

theorem blockRightInclusion_gram :
    (blockRightInclusion (ι := ι))ᵀ * blockRightInclusion (ι := ι) = (1 : Matrix ι ι ℝ) := by
  ext i j
  simp [blockRightInclusion, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.transpose_apply, Matrix.one_apply, eq_comm]

theorem norm_blockLeftInclusion [Nonempty ι] : ‖blockLeftInclusion (ι := ι)‖ = 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (blockLeftInclusion (ι := ι))
  rw [conjTranspose_eq_transpose_of_trivial, blockLeftInclusion_gram, norm_one] at h
  nlinarith [norm_nonneg (blockLeftInclusion (ι := ι))]

theorem norm_blockRightInclusion [Nonempty ι] : ‖blockRightInclusion (ι := ι)‖ = 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (blockRightInclusion (ι := ι))
  rw [conjTranspose_eq_transpose_of_trivial, blockRightInclusion_gram, norm_one] at h
  nlinarith [norm_nonneg (blockRightInclusion (ι := ι))]

noncomputable def symmetricDilation (A : Matrix ι ι ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ :=
  fromBlocks 0 A Aᵀ 0

omit [Fintype ι] [DecidableEq ι] in
theorem symmetricDilation_transpose (A : Matrix ι ι ℝ) :
    (symmetricDilation A)ᵀ = symmetricDilation A := by
  simp [symmetricDilation, fromBlocks_transpose]

theorem dilation_compression (A : Matrix ι ι ℝ) :
    blockLeftInclusionᵀ * symmetricDilation A * blockRightInclusion = A := by
  ext i j
  simp [blockLeftInclusion, blockRightInclusion, symmetricDilation, Matrix.mul_apply,
    Fintype.sum_sum_type, Matrix.transpose_apply]

/-- Compressing the symmetric dilation recovers A without increasing the
Euclidean operator norm. -/
theorem norm_le_symmetricDilation [Nonempty ι] (A : Matrix ι ι ℝ) :
    ‖A‖ ≤ ‖symmetricDilation A‖ := by
  have ht : ‖(blockLeftInclusion (ι := ι))ᵀ‖ = 1 := by
    have h := Matrix.l2_opNorm_conjTranspose (blockLeftInclusion (ι := ι))
    simpa only [conjTranspose_eq_transpose_of_trivial, norm_blockLeftInclusion] using h
  calc
    _ = ‖blockLeftInclusionᵀ * symmetricDilation A * blockRightInclusion‖ :=
      congrArg norm (dilation_compression A).symm
    _ ≤ ‖blockLeftInclusionᵀ * symmetricDilation A‖ * ‖blockRightInclusion (ι := ι)‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(blockLeftInclusion (ι := ι))ᵀ‖ * ‖symmetricDilation A‖) *
        ‖blockRightInclusion (ι := ι)‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
    _ = _ := by rw [ht, norm_blockRightInclusion, one_mul, mul_one]

end HadamardMultibase
