module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic

@[expose] public section

namespace HadamardMultibase

open Matrix

/-- Submatrix orthogonalization (Alexeev--Jasper--Mixon, Lemma 3).
The graph of `(1-A)⁻¹B` is preserved in its first component by the orthogonal
block matrix; preservation of its Gram matrix cancels that component. -/
theorem submatrix_orthogonalization
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (C : Matrix κ ι ℝ) (D : Matrix κ κ ℝ)
    (horth : (fromBlocks A B C D)ᵀ * fromBlocks A B C D = 1)
    (hinv : IsUnit (1 - A)) :
    (D + C * (1 - A)⁻¹ * B)ᵀ * (D + C * (1 - A)⁻¹ * B) = 1 := by
  let X : Matrix ι κ ℝ := (1 - A)⁻¹ * B
  let M : Matrix κ κ ℝ := D + C * (1 - A)⁻¹ * B
  let E : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := fromBlocks 0 X 0 1
  let F : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := fromBlocks 0 X 0 M
  have hAX : A * X + B = X := by
    have hx : (1 - A) * X = B := by
      dsimp [X]
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((1 - A).isUnit_iff_isUnit_det.mp hinv),
        Matrix.one_mul]
    rw [Matrix.sub_mul, Matrix.one_mul] at hx
    rw [← hx]
    abel
  have hgraph : fromBlocks A B C D * E = F := by
    dsimp [E, F]
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, Matrix.mul_one, hAX]
    congr 1
    dsimp [X, M]
    simp [Matrix.mul_assoc, add_comm]
  have hgram : Fᵀ * F = Eᵀ * E := by
    rw [← hgraph, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (fromBlocks A B C D)ᵀ,
      horth, Matrix.one_mul]
  have h := congrArg (fun T : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ => T.toBlocks₂₂) hgram
  dsimp [E, F] at h
  simp only [fromBlocks_transpose, transpose_zero, transpose_one, fromBlocks_multiply,
    toBlocks_fromBlocks₂₂, Matrix.one_mul] at h
  exact add_left_cancel h

end HadamardMultibase
