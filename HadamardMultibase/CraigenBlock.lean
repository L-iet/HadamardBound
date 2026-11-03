module

public import HadamardMultibase.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Circulant

@[expose] public section

namespace HadamardMultibase

open Matrix

variable {ι R : Type*} [Fintype ι] [Ring R] [StarRing R]

/-- The normalized block merge underlying Craigen's signed-group construction.
It is obtained directly after the Hadamard change of coordinates in Lemma 3.1. -/
def craigenMerge (A B : Matrix ι ι R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R :=
  Matrix.fromBlocks A B (-Bᴴ) Aᴴ

theorem craigenMerge_mul_conjTranspose (A B : Matrix ι ι R) (hAB : Commute A B) :
    craigenMerge A B * (craigenMerge A B)ᴴ =
      Matrix.fromBlocks (A * Aᴴ + B * Bᴴ) 0 0 (Bᴴ * B + Aᴴ * A) := by
  have hstar : Bᴴ * Aᴴ = Aᴴ * Bᴴ := by
    simpa only [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hAB.eq
  simp only [craigenMerge, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_neg,
    Matrix.conjTranspose_conjTranspose, Matrix.fromBlocks_multiply]
  congr 1 <;> noncomm_ring [hAB.eq, hstar]

/-- Normality makes both diagonal blocks equal to the sum of the input energies. -/
theorem craigenMerge_energy (A B : Matrix ι ι R) (hAB : Commute A B)
    (hA : Aᴴ * A = A * Aᴴ) (hB : Bᴴ * B = B * Bᴴ) :
    craigenMerge A B * (craigenMerge A B)ᴴ =
      Matrix.fromBlocks (A * Aᴴ + B * Bᴴ) 0 0 (A * Aᴴ + B * Bᴴ) := by
  rw [craigenMerge_mul_conjTranspose A B hAB, hA, hB, add_comm (B * Bᴴ)]

end HadamardMultibase
