module

public import HadamardMultibase.CraigenCirculant
public import HadamardMultibase.SignedPermutation

@[expose] public section

namespace HadamardMultibase

open Matrix

def mergeIndex (ι κ : Type*) : (ι ⊕ ι) × κ ≃ ι × (κ ⊕ κ) where
  toFun := fun p => match p with
    | (Sum.inl i, a) => (i, Sum.inl a)
    | (Sum.inr i, a) => (i, Sum.inr a)
  invFun := fun p => match p with
    | (i, Sum.inl a) => (Sum.inl i, a)
    | (i, Sum.inr a) => (Sum.inr i, a)
  left_inv := by rintro ⟨i | i, a⟩ <;> rfl
  right_inv := by rintro ⟨i, a | a⟩ <;> rfl

/-- Move the two-by-two merge index from the row index to the coefficient index. -/
def blockShuffle (ι κ R : Type*) [Fintype ι] [Fintype κ] [AddCommMonoid R] [Mul R] :
    Matrix (ι ⊕ ι) (ι ⊕ ι) (Matrix κ κ R) ≃+* Matrix ι ι (Matrix (κ ⊕ κ) (κ ⊕ κ) R) :=
  ((Matrix.compRingEquiv (ι ⊕ ι) κ R).trans
    (Matrix.reindexRingEquiv R (mergeIndex ι κ))).trans
      (Matrix.compRingEquiv ι (κ ⊕ κ) R).symm

theorem blockShuffle_fromBlocks {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid R] [Mul R] (A B C D : Matrix ι ι (Matrix κ κ R)) :
    blockShuffle ι κ R (Matrix.fromBlocks A B C D) =
      fun i j => Matrix.fromBlocks (A i j) (B i j) (C i j) (D i j) := by
  ext i j a b
  cases a <;> cases b <;> rfl

theorem blockShuffle_conjTranspose {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [AddCommMonoid R] [Mul R] [Star R]
    (A : Matrix (ι ⊕ ι) (ι ⊕ ι) (Matrix κ κ R)) :
    blockShuffle ι κ R Aᴴ = (blockShuffle ι κ R A)ᴴ := by
  ext i j a b
  cases a <;> cases b <;> rfl

def coefficientMerge {ι κ R : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] [Ring R] [StarRing R]
    (A B : Matrix ι ι (Matrix κ κ R)) : Matrix ι ι (Matrix (κ ⊕ κ) (κ ⊕ κ) R) :=
  blockShuffle ι κ R (craigenMerge A B)

theorem coefficientMerge_apply {ι κ R : Type*} [Fintype ι] [Fintype κ] [Ring R] [StarRing R]
    [DecidableEq κ]
    (A B : Matrix ι ι (Matrix κ κ R)) (i j : ι) :
    coefficientMerge A B i j =
      Matrix.fromBlocks (A i j) (B i j) (-(B j i)ᴴ) (A j i)ᴴ := by
  rw [coefficientMerge, craigenMerge, blockShuffle_fromBlocks]
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, star_eq_conjTranspose]

theorem coefficientMerge_energy {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [Ring R] [StarRing R] (A B : Matrix ι ι (Matrix κ κ R))
    (hAB : Commute A B) (hA : Aᴴ * A = A * Aᴴ) (hB : Bᴴ * B = B * Bᴴ) :
    coefficientMerge A B * (coefficientMerge A B)ᴴ =
      fun i j => Matrix.fromBlocks ((A * Aᴴ + B * Bᴴ) i j) 0 0
        ((A * Aᴴ + B * Bᴴ) i j) := by
  rw [coefficientMerge, ← blockShuffle_conjTranspose, ← map_mul,
    craigenMerge_energy A B hAB hA hB, blockShuffle_fromBlocks]
  rfl

theorem coefficientMerge_normal {ι κ R : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] [Ring R] [StarRing R] (A B : Matrix ι ι (Matrix κ κ R))
    (hAB : Commute A B) (hstarAB : Commute Aᴴ B)
    (hA : Aᴴ * A = A * Aᴴ) (hB : Bᴴ * B = B * Bᴴ) :
    (coefficientMerge A B)ᴴ * coefficientMerge A B =
      coefficientMerge A B * (coefficientMerge A B)ᴴ := by
  simpa only [coefficientMerge, map_mul, blockShuffle_conjTranspose] using
    congrArg (blockShuffle ι κ R) (craigenMerge_normal A B hAB hstarAB hA hB)

end HadamardMultibase
