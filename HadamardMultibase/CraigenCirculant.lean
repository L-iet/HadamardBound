module

public import HadamardMultibase.CraigenBlock
public import Mathlib.Data.Matrix.Composition

@[expose] public section

namespace HadamardMultibase

open Matrix

/-- Circulants commute when coefficients from the two sequences commute.
The coefficient ring itself need not be commutative. -/
theorem circulant_commute_of_coefficients {G R : Type*} [Fintype G] [AddCommGroup G]
    [NonUnitalNonAssocSemiring R] (f g : G → R)
    (h : ∀ i j, Commute (f i) (g j)) : Commute (circulant f) (circulant g) := by
  change circulant f * circulant g = circulant g * circulant f
  ext i j
  simp only [Matrix.mul_apply, circulant_apply]
  refine Fintype.sum_equiv ((Equiv.subLeft i).trans (Equiv.addRight j)) _ _ ?_
  intro x
  simp only [Equiv.trans_apply, Equiv.subLeft_apply, Equiv.coe_addRight,
    add_sub_cancel_right]
  rw [(h _ _).eq]
  congr 2
  abel

theorem circulant_commute_integer {G R : Type*} [Fintype G] [AddCommGroup G] [Ring R]
    (f : G → R) (g : G → ℤ) :
    Commute (circulant f) (circulant (fun i => (g i : R))) :=
  circulant_commute_of_coefficients f _ (fun i j => Int.commute_cast (f i) (g j))

/-- The reverse-energy half of the normalized block merge. -/
theorem craigenMerge_conjTranspose_mul {ι R : Type*} [Fintype ι] [Ring R] [StarRing R]
    (A B : Matrix ι ι R) (hAB : Commute Aᴴ B) :
    (craigenMerge A B)ᴴ * craigenMerge A B =
      Matrix.fromBlocks (Aᴴ * A + B * Bᴴ) 0 0 (Bᴴ * B + A * Aᴴ) := by
  have hstar : Bᴴ * A = A * Bᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
      congrArg Matrix.conjTranspose hAB.eq
  simp only [craigenMerge, Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_neg,
    Matrix.conjTranspose_conjTranspose, Matrix.fromBlocks_multiply]
  congr 1 <;> noncomm_ring [hAB.eq, hstar]

theorem craigenMerge_normal {ι R : Type*} [Fintype ι] [Ring R] [StarRing R]
    (A B : Matrix ι ι R) (hAB : Commute A B) (hstarAB : Commute Aᴴ B)
    (hA : Aᴴ * A = A * Aᴴ) (hB : Bᴴ * B = B * Bᴴ) :
    (craigenMerge A B)ᴴ * craigenMerge A B =
      craigenMerge A B * (craigenMerge A B)ᴴ := by
  rw [craigenMerge_conjTranspose_mul A B hstarAB, craigenMerge_energy A B hAB hA hB,
    hA, hB, add_comm (B * Bᴴ)]

/-- A matrix with matrix-valued entries can be flattened without changing star. -/
theorem matrix_comp_conjTranspose {ι κ R : Type*} [Star R]
    (A : Matrix ι ι (Matrix κ κ R)) :
    Matrix.comp ι ι κ κ R Aᴴ = (Matrix.comp ι ι κ κ R A)ᴴ := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rfl

end HadamardMultibase
