module

public import HadamardMultibase.CraigenSupport

@[expose] public section

namespace HadamardMultibase

open Matrix

def scalarLift (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] :
    Matrix ι ι ℤ →+* Matrix ι ι (Matrix κ κ ℤ) where
  toFun A := A.map (fun z => (z : Matrix κ κ ℤ))
  map_zero' := by ext i j; simp
  map_one' := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.map_apply, Matrix.one_apply, h]
  map_add' A B := by ext i j; simp
  map_mul' A B := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Int.cast_sum, Int.cast_mul]

theorem scalarLift_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι ι ℤ) (i j : ι) :
    scalarLift ι κ A i j = (A i j : Matrix κ κ ℤ) := rfl

theorem scalarLift_conjTranspose {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix ι ι ℤ) :
    scalarLift ι κ Aᴴ = (scalarLift ι κ A)ᴴ := by
  ext i j
  simp [scalarLift_apply, Matrix.conjTranspose_apply, Matrix.intCast_apply, eq_comm]

theorem scalarLift_circulant {G κ : Type*} [Fintype G] [DecidableEq G] [Sub G]
    [Fintype κ] [DecidableEq κ] (g : G → ℤ) :
    scalarLift G κ (circulant g) = circulant (fun x => (g x : Matrix κ κ ℤ)) := rfl

theorem scalarMatrix_eq_zero_iff {κ : Type*} [DecidableEq κ] [Nonempty κ] (z : ℤ) :
    (z : Matrix κ κ ℤ) = 0 ↔ z = 0 := by
  constructor
  · intro h
    obtain ⟨i⟩ := ‹Nonempty κ›
    simpa [Matrix.intCast_apply] using congrArg (fun A : Matrix κ κ ℤ => A i i) h
  · rintro rfl
    exact Int.cast_zero

theorem scalarMatrix_signedOrZero {κ : Type*} [DecidableEq κ] {z : ℤ}
    (hz : z = 0 ∨ z = 1 ∨ z = -1) : SignedOrZero (z : Matrix κ κ ℤ) := by
  rcases hz with rfl | rfl | rfl
  · exact Or.inl Int.cast_zero
  · exact Or.inr (by simpa using signedPermutation_one κ)
  · exact Or.inr (by simpa using (signedPermutation_one κ).neg)

theorem blockDiagonal_scalarMatrix {κ : Type*} [DecidableEq κ] (z : ℤ) :
    Matrix.fromBlocks (z : Matrix κ κ ℤ) 0 0 z = (z : Matrix (κ ⊕ κ) (κ ⊕ κ) ℤ) := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, Matrix.intCast_apply]

theorem scalar_circulant_normal {G R : Type*} [Fintype G] [AddCommGroup G]
    [Ring R] [StarRing R] (g : G → ℤ) :
    (circulant (fun x => (g x : R)))ᴴ * circulant (fun x => (g x : R)) =
      circulant (fun x => (g x : R)) * (circulant (fun x => (g x : R)))ᴴ := by
  have hf : star (fun x => (g (-x) : R)) = (fun x => (g (-x) : R)) := by
    funext x
    exact star_intCast (g (-x))
  rw [Matrix.conjTranspose_circulant, hf]
  exact (circulant_commute_integer (fun x => (g (-x) : R)) g).eq

theorem coefficientMerge_scalar_energy {G κ : Type*} [Fintype G] [DecidableEq G]
    [Fintype κ] [DecidableEq κ] (A B : Matrix G G (Matrix κ κ ℤ)) (S : Matrix G G ℤ)
    (hAB : Commute A B) (hA : Aᴴ * A = A * Aᴴ) (hB : Bᴴ * B = B * Bᴴ)
    (hS : A * Aᴴ + B * Bᴴ = scalarLift G κ S) :
    coefficientMerge A B * (coefficientMerge A B)ᴴ = scalarLift G (κ ⊕ κ) S := by
  rw [coefficientMerge_energy A B hAB hA hB, hS]
  funext i j
  exact blockDiagonal_scalarMatrix (S i j)

end HadamardMultibase
