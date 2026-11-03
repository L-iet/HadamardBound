module

public import HadamardMultibase.PeriodicAlgebra

@[expose] public section

namespace HadamardMultibase

open Matrix
open scoped LaurentPolynomial

theorem periodicEnergy_mul {G : Type*} [AddCommGroup G]
    (p q : AddMonoidAlgebra ℚ G) : periodicEnergy (p * q) = periodicEnergy p * periodicEnergy q := by
  simp only [periodicEnergy, map_mul]
  ring

theorem periodicEnergy_single_one {G : Type*} [AddCommGroup G] (x : G) :
    periodicEnergy (AddMonoidAlgebra.single x 1 : AddMonoidAlgebra ℚ G) = 1 := by
  simp only [periodicEnergy, periodicReverse_single, AddMonoidAlgebra.single_mul_single,
    add_neg_cancel, mul_one, ← AddMonoidAlgebra.one_def]

theorem periodicEnergy_shift {G : Type*} [AddCommGroup G] (x : G) (p : AddMonoidAlgebra ℚ G) :
    periodicEnergy (AddMonoidAlgebra.single x 1 * p) = periodicEnergy p := by
  rw [periodicEnergy_mul, periodicEnergy_single_one, one_mul]

theorem periodic_single_zero_natCast {G : Type*} [AddCommGroup G] (n : ℕ) :
    AddMonoidAlgebra.single (0 : G) (n : ℚ) = (n : AddMonoidAlgebra ℚ G) :=
  map_natCast (AddMonoidAlgebra.singleZeroRingHom : ℚ →+* AddMonoidAlgebra ℚ G) n

noncomputable def periodicGolayLeft {G : Type*} [AddCommGroup G] (e : ℤ →+ G)
    (offset : G) {n : ℕ} (A B : Fin n → ℤ) : AddMonoidAlgebra ℚ G :=
  AddMonoidAlgebra.single offset 1 * periodicEmbedding e (sequenceLaurent A) +
    periodicReverse (AddMonoidAlgebra.single offset 1 * periodicEmbedding e (sequenceLaurent B))

noncomputable def periodicGolayRight {G : Type*} [AddCommGroup G] (e : ℤ →+ G)
    (offset parity : G) {n : ℕ} (A B : Fin n → ℤ) : AddMonoidAlgebra ℚ G :=
  AddMonoidAlgebra.single parity 1 *
    (AddMonoidAlgebra.single offset 1 * periodicEmbedding e (sequenceLaurent B) -
      periodicReverse (AddMonoidAlgebra.single offset 1 * periodicEmbedding e (sequenceLaurent A)))

/-- The two reflected blocks of a length-n Golay pair have total periodic
energy 4n. Translations and the extra parity coordinate do not alter it. -/
theorem IsGolayPair.periodic_reflected_energy {G : Type*} [AddCommGroup G]
    (e : ℤ →+ G) (offset parity : G) {n : ℕ} {A B : Fin n → ℤ} (h : IsGolayPair A B) :
    periodicEnergy (periodicGolayLeft e offset A B) +
      periodicEnergy (periodicGolayRight e offset parity A B) =
      ((4 * n : ℕ) : AddMonoidAlgebra ℚ G) := by
  unfold periodicGolayLeft periodicGolayRight
  rw [periodicEnergy_shift, periodic_reflect_pair_energy,
    periodicEnergy_shift, periodicEnergy_shift, h.periodicEnergy_eq e]
  have hcast : AddMonoidAlgebra.single (0 : G) (2 * n : ℚ) =
      ((2 * n : ℕ) : AddMonoidAlgebra ℚ G) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using periodic_single_zero_natCast (G := G) (2 * n)
  rw [hcast]
  push_cast
  ring

/-- A constant total periodic energy is exactly the required sum of circulant
Gram matrices. -/
theorem periodic_gram_sum {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    {I : Type*} [Fintype I] {w : ℕ} (p : I → AddMonoidAlgebra ℚ G)
    (h : ∑ i, periodicEnergy (p i) = (w : AddMonoidAlgebra ℚ G)) :
    (∑ i, periodicMatrix (p i) * (periodicMatrix (p i))ᴴ) = (w : Matrix G G ℚ) := by
  have hp := congrArg periodicMatrix h
  simpa only [map_sum, periodicEnergy, map_mul, periodicMatrix_reverse, map_natCast] using hp

end HadamardMultibase
