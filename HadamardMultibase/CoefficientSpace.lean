module

public import HadamardMultibase.Basic
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Card

@[expose] public section

namespace HadamardMultibase

open Matrix

/-- The coefficient index doubles at each merge. The recursive type makes
the block construction type-correct without casts between matrix orders. -/
abbrev CoeffSpace : ℕ → Type
  | 0 => Unit
  | n + 1 => CoeffSpace n ⊕ CoeffSpace n

instance coeffSpaceFintype (n : ℕ) : Fintype (CoeffSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (CoeffSpace n ⊕ CoeffSpace n))

instance coeffSpaceDecidableEq (n : ℕ) : DecidableEq (CoeffSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (CoeffSpace n ⊕ CoeffSpace n))

instance coeffSpaceInhabited (n : ℕ) : Inhabited (CoeffSpace n) := by
  induction n with
  | zero => exact inferInstanceAs (Inhabited Unit)
  | succ n ih =>
    exact ⟨Sum.inl ih.default⟩

@[simp] theorem card_coeffSpace (n : ℕ) : Fintype.card (CoeffSpace n) = 2 ^ n := by
  induction n with
  | zero =>
    let e : CoeffSpace 0 ≃ Unit := Equiv.refl _
    exact (Fintype.card_congr e).trans Fintype.card_unit
  | succ n ih =>
    let e : CoeffSpace (n + 1) ≃ (CoeffSpace n ⊕ CoeffSpace n) := Equiv.refl _
    calc
      _ = Fintype.card (CoeffSpace n ⊕ CoeffSpace n) := Fintype.card_congr e
      _ = 2 ^ n + 2 ^ n := by rw [Fintype.card_sum, ih]
      _ = _ := by rw [pow_succ]; omega

theorem exists_hadamard_coeffSpace (n : ℕ) :
    ∃ H : Matrix (CoeffSpace n) (CoeffSpace n) ℤ, H.IsHadamard := by
  obtain ⟨_, H, hH⟩ := hadamardOrder_two_pow n
  let e : Fin (2 ^ n) ≃ CoeffSpace n := Fintype.equivOfCardEq (by simp)
  exact ⟨Matrix.reindex e e H, hH.reindex e e⟩

theorem hadamardOrder_of_index {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : Matrix ι ι ℤ) (hH : H.IsHadamard) : HadamardOrder (Fintype.card ι) := by
  let e := Fintype.equivFin ι
  exact ⟨Fintype.card_pos, Matrix.reindex e e H, hH.reindex e e⟩

end HadamardMultibase
