module

public import HadamardMultibase.CraigenShuffle

@[expose] public section

namespace HadamardMultibase

open Matrix

def SignedOrZero {κ : Type*} [DecidableEq κ] (A : Matrix κ κ ℤ) : Prop :=
  A = 0 ∨ IsSignedPermutation A

def mergeSequence {G κ : Type*} [Neg G] (f g : G → Matrix κ κ ℤ) :
    G → Matrix (κ ⊕ κ) (κ ⊕ κ) ℤ := fun x =>
  Matrix.fromBlocks (f x) (g x) (-(g (-x))ᴴ) (f (-x))ᴴ

theorem coefficientMerge_circulant {G κ : Type*} [Fintype G] [AddCommGroup G]
    [Fintype κ] [DecidableEq κ] (f g : G → Matrix κ κ ℤ) :
    coefficientMerge (circulant f) (circulant g) = circulant (mergeSequence f g) := by
  funext i j
  rw [coefficientMerge_apply]
  simp only [circulant_apply, mergeSequence, neg_sub]

/-- Exactly the union of the two original supports survives a merge. -/
theorem mergeSequence_eq_zero {G κ : Type*} [InvolutiveNeg G]
    (f g : G → Matrix κ κ ℤ)
    (hf : ∀ x, f x = 0 ↔ f (-x) = 0) (hg : ∀ x, g x = 0 ↔ g (-x) = 0) (x : G) :
    mergeSequence f g x = 0 ↔ f x = 0 ∧ g x = 0 := by
  constructor
  · intro h
    constructor
    · ext a b
      simpa [mergeSequence, Matrix.fromBlocks] using
        congrArg (fun M : Matrix (κ ⊕ κ) (κ ⊕ κ) ℤ => M (Sum.inl a) (Sum.inl b)) h
    · ext a b
      simpa [mergeSequence, Matrix.fromBlocks] using
        congrArg (fun M : Matrix (κ ⊕ κ) (κ ⊕ κ) ℤ => M (Sum.inl a) (Sum.inr b)) h
  · rintro ⟨hfx, hgx⟩
    have hfx' := (hf x).mp hfx
    have hgx' := (hg x).mp hgx
    simp [mergeSequence, hfx, hgx, hfx', hgx']

theorem mergeSequence_quasisymmetric {G κ : Type*} [InvolutiveNeg G]
    (f g : G → Matrix κ κ ℤ)
    (hf : ∀ x, f x = 0 ↔ f (-x) = 0) (hg : ∀ x, g x = 0 ↔ g (-x) = 0) (x : G) :
    mergeSequence f g x = 0 ↔ mergeSequence f g (-x) = 0 := by
  rw [mergeSequence_eq_zero f g hf hg, mergeSequence_eq_zero f g hf hg]
  exact and_congr (hf x) (hg x)

theorem mergeSequence_signedOrZero {G κ : Type*} [InvolutiveNeg G] [DecidableEq κ]
    (f g : G → Matrix κ κ ℤ)
    (hf : ∀ x, SignedOrZero (f x)) (hg : ∀ x, SignedOrZero (g x))
    (hfsym : ∀ x, f x = 0 ↔ f (-x) = 0) (hgsym : ∀ x, g x = 0 ↔ g (-x) = 0)
    (hdisj : ∀ x, f x = 0 ∨ g x = 0) : ∀ x, SignedOrZero (mergeSequence f g x) := by
  intro x
  by_cases hfx : f x = 0
  · have hfx' := (hfsym x).mp hfx
    by_cases hgx : g x = 0
    · exact Or.inl ((mergeSequence_eq_zero f g hfsym hgsym x).mpr ⟨hfx, hgx⟩)
    · have hgx' : g (-x) ≠ 0 := fun h => hgx ((hgsym x).mpr h)
      have hgxS := (hg x).resolve_left hgx
      have hgxS' := (hg (-x)).resolve_left hgx'
      apply Or.inr
      simpa [mergeSequence, hfx, hfx'] using
        hgxS.blockAntiDiagonal hgxS'.conjTranspose.neg
  · have hgx : g x = 0 := (hdisj x).resolve_left hfx
    have hgx' := (hgsym x).mp hgx
    have hfx' : f (-x) ≠ 0 := fun h => hfx ((hfsym x).mpr h)
    have hfxS := (hf x).resolve_left hfx
    have hfxS' := (hf (-x)).resolve_left hfx'
    apply Or.inr
    simpa [mergeSequence, hgx, hgx'] using hfxS.blockDiagonal hfxS'.conjTranspose

theorem mergeSequence_disjoint {G κ : Type*} [InvolutiveNeg G]
    (f g h : G → Matrix κ κ ℤ)
    (hf : ∀ x, f x = 0 ↔ f (-x) = 0) (hg : ∀ x, g x = 0 ↔ g (-x) = 0)
    (hfh : ∀ x, f x = 0 ∨ h x = 0) (hgh : ∀ x, g x = 0 ∨ h x = 0) (x : G) :
    mergeSequence f g x = 0 ∨ h x = 0 := by
  by_cases hh : h x = 0
  · exact Or.inr hh
  · exact Or.inl ((mergeSequence_eq_zero f g hf hg x).mpr
      ⟨(hfh x).resolve_right hh, (hgh x).resolve_right hh⟩)

end HadamardMultibase
