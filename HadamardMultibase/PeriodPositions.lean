module

public import HadamardMultibase.PackedPositions
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Fintype.Sum

@[expose] public section

namespace HadamardMultibase

def signedResidue (L : ℕ) (k : Fin L) (b : Bool) : ZMod (2 * L + 1) :=
  if b then -((k.val + 1 : ℕ) : ZMod (2 * L + 1)) else (k.val + 1 : ℕ)

theorem signedResidue_val (L : ℕ) (k : Fin L) (b : Bool) :
    (signedResidue L k b).val = if b then 2 * L + 1 - (k.val + 1) else k.val + 1 := by
  have hk := k.isLt
  have hlt : k.val + 1 < 2 * L + 1 := by omega
  have hv := ZMod.val_natCast_of_lt hlt
  have hne : ((k.val + 1 : ℕ) : ZMod (2 * L + 1)) ≠ 0 := by
    intro h
    have hzero := congrArg ZMod.val h
    rw [hv, ZMod.val_zero] at hzero
    omega
  cases b with
  | false => exact hv
  | true =>
    change (-((k.val + 1 : ℕ) : ZMod (2 * L + 1))).val = 2 * L + 1 - (k.val + 1)
    rw [ZMod.neg_val, ite_eq_right hne, hv]

theorem signedResidue_ne_zero (L : ℕ) (k : Fin L) (b : Bool) : signedResidue L k b ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [signedResidue_val, ZMod.val_zero] at hv
  have hk := k.isLt
  cases b <;> simp at hv; omega

theorem signedResidue_injective (L : ℕ) :
    Function.Injective (fun p : Fin L × Bool => signedResidue L p.1 p.2) := by
  rintro ⟨k, b⟩ ⟨l, c⟩ h
  change signedResidue L k b = signedResidue L l c at h
  have hv := congrArg ZMod.val h
  rw [signedResidue_val, signedResidue_val] at hv
  have hk := k.isLt
  have hl := l.isLt
  cases b <;> cases c <;> simp at hv
  · have hkl : k = l := Fin.ext (by omega)
    exact congrArg (fun k : Fin L => (k, false)) hkl
  · omega
  · omega
  · have hkl : k = l := Fin.ext (by omega)
    exact congrArg (fun k : Fin L => (k, true)) hkl

def residuePosition (L : ℕ) : Unit ⊕ (Fin L × Bool) → ZMod (2 * L + 1)
  | Sum.inl _ => 0
  | Sum.inr p => signedResidue L p.1 p.2

theorem residuePosition_injective (L : ℕ) : Function.Injective (residuePosition L) := by
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl (Subsingleton.elim a b)
  · exact False.elim (signedResidue_ne_zero L b.1 b.2 h.symm)
  · exact False.elim (signedResidue_ne_zero L a.1 a.2 h)
  · exact congrArg Sum.inr (signedResidue_injective L h)

theorem residuePosition_bijective (L : ℕ) : Function.Bijective (residuePosition L) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨residuePosition_injective L, ?_⟩
  simp
  omega

noncomputable def residueEquiv (L : ℕ) : Unit ⊕ (Fin L × Bool) ≃ ZMod (2 * L + 1) :=
  Equiv.ofBijective _ (residuePosition_bijective L)

def parityBit (b : Bool) : ZMod 2 := if b then 1 else 0

theorem parityBit_bijective : Function.Bijective parityBit := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro b c h
    cases b <;> cases c <;> simp [parityBit] at h <;> rfl
  · simp

noncomputable def parityEquiv : Bool ≃ ZMod 2 := Equiv.ofBijective _ parityBit_bijective

abbrev PlacementSlots {r : ℕ} (l : Fin r → ℕ) :=
  (Unit ⊕ ((Σ i, Fin (l i)) × Bool)) × Bool

abbrev PlacementGroup (L : ℕ) := ZMod (2 * L + 1) × ZMod 2

noncomputable def placementEquiv {r : ℕ} (l : Fin r → ℕ) :
    PlacementSlots l ≃ PlacementGroup (∑ i, l i) :=
  Equiv.prodCongr
    ((Equiv.sumCongr (Equiv.refl Unit) (Equiv.prodCongr (packedEquiv l) (Equiv.refl Bool))).trans
      (residueEquiv (∑ i, l i))) parityEquiv

theorem placementEquiv_delta {r : ℕ} (l : Fin r → ℕ) (b : Bool) :
    placementEquiv l (Sum.inl (), b) = (0, parityBit b) := rfl

theorem placementEquiv_pair {r : ℕ} (l : Fin r → ℕ) (t : Σ i, Fin (l i)) (s b : Bool) :
    placementEquiv l (Sum.inr (t, s), b) =
      (if s then -((prefixLength l t.1 + t.2.val + 1 : ℕ) : ZMod (2 * (∑ i, l i) + 1))
        else ((prefixLength l t.1 + t.2.val + 1 : ℕ) : ZMod (2 * (∑ i, l i) + 1)),
        parityBit b) := rfl

def mirrorSlot {r : ℕ} {l : Fin r → ℕ} : PlacementSlots l → PlacementSlots l
  | (Sum.inl u, b) => (Sum.inl u, b)
  | (Sum.inr (t, s), b) => (Sum.inr (t, !s), b)

theorem placementEquiv_mirror {r : ℕ} (l : Fin r → ℕ) (t : PlacementSlots l) :
    placementEquiv l (mirrorSlot t) = -(placementEquiv l t) := by
  rcases t with ⟨u | ⟨t, s⟩, b⟩
  · cases u
    cases b <;> simp [mirrorSlot, placementEquiv_delta, parityBit]
  · cases s <;> cases b <;> simp [mirrorSlot, placementEquiv_pair, parityBit]

end HadamardMultibase
