module

public import HadamardMultibase.Basic
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Fintype.Sigma

@[expose] public section

namespace HadamardMultibase

def prefixLength {r : ℕ} (l : Fin r → ℕ) (i : Fin r) : ℕ :=
  ∑ k ∈ Finset.Iio i, l k

theorem prefixLength_add_le_total {r : ℕ} (l : Fin r → ℕ) (i : Fin r) :
    prefixLength l i + l i ≤ ∑ k, l k := by
  calc
    _ = ∑ k ∈ insert i (Finset.Iio i), l k := by
      rw [Finset.sum_insert (by simp)]
      exact Nat.add_comm _ _
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem prefixLength_separated {r : ℕ} (l : Fin r → ℕ) {i j : Fin r} (hij : i < j) :
    prefixLength l i + l i ≤ prefixLength l j := by
  calc
    _ = ∑ k ∈ insert i (Finset.Iio i), l k := by
      rw [Finset.sum_insert (by simp)]
      exact Nat.add_comm _ _
    _ ≤ _ := Finset.sum_le_sum_of_subset (by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact Finset.mem_Iio.mpr hij
      · exact Finset.mem_Iio.mpr ((Finset.mem_Iio.mp hk).trans hij))

def packedPosition {r : ℕ} (l : Fin r → ℕ) (t : Σ i, Fin (l i)) : ℕ :=
  prefixLength l t.1 + t.2.val

theorem packedPosition_lt {r : ℕ} (l : Fin r → ℕ) (t : Σ i, Fin (l i)) :
    packedPosition l t < ∑ i, l i := by
  have h := prefixLength_add_le_total l t.1
  have ht := t.2.isLt
  dsimp [packedPosition]
  omega

theorem packedPosition_injective {r : ℕ} (l : Fin r → ℕ) :
    Function.Injective (packedPosition l) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hij : i = j := by
    by_contra hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hs := prefixLength_separated l hij
      have ha := a.isLt
      dsimp [packedPosition] at h
      omega
    · have hs := prefixLength_separated l hji
      have hb := b.isLt
      dsimp [packedPosition] at h
      omega
  subst j
  have hab : a = b := Fin.ext (by dsimp [packedPosition] at h; omega)
  cases hab
  rfl

def packedIndex {r : ℕ} (l : Fin r → ℕ) (t : Σ i, Fin (l i)) : Fin (∑ i, l i) :=
  ⟨packedPosition l t, packedPosition_lt l t⟩

theorem packedIndex_bijective {r : ℕ} (l : Fin r → ℕ) : Function.Bijective (packedIndex l) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b h
    exact packedPosition_injective l (congrArg Fin.val h)
  · simp

noncomputable def packedEquiv {r : ℕ} (l : Fin r → ℕ) :
    (Σ i, Fin (l i)) ≃ Fin (∑ i, l i) := Equiv.ofBijective _ (packedIndex_bijective l)

@[simp] theorem packedEquiv_apply {r : ℕ} (l : Fin r → ℕ) (t : Σ i, Fin (l i)) :
    (packedEquiv l t).val = prefixLength l t.1 + t.2.val := rfl

end HadamardMultibase
