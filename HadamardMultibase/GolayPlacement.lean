module

public import HadamardMultibase.PeriodPositions
public import HadamardMultibase.PartitionedFamily

@[expose] public section

namespace HadamardMultibase

abbrev PlacementComponents (r : ℕ) := (Unit ⊕ Fin r) × Bool

def placementOwner {r : ℕ} {l : Fin r → ℕ} : PlacementSlots l → PlacementComponents r
  | (Sum.inl u, b) => (Sum.inl u, b)
  | (Sum.inr (t, _), b) => (Sum.inr t.1, b)

def placementSign {r : ℕ} {l : Fin r → ℕ} (A B : ∀ i, Fin (l i) → ℤ) : PlacementSlots l → ℤ
  | (Sum.inl _, _) => 1
  | (Sum.inr (⟨i, j⟩, s), b) =>
      if s then (if b then -A i j else B i j) else (if b then B i j else A i j)

theorem placementSign_binary {r : ℕ} {l : Fin r → ℕ} (A B : ∀ i, Fin (l i) → ℤ)
    (hA : ∀ i, IsBinary (A i)) (hB : ∀ i, IsBinary (B i)) :
    ∀ d, placementSign A B d = 1 ∨ placementSign A B d = -1 := by
  rintro ⟨u | ⟨⟨i, j⟩, s⟩, b⟩
  · exact Or.inl rfl
  · cases s <;> cases b
    · exact hA i j
    · exact hB i j
    · exact hB i j
    · obtain h | h := hA i j <;> simp [placementSign, h]

theorem placementOwner_mirror {r : ℕ} {l : Fin r → ℕ} (d : PlacementSlots l) :
    placementOwner (mirrorSlot d) = placementOwner d := by
  rcases d with ⟨u | ⟨t, s⟩, b⟩ <;> rfl

def placementStep {r : ℕ} (l : Fin r → ℕ) : ℤ →+ PlacementGroup (∑ i, l i) where
  toFun k := (k, 0)
  map_zero' := by simp
  map_add' := by intros; simp

def placementOffset {r : ℕ} (l : Fin r → ℕ) (i : Fin r) : PlacementGroup (∑ i, l i) :=
  ((prefixLength l i + 1 : ℕ), 0)

def placementParity {r : ℕ} (l : Fin r → ℕ) : PlacementGroup (∑ i, l i) := (0, 1)

theorem placement_pair_affine {r : ℕ} (l : Fin r → ℕ) (i : Fin r) (j : Fin (l i)) (s b : Bool) :
    placementEquiv l (Sum.inr (⟨i, j⟩, s), b) =
      (if s then -(placementOffset l i + placementStep l j.val)
        else placementOffset l i + placementStep l j.val) +
      (if b then placementParity l else 0) := by
  rw [placementEquiv_pair]
  cases s <;> cases b <;> ext <;>
    simp [placementOffset, placementStep, placementParity, parityBit, Nat.cast_add,
      Nat.cast_one, Int.cast_natCast] <;> ring

theorem periodicShift_expansion {G : Type*} [AddCommGroup G] (e : ℤ →+ G) (offset : G)
    {n : ℕ} (A : Fin n → ℤ) :
    AddMonoidAlgebra.single offset 1 * periodicEmbedding e (sequenceLaurent A) =
      ∑ j : Fin n, AddMonoidAlgebra.single (offset + e j.val) (A j : ℚ) := by
  unfold sequenceLaurent
  simp only [map_sum, periodicEmbedding_single, Finset.mul_sum,
    AddMonoidAlgebra.single_mul_single, one_mul]

theorem placementPolynomial_delta {r : ℕ} (l : Fin r → ℕ) (A B : ∀ i, Fin (l i) → ℤ) (b : Bool) :
    partitionPolynomial placementOwner (placementEquiv l) (placementSign A B) (Sum.inl (), b) =
      AddMonoidAlgebra.single (0, parityBit b) 1 := by
  cases b <;>
    simp [partitionPolynomial, placementOwner, placementSign, Fintype.sum_prod_type,
      Fintype.sum_sum_type, placementEquiv_delta]

set_option maxHeartbeats 2000000 in
theorem placementPolynomial_left {r : ℕ} (l : Fin r → ℕ) (A B : ∀ i, Fin (l i) → ℤ) (i : Fin r) :
    partitionPolynomial placementOwner (placementEquiv l) (placementSign A B) (Sum.inr i, false) =
      periodicGolayLeft (placementStep l) (placementOffset l i) (A i) (B i) := by
  unfold periodicGolayLeft
  rw [periodicShift_expansion, periodicShift_expansion, map_sum]
  simp [partitionPolynomial, placementOwner, placementSign, Fintype.sum_prod_type,
    Fintype.sum_sum_type, Fintype.sum_sigma, placement_pair_affine,
    periodicReverse_single, Finset.sum_ite_irrel, Finset.sum_add_distrib]
  abel

set_option maxHeartbeats 2000000 in
theorem placementPolynomial_right {r : ℕ} (l : Fin r → ℕ) (A B : ∀ i, Fin (l i) → ℤ) (i : Fin r) :
    partitionPolynomial placementOwner (placementEquiv l) (placementSign A B) (Sum.inr i, true) =
      periodicGolayRight (placementStep l) (placementOffset l i) (placementParity l) (A i) (B i) := by
  unfold periodicGolayRight
  rw [periodicShift_expansion, periodicShift_expansion, map_sum]
  simp [partitionPolynomial, placementOwner, placementSign, Fintype.sum_prod_type,
    Fintype.sum_sum_type, Fintype.sum_sigma, placement_pair_affine,
    periodicReverse_single, Finset.sum_ite_irrel, Finset.sum_add_distrib,
    mul_add, mul_neg, Finset.mul_sum, AddMonoidAlgebra.single_mul_single, one_mul,
    AddMonoidAlgebra.single_neg, Int.cast_neg, Finset.sum_neg_distrib, sub_eq_add_neg]
  simp only [add_left_comm, add_comm]

end HadamardMultibase
