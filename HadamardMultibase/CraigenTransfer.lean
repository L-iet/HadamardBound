module

public import HadamardMultibase.GolayPlacement
public import HadamardMultibase.Transfer
public import Mathlib.Data.List.OfFn

@[expose] public section

namespace HadamardMultibase

theorem placement_energy_sum {r : ℕ} (l : Fin r → ℕ) (A B : ∀ i, Fin (l i) → ℤ)
    (hAB : ∀ i, IsGolayPair (A i) (B i)) :
    (∑ c : PlacementComponents r,
      periodicEnergy (partitionPolynomial placementOwner (placementEquiv l) (placementSign A B) c)) =
      (Fintype.card (PlacementGroup (∑ i, l i)) : AddMonoidAlgebra ℚ (PlacementGroup (∑ i, l i))) := by
  have hdelta (b : Bool) :
      periodicEnergy (partitionPolynomial placementOwner (placementEquiv l) (placementSign A B)
        (Sum.inl (), b)) = 1 := by
    rw [placementPolynomial_delta]
    exact periodicEnergy_single_one _
  have hpair (i : Fin r) :
      periodicEnergy (partitionPolynomial placementOwner (placementEquiv l) (placementSign A B)
          (Sum.inr i, true)) +
        periodicEnergy (partitionPolynomial placementOwner (placementEquiv l) (placementSign A B)
          (Sum.inr i, false)) = ((4 * l i : ℕ) : AddMonoidAlgebra ℚ (PlacementGroup (∑ i, l i))) := by
    rw [placementPolynomial_right, placementPolynomial_left, add_comm]
    exact (hAB i).periodic_reflected_energy (placementStep l) (placementOffset l i) (placementParity l)
  have hcard : Fintype.card (PlacementGroup (∑ i, l i)) = 4 * (∑ i, l i) + 2 := by
    simp only [PlacementGroup, Fintype.card_prod, ZMod.card]
    omega
  rw [hcard]
  calc
    _ = 2 + ∑ i : Fin r, ((4 * l i : ℕ) : AddMonoidAlgebra ℚ (PlacementGroup (∑ i, l i))) := by
      simp [PlacementComponents, Fintype.sum_prod_type, Fintype.sum_sum_type,
        hdelta, hpair]
      norm_num
    _ = _ := by
      push_cast
      rw [← Finset.mul_sum]
      ring

/-- The finite-family form of Craigen's Golay-pair transfer. All placements,
support properties, periodic energies, and matrix constructions are proved. -/
theorem hadamardOrder_of_golay_family {r : ℕ} (l : Fin r → ℕ)
    (A B : ∀ i, Fin (l i) → ℤ) (hAB : ∀ i, IsGolayPair (A i) (B i)) :
    HadamardOrder (4 ^ (r + 1) * (2 * (∑ i, l i) + 1)) := by
  have hcard : Fintype.card (PlacementComponents r) = (2 * r + 1) + 1 := by
    simp only [PlacementComponents, Fintype.card_prod, Fintype.card_sum,
      Fintype.card_unit, Fintype.card_fin, Fintype.card_bool]
    omega
  have horder := hadamardOrder_of_partition (2 * r + 1) hcard placementOwner
    (placementEquiv l) (placementSign A B)
    (placementSign_binary A B (fun i => (hAB i).1) (fun i => (hAB i).2.1))
    mirrorSlot placementOwner_mirror (placementEquiv_mirror l) (placement_energy_sum l A B hAB)
  have hperiod : Fintype.card (PlacementGroup (∑ i, l i)) = (2 * (∑ i, l i) + 1) * 2 := by
    simp only [PlacementGroup, Fintype.card_prod, ZMod.card]
  have hpower : Fintype.card (PlacementGroup (∑ i, l i)) * 2 ^ (2 * r + 1) =
      4 ^ (r + 1) * (2 * (∑ i, l i) + 1) := by
    rw [hperiod, four_pow_eq_two_pow,
      show 2 * r + 2 = (2 * r + 1) + 1 by omega, pow_succ (2 : ℕ) (2 * r + 1)]
    ring
  simpa only [hpower] using horder

/-- The Craigen input is now discharged by a complete construction. -/
theorem craigenTransfer : CraigenTransfer := by
  classical
  intro l hGolay
  choose A B hAB using (fun i : Fin l.length => (hGolay (l.get i) (List.get_mem l i)).2)
  have hsum : (∑ i : Fin l.length, l.get i) = l.sum := by
    rw [← List.sum_ofFn, List.ofFn_get]
  simpa only [hsum] using hadamardOrder_of_golay_family (l.get) A B hAB

end HadamardMultibase
