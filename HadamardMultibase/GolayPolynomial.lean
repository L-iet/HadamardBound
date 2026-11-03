module

public import HadamardMultibase.GolayAlgebra

@[expose] public section

namespace HadamardMultibase

open scoped LaurentPolynomial

noncomputable def sequenceLaurent {n : ℕ} (A : Fin n → ℤ) : ℚ[T;T⁻¹] :=
  ∑ i : Fin n, AddMonoidAlgebra.single (i.val : ℤ) (A i : ℚ)

theorem laurent_invert_single (k : ℤ) (a : ℚ) :
    LaurentPolynomial.invert (AddMonoidAlgebra.single k a : ℚ[T;T⁻¹]) =
      AddMonoidAlgebra.single (-k) a := by
  simp only [LaurentPolynomial.single_eq_C_mul_T, map_mul,
    LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]

theorem sequenceLaurent_energy_expansion {n : ℕ} (A : Fin n → ℤ) :
    laurentEnergy (sequenceLaurent A) =
      ∑ j : Fin n, ∑ i : Fin n,
        AddMonoidAlgebra.single ((i.val : ℤ) - j.val) ((A i : ℚ) * A j) := by
  unfold laurentEnergy sequenceLaurent
  simp only [map_sum, laurent_invert_single, Finset.sum_mul, Finset.mul_sum,
    AddMonoidAlgebra.single_mul_single, sub_eq_add_neg]

theorem sequenceLaurent_energy_coeff_nat {n : ℕ} (A : Fin n → ℤ) (s : ℕ) :
    (laurentEnergy (sequenceLaurent A)).coeff s =
      ∑ j : Fin n, if h : j.val + s < n then
        (A j : ℚ) * A ⟨j.val + s, h⟩ else 0 := by
  rw [sequenceLaurent_energy_expansion]
  simp only [AddMonoidAlgebra.coeff_sum, Finset.sum_apply', AddMonoidAlgebra.coeff_single]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val + s < n
  · rw [dite_eq_left hj]
    let i₀ : Fin n := ⟨j.val + s, hj⟩
    rw [Finset.sum_eq_single i₀]
    · simp [i₀, mul_comm]
    · intro i _ hi
      apply Finsupp.single_eq_of_ne
      intro he
      apply hi
      apply Fin.ext
      dsimp [i₀]
      omega
    · simp
  · rw [dite_eq_right hj]
    apply Finset.sum_eq_zero
    intro i _
    apply Finsupp.single_eq_of_ne
    intro he
    have hi := i.isLt
    omega

theorem autocorrelation_eq_fin_sum {n : ℕ} (A : Fin n → ℤ) (s : ℕ) :
    autocorrelation A s = ∑ j : Fin n, if h : j.val + s < n then
      A j * A ⟨j.val + s, h⟩ else 0 := by
  let f : ℕ → ℤ := fun j =>
    if h : j + s < n then A ⟨j, by omega⟩ * A ⟨j + s, h⟩ else 0
  have hsum : (∑ j ∈ Finset.range n, f j) = ∑ j ∈ Finset.range (n - s), f j := by
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.sub_le n s))
    intro j _ hj
    have h : ¬ j + s < n := by simp only [Finset.mem_range] at hj; omega
    simp [f, h]
  change (∑ j ∈ Finset.range (n - s), f j) = _
  rw [← hsum, Finset.sum_range]

theorem sequenceLaurent_energy_coeff_autocorrelation {n : ℕ} (A : Fin n → ℤ) (s : ℕ) :
    (laurentEnergy (sequenceLaurent A)).coeff s = (autocorrelation A s : ℚ) := by
  rw [sequenceLaurent_energy_coeff_nat, autocorrelation_eq_fin_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

theorem IsBinary.energy_coeff_zero {n : ℕ} {A : Fin n → ℤ} (hA : IsBinary A) :
    (laurentEnergy (sequenceLaurent A)).coeff 0 = (n : ℚ) := by
  rw [show (0 : ℤ) = (0 : ℕ) by rfl, sequenceLaurent_energy_coeff_nat]
  calc
    _ = ∑ j : Fin n, (1 : ℚ) := by
      apply Finset.sum_congr rfl
      intro j _
      obtain h | h := hA j <;> simp [j.isLt, h]
    _ = _ := by simp

theorem laurentEnergy_coeff_neg (p : ℚ[T;T⁻¹]) (k : ℤ) :
    (laurentEnergy p).coeff (-k) = (laurentEnergy p).coeff k := by
  have h : LaurentPolynomial.invert (laurentEnergy p) = laurentEnergy p := by
    simp [laurentEnergy, mul_comm]
  simpa using congrArg (fun q : ℚ[T;T⁻¹] => q.coeff k) h

theorem IsGolayPair.laurentEnergy_eq {n : ℕ} {A B : Fin n → ℤ}
    (h : IsGolayPair A B) :
    laurentEnergy (sequenceLaurent A) + laurentEnergy (sequenceLaurent B) =
      LaurentPolynomial.C (2 * n : ℚ) := by
  ext k
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, LaurentPolynomial.C_apply]
  have hpos (s : ℕ) (hs : 0 < s) :
      (laurentEnergy (sequenceLaurent A)).coeff s +
        (laurentEnergy (sequenceLaurent B)).coeff s = 0 := by
    rw [sequenceLaurent_energy_coeff_autocorrelation,
      sequenceLaurent_energy_coeff_autocorrelation, ← Int.cast_add, h.correlation_sum hs]
    rfl
  rcases k with s | s
  · cases s with
    | zero => simp [h.1.energy_coeff_zero, h.2.1.energy_coeff_zero]; ring
    | succ s =>
      have hs : Int.ofNat (s + 1) ≠ 0 := by
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [ite_eq_right hs]
      exact hpos (s + 1) (by omega)
  · have he : Int.negSucc s = -((s + 1 : ℕ) : ℤ) := by omega
    rw [he, laurentEnergy_coeff_neg, laurentEnergy_coeff_neg]
    rw [ite_eq_right (by omega)]
    exact hpos (s + 1) (by omega)

theorem isGolayPair_of_laurentEnergy {n : ℕ} {A B : Fin n → ℤ}
    (hA : IsBinary A) (hB : IsBinary B)
    (h : laurentEnergy (sequenceLaurent A) + laurentEnergy (sequenceLaurent B) =
      LaurentPolynomial.C (2 * n : ℚ)) : IsGolayPair A B := by
  refine ⟨hA, hB, ?_⟩
  intro s hs _
  have hc := congrArg (fun p : ℚ[T;T⁻¹] => p.coeff (s : ℤ)) h
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, LaurentPolynomial.C_apply,
    sequenceLaurent_energy_coeff_autocorrelation] at hc
  have hs0 : (s : ℤ) ≠ 0 := by omega
  rw [ite_eq_right hs0, ← Int.cast_add] at hc
  exact_mod_cast hc

end HadamardMultibase
