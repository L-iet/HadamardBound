module

public import HadamardMultibase.Arithmetic

@[expose] public section

namespace HadamardMultibase

/-- A distinct-summand representation over a general multiplicative alphabet. -/
def DistinctSum (S : Set ℕ) (n : ℕ) (s : Finset ℕ) : Prop :=
  (∀ a ∈ s, a ∈ S) ∧ ∑ a ∈ s, a = n

theorem distinctSum_golay_iff (n : ℕ) (s : Finset ℕ) :
    DistinctSum golayMonoid₂ n s ↔ SparseDecomposition n s := Iff.rfl

theorem DistinctSum.member_le {S : Set ℕ} {n : ℕ} {s : Finset ℕ}
    (h : DistinctSum S n s) {a : ℕ} (ha : a ∈ s) : a ≤ n := by
  have hle : a ≤ ∑ x ∈ s, x :=
    Finset.single_le_sum (f := fun x : ℕ => x) (fun _ _ => Nat.zero_le _) ha
  exact hle.trans_eq h.2

theorem DistinctSum.card_le {S : Set ℕ} {n : ℕ} {s : Finset ℕ}
    (h : DistinctSum S n s) (hpos : ∀ a ∈ S, 0 < a) : s.card ≤ n := by
  calc
    s.card = ∑ _a ∈ s, 1 := by simp
    _ ≤ ∑ a ∈ s, a := Finset.sum_le_sum (fun a ha => hpos a (h.1 a ha))
    _ = n := h.2

/-- Greedy strong induction with an explicit real budget. The residual being
smaller than the new summand ensures that the representation stays distinct. -/
theorem greedy_distinct_sum {S : Set ℕ} (F : ℕ → ℝ) (N : ℕ)
    (hbase : ∀ n ≤ N, ∃ s : Finset ℕ, DistinctSum S n s ∧ (s.card : ℝ) ≤ F n)
    (hstep : ∀ n : ℕ, N < n → ∃ b : ℕ, b ∈ S ∧ 0 < b ∧ b ≤ n ∧
      n - b < b ∧ F (n - b) + 1 ≤ F n) :
    ∀ n : ℕ, ∃ s : Finset ℕ, DistinctSum S n s ∧ (s.card : ℝ) ≤ F n := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ N
    · exact hbase n hn
    · obtain ⟨b, hbS, hbpos, hbn, hsmall, hbudget⟩ := hstep n (by omega)
      obtain ⟨s, hs, hcard⟩ := ih (n - b) (by omega)
      have hbnot : b ∉ s := by
        intro hbs
        have hle := hs.member_le hbs
        omega
      refine ⟨insert b s, ⟨?_, ?_⟩, ?_⟩
      · intro a ha
        rcases Finset.mem_insert.mp ha with rfl | ha
        · exact hbS
        · exact hs.1 a ha
      · rw [Finset.sum_insert hbnot, hs.2]
        omega
      · rw [Finset.card_insert_of_notMem hbnot, Nat.cast_add, Nat.cast_one]
        linarith

theorem exists_distinctSum_of_powers_two {S : Set ℕ}
    (htwo : ∀ a : ℕ, 2 ^ a ∈ S) (n : ℕ) : ∃ s : Finset ℕ, DistinctSum S n s := by
  let s := n.bitIndices.toFinset.image (fun i => 2 ^ i)
  refine ⟨s, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact htwo a
  · dsimp [s]
    rw [Finset.sum_image]
    · simpa using (List.sum_toFinset (fun i => 2 ^ i) Nat.bitIndices_nodup).trans
        (Nat.sum_map_two_pow_bitIndices n)
    · intro a _ b _ h
      exact Nat.pow_right_injective (by omega) h

end HadamardMultibase
