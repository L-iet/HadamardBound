module

public import HadamardMultibase.Arithmetic
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace HadamardMultibase

theorem SumOfAtMost.mono_terms {S : Set ℕ} {m k n : ℕ}
    (h : SumOfAtMost S m n) (hm : m ≤ k) : SumOfAtMost S k n := by
  obtain ⟨l, hl, hS, hn⟩ := h
  exact ⟨l, hl.trans hm, hS, hn⟩

theorem SumOfAtMost.mono_set {S T : Set ℕ} {m n : ℕ}
    (h : SumOfAtMost S m n) (hST : S ⊆ T) : SumOfAtMost T m n := by
  obtain ⟨l, hl, hS, hn⟩ := h
  exact ⟨l, hl, fun x hx => hST (hS x hx), hn⟩

theorem sumOfAtMost_zero (S : Set ℕ) (m : ℕ) : SumOfAtMost S m 0 :=
  ⟨[], by simp, by simp, rfl⟩

/-- Sums of at most m entries of a finite alphabet, padded with zero to
exactly m entries so that stars-and-bars applies. -/
def boundedSums (s : Finset ℕ) (m : ℕ) : Finset ℕ :=
  ((insert 0 s).sym m).image (fun v => v.val.sum)

theorem mem_boundedSums_of_representation {s : Finset ℕ} {m n : ℕ}
    (h : SumOfAtMost (s : Set ℕ) m n) : n ∈ boundedSums s m := by
  obtain ⟨l, hl, hmem, hsum⟩ := h
  let v : Sym ℕ m := ⟨(l : Multiset ℕ) + Multiset.replicate (m - l.length) 0, by
    simp only [Multiset.card_add, Multiset.coe_card, Multiset.card_replicate]
    omega⟩
  apply Finset.mem_image.mpr
  refine ⟨v, Finset.mem_sym_iff.mpr ?_, ?_⟩
  · intro x hx
    change x ∈ (l : Multiset ℕ) + Multiset.replicate (m - l.length) 0 at hx
    simp only [Multiset.mem_add, Multiset.mem_coe, Multiset.mem_replicate] at hx
    rcases hx with hx | ⟨_, rfl⟩
    · exact Finset.mem_insert_of_mem (hmem x hx)
    · simp
  · simp [v, hsum]

theorem card_finset_sym (s : Finset ℕ) (m : ℕ) :
    (s.sym m).card = (s.card + m - 1).choose m := by
  let e : s ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have he : (Finset.univ : Finset s).map e = s := by
    ext x
    simp [e]
  have h := Finset.sym_map e (Finset.univ : Finset s) (n := m)
  rw [he, Finset.sym_univ] at h
  rw [h, Finset.card_map, Finset.card_univ, Sym.card_sym_eq_choose, Fintype.card_coe]

theorem boundedSums_card_le (s : Finset ℕ) (m : ℕ) (h0 : 0 ∉ s) :
    (boundedSums s m).card ≤ (s.card + m).choose m := by
  calc
    _ ≤ ((insert 0 s).sym m).card := Finset.card_image_le
    _ = _ := by
      rw [card_finset_sym, Finset.card_insert_of_notMem h0]
      congr 1
      omega

/-- Finite pigeonhole step of the covering upper bound, with the sharp
multiset count from the manuscript. -/
theorem exists_missing_of_count {S : Set ℕ} {s : Finset ℕ} {m N : ℕ}
    (hs : ∀ x ∈ S, x ≤ N → x ∈ s) (h0 : 0 ∉ s)
    (hcount : (s.card + m).choose m < N) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧ ¬ SumOfAtMost S m n := by
  by_contra h
  push Not at h
  have hsub : Finset.Icc 1 N ⊆ boundedSums s m := by
    intro n hn
    obtain ⟨hn₁, hnN⟩ := Finset.mem_Icc.mp hn
    obtain ⟨l, hl, hS, hsum⟩ := h n hn₁ hnN
    apply mem_boundedSums_of_representation
    refine ⟨l, hl, ?_, hsum⟩
    intro x hx
    apply hs x (hS x hx)
    have hxle : x ≤ l.sum := List.le_sum_of_mem hx
    omega
  have hc := (Finset.card_le_card hsub).trans (boundedSums_card_le s m h0)
  have hIcc : (Finset.Icc 1 N).card = N := by simp
  omega

/-- A witness is mandatory: no minimum is assigned before existence is proved. -/
def HasMissing (S : Set ℕ) (m : ℕ) : Prop := ∃ n : ℕ, 0 < n ∧ ¬ SumOfAtMost S m n

noncomputable def coveringNumber (S : Set ℕ) (m : ℕ) (h : HasMissing S m) : ℕ := by
  classical
  exact Nat.find h

theorem coveringNumber_pos {S : Set ℕ} {m : ℕ} (h : HasMissing S m) :
    0 < coveringNumber S m h := by
  classical
  exact (Nat.find_spec h).1

theorem coveringNumber_not_representable {S : Set ℕ} {m : ℕ} (h : HasMissing S m) :
    ¬ SumOfAtMost S m (coveringNumber S m h) := by
  classical
  exact (Nat.find_spec h).2

theorem coveringNumber_le_of_missing {S : Set ℕ} {m n : ℕ}
    (h : HasMissing S m) (hn : 0 < n) (hnot : ¬ SumOfAtMost S m n) :
    coveringNumber S m h ≤ n := by
  classical
  exact Nat.find_min' h ⟨hn, hnot⟩

theorem representable_below_coveringNumber {S : Set ℕ} {m n : ℕ}
    (h : HasMissing S m) (hn : n < coveringNumber S m h) : SumOfAtMost S m n := by
  classical
  by_cases hn0 : n = 0
  · simpa [hn0] using sumOfAtMost_zero S m
  · by_contra hrep
    exact (Nat.find_min h hn) ⟨by omega, hrep⟩

end HadamardMultibase
