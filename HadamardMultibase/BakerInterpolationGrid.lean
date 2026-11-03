/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerConfluentInterpolation

@[expose] public section

/-! # Confluent integer grids

The grid repeats each positive integer k times. Contiguous windows satisfy
the divided-difference recurrence; their endpoint separation controls its
denominator and supplies factorial decay beyond order k-1.
-/

namespace HadamardMultibase

def interpolationGridNode (k s : ℕ) : ℕ := s / k + 1

noncomputable def interpolationGridList (k s count : ℕ) : List ℂ :=
  (List.range count).map (fun j => (interpolationGridNode k (s + j) : ℂ))

@[simp] theorem interpolationGridList_length (k s count : ℕ) :
    (interpolationGridList k s count).length = count := by
  simp [interpolationGridList]

@[simp] theorem interpolationGridList_zero (k s : ℕ) : interpolationGridList k s 0 = [] := by
  simp [interpolationGridList]

theorem interpolationGridList_succ (k s count : ℕ) :
    interpolationGridList k s (count + 1) =
      (interpolationGridNode k s : ℂ) :: interpolationGridList k (s + 1) count := by
  simp only [interpolationGridList, List.range_succ_eq_map, List.map_cons, List.map_map,
    Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro j _
  simp [Nat.add_comm, Nat.add_left_comm]

theorem interpolationGridList_append_last (k s count : ℕ) :
    interpolationGridList k s (count + 1) = interpolationGridList k s count ++
      [(interpolationGridNode k (s + count) : ℂ)] := by
  simp [interpolationGridList, List.range_succ]

theorem interpolationGridList_take (k s count j : ℕ) (hj : j ≤ count) :
    (interpolationGridList k s count).take j = interpolationGridList k s j := by
  unfold interpolationGridList
  rw [← List.map_take, List.take_range, Nat.min_eq_left hj]

theorem interpolationGridNode_mono (k : ℕ) : Monotone (interpolationGridNode k) := by
  intro s t hst
  exact Nat.add_le_add_right (Nat.div_le_div_right hst) 1

theorem interpolationGridList_eq_replicate {k s n : ℕ}
    (he : interpolationGridNode k s = interpolationGridNode k (s + n)) :
    interpolationGridList k s (n + 1) =
      List.replicate (n + 1) (interpolationGridNode k s : ℂ) := by
  have hmem : ∀ a ∈ interpolationGridList k s (n + 1), a = (interpolationGridNode k s : ℂ) := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
    have hjn : j ≤ n := by have := List.mem_range.mp hj; omega
    have hlo := interpolationGridNode_mono k (Nat.le_add_right s j)
    have hhi := interpolationGridNode_mono k (Nat.add_le_add_left hjn s)
    rw [← he] at hhi
    congr 1
    omega
  have heq := List.eq_replicate_length.mpr hmem
  simpa only [interpolationGridList_length] using heq

theorem interpolationGridNode_lt_multiplicity {k s n : ℕ} (hk : 0 < k)
    (he : interpolationGridNode k s = interpolationGridNode k (s + n)) : n < k := by
  have hq : s / k = (s + n) / k := by simpa [interpolationGridNode] using he
  have hstart := Nat.div_add_mod s k
  have hend := Nat.div_add_mod (s + n) k
  have hrem := Nat.mod_lt (s + n) hk
  rw [← hq] at hend
  nlinarith [Nat.zero_le (s % k)]

theorem interpolationGridNode_separation {k s n : ℕ} (hk : 0 < k) :
    n + 1 - k ≤ k * (interpolationGridNode k (s + n) - interpolationGridNode k s) := by
  have hmono := interpolationGridNode_mono k (Nat.le_add_right s n)
  have hstart := Nat.div_add_mod s k
  have hend := Nat.div_add_mod (s + n) k
  have hrem := Nat.mod_lt (s + n) hk
  have hquot : s / k ≤ (s + n) / k := Nat.div_le_div_right (Nat.le_add_right s n)
  have hdiff : (s + n) / k - s / k =
      interpolationGridNode k (s + n) - interpolationGridNode k s := by
    simp [interpolationGridNode]
  have hsplit : (s + n) / k = ((s + n) / k - s / k) + s / k := by omega
  rw [hsplit] at hend
  rw [← hdiff]
  by_cases hn : n + 1 ≤ k
  · omega
  · have hsub : n + 1 - k + k = n + 1 := by omega
    nlinarith [Nat.zero_le (s % k)]

theorem interpolationGridNode_le {k N s : ℕ} (hk : 0 < k) (hs : s < k * N) :
    1 ≤ interpolationGridNode k s ∧ interpolationGridNode k s ≤ N := by
  have hq : s / k < N := (Nat.div_lt_iff_lt_mul hk).mpr (by simpa [Nat.mul_comm] using hs)
  exact ⟨Nat.succ_le_succ (Nat.zero_le _), Nat.succ_le_of_lt hq⟩

theorem interpolationGridList_norm_le {k N s count : ℕ} (hk : 0 < k)
    (hs : s + count ≤ k * N) :
    ∀ a ∈ interpolationGridList k s count, ‖a‖ ≤ (N : ℝ) := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
  have hjc := List.mem_range.mp hj
  have hnode := (interpolationGridNode_le hk (show s + j < k * N by omega)).2
  simpa only [Complex.norm_natCast] using (show (interpolationGridNode k (s + j) : ℝ) ≤ N by exact_mod_cast hnode)

theorem interpolationGrid_cauchy_recurrence {R : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.sphere 0 R)) {k N s n : ℕ}
    (hk : 0 < k) (hs : s + (n + 2) ≤ k * N) (hNR : (N : ℝ) < R) :
    ((interpolationGridNode k (s + n + 1) : ℂ) - interpolationGridNode k s) *
      cauchyDividedDifference R f (interpolationGridList k s (n + 2)) =
      cauchyDividedDifference R f (interpolationGridList k (s + 1) (n + 1)) -
        cauchyDividedDifference R f (interpolationGridList k s (n + 1)) := by
  let a : ℂ := interpolationGridNode k s
  let b : ℂ := interpolationGridNode k (s + n + 1)
  let middle := interpolationGridList k (s + 1) n
  have ha : ‖a‖ < R := by
    apply lt_of_le_of_lt _ hNR
    have he : (interpolationGridNode k s : ℝ) ≤ N := by
      exact_mod_cast (interpolationGridNode_le hk (show s < k * N by omega)).2
    simpa only [a, Complex.norm_natCast] using he
  have hb : ‖b‖ < R := by
    apply lt_of_le_of_lt _ hNR
    have he : (interpolationGridNode k (s + n + 1) : ℝ) ≤ N := by
      exact_mod_cast (interpolationGridNode_le hk (show s + n + 1 < k * N by omega)).2
    simpa only [b, Complex.norm_natCast] using he
  have hm : ∀ x ∈ middle, ‖x‖ < R := fun x hx =>
    (interpolationGridList_norm_le hk (show s + 1 + n ≤ k * N by omega) x hx).trans_lt hNR
  have hfull : (interpolationGridList k s (n + 2)).Perm (b :: a :: middle) := by
    rw [show n + 2 = (n + 1) + 1 by omega, interpolationGridList_append_last,
      interpolationGridList_succ]
    exact List.perm_append_comm
  have htail : (interpolationGridList k (s + 1) (n + 1)).Perm (b :: middle) := by
    rw [interpolationGridList_append_last]
    convert (List.perm_append_comm : (middle ++ [b]).Perm ([b] ++ middle)) using 1 <;>
      simp [middle, b, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [cauchyDividedDifference_perm R f hfull, cauchyDividedDifference_perm R f htail,
    interpolationGridList_succ]
  exact cauchyDividedDifference_recurrence hR hf b a middle hb ha hm

end HadamardMultibase
