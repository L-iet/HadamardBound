/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic

@[expose] public section

/-!
# A finite-box form of Siegel's elementary construction

An integer matrix whose images of a sufficiently large box fit in a smaller
box has two equal images. Their difference is a bounded nonzero integer kernel
vector. The cardinality inequality and coefficient bound are explicit.
-/

namespace HadamardMultibase

open scoped BigOperators

theorem integer_row_box_bound {n H M : ℕ} (a : Fin n → ℤ)
    (ha : ∀ j, |a j| ≤ (M : ℤ)) (x : Fin n → Fin (H + 1)) :
    |∑ j, a j * (x j : ℕ)| ≤ (n * M * H : ℕ) := by
  calc |∑ j, a j * (x j : ℕ)| ≤ ∑ j, |a j * (x j : ℕ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, (M : ℤ) * H := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ (x j : ℕ) by positivity)]
      have hx : ((x j : ℕ) : ℤ) ≤ H := by exact_mod_cast (Nat.le_of_lt_succ (x j).isLt)
      exact mul_le_mul (ha j) hx (by positivity) (by positivity)
    _ = _ := by simp; ring

/-- Explicit finite-box criterion for a small nonzero integer kernel vector. -/
theorem exists_bounded_integer_kernel {m n H M : ℕ} (A : Fin m → Fin n → ℤ)
    (hA : ∀ i j, |A i j| ≤ (M : ℤ))
    (hcount : (2 * (n * M * H) + 1) ^ m < (H + 1) ^ n) :
    ∃ v : Fin n → ℤ, v ≠ 0 ∧ (∀ j, |v j| ≤ (H : ℤ)) ∧
      ∀ i, ∑ j, A i j * v j = 0 := by
  classical
  let B : ℕ := n * M * H
  let F : (Fin n → Fin (H + 1)) → (Fin m → Fin (2 * B + 1)) := fun x i =>
    ⟨(∑ j, A i j * (x j : ℕ) + (B : ℤ)).toNat, by
      apply Nat.lt_succ_of_le
      apply Int.toNat_le.mpr
      have hu : (∑ j, A i j * (x j : ℕ)) ≤ (B : ℤ) :=
        (le_abs_self _).trans (integer_row_box_bound (A i) (hA i) x)
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        (show (∑ j, A i j * (x j : ℕ)) + (B : ℤ) ≤ 2 * (B : ℤ) by linarith)⟩
  have hcard : Fintype.card (Fin m → Fin (2 * B + 1)) <
      Fintype.card (Fin n → Fin (H + 1)) := by
    simpa only [Fintype.card_fun, Fintype.card_fin, B] using hcount
  obtain ⟨x, y, hxy, hF⟩ := Fintype.exists_ne_map_eq_of_card_lt F hcard
  let v : Fin n → ℤ := fun j => ((x j : ℕ) : ℤ) - ((y j : ℕ) : ℤ)
  refine ⟨v, ?_, ?_, ?_⟩
  · intro hv
    apply hxy
    funext j
    apply Fin.ext
    have hz := congrFun hv j
    dsimp [v] at hz
    exact_mod_cast sub_eq_zero.mp hz
  · intro j
    have hx := (x j).isLt
    have hy := (y j).isLt
    dsimp [v]
    rw [abs_le]
    constructor <;> omega
  · intro i
    have heq := congrArg Fin.val (congrFun hF i)
    change (∑ j, A i j * (x j : ℕ) + (B : ℤ)).toNat =
      (∑ j, A i j * (y j : ℕ) + (B : ℤ)).toNat at heq
    have hx := integer_row_box_bound (A i) (hA i) x
    have hy := integer_row_box_bound (A i) (hA i) y
    rw [abs_le] at hx hy
    have hsum : (∑ j, A i j * (x j : ℕ)) = ∑ j, A i j * (y j : ℕ) := by
      dsimp [B] at *
      omega
    simp only [v, mul_sub, Finset.sum_sub_distrib, hsum, sub_self]

/-- A convenient explicit height bound when there are at least twice as many
unknowns as equations. No nonconstructive choice of an unbounded kernel vector
is needed in the later auxiliary-function construction. -/
theorem exists_bounded_integer_kernel_of_twice_rows_le {m n M : ℕ}
    (hn : 0 < n) (hmn : 2 * m ≤ n) (A : Fin m → Fin n → ℤ)
    (hA : ∀ i j, |A i j| ≤ (M : ℤ)) :
    ∃ v : Fin n → ℤ, v ≠ 0 ∧ (∀ j, |v j| ≤ (2 * n * M + 1 : ℕ)) ∧
      ∀ i, ∑ j, A i j * v j = 0 := by
  let H := 2 * n * M + 1
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hbox : 2 * (n * M * H) + 1 ≤ H ^ 2 := by dsimp [H]; nlinarith
  have hcount : (2 * (n * M * H) + 1) ^ m < (H + 1) ^ n := by
    calc (2 * (n * M * H) + 1) ^ m ≤ (H ^ 2) ^ m := Nat.pow_le_pow_left hbox m
      _ = H ^ (2 * m) := by rw [pow_mul]
      _ ≤ H ^ n := Nat.pow_le_pow_right hH hmn
      _ < (H + 1) ^ n := Nat.pow_lt_pow_left (Nat.lt_succ_self H) (by omega)
  exact exists_bounded_integer_kernel A hA hcount

end HadamardMultibase
