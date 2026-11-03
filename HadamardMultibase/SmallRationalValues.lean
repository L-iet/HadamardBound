/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic

@[expose] public section

/-!
# Turning small rational values into exact zeros

The auxiliary-function argument evaluates comparison expressions in the
rationals with a controlled common denominator. A nonzero cleared value is
an integer of absolute value at least one. All arithmetic here is proved
directly and imports no transcendence theorem.
-/

namespace HadamardMultibase

theorem integer_eq_zero_of_real_abs_lt_one {z : ℤ} (hz : |(z : ℝ)| < 1) : z = 0 := by
  by_contra hne
  have h : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hne
  linarith

/-- A denominator certificate is an explicit integer witness. -/
def HasIntegerMultiple (D : ℕ) (x : ℚ) : Prop :=
  ∃ z : ℤ, (D : ℚ) * x = (z : ℚ)

theorem rat_eq_zero_of_small_integer_multiple {D : ℕ} (hD : 0 < D) {x : ℚ}
    (hint : HasIntegerMultiple D x) (hsmall : |(D : ℝ) * (x : ℝ)| < 1) : x = 0 := by
  obtain ⟨z, hz⟩ := hint
  have hzR : (D : ℝ) * (x : ℝ) = (z : ℝ) := by exact_mod_cast hz
  rw [hzR] at hsmall
  have hzero := integer_eq_zero_of_real_abs_lt_one hsmall
  rw [hzero, Int.cast_zero] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by positivity)

theorem rat_eq_zero_of_small_abs {D : ℕ} (hD : 0 < D) {x : ℚ}
    (hint : HasIntegerMultiple D x) (hsmall : |(x : ℝ)| < 1 / (D : ℝ)) : x = 0 := by
  apply rat_eq_zero_of_small_integer_multiple hD hint
  rw [abs_mul, abs_of_pos (show (0 : ℝ) < D by positivity)]
  have h := (lt_div_iff₀ (show (0 : ℝ) < D by positivity)).mp hsmall
  nlinarith

theorem HasIntegerMultiple.add {D : ℕ} {x y : ℚ}
    (hx : HasIntegerMultiple D x) (hy : HasIntegerMultiple D y) :
    HasIntegerMultiple D (x + y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  rw [mul_add, ha, hb, Int.cast_add]

theorem HasIntegerMultiple.mul_int {D : ℕ} {x : ℚ}
    (hx : HasIntegerMultiple D x) (z : ℤ) : HasIntegerMultiple D (z * x) := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨z * a, ?_⟩
  rw [mul_left_comm, ha, Int.cast_mul]

theorem HasIntegerMultiple.mul {D E : ℕ} {x y : ℚ}
    (hx : HasIntegerMultiple D x) (hy : HasIntegerMultiple E y) :
    HasIntegerMultiple (D * E) (x * y) := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a * b, ?_⟩
  push_cast
  calc (D : ℚ) * E * (x * y) = ((D : ℚ) * x) * ((E : ℚ) * y) := by ring
    _ = _ := by rw [ha, hb]

theorem HasIntegerMultiple.pow {D : ℕ} {x : ℚ}
    (hx : HasIntegerMultiple D x) (m : ℕ) : HasIntegerMultiple (D ^ m) (x ^ m) := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨a ^ m, ?_⟩
  rw [Nat.cast_pow, ← mul_pow, ha, Int.cast_pow]

theorem HasIntegerMultiple.sum {ι : Type*} (s : Finset ι) {D : ℕ} (f : ι → ℚ)
    (hf : ∀ i ∈ s, HasIntegerMultiple D (f i)) :
    HasIntegerMultiple D (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem rational_slope_integer_multiple (q : ℕ) (hq : 0 < q) (p lam mu : ℤ) :
    HasIntegerMultiple q ((lam : ℚ) + (mu : ℚ) * p / q) := by
  refine ⟨(q : ℤ) * lam + mu * p, ?_⟩
  have hq0 : (q : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

end HadamardMultibase
