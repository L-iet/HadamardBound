/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Elementary arithmetic lower bounds for logarithmic forms

These lemmas use only mathlib. They are the elementary baseline for a
from-scratch quantitative logarithm proof. They do not assert a polynomial
irrationality measure: the height of `p ^ k` grows exponentially in `k`.
-/

namespace HadamardMultibase

theorem sub_le_mul_log_sub {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    u - v ≤ u * (Real.log u - Real.log v) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hv hu)
  rw [Real.log_div hv.ne' hu.ne'] at h
  have hs := mul_le_mul_of_nonneg_left h hu.le
  have hcancel : u * (v / u - 1) = v - u := by field_simp
  rw [hcancel] at hs
  nlinarith

theorem abs_sub_le_max_mul_abs_log_sub {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    |u - v| ≤ max u v * |Real.log u - Real.log v| := by
  rcases le_total v u with h | h
  · rw [max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h),
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hv h))]
    exact sub_le_mul_log_sub hu hv
  · rw [max_eq_right h, abs_sub_comm u v, abs_sub_comm (Real.log u),
      abs_of_nonneg (sub_nonneg.mpr h),
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hu h))]
    exact sub_le_mul_log_sub hv hu

/-- A nonzero difference of integers has absolute value at least one. -/
theorem one_le_abs_natCast_sub {a b : ℕ} (hab : a ≠ b) :
    (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
  have hcast : (a : ℤ) ≠ (b : ℤ) := by exact_mod_cast hab
  have h := Int.one_le_abs (sub_ne_zero.mpr hcast)
  exact_mod_cast h

/-- Logarithms of distinct positive integers are separated at the scale of
their integer height. This is weaker than separation in exponent height. -/
theorem integer_logarithm_height_bound {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ≠ b) :
    (1 : ℝ) ≤ max (a : ℝ) (b : ℝ) * |Real.log (a : ℝ) - Real.log (b : ℝ)| :=
  (one_le_abs_natCast_sub hab).trans
    (abs_sub_le_max_mul_abs_log_sub (by positivity) (by positivity))

/-- The elementary lower bound for two powers. Its exponential coefficient
height must not be mistaken for the polynomial bound still needed downstream. -/
theorem integer_log_form_exponential_height_bound {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (k m : ℕ) (hne : p ^ k ≠ q ^ m) :
    (1 : ℝ) ≤ max ((p : ℝ) ^ k) ((q : ℝ) ^ m) *
      |(k : ℝ) * Real.log (p : ℝ) - (m : ℝ) * Real.log (q : ℝ)| := by
  simpa only [Nat.cast_pow, Real.log_pow] using
    integer_logarithm_height_bound (pow_pos hp k) (pow_pos hq m) hne

end HadamardMultibase
