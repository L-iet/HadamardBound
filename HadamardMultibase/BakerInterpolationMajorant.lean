/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic

@[expose] public section

/-! # Factorial majorants for confluent divided differences

Integer spacing yields a factor 2 at low orders. At orders beyond the node
multiplicity k, endpoint separation grows at least as (n+1-k)/k, supplying
the factorial denominator needed for stability uniformly in the grid length.
-/

namespace HadamardMultibase

noncomputable def confluentMajorant (k n : ℕ) (ε : ℝ) : ℝ :=
  ε * (2 * (k : ℝ)) ^ n / ((n + 1 - k).factorial : ℝ)

theorem confluentMajorant_nonneg (k n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ confluentMajorant k n ε := by
  unfold confluentMajorant
  positivity

theorem le_confluentMajorant_of_lt {k n : ℕ} (hk : 0 < k) (hn : n < k)
    {ε : ℝ} (hε : 0 ≤ ε) : ε ≤ confluentMajorant k n ε := by
  have he : n + 1 - k = 0 := by omega
  simp only [confluentMajorant, he, Nat.factorial_zero, Nat.cast_one, div_one]
  apply le_mul_of_one_le_right hε
  apply one_le_pow₀
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

theorem confluentMajorant_step {k n : ℕ} (hk : 0 < k) {ε d : ℝ}
    (hε : 0 ≤ ε) (hd : 1 ≤ d) (hsep : ((n + 2 - k : ℕ) : ℝ) ≤ (k : ℝ) * d) :
    2 * confluentMajorant k n ε / d ≤ confluentMajorant k (n + 1) ε := by
  have hdpos : 0 < d := by linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hprev := confluentMajorant_nonneg k n hε
  have hnext := confluentMajorant_nonneg k (n + 1) hε
  by_cases hg : n + 2 ≤ k
  · have hzero : n + 1 - k = 0 := by omega
    have hzero' : n + 1 + 1 - k = 0 := by omega
    have he : confluentMajorant k (n + 1) ε = 2 * (k : ℝ) * confluentMajorant k n ε := by
      simp only [confluentMajorant, hzero, hzero', Nat.factorial_zero, Nat.cast_one, div_one, pow_succ]
      ring
    calc 2 * confluentMajorant k n ε / d ≤ 2 * confluentMajorant k n ε :=
        div_le_self (by positivity) hd
      _ ≤ confluentMajorant k (n + 1) ε := by
        rw [he]
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        nlinarith
  · have hsucc : n + 1 + 1 - k = (n + 1 - k) + 1 := by omega
    have hfact : (((n + 1 - k).factorial : ℝ)) ≠ 0 := by positivity
    have hnpos : (((n + 1 - k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have he : ((n + 2 - k : ℕ) : ℝ) * confluentMajorant k (n + 1) ε =
        2 * (k : ℝ) * confluentMajorant k n ε := by
      simp only [confluentMajorant, hsucc, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
    have hb := mul_le_mul_of_nonneg_right hsep hnext
    rw [he] at hb
    apply (div_le_iff₀ hdpos).mpr
    apply (mul_le_mul_iff_right₀ hkpos).mp
    nlinarith [hb]

theorem confluentMajorant_mul_pow_bound {k : ℕ} (hk : 0 < k)
    (n : ℕ) {ε A : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A) :
    confluentMajorant k n ε * A ^ n ≤
      ε * (1 + 2 * (k : ℝ) * A) ^ (k - 1) * Real.exp (2 * (k : ℝ) * A) := by
  let x := 2 * (k : ℝ) * A
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hindex : n + 1 - k = n - (k - 1) := by omega
  have hcoeff : confluentMajorant k n ε * A ^ n =
      ε * (x ^ n / ((n - (k - 1)).factorial : ℝ)) := by
    simp only [confluentMajorant, hindex, x, mul_pow]
    ring
  rw [hcoeff]
  have hb : x ^ n / ((n - (k - 1)).factorial : ℝ) ≤
      (1 + x) ^ (k - 1) * Real.exp x := by
    by_cases hn : n < k - 1
    · have hzero : n - (k - 1) = 0 := by omega
      rw [hzero, Nat.factorial_zero, Nat.cast_one, div_one]
      calc x ^ n ≤ (1 + x) ^ n := pow_le_pow_left₀ hx (by linarith) _
        _ ≤ (1 + x) ^ (k - 1) := pow_le_pow_right₀ (by linarith) hn.le
        _ ≤ _ := le_mul_of_one_le_right (by positivity) (Real.one_le_exp hx)
    · have hs : n = (k - 1) + (n - (k - 1)) := by omega
      rw [hs, pow_add]
      have hexp := Real.pow_div_factorial_le_exp x hx (n - (k - 1))
      have hpow : x ^ (k - 1) ≤ (1 + x) ^ (k - 1) := pow_le_pow_left₀ hx (by linarith) _
      calc x ^ (k - 1) * x ^ (n - (k - 1)) /
          (((k - 1 + (n - (k - 1)) - (k - 1)).factorial : ℕ) : ℝ)
          = x ^ (k - 1) * (x ^ (n - (k - 1)) / ((n - (k - 1)).factorial : ℝ)) := by
            rw [Nat.add_sub_cancel_left, mul_div_assoc]
        _ ≤ _ := mul_le_mul hpow hexp (by positivity) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hb hε
  simpa only [mul_assoc, x] using hh

end HadamardMultibase
