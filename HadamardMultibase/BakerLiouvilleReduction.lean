/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

@[expose] public section

/-! # Reducing the final contradiction to exponentially small grid defects

An assumed Liouville ratio supplies arbitrarily large denominators. Its
approximation exponent can be chosen after all fixed auxiliary parameters,
so that h=ceil(log q) gives any required exponential accuracy in h.
-/

namespace HadamardMultibase

open Filter

theorem liouville_tiny_grid_approximation {α : ℝ} (hL : Liouville α)
    {y A : ℝ} (hy : 0 < y) (hA : 0 < A) (H : ℕ) :
    ∃ h q : ℕ, H ≤ h ∧ 1 < q ∧ (q : ℝ) ≤ Real.exp h ∧
      ∃ p : ℤ, |(p : ℝ) / q| ≤ |α| + 1 ∧
        |y * ((p : ℝ) / q - α)| < Real.exp (-A * h) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * A + 1)
  have hfreq := hL.frequently_exists_num n
  have hlarge : ∀ᶠ q : ℕ in atTop,
      2 ≤ q ∧ max y (Real.exp (max (1 : ℝ) (H : ℝ))) ≤ (q : ℝ) :=
    (eventually_ge_atTop 2).and
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop _)
  obtain ⟨q, ⟨p, _, herr⟩, hqNat, hqLarge⟩ := (hfreq.and_eventually hlarge).exists
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hyq : y ≤ (q : ℝ) := (le_max_left _ _).trans hqLarge
  have hqexp : Real.exp (max (1 : ℝ) (H : ℝ)) ≤ q := (le_max_right _ _).trans hqLarge
  have hlog : max (1 : ℝ) (H : ℝ) ≤ Real.log (q : ℝ) := by
    have he := Real.log_le_log (Real.exp_pos _) hqexp
    simpa only [Real.log_exp] using he
  have hlogone : 1 ≤ Real.log (q : ℝ) := (le_max_left _ _).trans hlog
  have hlogH : (H : ℝ) ≤ Real.log (q : ℝ) := (le_max_right _ _).trans hlog
  let h : ℕ := ⌈Real.log (q : ℝ)⌉₊
  have hceil : Real.log (q : ℝ) ≤ (h : ℝ) := Nat.le_ceil _
  have hH : H ≤ h := by exact_mod_cast hlogH.trans hceil
  have htwolog : (h : ℝ) ≤ 2 * Real.log (q : ℝ) := by
    have he := (Nat.ceil_lt_add_one (show 0 ≤ Real.log (q : ℝ) by linarith)).le
    dsimp [h]
    linarith
  have hheight : (q : ℝ) ≤ Real.exp (h : ℝ) := by
    simpa only [Real.exp_log hqpos] using (Real.exp_le_exp.mpr hceil)
  have hpower : 1 / (q : ℝ) ^ n ≤ 1 := by
    exact (div_le_one (pow_pos hqpos n)).mpr (one_le_pow₀ hqone)
  have herrone : |α - (p : ℝ) / q| < 1 := herr.trans_le hpower
  have habs : |(p : ℝ) / q| ≤ |α| + 1 := by
    have he : (p : ℝ) / q = α - (α - (p : ℝ) / q) := by ring
    calc |(p : ℝ) / q| = |α - (α - (p : ℝ) / q)| := congrArg abs he
      _ ≤ |α| + |α - (p : ℝ) / q| := abs_sub _ _
      _ ≤ _ := by linarith
  have hpowexp : (q : ℝ) * (1 / (q : ℝ) ^ n) =
      Real.exp ((1 - (n : ℝ)) * Real.log (q : ℝ)) := by
    have hp : 1 / (q : ℝ) ^ n = Real.exp (-((n : ℝ) * Real.log (q : ℝ))) := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hqpos]
      simp only [one_div]
    calc (q : ℝ) * (1 / (q : ℝ) ^ n) =
          Real.exp (Real.log (q : ℝ)) * Real.exp (-((n : ℝ) * Real.log (q : ℝ))) := by
            rw [hp, Real.exp_log hqpos]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  refine ⟨h, q, hH, by omega, hheight, p, habs, ?_⟩
  calc
    |y * ((p : ℝ) / q - α)| = y * |α - (p : ℝ) / q| := by
      rw [abs_mul, abs_of_pos hy, abs_sub_comm]
    _ < y * (1 / (q : ℝ) ^ n) := mul_lt_mul_of_pos_left herr hy
    _ ≤ (q : ℝ) * (1 / (q : ℝ) ^ n) := mul_le_mul_of_nonneg_right hyq (by positivity)
    _ = Real.exp ((1 - (n : ℝ)) * Real.log (q : ℝ)) := hpowexp
    _ < Real.exp (-2 * A * Real.log (q : ℝ)) := by
      apply Real.exp_lt_exp.mpr
      nlinarith
    _ ≤ Real.exp (-A * h) := by
      apply Real.exp_le_exp.mpr
      nlinarith

end HadamardMultibase
