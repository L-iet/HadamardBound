/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerDenominators
public import HadamardMultibase.SmallRationalValues
public import Mathlib.NumberTheory.Chebyshev

@[expose] public section

/-!
# Exponentially bounded common denominators

Mathlib's elementary Chebyshev estimate bounds log lcm(1,...,h) by a constant
times h. Combining it with the block-polynomial construction gives a precise
small-value-to-zero lemma whose denominator cost is independent of the degree
index. The analytic small-value estimate remains a separate obligation.
-/

namespace HadamardMultibase

theorem baker_lcm_log_bound (h : ℕ) :
    Real.log (Nat.lcmUpto h : ℝ) ≤ (Real.log 4 + 4) * (h : ℝ) := by
  rw [← Chebyshev.psi_eq_log_lcmUpto]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)

theorem baker_lcm_power_bound (h m : ℕ) :
    (Nat.lcmUpto h : ℝ) ^ m ≤
      Real.exp ((Real.log 4 + 4) * (h : ℝ) * (m : ℝ)) := by
  have hpos : (0 : ℝ) < Nat.lcmUpto h := by
    exact_mod_cast Nat.lcmUpto_pos h
  calc (Nat.lcmUpto h : ℝ) ^ m =
      Real.exp ((m : ℝ) * Real.log (Nat.lcmUpto h : ℝ)) := by
        rw [← Real.log_pow, Real.exp_log (pow_pos hpos m)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hs := mul_le_mul_of_nonneg_left (baker_lcm_log_bound h) (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
      nlinarith

theorem bakerBlock_hasse_common_denominator {h : ℕ} (hh : 0 < h)
    (a m : ℕ) (z : ℤ) :
    HasIntegerMultiple (Nat.lcmUpto h ^ m)
      ((Polynomial.hasseDeriv m (bakerBlock h a)).eval (z : ℚ)) := by
  have hdiv (j : ℕ) (hj : 1 ≤ j) (hjh : j ≤ h) :
      (j : ℤ) ∣ (Nat.lcmUpto h : ℤ) := by
    apply Int.natCast_dvd_natCast.mpr
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hj, hjh⟩)
  obtain ⟨v, hv⟩ := bakerBlock_hasse_integer hh hdiv a m z
  refine ⟨v, ?_⟩
  simpa only [Int.cast_natCast, Nat.cast_pow] using hv

theorem bakerBlock_hasse_eq_zero_of_exp_small {h : ℕ} (hh : 0 < h)
    (a m : ℕ) (z : ℤ)
    (hsmall : |(((Polynomial.hasseDeriv m (bakerBlock h a)).eval (z : ℚ) : ℚ) : ℝ)| <
      Real.exp (-((Real.log 4 + 4) * (h : ℝ) * (m : ℝ)))) :
    (Polynomial.hasseDeriv m (bakerBlock h a)).eval (z : ℚ) = 0 := by
  apply rat_eq_zero_of_small_abs (pow_pos (Nat.lcmUpto_pos h) m)
    (bakerBlock_hasse_common_denominator hh a m z)
  apply hsmall.trans_le
  rw [Real.exp_neg, ← one_div, Nat.cast_pow]
  apply one_div_le_one_div_of_le (pow_pos (by exact_mod_cast Nat.lcmUpto_pos h) m)
  exact baker_lcm_power_bound h m

end HadamardMultibase
