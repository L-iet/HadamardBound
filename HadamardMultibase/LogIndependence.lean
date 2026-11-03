module

public import HadamardMultibase.Arithmetic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Data.Rat.Cast.CharZero

@[expose] public section

namespace HadamardMultibase

/-- The qualitative Diophantine prerequisite for KSW's approximation lemma.
Its quantitative strengthening (finite irrationality measure) remains separate. -/
theorem irrational_log_ten_div_log_two : Irrational (Real.log 10 / Real.log 2) := by
  rw [irrational_iff_ne_rational]
  intro a b hb heq
  have hlog₂ : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  have hcross := (div_eq_div_iff hlog₂.ne' hbR).mp heq
  have hlogs : Real.log ((10 : ℝ) ^ b) = Real.log ((2 : ℝ) ^ a) := by
    rw [Real.log_zpow, Real.log_zpow]
    nlinarith
  have hpowers : (10 : ℝ) ^ b = (2 : ℝ) ^ a :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity))
      (Set.mem_Ioi.mpr (by positivity)) hlogs
  have hpowersQ : (10 : ℚ) ^ b = (2 : ℚ) ^ a := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact hpowers
  have hind : (2 : ℚ) ^ (-a) * 10 ^ b = 1 := by
    rw [zpow_neg, hpowersQ, inv_mul_cancel₀ (by positivity)]
  exact hb (independent_two_ten (-a) b hind).2

end HadamardMultibase
