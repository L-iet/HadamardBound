module

public import HadamardMultibase.CoveringExistence
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

namespace HadamardMultibase

open Filter
open scoped Topology

/-- The elementary factorial estimate needed for the sharp covering count.
It follows from a single term of the exponential series, without Stirling. -/
theorem log_factorial_lower {m : ℕ} (hm : 0 < m) :
    (m : ℝ) * Real.log m - m ≤ Real.log m.factorial := by
  have h := Real.log_le_log (show (0 : ℝ) < (m : ℝ) ^ m / m.factorial by positivity)
    (Real.pow_div_factorial_le_exp (m : ℝ) (Nat.cast_nonneg m) m)
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_exp] at h
  linarith

/-- Logarithmic stars-and-bars estimate, retaining the factorial saving that
produces the leading coefficient r−1 rather than r. -/
theorem log_choose_add_le (u : ℕ) {m : ℕ} (hm : 0 < m) :
    Real.log (((u + m).choose m : ℕ) : ℝ) ≤
      (m : ℝ) * (1 + Real.log (u + m) - Real.log m) := by
  have hpos : (0 : ℝ) < ((u + m).choose m : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega : m ≤ u + m)
  have h := Real.log_le_log hpos (Nat.choose_le_pow_div m (u + m) (α := ℝ))
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow] at h
  have hfac := log_factorial_lower hm
  push_cast at h
  linarith

/-- Real logarithmic form of the exponent-box bound, valid without
multiplicative independence. -/
theorem truncatedMonoid_card_le_real_log {r : ℕ} {b : Fin r → ℕ}
    (hb : ∀ i, 2 ≤ b i) (N : ℕ) :
    ((truncatedMonoid b N).card : ℝ) ≤
      (Real.log N / Real.log 2 + 1) ^ r := by
  have h := Real.natLog_le_logb N 2
  rw [Real.logb] at h
  have hc : ((truncatedMonoid b N).card : ℝ) ≤ ((Nat.log 2 N : ℝ) + 1) ^ r := by
    exact_mod_cast truncatedMonoid_card_le hb N
  exact hc.trans (pow_le_pow_left₀ (by positivity) (by linarith) _)

/-- The manuscript's count T(N) ≤ C₀ (log N)^r, with an explicit constant. -/
theorem truncatedMonoid_card_le_log_power {r : ℕ} {b : Fin r → ℕ}
    (hb : ∀ i, 2 ≤ b i) {N : ℕ} (hN : 2 ≤ N) :
    ((truncatedMonoid b N).card : ℝ) ≤
      (2 / Real.log 2) ^ r * (Real.log N) ^ r := by
  have hlog₂ : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log (2 : ℝ) ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hratio : 1 ≤ Real.log N / Real.log 2 := (le_div_iff₀ hlog₂).mpr (by simpa)
  calc
    _ ≤ (Real.log N / Real.log 2 + 1) ^ r := truncatedMonoid_card_le_real_log hb N
    _ ≤ (2 * (Real.log N / Real.log 2)) ^ r :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    _ = _ := by rw [← mul_div_assoc, mul_div_right_comm, mul_pow]

/-- The sharp entropy estimate after substituting a polynomial logarithmic
alphabet count. The lower order terms are explicit. -/
theorem log_choose_le_of_polynomial_bound {r u m : ℕ} {C : ℝ}
    (hr : 0 < r) (hC : 0 ≤ C) (hm : 1 ≤ (m : ℝ))
    (hlog : 1 ≤ Real.log m)
    (hu : (u : ℝ) ≤ C * ((m : ℝ) * Real.log m) ^ r) :
    Real.log (((u + m).choose m : ℕ) : ℝ) ≤
      (m : ℝ) * (((r : ℝ) - 1) * Real.log m +
        r * Real.log (Real.log m) + 1 + Real.log (C + 1)) := by
  have hmpos : (0 : ℝ) < m := by linarith
  have hlogpos : 0 < Real.log (m : ℝ) := by linarith
  have hbase : (m : ℝ) ≤ m * Real.log m := by nlinarith
  have hpow : (m : ℝ) ≤ ((m : ℝ) * Real.log m) ^ r :=
    hbase.trans (le_self_pow₀ (by linarith) (by omega))
  have hub : (u : ℝ) + m ≤ (C + 1) * ((m : ℝ) * Real.log m) ^ r := by
    nlinarith
  have hl := Real.log_le_log (show 0 < (u : ℝ) + m by positivity) hub
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul hmpos.ne' hlogpos.ne'] at hl
  have hmnat : 0 < m := by exact_mod_cast hmpos
  refine (log_choose_add_le u hmnat).trans ?_
  apply mul_le_mul_of_nonneg_left _ hmpos.le
  nlinarith

/-- The explicit lower order terms in the entropy estimate vanish after
normalization by log m. -/
theorem tendsto_covering_count_error (r : ℕ) (C : ℝ) :
    Tendsto (fun m : ℕ =>
      ((r : ℝ) * Real.log (Real.log m) + 1 + Real.log (C + 1)) / Real.log m)
      atTop (𝓝 0) := by
  have htlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp htlog
  have hconst : Tendsto (fun m : ℕ => (1 + Real.log (C + 1)) / Real.log m)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop htlog
  simpa only [mul_zero, zero_add] using
    ((hratio.const_mul (r : ℝ)).add hconst).congr
      (fun m => by dsimp; ring)

/-- The leading coefficient of the multiset logarithm is r−1. This theorem
separates the entropy estimate from the choice of the truncation threshold. -/
theorem eventually_log_choose_lt {r : ℕ} {C η : ℝ} {u : ℕ → ℕ}
    (hr : 0 < r) (hC : 0 ≤ C) (hη : 0 < η)
    (hu : ∀ᶠ m : ℕ in atTop, (u m : ℝ) ≤ C * ((m : ℝ) * Real.log m) ^ r) :
    ∀ᶠ m : ℕ in atTop, Real.log ((((u m + m).choose m) : ℕ) : ℝ) <
      ((r : ℝ) - 1 + η) * m * Real.log m := by
  have herror := (tendsto_order.mp (tendsto_covering_count_error r C)).2 η hη
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hu, herror, hlog, eventually_ge_atTop (1 : ℕ)] with m hum hem hlm hm
  change 1 ≤ Real.log (m : ℝ) at hlm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hlpos : 0 < Real.log (m : ℝ) := by linarith
  have he := (div_lt_iff₀ hlpos).mp hem
  have hb := log_choose_le_of_polynomial_bound hr hC hmR hlm hum
  refine hb.trans_lt ?_
  have hh := mul_lt_mul_of_pos_left he hmpos
  nlinarith

end HadamardMultibase
