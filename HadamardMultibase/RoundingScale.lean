module

public import HadamardMultibase.DilationRounding
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

namespace HadamardMultibase

open Filter
open scoped Topology

noncomputable def flatRoundingScale (x ε : ℝ) : ℝ := 1 / (Real.sqrt x - x ^ ε)

noncomputable def roundingErrorBound (n : ℕ) (u : ℝ) : ℝ :=
  4 * (2 * (concentrationMomentOrder (2 * n) : ℝ) + 1) *
    Real.sqrt (max 1 ((n : ℝ) - 1 / u ^ 2))

theorem concentrationMomentOrder_le_log {N : ℕ} (hN : 1 ≤ N) :
    (concentrationMomentOrder N : ℝ) ≤ Real.log N / Real.log 4 + 1 := by
  have hlog : 0 ≤ Real.logb (4 : ℝ) N :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hN)
  have hc : (Nat.clog 4 N : ℝ) ≤ Real.logb (4 : ℝ) N + 1 := by
    rw [← Real.natCeil_logb_natCast 4 N]
    exact (Nat.ceil_lt_add_one hlog).le
  unfold concentrationMomentOrder
  rw [Nat.cast_max, Nat.cast_one]
  change max 1 (Nat.clog 4 N : ℝ) ≤ Real.logb (4 : ℝ) N + 1
  exact max_le (by linarith) hc

theorem rounding_sqrt_variance_le {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    Real.sqrt (max 1 (x - 1 / (flatRoundingScale x ε) ^ 2)) ≤
      2 * x ^ (1 / 4 + ε / 2) := by
  have hxpos : 0 < x := by linarith
  have hs : 1 ≤ Real.sqrt x := by simpa using Real.sqrt_le_sqrt hx
  have hp : 1 ≤ x ^ ε := Real.one_le_rpow hx hε
  have hsq : (x ^ (1 / 4 + ε / 2)) ^ 2 = Real.sqrt x * x ^ ε := by
    rw [← Real.rpow_two, ← Real.rpow_mul hxpos.le, Real.sqrt_eq_rpow, ← Real.rpow_add hxpos]
    congr 1
    ring
  have hvar : x - 1 / (flatRoundingScale x ε) ^ 2 ≤ 2 * Real.sqrt x * x ^ ε := by
    unfold flatRoundingScale
    simp only [one_div, inv_pow, inv_inv]
    nlinarith [Real.sq_sqrt hxpos.le, sq_nonneg (x ^ ε)]
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · have hmax : max 1 (x - 1 / (flatRoundingScale x ε) ^ 2) ≤
        2 * Real.sqrt x * x ^ ε := max_le (by nlinarith) hvar
    rw [mul_pow, hsq]
    nlinarith

theorem eventually_flatRoundingScale_bound {ε : ℝ} (hε : ε < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, 0 < flatRoundingScale n ε ∧
      flatRoundingScale n ε ≤ 2 / Real.sqrt n := by
  have ht := (tendsto_rpow_neg_atTop (y := 1 / 2 - ε) (by linarith)).comp
    tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ ε / Real.sqrt n) atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    dsimp only [Function.comp_apply]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hnpos]
    congr 1
    ring
  filter_upwards [(tendsto_order.mp hratio).2 (1 / 2) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hsmall hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hp : (n : ℝ) ^ ε < Real.sqrt n / 2 := by
    have h := (div_lt_iff₀ hs).mp hsmall
    linarith
  have hden : 0 < Real.sqrt n - (n : ℝ) ^ ε := by linarith
  refine ⟨one_div_pos.mpr hden, ?_⟩
  unfold flatRoundingScale
  apply (div_le_div_iff₀ hden hs).mpr
  linarith

theorem concentration_coefficient_le {n : ℕ} (hn : 1 ≤ n) :
    2 * (concentrationMomentOrder (2 * n) : ℝ) + 1 ≤
      (5 + 2 / Real.log 4) * (Real.log n + 1) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hl2 : Real.log (2 : ℝ) ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have hlN : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have ht := concentrationMomentOrder_le_log (show 1 ≤ 2 * n by omega)
  have hlog : Real.log (2 * n : ℕ) = Real.log 2 + Real.log (n : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.log_mul (by norm_num) hnpos.ne']
  rw [hlog, add_div] at ht
  have hratio : Real.log (2 : ℝ) / Real.log 4 ≤ 1 := (div_le_one hl4).mpr hl2
  have hinv : 0 ≤ 2 / Real.log 4 := by positivity
  simp only [div_eq_mul_inv] at ht hratio hinv ⊢
  nlinarith [mul_nonneg hinv hlN]

/-- Every fixed logarithmic factor is eventually absorbed by a positive power. -/
theorem eventually_log_plus_one_bound {γ : ℝ} (hγ : 0 < γ) (D : ℝ) :
    ∀ᶠ n : ℕ in atTop, D * (Real.log n + 1) ≤ (n : ℝ) ^ γ := by
  have hlog := (isLittleO_log_rpow_atTop hγ).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ γ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hγ).comp tendsto_natCast_atTop_atTop)
  have hsum : Tendsto (fun n : ℕ => D * ((Real.log n + 1) / (n : ℝ) ^ γ)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, zero_add, mul_zero, ← add_div] using (hlog.add hpow).const_mul D
  filter_upwards [(tendsto_order.mp hsum).2 1 (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hn hN
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hden : (0 : ℝ) < (n : ℝ) ^ γ := Real.rpow_pos_of_pos hnpos _
  have h := (div_lt_iff₀ hden).mp
    (show D * (Real.log n + 1) / (n : ℝ) ^ γ < 1 by simpa only [mul_div_assoc] using hn)
  linarith

end HadamardMultibase
