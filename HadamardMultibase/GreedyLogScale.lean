module

public import HadamardMultibase.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

namespace HadamardMultibase

open Filter
open scoped Topology

noncomputable def shrinkingRemainder (C κ x : ℝ) : ℝ := C * x / (Real.log x) ^ κ

/-- A quantitative decrease of t/log t under the logarithmic decrement used
by the greedy multi-base algorithm. The constant κ/4 leaves ample slack. -/
theorem logQuotient_decrease {t h κ : ℝ} (ht : 0 < t) (hκ : 0 < κ)
    (hs : 4 ≤ Real.log t) (hlower : κ / 2 * Real.log t ≤ h) (hupper : h ≤ t / 2) :
    (t - h) / Real.log (t - h) ≤ t / Real.log t - κ / 4 := by
  have hspos : 0 < Real.log t := by linarith
  have hh : 0 ≤ h := (by positivity : 0 ≤ κ / 2 * Real.log t).trans hlower
  have hl2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have ht2 : 2 < t := by
    by_contra ht2
    have h := Real.log_le_log ht (le_of_not_gt ht2)
    linarith
  have hr : 1 < t - h := by linarith
  have hrpos : 0 < t - h := by linarith
  have hlogr : 0 < Real.log (t - h) := Real.log_pos hr
  have hlogle : Real.log (t - h) ≤ Real.log t := Real.log_le_log hrpos (by linarith)
  have hgap0 : 0 ≤ Real.log t - Real.log (t - h) := by linarith
  have hlogratio := Real.log_le_sub_one_of_pos (div_pos ht hrpos)
  rw [Real.log_div ht.ne' hrpos.ne'] at hlogratio
  have hgap : (Real.log t - Real.log (t - h)) * (t - h) ≤ h := by
    have hc := (le_div_iff₀ hrpos).mp
      (show Real.log t - Real.log (t - h) + 1 ≤ t / (t - h) by linarith)
    nlinarith
  have hgapT : t * (Real.log t - Real.log (t - h)) ≤ 2 * h := by
    have hc := mul_le_mul_of_nonneg_left (show t ≤ 2 * (t - h) by linarith) hgap0
    nlinarith
  have h₁ := mul_le_mul_of_nonneg_right hlower (show 0 ≤ Real.log t - 2 by linarith)
  have h₂ : κ / 4 * Real.log t * Real.log t ≤
      (κ / 2 * Real.log t) * (Real.log t - 2) := by
    have hc := mul_nonneg (mul_nonneg hκ.le hspos.le) (show 0 ≤ Real.log t - 4 by linarith)
    nlinarith
  have h₃ : κ / 4 * Real.log t * Real.log (t - h) ≤ κ / 4 * Real.log t * Real.log t :=
    mul_le_mul_of_nonneg_left hlogle (by positivity)
  have hkey : κ / 4 * Real.log t * Real.log (t - h) ≤ h * (Real.log t - 2) :=
    h₃.trans (h₂.trans h₁)
  apply (div_le_iff₀ hlogr).mpr
  rw [sub_mul, div_mul_eq_mul_div]
  apply (le_sub_iff_add_le).mpr
  apply (le_div_iff₀ hspos).mpr
  nlinarith

/-- The real remainder threshold tends to infinity, so finitely many small
residuals can be handled before applying monotonicity of log/loglog. -/
theorem shrinkingRemainder_tendsto_atTop {C : ℝ} (hC : 0 < C) (κ : ℝ) :
    Tendsto (fun n : ℕ => shrinkingRemainder C κ n) atTop atTop := by
  have hlim : Tendsto (fun n : ℕ => (Real.log n) ^ κ / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop κ (s := 1) (by norm_num)).tendsto_div_nhds_zero.comp
        tendsto_natCast_atTop_atTop
  apply tendsto_atTop.mpr
  intro A
  let A' : ℝ := max A 1
  have hA : 0 < A' := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  filter_upwards [(tendsto_order.mp hlim).2 (C / A') (div_pos hC hA),
    eventually_ge_atTop (2 : ℕ)] with n hn hn₂
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hpow : 0 < (Real.log (n : ℝ)) ^ κ := Real.rpow_pos_of_pos hlog _
  have hcross := (div_lt_div_iff₀ hnpos hA).mp hn
  have hbound : A' ≤ shrinkingRemainder C κ n := by
    apply (le_div_iff₀ hpow).mpr
    nlinarith
  exact (le_max_left _ _).trans hbound

theorem eventually_shrinkingRemainder_lt_half {C κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, shrinkingRemainder C κ n < (n : ℝ) / 2 := by
  have hden := (tendsto_rpow_atTop hκ).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have ht : Tendsto (fun n : ℕ => C / (Real.log n) ^ κ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  filter_upwards [(tendsto_order.mp ht).2 (1 / 2) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hn hn₁
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := mul_lt_mul_of_pos_left hn hnpos
  unfold shrinkingRemainder
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, one_mul] using h

/-- The logarithmic budget drops by a fixed positive amount after a greedy
step with a polynomial logarithmic remainder bound. -/
theorem eventually_shrinking_logScale_drop {C κ : ℝ} (hC : 0 < C) (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop,
      logScaleReal (shrinkingRemainder C κ n) ≤ logScale n - κ / 4 := by
  have htlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hslog := Real.tendsto_log_atTop.comp htlog
  have hratio : Tendsto (fun n : ℕ =>
      (κ * Real.log (Real.log n) - Real.log C) / Real.log n) atTop (𝓝 0) := by
    have ha := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp htlog
    have hb : Tendsto (fun n : ℕ => Real.log C / Real.log n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop htlog
    simpa only [Function.comp_apply, id_eq, mul_zero, sub_zero, ← mul_div_assoc, ← sub_div] using
      (ha.const_mul κ).sub hb
  filter_upwards [hslog.eventually_ge_atTop (max 4 (2 * Real.log C / κ)),
    htlog.eventually_ge_atTop 1, (tendsto_order.mp hratio).2 (1 / 2) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hs ht hh hn
  change max 4 (2 * Real.log C / κ) ≤ Real.log (Real.log (n : ℝ)) at hs
  change 1 ≤ Real.log (n : ℝ) at ht
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have htpos : 0 < Real.log (n : ℝ) := by linarith
  have hslow : 4 ≤ Real.log (Real.log (n : ℝ)) := (le_max_left _ _).trans hs
  have hconst := (div_le_iff₀ hκ).mp ((le_max_right _ _).trans hs)
  have hlower : κ / 2 * Real.log (Real.log (n : ℝ)) ≤
      κ * Real.log (Real.log n) - Real.log C := by nlinarith
  have hupper : κ * Real.log (Real.log (n : ℝ)) - Real.log C ≤ Real.log n / 2 := by
    have h := (div_lt_iff₀ htpos).mp hh
    linarith
  have hdrop := logQuotient_decrease htpos hκ hslow hlower hupper
  have hlogR : Real.log (shrinkingRemainder C κ n) =
      Real.log n - (κ * Real.log (Real.log n) - Real.log C) := by
    unfold shrinkingRemainder
    rw [Real.log_div (mul_ne_zero hC.ne' hnpos.ne') (Real.rpow_pos_of_pos htpos κ).ne',
      Real.log_mul hC.ne' hnpos.ne', Real.log_rpow htpos]
    ring
  unfold logScaleReal logScale
  rw [hlogR]
  exact hdrop

end HadamardMultibase
