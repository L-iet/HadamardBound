module

public import HadamardMultibase.Transfer
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Analysis.SpecialFunctions.Log.InvLog

@[expose] public section

namespace HadamardMultibase

open Filter

/-- The real-variable version of the scale used in the manuscript. -/
noncomputable def logScaleReal (x : ℝ) : ℝ := Real.log x / Real.log (Real.log x)

theorem logScaleReal_natCast (n : ℕ) : logScaleReal n = logScale n := rfl

theorem logScaleReal_pos {x : ℝ} (hx : Real.exp 1 ≤ Real.log x) :
    0 < logScaleReal x := by
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  exact div_pos (by linarith) (Real.log_pos (by linarith))

theorem one_le_logScaleReal {x : ℝ} (hx : Real.exp 1 ≤ Real.log x) :
    1 ≤ logScaleReal x := by
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hl : 0 < Real.log (Real.log x) := Real.log_pos (by linarith)
  apply (le_div_iff₀ hl).mpr
  have h := Real.log_le_sub_one_of_pos (show 0 < Real.log x by linarith)
  linarith

/-- Eventual monotonicity with an explicit real threshold. -/
theorem logScaleReal_mono {x y : ℝ} (hxpos : 0 < x)
    (hx : Real.exp 1 ≤ Real.log x) (hxy : x ≤ y) :
    logScaleReal x ≤ logScaleReal y := by
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log hxpos hxy
  have hy := hx.trans hlog
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hx₀ : 0 < Real.log x := by linarith
  have hy₀ : 0 < Real.log y := by linarith
  have hxx : 0 < Real.log (Real.log x) := Real.log_pos (by linarith)
  have hyy : 0 < Real.log (Real.log y) := Real.log_pos (by linarith)
  have h := Real.log_div_self_antitoneOn hx hy hlog
  have h' := (div_le_div_iff₀ hy₀ hx₀).mp h
  exact (div_le_div_iff₀ hxx hyy).mpr (by nlinarith)

theorem eventually_logScale_threshold :
    ∀ᶠ n : ℕ in atTop, Real.exp 1 ≤ Real.log (n : ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _

/-- The scale is sublogarithmic; this analytic fact has no construction inputs. -/
theorem tendsto_logScale_div_log :
    Tendsto (fun n : ℕ => logScale n / Real.log n) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ => Real.log (Real.log n)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply ht.inv_tendsto_atTop.congr'
  filter_upwards [eventually_logScale_threshold] with n hn
  have hpos : 0 < Real.log (n : ℝ) := (Real.exp_pos 1).trans_le hn
  dsimp [logScale]
  field_simp [ne_of_gt hpos]

/-- The main exponent estimate from construction and representation inputs.
All change-of-variable and constant-absorption
steps from the manuscript are discharged here. -/
theorem main_bound_of_inputs (hG : GolayFamily) (hC : CraigenTransfer)
    (hS : SparseRepresentationBound) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ p : ℕ, N ≤ p → Odd p →
      ∃ t : ℕ, HadamardOrder (2 ^ t * p) ∧ (t : ℝ) ≤ C * logScale p := by
  obtain ⟨K, hK, hbound⟩ := exponent_bound_of_inputs hG hC hS
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp eventually_logScale_threshold
  let N := max N₀ 3
  refine ⟨2 * K + 2, by positivity, 2 * N + 1, ?_⟩
  intro p hp hpodd
  obtain ⟨q, rfl⟩ := hpodd.exists_bit1
  have hq : N ≤ q := by omega
  have hq₃ : 2 < q := by dsimp [N] at hq; omega
  have hqlog := hN₀ q (le_trans (le_max_left _ _) hq)
  have hqp : (q : ℝ) ≤ (2 * q + 1 : ℕ) := by exact_mod_cast (show q ≤ 2 * q + 1 by omega)
  have hpScale : 1 ≤ logScale (2 * q + 1) :=
    one_le_logScaleReal (hqlog.trans (Real.log_le_log (by positivity) hqp))
  have hscale : logScale q ≤ logScale (2 * q + 1) :=
    logScaleReal_mono (by positivity) hqlog hqp
  obtain ⟨t, ht, htb⟩ := hbound q hq₃
  refine ⟨t, ht, ?_⟩
  nlinarith

theorem tau_bound_of_inputs (hG : GolayFamily) (hC : CraigenTransfer)
    (hS : SparseRepresentationBound) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ p : ℕ, N ≤ p → Odd p →
      ∀ h : HasExponent p, (tau p h : ℝ) ≤ C * logScale p := by
  obtain ⟨C, hCpos, N, h⟩ := main_bound_of_inputs hG hC hS
  refine ⟨C, hCpos, N, ?_⟩
  intro p hp hodd hex
  obtain ⟨t, ht, htb⟩ := h p hp hodd
  exact (show (tau p hex : ℝ) ≤ t by exact_mod_cast tau_le hex ht).trans htb

end HadamardMultibase
