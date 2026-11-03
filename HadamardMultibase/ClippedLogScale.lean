module

public import HadamardMultibase.GreedyLogScale
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

namespace HadamardMultibase

open Filter

theorem logScale_pos_of_gt_two {n : ℕ} (hn : 2 < n) : 0 < logScale n := by
  have hlog : 1 < Real.log (n : ℝ) := by
    have hnreal : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 3 ≤ n by omega)
    have h := Real.log_lt_log (Real.exp_pos 1)
      (Real.exp_one_lt_three.trans_le hnreal)
    simpa only [Real.log_exp] using h
  exact div_pos (by linarith) (Real.log_pos hlog)

/-- Freeze the finite initial interval at a safe monotonicity threshold. -/
noncomputable def clippedLogScale (N n : ℕ) : ℝ := logScale (max N n)

theorem clippedLogScale_eq {N n : ℕ} (hn : N ≤ n) : clippedLogScale N n = logScale n := by
  rw [clippedLogScale, max_eq_right hn]

theorem clippedLogScale_lower {N : ℕ} (hN : 0 < N)
    (hlogN : Real.exp 1 ≤ Real.log (N : ℝ)) (n : ℕ) :
    logScale N ≤ clippedLogScale N n := by
  exact logScaleReal_mono (by exact_mod_cast hN) hlogN (Nat.cast_le.mpr (le_max_left N n))

theorem clippedLogScale_le_real {N n : ℕ} {R : ℝ} (hN : 0 < N)
    (hlogN : Real.exp 1 ≤ Real.log (N : ℝ)) (hNR : (N : ℝ) ≤ R) (hnR : (n : ℝ) ≤ R) :
    clippedLogScale N n ≤ logScaleReal R := by
  have hmaxpos : (0 : ℝ) < (max N n : ℕ) := by exact_mod_cast (show 0 < max N n by omega)
  have hmaxlog : Real.exp 1 ≤ Real.log (max N n : ℕ) :=
    hlogN.trans (Real.log_le_log (by exact_mod_cast hN) (Nat.cast_le.mpr (le_max_left N n)))
  have hmaxR : ((max N n : ℕ) : ℝ) ≤ R := by rw [Nat.cast_max]; exact max_le hNR hnR
  exact logScaleReal_mono hmaxpos hmaxlog hmaxR

theorem eventually_clippedLogScale_drop {N : ℕ} (hN : 0 < N)
    (hlogN : Real.exp 1 ≤ Real.log (N : ℝ)) {C κ : ℝ} (hC : 0 < C) (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, (r : ℝ) ≤ shrinkingRemainder C κ n →
      clippedLogScale N r ≤ logScale n - κ / 4 := by
  filter_upwards [eventually_shrinking_logScale_drop hC hκ,
    (shrinkingRemainder_tendsto_atTop hC κ).eventually_ge_atTop (N : ℝ)] with n hdrop hlarge
  intro r hr
  exact (clippedLogScale_le_real hN hlogN hlarge hr).trans hdrop

end HadamardMultibase
