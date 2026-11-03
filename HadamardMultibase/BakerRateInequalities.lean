/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerParameters

@[expose] public section

/-! # Rate inequalities independent of the varying height -/
namespace HadamardMultibase

theorem baker_circle_rate_linear {K L w a b : ℕ} {B C : ℝ}
    (hL : 1 ≤ L) (hLK : L ≤ K)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hC : Real.log 4 + 5 + 10 * Real.log 2 + Real.log ((a * b : ℕ) : ℝ) + 3 ≤ C)
    (hCB : 2 * Real.log 2 + (1 + B) * |Real.log a| ≤ C) :
    bakerMixedCircleRate L w a ((L : ℝ) * (1 + B))
      (bakerInitialHeightRate K L a b + 1) ≤
        C * K + C * L * w := by
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  have hab : (1 : ℝ) ≤ ((a * b : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ a * b by nlinarith)
  have hlogab := Real.log_nonneg hab
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLKR : (L : ℝ) ≤ K := by exact_mod_cast hLK
  have hKR : (1 : ℝ) ≤ K := hLR.trans hLKR
  have hcoef : (Real.log 4 + 5) * (K : ℝ) +
      5 * ((L : ℝ) + 1) * Real.log 2 +
      (L : ℝ) * Real.log ((a * b : ℕ) : ℝ) + 3 ≤ C * K := by
    have htwoL : (L : ℝ) + 1 ≤ 2 * K := by linarith
    have h1 := mul_le_mul_of_nonneg_right htwoL (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hlog2)
    have h2 := mul_le_mul_of_nonneg_right hLKR hlogab
    have h3 := mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg K : (0 : ℝ) ≤ K)
    nlinarith
  have hboundary : ((L : ℝ) + 1) * Real.log 2 +
      ((L : ℝ) * (1 + B)) * |Real.log a| ≤ C * L := by
    have h1 := mul_le_mul_of_nonneg_right (show (L : ℝ) + 1 ≤ 2 * L by linarith) hlog2
    have h2 := mul_le_mul_of_nonneg_right hCB (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    nlinarith
  have hw := mul_le_mul_of_nonneg_right hboundary (Nat.cast_nonneg w : (0 : ℝ) ≤ w)
  unfold bakerMixedCircleRate bakerInitialHeightRate
  nlinarith [hcoef, hw]

theorem baker_contour_rate_of_log_bound {v j a b : ℕ} {B C : ℝ}
    (hv : 4 ≤ v) (hj : j < 20) (hC1 : 1 ≤ C)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hC : Real.log 4 + 5 + 10 * Real.log 2 + Real.log ((a * b : ℕ) : ℝ) + 3 ≤ C)
    (hCB : 2 * Real.log 2 + (1 + B) * |Real.log a| ≤ C)
    (hlog : Real.log (((bakerGridScale v (j + 1) : ℝ) + bakerGridScale v j) /
      ((bakerGridScale v (j + 2) : ℝ) - bakerGridScale v (j + 1))) ≤ -6 * C) :
    bakerMixedCircleRate (bakerWidth v) (bakerGridScale v (j + 2)) a
      ((bakerWidth v : ℝ) * (1 + B))
      (bakerInitialHeightRate (bakerBudget v 0) (bakerWidth v) a b + 1) +
      ((2 * bakerBudget v (j + 1) * bakerGridScale v j : ℕ) : ℝ) *
        Real.log (((bakerGridScale v (j + 1) : ℝ) + bakerGridScale v j) /
          ((bakerGridScale v (j + 2) : ℝ) - bakerGridScale v (j + 1))) + 1 ≤
      -bakerComparisonZeroRate (bakerBudget v 0) - 2 := by
  have hv1 : 1 ≤ v := by omega
  have hL : 1 ≤ bakerWidth v := Nat.one_le_pow _ _ hv1
  have hLK : bakerWidth v ≤ bakerBudget v 0 := by
    unfold bakerWidth bakerBudget
    have hp : v ^ 6 ≤ v ^ 8 := Nat.pow_le_pow_right hv1 (by norm_num)
    have hmul : v ^ 8 ≤ 4 ^ (20 - 0) * v ^ 8 := by
      have hm := Nat.mul_le_mul_right (v ^ 8) (show 1 ≤ 4 ^ (20 - 0) by norm_num)
      simpa using hm
    exact hp.trans hmul
  have hr := baker_circle_rate_linear (w := bakerGridScale v (j + 2))
    hL hLK ha hb hC hCB
  have hK : (bakerBudget v 0 : ℝ) ≤
      4 * (bakerBudget v (j + 1) : ℝ) * bakerGridScale v j := by
    exact_mod_cast bakerBudget_grid_dominates hv hj
  have hLw : (bakerWidth v : ℝ) * bakerGridScale v (j + 2) ≤
      (bakerBudget v (j + 1) : ℝ) * bakerGridScale v j := by
    exact_mod_cast bakerWidth_outer_dominated v j
  have hks : (1 : ℝ) ≤ (bakerBudget v (j + 1) : ℝ) * bakerGridScale v j := by
    exact_mod_cast Nat.mul_pos (bakerBudget_pos (show 0 < v by omega)) (pow_pos (by omega) _)
  have hd : Real.log 4 + 5 ≤ C := by
    have hlog2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    have hlogab := Real.log_nonneg (show (1 : ℝ) ≤ ((a * b : ℕ) : ℝ) by
      exact_mod_cast (show 1 ≤ a * b by nlinarith))
    linarith
  have hD := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg (bakerBudget v 0) : (0 : ℝ) ≤ _)
  have hK' := mul_le_mul_of_nonneg_left hK (show 0 ≤ C by linarith)
  have hLw' := mul_le_mul_of_nonneg_left hLw (show 0 ≤ C by linarith)
  have hlog' := mul_le_mul_of_nonneg_left hlog
    (show (0 : ℝ) ≤ 2 * (bakerBudget v (j + 1) : ℝ) * bakerGridScale v j by positivity)
  unfold bakerComparisonZeroRate
  push_cast
  nlinarith [hr, hD, hK', hLw', hlog',
    mul_nonneg (sub_nonneg.mpr hC1) (sub_nonneg.mpr hks)]

end HadamardMultibase
