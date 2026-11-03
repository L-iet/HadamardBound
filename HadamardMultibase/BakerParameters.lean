/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerArithmeticStep

@[expose] public section

/-! # Fixed parameters for the twenty-step extrapolation -/
namespace HadamardMultibase

def bakerWidth (v : ℕ) : ℕ := v ^ 6
def bakerBudget (v j : ℕ) : ℕ := 4 ^ (20 - j) * v ^ 8
def bakerGridScale (v j : ℕ) : ℕ := v ^ j

theorem bakerBudget_step (v j : ℕ) (hj : j < 20) :
    bakerBudget v j = 4 * bakerBudget v (j + 1) := by
  unfold bakerBudget
  have he : 20 - j = (20 - (j + 1)) + 1 := by omega
  rw [he, pow_succ']
  ring

theorem bakerBudget_pos {v j : ℕ} (hv : 0 < v) : 0 < bakerBudget v j := by
  unfold bakerBudget
  positivity

theorem bakerBudget_le_initial (v j : ℕ) : bakerBudget v j ≤ bakerBudget v 0 := by
  unfold bakerBudget
  apply Nat.mul_le_mul_right
  exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)

theorem bakerBudget_grid_dominates {v j : ℕ} (hv : 4 ≤ v) (hj : j < 20) :
    bakerBudget v 0 ≤ 4 * bakerBudget v (j + 1) * bakerGridScale v j := by
  have hj19 : j ≤ 19 := by omega
  have he : 20 - (j + 1) + j = 19 := by omega
  have hp : 4 ^ j ≤ v ^ j := Nat.pow_le_pow_left hv j
  have hm := Nat.mul_le_mul_left (4 ^ (20 - (j + 1))) hp
  rw [← pow_add, he] at hm
  unfold bakerBudget bakerGridScale
  have hm2 := Nat.mul_le_mul_right (4 * v ^ 8) hm
  norm_num only [Nat.sub_zero, Nat.reducePow] at hm2 ⊢
  nlinarith [hm2]

theorem bakerWidth_outer_dominated (v j : ℕ) :
    bakerWidth v * bakerGridScale v (j + 2) ≤
      bakerBudget v (j + 1) * bakerGridScale v j := by
  have hpow : v ^ 6 * v ^ (j + 2) = v ^ 8 * v ^ j := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  unfold bakerWidth bakerGridScale bakerBudget
  rw [hpow]
  have hfour : 1 ≤ 4 ^ (20 - (j + 1)) := Nat.one_le_pow _ _ (by norm_num)
  nlinarith [Nat.mul_le_mul_right (v ^ 8 * v ^ j) hfour]

theorem baker_final_grid_large {v : ℕ} (hv : 4 ≤ v) :
    (bakerWidth v + 1) ^ 3 ≤ bakerGridScale v 20 := by
  have hv1 : 1 ≤ v := by omega
  have hp : 1 ≤ v ^ 6 := Nat.one_le_pow _ _ hv1
  have hcube : (v ^ 6 + 1) ^ 3 ≤ (2 * v ^ 6) ^ 3 := by gcongr; omega
  have hsq : 8 ≤ v ^ 2 := by nlinarith
  have hm := Nat.mul_le_mul_right (v ^ 18) hsq
  have he : (2 * v ^ 6) ^ 3 = 8 * v ^ 18 := by ring
  have he2 : v ^ 2 * v ^ 18 = v ^ 20 := by ring
  unfold bakerWidth bakerGridScale
  exact hcube.trans (by simpa only [he, he2] using hm)

theorem baker_initial_equations_fewer {v : ℕ} (hv : 2 * 4 ^ 20 ≤ v) :
    2 * bakerBudget v 0 ^ 2 ≤ (bakerWidth v + 1) ^ 3 := by
  have hsq : 2 * (4 : ℕ) ^ 40 ≤ v ^ 2 := by
    have hp := Nat.pow_le_pow_left hv 2
    norm_num at hp ⊢
    nlinarith [hp]
  have hm := Nat.mul_le_mul_right (v ^ 16) hsq
  have he : v ^ 2 * v ^ 16 = v ^ 18 := by ring
  rw [he] at hm
  have hcube : v ^ 18 ≤ (v ^ 6 + 1) ^ 3 := by
    calc
      v ^ 18 = (v ^ 6) ^ 3 := by ring
      _ ≤ _ := by gcongr; omega
  unfold bakerBudget bakerWidth
  norm_num only [Nat.sub_zero]
  calc
    2 * (4 ^ 20 * v ^ 8) ^ 2 = (2 * 4 ^ 40) * v ^ 16 := by ring
    _ ≤ v ^ 18 := hm
    _ ≤ _ := hcube

theorem baker_grid_log_ratio {v : ℕ} (hv : 4 ≤ v) (j : ℕ) :
    Real.log (((bakerGridScale v (j + 1) : ℝ) + bakerGridScale v j) /
      ((bakerGridScale v (j + 2) : ℝ) - bakerGridScale v (j + 1))) ≤
        Real.log 2 - Real.log v := by
  have hvR : (4 : ℝ) ≤ v := by exact_mod_cast hv
  have hv0 : (0 : ℝ) < v := by linarith
  have hp : (0 : ℝ) < (v : ℝ) ^ j := pow_pos hv0 _
  have hden : (0 : ℝ) < (v : ℝ)^2 - v := by nlinarith
  have he : (((bakerGridScale v (j + 1) : ℝ) + bakerGridScale v j) /
      ((bakerGridScale v (j + 2) : ℝ) - bakerGridScale v (j + 1))) =
      ((v : ℝ) + 1) / ((v : ℝ)^2 - v) := by
    unfold bakerGridScale
    push_cast
    rw [pow_add, pow_add]
    norm_num
    field_simp
  rw [he, ← Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hv0.ne']
  apply (Real.log_le_log_iff (div_pos (by linarith) hden) (div_pos (by norm_num) hv0)).mpr
  apply (div_le_div_iff₀ hden hv0).mpr
  nlinarith

end HadamardMultibase
