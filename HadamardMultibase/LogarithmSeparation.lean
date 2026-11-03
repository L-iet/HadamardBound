/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerFiniteExtrapolation
public import HadamardMultibase.BakerLiouvilleReduction
public import HadamardMultibase.NonLiouvilleSeparation

@[expose] public section

/-! # Finite irrationality measure for an irrational ratio of integer logarithms -/
namespace HadamardMultibase

theorem not_liouville_log_ratio {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hirr : Irrational (Real.log (b : ℝ) / Real.log (a : ℝ))) :
    ¬Liouville (Real.log (b : ℝ) / Real.log (a : ℝ)) := by
  intro hLiouville
  let B : ℝ := |Real.log (b : ℝ) / Real.log (a : ℝ)| + 1
  let C : ℝ := max 1 (max
    (Real.log 4 + 5 + 10 * Real.log 2 + Real.log ((a * b : ℕ) : ℝ) + 3)
    (2 * Real.log 2 + (1 + B) * |Real.log a|))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC : Real.log 4 + 5 + 10 * Real.log 2 + Real.log ((a * b : ℕ) : ℝ) + 3 ≤ C :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hCB : 2 * Real.log 2 + (1 + B) * |Real.log a| ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨v, hv⟩ := exists_nat_gt
    (max (((2 * 4 ^ 20 : ℕ) : ℝ)) (Real.exp (Real.log 2 + 6 * C) + 4))
  have hvlargeR : (((2 * 4 ^ 20 : ℕ) : ℝ)) < v := (le_max_left _ _).trans_lt hv
  have hvlarge : 2 * 4 ^ 20 ≤ v := by exact_mod_cast hvlargeR.le
  have hv4 : 4 ≤ v := by norm_num at hvlarge ⊢; omega
  have hvR : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  have hvexp : Real.exp (Real.log 2 + 6 * C) ≤ (v : ℝ) := by
    have hx := (le_max_right _ _).trans_lt hv
    linarith
  have hvlog : Real.log 2 - Real.log (v : ℝ) ≤ -6 * C := by
    have hx := Real.log_le_log (Real.exp_pos _) hvexp
    rw [Real.log_exp] at hx
    linarith
  have he := eventually_baker_tiny_approximation_impossible ha hb hirr hv4 hvlarge hB hC1 hC hCB hvlog
  obtain ⟨H, hH⟩ := Filter.eventually_atTop.mp he
  have hloga : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hA : 0 < bakerAccuracyRate v a b := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  obtain ⟨h, q, hHh, hq, hqheight, p, hβ, hdef⟩ :=
    liouville_tiny_grid_approximation hLiouville hloga hA H
  apply hH h hHh p q (by omega) hqheight hβ
  have heq : Real.log (a : ℝ) * ((p : ℝ) / q - Real.log (b : ℝ) / Real.log (a : ℝ)) =
      ((p : ℝ) / q) * Real.log a - Real.log b := by
    field_simp
  rw [heq] at hdef
  exact hdef.le

theorem polynomialRotationSeparation_log_ratio {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hirr : Irrational (Real.log (b : ℝ) / Real.log (a : ℝ))) :
    PolynomialRotationSeparation (Real.log (b : ℝ) / Real.log (a : ℝ)) :=
  polynomialRotationSeparation_of_not_liouville hirr (not_liouville_log_ratio ha hb hirr)

end HadamardMultibase
