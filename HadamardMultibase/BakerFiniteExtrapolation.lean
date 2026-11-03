/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerRateInequalities
public import HadamardMultibase.BakerInitialAuxiliary
public import HadamardMultibase.BakerZeroGridContradiction

@[expose] public section

/-! # Finite extrapolation from the initial equations to a forbidden zero grid -/
namespace HadamardMultibase
open Filter

noncomputable def bakerAccuracyRate (v a b : ℕ) : ℝ :=
  max 1 (bakerInitialHeightRate (bakerBudget v 0) (bakerWidth v) a b + 1 +
    bakerGridEntryRate (bakerWidth v) (bakerGridScale v 20) a b +
    bakerComparisonZeroRate (bakerBudget v 0) + 5 +
    ∑ j : Fin 20, 4 * (bakerBudget v (j.val + 1) : ℝ) *
      ((bakerGridScale v (j.val + 1) : ℝ) + bakerGridScale v j.val))

theorem bakerAccuracyRate_data (v a b : ℕ) (j : Fin 20) :
    (bakerInitialHeightRate (bakerBudget v 0) (bakerWidth v) a b + 1) +
      bakerGridEntryRate (bakerWidth v) (bakerGridScale v 20) a b + 1 - bakerAccuracyRate v a b + 2 +
      4 * (bakerBudget v (j.val + 1) : ℝ) *
        ((bakerGridScale v (j.val + 1) : ℝ) + bakerGridScale v j.val) ≤
      -bakerComparisonZeroRate (bakerBudget v 0) - 2 := by
  have hj := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : Fin 20 => 4 * (bakerBudget v (j.val + 1) : ℝ) *
      ((bakerGridScale v (j.val + 1) : ℝ) + bakerGridScale v j.val))
    (fun _ _ => by positivity) (Finset.mem_univ j)
  have hA := le_max_right 1 (bakerInitialHeightRate (bakerBudget v 0) (bakerWidth v) a b + 1 +
    bakerGridEntryRate (bakerWidth v) (bakerGridScale v 20) a b +
    bakerComparisonZeroRate (bakerBudget v 0) + 5 +
    ∑ j : Fin 20, 4 * (bakerBudget v (j.val + 1) : ℝ) *
      ((bakerGridScale v (j.val + 1) : ℝ) + bakerGridScale v j.val))
  unfold bakerAccuracyRate
  linarith

theorem eventually_baker_tiny_approximation_impossible {v a b : ℕ} {B C : ℝ}
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hirr : Irrational (Real.log (b : ℝ) / Real.log (a : ℝ)))
    (hv : 4 ≤ v) (hvlarge : 2 * 4 ^ 20 ≤ v) (hB : 0 ≤ B) (hC1 : 1 ≤ C)
    (hC : Real.log 4 + 5 + 10 * Real.log 2 + Real.log ((a * b : ℕ) : ℝ) + 3 ≤ C)
    (hCB : 2 * Real.log 2 + (1 + B) * |Real.log a| ≤ C)
    (hvlog : Real.log 2 - Real.log v ≤ -6 * C) :
    ∀ᶠ h : ℕ in atTop, ∀ p : ℤ, ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp h →
      |(p : ℝ) / q| ≤ B →
      |((p : ℝ) / q) * Real.log a - Real.log b| ≤
        Real.exp (-bakerAccuracyRate v a b * h) → False := by
  have hv0 : 0 < v := by omega
  have hv1 : 1 ≤ v := by omega
  have hL : 1 ≤ bakerWidth v := Nat.one_le_pow _ _ hv1
  have hΓ : (1 : ℝ) ≤ (bakerWidth v : ℝ) * (1 + B) := by
    have hLR : (1 : ℝ) ≤ bakerWidth v := by exact_mod_cast hL
    nlinarith
  have hsteps : ∀ j : Fin 20, ∀ᶠ h : ℕ in atTop, ∀ p : ℤ, ∀ q : ℕ,
      0 < q → (q : ℝ) ≤ Real.exp h →
      ∀ c : Fin (bakerColumnCount h (bakerWidth v)) → ℤ,
      (∀ i, |(c i : ℝ)| ≤ Real.exp
        ((bakerInitialHeightRate (bakerBudget v 0) (bakerWidth v) a b + 1) * h)) →
      (∀ i, |(bakerColumnLam h (bakerWidth v) i : ℝ) +
        (bakerColumnMu h (bakerWidth v) i : ℝ) * p / q| ≤ (bakerWidth v : ℝ) * (1 + B)) →
      |((p : ℝ) / q) * Real.log a - Real.log b| ≤ Real.exp (-bakerAccuracyRate v a b * h) →
      (∀ u r : ℕ, u < bakerBudget v j.val → r < bakerBudget v j.val → ∀ l : ℕ,
        1 ≤ l → l ≤ bakerGridScale v j.val * h →
          bakerIndexedComparison h (bakerWidth v) u r l p q a b c = 0) →
      ∀ u r : ℕ, u < bakerBudget v (j.val + 1) → r < bakerBudget v (j.val + 1) →
        ∀ l : ℕ, 1 ≤ l → l ≤ bakerGridScale v (j.val + 1) * h →
          bakerIndexedComparison h (bakerWidth v) u r l p q a b c = 0 := by
    intro j
    have hs : 0 < bakerGridScale v j.val := pow_pos hv0 _
    have hst : bakerGridScale v j.val ≤ bakerGridScale v (j.val + 1) :=
      Nat.pow_le_pow_right hv1 (by omega)
    have htw : bakerGridScale v (j.val + 1) < bakerGridScale v (j.val + 2) := by
      exact Nat.pow_lt_pow_right (by omega) (by omega)
    have htS : bakerGridScale v (j.val + 1) ≤ bakerGridScale v 20 :=
      Nat.pow_le_pow_right hv1 (by omega)
    have hbgt : 4 * bakerBudget v (j.val + 1) ≤ bakerBudget v 0 := by
      rw [← bakerBudget_step v j.val j.isLt]
      exact bakerBudget_le_initial v j.val
    have hc := baker_contour_rate_of_log_bound hv j.isLt hC1 (by omega) (by omega) hC hCB
      ((baker_grid_log_ratio hv j.val).trans hvlog)
    have he := eventually_baker_comparison_grid_step (L := bakerWidth v)
      (S := bakerGridScale v 20) (K := bakerBudget v 0)
      (by omega : 1 ≤ a) (by omega : 1 ≤ b) (bakerBudget_pos hv0) hs hst htw htS hbgt hΓ
      (bakerInitialHeightRate (bakerBudget v 0) (bakerWidth v) a b + 1)
      (bakerAccuracyRate v a b) (le_max_left _ _) (bakerAccuracyRate_data v a b j) hc
    simpa only [← bakerBudget_step v j.val j.isLt] using he
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_exists_initial_baker_auxiliary (K := bakerBudget v 0) (L := bakerWidth v)
      (by omega : 1 ≤ a) (by omega : 1 ≤ b) (baker_initial_equations_fewer hvlarge) hΓ,
    Filter.eventually_all.mpr hsteps] with h hh hinit hstep
  intro p q hq hqheight hβ hdef
  have hgamma (i : Fin (bakerColumnCount h (bakerWidth v))) :
      |(bakerColumnLam h (bakerWidth v) i : ℝ) +
        (bakerColumnMu h (bakerWidth v) i : ℝ) * p / q| ≤ (bakerWidth v : ℝ) * (1 + B) := by
    simpa [mul_div_assoc] using bounded_slope_frequency hB hβ
      (bakerColumnLam_le h (bakerWidth v) i) (bakerColumnMu_le h (bakerWidth v) i)
  obtain ⟨c, hc, hcoef, hzero⟩ := hinit q hq hqheight p hgamma
  have hall : ∀ j : ℕ, j ≤ 20 → ∀ u r : ℕ, u < bakerBudget v j → r < bakerBudget v j →
      ∀ l : ℕ, 1 ≤ l → l ≤ bakerGridScale v j * h →
        bakerIndexedComparison h (bakerWidth v) u r l p q a b c = 0 := by
    intro j
    induction j with
    | zero =>
      intro _ u r hu hr l hl hlmax
      exact hzero l u r hl (by simpa [bakerGridScale] using hlmax) hu hr
    | succ j ih =>
      intro hj u r hu hr l hl hlmax
      exact hstep ⟨j, by omega⟩ p q hq hqheight c hcoef hgamma hdef
        (ih (by omega)) u r hu hr l hl hlmax
  apply bakerIndexedComparison_zero_grid_impossible ha hb hirr c hc
    (T := bakerGridScale v 20 * h) ?_ p q
  · intro l hl hlmax
    exact hall 20 (by omega) 0 0 (bakerBudget_pos hv0) (bakerBudget_pos hv0) l hl hlmax
  · rw [bakerColumnCount_eq]
    simpa only [mul_comm] using Nat.mul_le_mul_right h (baker_final_grid_large hv)

end HadamardMultibase
