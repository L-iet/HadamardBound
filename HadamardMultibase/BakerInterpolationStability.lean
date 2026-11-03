/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerInterpolationGrid
public import HadamardMultibase.BakerInterpolationMajorant

@[expose] public section

/-! # Stability of interpolation from small derivative data

The constants depend on the multiplicity k, while the order-dependent
factorial controls arbitrarily long integer grids. This is a quantitative
estimate: the original derivative data need only be small, not exactly zero.
-/

namespace HadamardMultibase

theorem cauchyGrid_constant_window_bound {R ε : ℝ} (hR : 0 < R)
    {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f (Metric.ball 0 R))
    {k N s n : ℕ} (hk : 0 < k) (hs : s + (n + 1) ≤ k * N) (hNR : (N : ℝ) < R)
    (hε : 0 ≤ ε)
    (hjet : ∀ l : ℕ, 1 ≤ l → l ≤ N → ∀ u : ℕ, u < k →
      ‖iteratedDeriv u f (l : ℂ)‖ / (u.factorial : ℝ) ≤ ε)
    (he : interpolationGridNode k s = interpolationGridNode k (s + n)) :
    ‖cauchyDividedDifference R f (interpolationGridList k s (n + 1))‖ ≤
      confluentMajorant k n ε := by
  have hn : n < k := interpolationGridNode_lt_multiplicity hk he
  have hnode := interpolationGridNode_le hk (show s < k * N by omega)
  have hnodeR : ‖(interpolationGridNode k s : ℂ)‖ < R := by
    rw [Complex.norm_natCast]
    exact (show (interpolationGridNode k s : ℝ) ≤ N by exact_mod_cast hnode.2).trans_lt hNR
  calc ‖cauchyDividedDifference R f (interpolationGridList k s (n + 1))‖
      = ‖iteratedDeriv n f (interpolationGridNode k s : ℂ)‖ / (n.factorial : ℝ) := by
        rw [interpolationGridList_eq_replicate he,
          cauchyDividedDifference_replicate hR hf n hnodeR, norm_div, Complex.norm_natCast]
    _ ≤ ε := hjet _ hnode.1 hnode.2 n hn
    _ ≤ confluentMajorant k n ε := le_confluentMajorant_of_lt hk hn hε

theorem cauchyGrid_coefficient_bound {R ε : ℝ} (hR : 0 < R)
    {f : ℂ → ℂ} (hf : DiffContOnCl ℂ f (Metric.ball 0 R))
    {k N : ℕ} (hk : 0 < k) (hNR : (N : ℝ) < R) (hε : 0 ≤ ε)
    (hjet : ∀ l : ℕ, 1 ≤ l → l ≤ N → ∀ u : ℕ, u < k →
      ‖iteratedDeriv u f (l : ℂ)‖ / (u.factorial : ℝ) ≤ ε)
    (n s : ℕ) (hs : s + (n + 1) ≤ k * N) :
    ‖cauchyDividedDifference R f (interpolationGridList k s (n + 1))‖ ≤
      confluentMajorant k n ε := by
  induction n generalizing s with
  | zero =>
    apply cauchyGrid_constant_window_bound hR hf hk hs hNR hε hjet
    simp
  | succ n ih =>
    by_cases he : interpolationGridNode k s = interpolationGridNode k (s + (n + 1))
    · exact cauchyGrid_constant_window_bound hR hf hk hs hNR hε hjet he
    have hmono : interpolationGridNode k s ≤ interpolationGridNode k (s + (n + 1)) :=
      interpolationGridNode_mono k (Nat.le_add_right s (n + 1))
    let gap := interpolationGridNode k (s + (n + 1)) - interpolationGridNode k s
    have hgap : 1 ≤ gap := by dsimp [gap]; omega
    have hgapR : (1 : ℝ) ≤ gap := by exact_mod_cast hgap
    have hgapPos : (0 : ℝ) < gap := by linarith
    have hhead := ih s (show s + (n + 1) ≤ k * N by omega)
    have htail := ih (s + 1) (show s + 1 + (n + 1) ≤ k * N by omega)
    have hcont : ContinuousOn f (Metric.sphere 0 R) :=
      hf.continuousOn_ball.mono Metric.sphere_subset_closedBall
    have hrec := interpolationGrid_cauchy_recurrence hR.le hcont hk
      (show s + (n + 2) ≤ k * N by omega) hNR
    simp only [Nat.add_assoc] at hrec
    have hnorm : ‖(interpolationGridNode k (s + (n + 1)) : ℂ) - interpolationGridNode k s‖ =
        (gap : ℝ) := by
      rw [← Nat.cast_sub hmono, Complex.norm_natCast]
    have hbound : (gap : ℝ) *
        ‖cauchyDividedDifference R f (interpolationGridList k s (n + 2))‖ ≤
        2 * confluentMajorant k n ε := by
      calc (gap : ℝ) * ‖cauchyDividedDifference R f (interpolationGridList k s (n + 2))‖
          = ‖((interpolationGridNode k (s + (n + 1)) : ℂ) - interpolationGridNode k s) *
              cauchyDividedDifference R f (interpolationGridList k s (n + 2))‖ := by
                rw [norm_mul, hnorm]
        _ = _ := congrArg norm hrec
        _ ≤ ‖cauchyDividedDifference R f (interpolationGridList k (s + 1) (n + 1))‖ +
            ‖cauchyDividedDifference R f (interpolationGridList k s (n + 1))‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    have hsep : ((n + 2 - k : ℕ) : ℝ) ≤ (k : ℝ) * (gap : ℝ) := by
      exact_mod_cast (interpolationGridNode_separation (s := s) (n := n + 1) hk)
    calc ‖cauchyDividedDifference R f (interpolationGridList k s (n + 1 + 1))‖
        ≤ 2 * confluentMajorant k n ε / (gap : ℝ) := by
          apply (le_div_iff₀ hgapPos).mpr
          nlinarith [hbound]
      _ ≤ confluentMajorant k (n + 1) ε := confluentMajorant_step hk hε hgapR hsep

end HadamardMultibase
