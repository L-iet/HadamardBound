/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Tactic

@[expose] public section

/-! # Cauchy divided differences for quantitative interpolation

Repeated nodes are permitted. A list of m+1 nodes represents a divided
difference of order m. The symmetric integral definition avoids choosing
between distinct-node and repeated-node formulas during extrapolation.
-/

namespace HadamardMultibase

open scoped Real

noncomputable def cauchyNodeKernel (nodes : List ℂ) (w : ℂ) : ℂ :=
  ((nodes.map (fun a => w - a)).prod)⁻¹

@[simp] theorem cauchyNodeKernel_nil (w : ℂ) : cauchyNodeKernel [] w = 1 := by
  simp [cauchyNodeKernel]

@[simp] theorem cauchyNodeKernel_cons (a : ℂ) (nodes : List ℂ) (w : ℂ) :
    cauchyNodeKernel (a :: nodes) w = (w - a)⁻¹ * cauchyNodeKernel nodes w := by
  simp [cauchyNodeKernel, mul_inv_rev, mul_comm]

theorem cauchyNodeKernel_perm {s t : List ℂ} (h : s.Perm t) (w : ℂ) :
    cauchyNodeKernel s w = cauchyNodeKernel t w := by
  unfold cauchyNodeKernel
  rw [(h.map (fun a => w - a)).prod_eq]

theorem cauchyNodeKernel_difference (a b w : ℂ) (nodes : List ℂ)
    (ha : w - a ≠ 0) (hb : w - b ≠ 0) :
    cauchyNodeKernel (a :: nodes) w - cauchyNodeKernel (b :: nodes) w =
      (a - b) * cauchyNodeKernel (a :: b :: nodes) w := by
  simp only [cauchyNodeKernel_cons]
  field_simp
  ring

theorem cauchyNode_ne_boundary {R : ℝ} {a w : ℂ} (ha : ‖a‖ < R)
    (hw : w ∈ Metric.sphere 0 R) : w - a ≠ 0 := by
  have hwR : ‖w‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hw
  intro h
  rw [sub_eq_zero.mp h] at hwR
  linarith

theorem cauchyNodeKernel_continuousOn {R : ℝ} (nodes : List ℂ)
    (hnodes : ∀ a ∈ nodes, ‖a‖ < R) :
    ContinuousOn (cauchyNodeKernel nodes) (Metric.sphere 0 R) := by
  induction nodes with
  | nil =>
    rw [show cauchyNodeKernel ([] : List ℂ) = (fun _ => 1) from funext cauchyNodeKernel_nil]
    exact continuousOn_const
  | cons a nodes ih =>
    have ha := hnodes a (by simp)
    have ht := ih (fun b hb => hnodes b (List.mem_cons_of_mem _ hb))
    have hi : ContinuousOn (fun w : ℂ => (w - a)⁻¹) (Metric.sphere 0 R) :=
      (continuousOn_id.sub continuousOn_const).inv₀ (fun w hw => cauchyNode_ne_boundary ha hw)
    change ContinuousOn (fun w => cauchyNodeKernel (a :: nodes) w) (Metric.sphere 0 R)
    simpa only [cauchyNodeKernel_cons, Pi.mul_def] using hi.mul ht

noncomputable def cauchyDividedDifference (R : ℝ) (f : ℂ → ℂ) (nodes : List ℂ) : ℂ :=
  (2 * π * Complex.I : ℂ)⁻¹ * ∮ w in C(0, R), f w * cauchyNodeKernel nodes w

theorem cauchyDividedDifference_perm (R : ℝ) (f : ℂ → ℂ) {s t : List ℂ} (h : s.Perm t) :
    cauchyDividedDifference R f s = cauchyDividedDifference R f t := by
  unfold cauchyDividedDifference
  congr 1
  congr 1
  funext w
  rw [cauchyNodeKernel_perm h]

theorem cauchyDividedDifference_singleton {R : ℝ} {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (Metric.ball 0 R)) {a : ℂ} (ha : ‖a‖ < R) :
    cauchyDividedDifference R f [a] = f a := by
  have hmem : a ∈ Metric.ball 0 R := by simpa [Metric.mem_ball, dist_zero_right] using ha
  simpa [cauchyDividedDifference, smul_eq_mul, mul_comm] using
    hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hmem

theorem cauchyDividedDifference_recurrence {R : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.sphere 0 R)) (a b : ℂ) (nodes : List ℂ)
    (ha : ‖a‖ < R) (hb : ‖b‖ < R) (hnodes : ∀ x ∈ nodes, ‖x‖ < R) :
    (a - b) * cauchyDividedDifference R f (a :: b :: nodes) =
      cauchyDividedDifference R f (a :: nodes) - cauchyDividedDifference R f (b :: nodes) := by
  have hia : CircleIntegrable (fun w => f w * cauchyNodeKernel (a :: nodes) w) 0 R :=
    (hf.mul (cauchyNodeKernel_continuousOn _ (by simpa using And.intro ha hnodes))).circleIntegrable hR
  have hib : CircleIntegrable (fun w => f w * cauchyNodeKernel (b :: nodes) w) 0 R :=
    (hf.mul (cauchyNodeKernel_continuousOn _ (by simpa using And.intro hb hnodes))).circleIntegrable hR
  have hi : (∮ w in C(0, R), f w * cauchyNodeKernel (a :: nodes) w) -
      (∮ w in C(0, R), f w * cauchyNodeKernel (b :: nodes) w) =
      (a - b) * ∮ w in C(0, R), f w * cauchyNodeKernel (a :: b :: nodes) w := by
    rw [← circleIntegral.integral_sub hia hib, ← circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hR
    intro w hw
    dsimp only
    rw [← mul_sub, cauchyNodeKernel_difference a b w nodes
      (cauchyNode_ne_boundary ha hw) (cauchyNode_ne_boundary hb hw)]
    ring
  unfold cauchyDividedDifference
  rw [← mul_sub, hi]
  ring

theorem cauchyNodeKernel_norm_bound {R r : ℝ} (hR : r < R) (nodes : List ℂ)
    (hnodes : ∀ a ∈ nodes, ‖a‖ ≤ r) (w : ℂ) (hw : w ∈ Metric.sphere 0 R) :
    ‖cauchyNodeKernel nodes w‖ ≤ 1 / (R - r) ^ nodes.length := by
  have hpos : 0 < R - r := sub_pos.mpr hR
  have hwR : ‖w‖ = R := by simpa [Metric.mem_sphere, dist_zero_right] using hw
  induction nodes with
  | nil => simp
  | cons a nodes ih =>
    have ha := hnodes a (by simp)
    have ht := ih (fun b hb => hnodes b (List.mem_cons_of_mem _ hb))
    have hd : R - r ≤ ‖w - a‖ := by
      have := norm_sub_norm_le w a
      rw [hwR] at this
      linarith
    have hinv : ‖(w - a)⁻¹‖ ≤ (R - r)⁻¹ := by
      rw [norm_inv]
      exact inv_anti₀ hpos hd
    rw [cauchyNodeKernel_cons, norm_mul, List.length_cons]
    calc ‖(w - a)⁻¹‖ * ‖cauchyNodeKernel nodes w‖ ≤
        (R - r)⁻¹ * (1 / (R - r) ^ nodes.length) :=
          mul_le_mul hinv ht (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_succ]; field_simp

theorem cauchyDividedDifference_norm_bound {R r M : ℝ} (hR : 0 ≤ R) (hrR : r < R)
    (f : ℂ → ℂ) (nodes : List ℂ) (hnodes : ∀ a ∈ nodes, ‖a‖ ≤ r)
    (hM : 0 ≤ M) (hf : ∀ w ∈ Metric.sphere 0 R, ‖f w‖ ≤ M) :
    ‖cauchyDividedDifference R f nodes‖ ≤ R * M / (R - r) ^ nodes.length := by
  change ‖(2 * π * Complex.I : ℂ)⁻¹ •
    ∮ w in C(0, R), f w * cauchyNodeKernel nodes w‖ ≤ _
  have hb : ∀ w ∈ Metric.sphere 0 R,
      ‖f w * cauchyNodeKernel nodes w‖ ≤ M / (R - r) ^ nodes.length := by
    intro w hw
    rw [norm_mul, div_eq_mul_inv]
    have hk : ‖cauchyNodeKernel nodes w‖ ≤ ((R - r) ^ nodes.length)⁻¹ := by
      simpa only [one_div] using (cauchyNodeKernel_norm_bound hrR nodes hnodes w hw)
    exact mul_le_mul (hf w hw) hk (norm_nonneg _) hM
  have he := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR hb
  simpa only [mul_div_assoc] using he

end HadamardMultibase
