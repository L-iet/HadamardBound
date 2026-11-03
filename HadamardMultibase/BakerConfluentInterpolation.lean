/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerInterpolation

@[expose] public section

/-! # Repeated Cauchy nodes and divided derivatives

The contour stays fixed while the interpolation point varies inside it.
Differentiating the Cauchy transform proves the repeated-node formula at
every interior point, rather than only at the contour's centre.
-/

namespace HadamardMultibase

open scoped Real Topology

noncomputable def cauchyDerivativeIntegral (R : ℝ) (f : ℂ → ℂ) (n : ℕ) (a : ℂ) : ℂ :=
  (2 * π * Complex.I : ℂ)⁻¹ *
    ∮ w in C(0, R), (w - a) ^ (-((n : ℤ) + 1)) * f w

theorem cauchyDerivativeIntegral_zero {R : ℝ} {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (Metric.ball 0 R)) {a : ℂ} (ha : ‖a‖ < R) :
    cauchyDerivativeIntegral R f 0 a = f a := by
  have hmem : a ∈ Metric.ball 0 R := by simpa [Metric.mem_ball, dist_zero_right] using ha
  simpa [cauchyDerivativeIntegral, smul_eq_mul] using
    hf.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hmem

theorem cauchyDerivativeIntegral_hasDerivAt {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : CircleIntegrable f 0 R) (n : ℕ) {a : ℂ} (ha : ‖a‖ < R) :
    HasDerivAt (cauchyDerivativeIntegral R f n)
      ((n + 1 : ℕ) * cauchyDerivativeIntegral R f (n + 1) a) a := by
  have hboundary : a ∉ Metric.sphere 0 |R| := by
    intro hm
    have he : ‖a‖ = |R| := by simpa [Metric.mem_sphere, dist_zero_right] using hm
    rw [abs_of_pos hR] at he
    linarith
  have he := (Complex.hasDerivAt_circleIntegral_sub_zpow_smul
    (n := -((n : ℤ) + 1)) hf hboundary).const_mul (2 * π * Complex.I : ℂ)⁻¹
  have hexp : -((n : ℤ) + 1) - 1 = -(((n + 1 : ℕ) : ℤ) + 1) := by omega
  convert he using 1
  · rfl
  · simp only [cauchyDerivativeIntegral, smul_eq_mul, hexp, Int.cast_neg, neg_neg,
      Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one]
    ring

theorem cauchyDerivativeIntegral_iteratedDeriv {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (Metric.ball 0 R)) (n : ℕ) {a : ℂ} (ha : ‖a‖ < R) :
    iteratedDeriv n f a = (n.factorial : ℂ) * cauchyDerivativeIntegral R f n a := by
  have hcont : ContinuousOn f (Metric.sphere 0 R) :=
    hf.continuousOn_ball.mono Metric.sphere_subset_closedBall
  have hint := hcont.circleIntegrable hR.le
  induction n generalizing a with
  | zero => simp [cauchyDerivativeIntegral_zero hf ha]
  | succ n ih =>
    have hmem : a ∈ Metric.ball 0 R := by simpa [Metric.mem_ball, dist_zero_right] using ha
    have heq : iteratedDeriv n f =ᶠ[𝓝 a]
        (fun w => (n.factorial : ℂ) * cauchyDerivativeIntegral R f n w) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hmem] with w hw
      exact ih (by simpa [Metric.mem_ball, dist_zero_right] using hw)
    have hd := ((cauchyDerivativeIntegral_hasDerivAt hR hint n ha).const_mul
      (n.factorial : ℂ)).congr_of_eventuallyEq heq
    have hder := hd.deriv
    rw [← iteratedDeriv_succ] at hder
    simpa only [Nat.factorial_succ, Nat.cast_mul, mul_assoc, mul_comm, mul_left_comm] using hder

theorem cauchyDividedDifference_replicate {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (Metric.ball 0 R)) (n : ℕ) {a : ℂ} (ha : ‖a‖ < R) :
    cauchyDividedDifference R f (List.replicate (n + 1) a) =
      iteratedDeriv n f a / (n.factorial : ℂ) := by
  have hexp : -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) := by omega
  have hi : cauchyDividedDifference R f (List.replicate (n + 1) a) =
      cauchyDerivativeIntegral R f n a := by
    simp only [cauchyDividedDifference, cauchyDerivativeIntegral, cauchyNodeKernel,
      List.map_replicate, List.prod_replicate, hexp, zpow_neg, zpow_natCast]
    congr 1
    congr 1
    funext w
    ring
  rw [hi]
  apply (eq_div_iff (show (n.factorial : ℂ) ≠ 0 by exact_mod_cast n.factorial_ne_zero)).mpr
  simpa only [mul_comm] using (cauchyDerivativeIntegral_iteratedDeriv hR hf n ha).symm

end HadamardMultibase
