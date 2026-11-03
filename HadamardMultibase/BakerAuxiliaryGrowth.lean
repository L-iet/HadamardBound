/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerAuxiliaryNonvanishing
public import HadamardMultibase.BakerPolynomialGrowth
public import HadamardMultibase.BakerDerivativeGrowth
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

/-! # Complex growth of the block auxiliary function

The finite coefficient count, coefficient height, polynomial growth and
frequency growth are kept explicit. This estimate is suitable for Cauchy
derivative bounds on circles whose radius scales with the extrapolation grid.
-/

namespace HadamardMultibase

open Polynomial

noncomputable def bakerAuxiliaryComplexValue {ι : Type*} [Fintype ι] {D : ℕ}
    (h : ℕ) (ω : ι → ℝ) (c : ι → Fin D → ℝ) (z : ℂ) : ℂ :=
  ∑ i, ∑ d, (c i d : ℂ) * (bakerBlock h d.val).eval₂ (Rat.castHom ℂ) z *
    Complex.exp ((ω i : ℂ) * z)

theorem complex_exp_frequency_norm_bound (ω Ω R : ℝ) (hΩ : 0 ≤ Ω)
    (hω : |ω| ≤ Ω) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖Complex.exp ((ω : ℂ) * z)‖ ≤ Real.exp (Ω * R) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc ((ω : ℂ) * z).re ≤ ‖(ω : ℂ) * z‖ := Complex.re_le_norm _
    _ = |ω| * ‖z‖ := by simp
    _ ≤ Ω * R := mul_le_mul hω hz (norm_nonneg _) hΩ

theorem bakerAuxiliaryComplex_norm_bound {ι : Type*} [Fintype ι] {h D L T : ℕ}
    (hh : 0 < h) (hD : D ≤ h * (L + 1)) (ω : ι → ℝ) (c : ι → Fin D → ℝ)
    (H Ω : ℝ) (hH : 0 ≤ H) (hΩ : 0 ≤ Ω)
    (hc : ∀ i d, |c i d| ≤ H) (hω : ∀ i, |ω i| ≤ Ω)
    (z : ℂ) (hz : ‖z‖ ≤ (T * h : ℕ)) :
    ‖bakerAuxiliaryComplexValue h ω c z‖ ≤
      (Fintype.card ι : ℝ) * D * H *
        (2 : ℝ) ^ (h * (T + 1) * (L + 1)) * Real.exp (Ω * (T * h : ℕ)) := by
  classical
  let B := (2 : ℝ) ^ (h * (T + 1) * (L + 1))
  let E := Real.exp (Ω * (T * h : ℕ))
  have hterm (i : ι) (d : Fin D) :
      ‖(c i d : ℂ) * (bakerBlock h d.val).eval₂ (Rat.castHom ℂ) z *
        Complex.exp ((ω i : ℂ) * z)‖ ≤ H * B * E := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hb := bakerBlock_norm_le_uniform hh (d.isLt.trans_le hD) z hz
    have he := complex_exp_frequency_norm_bound (ω i) Ω (T * h : ℕ) hΩ (hω i) z hz
    apply mul_le_mul _ he (norm_nonneg _) (mul_nonneg hH (by dsimp [B]; positivity))
    exact mul_le_mul (hc i d) hb (norm_nonneg _) hH
  calc ‖bakerAuxiliaryComplexValue h ω c z‖
      ≤ ∑ i, ‖∑ d, (c i d : ℂ) * (bakerBlock h d.val).eval₂ (Rat.castHom ℂ) z *
          Complex.exp ((ω i : ℂ) * z)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ d : Fin D, H * B * E := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun d _ => hterm i d))
    _ = _ := by simp [B, E]; ring

theorem ratPolynomial_eval_complex_real (P : ℚ[X]) (x : ℝ) :
    P.eval₂ (Rat.castHom ℂ) (x : ℂ) = (((P.map (Rat.castHom ℝ)).eval x : ℝ) : ℂ) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [Polynomial.map_add, hP, hQ]
  | monomial n a => simp

theorem bakerAuxiliaryComplex_eval_real {ι : Type*} [Fintype ι] {D : ℕ}
    (h : ℕ) (ω : ι → ℝ) (c : ι → Fin D → ℝ) (x : ℝ) :
    bakerAuxiliaryComplexValue h ω c (x : ℂ) =
      ((exponentialPolynomialEval ω (fun i => bakerAuxiliaryPolynomial h (c i)) x : ℝ) : ℂ) := by
  classical
  simp [bakerAuxiliaryComplexValue, exponentialPolynomialEval, bakerAuxiliaryPolynomial,
    ratPolynomial_eval_complex_real, eval_finsetSum, eval_smul, smul_eq_mul,
    Finset.sum_mul, Complex.ofReal_exp]

theorem bakerAuxiliaryComplex_differentiable {ι : Type*} [Fintype ι] {D : ℕ}
    (h : ℕ) (ω : ι → ℝ) (c : ι → Fin D → ℝ) :
    Differentiable ℂ (bakerAuxiliaryComplexValue h ω c) := by
  classical
  have hpoly (d : Fin D) :
      Differentiable ℂ (fun z => (bakerBlock h d.val).eval₂ (Rat.castHom ℂ) z) := by
    simpa only [eval₂_eq_eval_map] using
      ((bakerBlock h d.val).map (Rat.castHom ℂ)).differentiable
  unfold bakerAuxiliaryComplexValue
  fun_prop

theorem bakerAuxiliaryComplex_iteratedDeriv_norm_bound {ι : Type*} [Fintype ι]
    {h D L T : ℕ} (hh : 0 < h) (hD : D ≤ h * (L + 1))
    (ω : ι → ℝ) (c : ι → Fin D → ℝ) (H Ω : ℝ) (hH : 0 ≤ H) (hΩ : 0 ≤ Ω)
    (hc : ∀ i d, |c i d| ≤ H) (hω : ∀ i, |ω i| ≤ Ω)
    (m : ℕ) (z : ℂ) (R : ℝ) (hR : 0 < R)
    (hz : ‖z‖ + R ≤ (T * h : ℕ)) :
    ‖iteratedDeriv m (bakerAuxiliaryComplexValue h ω c) z‖ ≤
      (m.factorial : ℝ) * ((Fintype.card ι : ℝ) * D * H *
        (2 : ℝ) ^ (h * (T + 1) * (L + 1)) * Real.exp (Ω * (T * h : ℕ))) / R ^ m := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hR
    (bakerAuxiliaryComplex_differentiable h ω c).diffContOnCl
  intro w hw
  apply bakerAuxiliaryComplex_norm_bound hh hD ω c H Ω hH hΩ hc hω
  have hwz : ‖w - z‖ = R := mem_sphere_iff_norm.mp hw
  calc ‖w‖ = ‖w - z + z‖ := by congr 1; ring
    _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ _ := by rw [hwz]; linarith

end HadamardMultibase
