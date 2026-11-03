/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerPolynomialGrowth
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Complex.Liouville

@[expose] public section

/-!
# Divided derivative bounds

Cauchy's estimate on a unit circle cancels the factorial in the Hasse
derivative. This supplies a bound uniform in the derivative order, using
the previously proved block-polynomial bound on a disk enlarged by one.
-/

namespace HadamardMultibase

open Polynomial

theorem polynomial_iteratedDeriv_eval (P : ℂ[X]) (m : ℕ) :
    iteratedDeriv m (fun z => P.eval z) = fun z => (derivative^[m] P).eval z := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    rw [Polynomial.deriv, Function.iterate_succ_apply']

theorem polynomial_hasse_norm_le_circle_bound (P : ℂ[X]) (m : ℕ) (z : ℂ) (C : ℝ)
    (hC : ∀ w ∈ Metric.sphere z 1, ‖P.eval w‖ ≤ C) :
    ‖(hasseDeriv m P).eval z‖ ≤ C := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m
    (by norm_num : (0 : ℝ) < 1) P.differentiable.diffContOnCl hC
  have hid : iteratedDeriv m (fun w => P.eval w) z =
      (m.factorial : ℂ) * (hasseDeriv m P).eval z := by
    rw [polynomial_iteratedDeriv_eval, ← factorial_smul_hasseDeriv]
    simp [nsmul_eq_mul]
  rw [hid, norm_mul, Complex.norm_natCast] at h
  simp only [one_pow, div_one] at h
  have hpos : (0 : ℝ) < m.factorial := by positivity
  nlinarith

/-- The radius is retained explicitly: choosing it proportional to the grid
size avoids an artificial log(grid size) loss in high derivative bounds. -/
theorem polynomial_hasse_norm_le_circle_bound_radius (P : ℂ[X]) (m : ℕ)
    (z : ℂ) (C R : ℝ) (hR : 0 < R)
    (hC : ∀ w ∈ Metric.sphere z R, ‖P.eval w‖ ≤ C) :
    ‖(hasseDeriv m P).eval z‖ ≤ C / R ^ m := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m
    hR P.differentiable.diffContOnCl hC
  have hid : iteratedDeriv m (fun w => P.eval w) z =
      (m.factorial : ℂ) * (hasseDeriv m P).eval z := by
    rw [polynomial_iteratedDeriv_eval, ← factorial_smul_hasseDeriv]
    simp [nsmul_eq_mul]
  rw [hid, norm_mul, Complex.norm_natCast] at h
  have hpos : (0 : ℝ) < m.factorial := by positivity
  apply (mul_le_mul_iff_right₀ hpos).mp
  simpa only [mul_div_assoc] using h

theorem bakerBlock_hasse_norm_le_two_pow (h a m R : ℕ) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖(hasseDeriv m (bakerBlock h a)).eval₂ (Rat.castHom ℂ) z‖ ≤
      (2 : ℝ) ^ ((R + 1 + h) * (a / h) + (R + 1 + a % h)) := by
  rw [eval₂_eq_eval_map, ← hasseDeriv_map]
  apply polynomial_hasse_norm_le_circle_bound
  intro w hw
  rw [← eval₂_eq_eval_map]
  apply bakerBlock_norm_le_two_pow
  have hdist : ‖w - z‖ = 1 := mem_sphere_iff_norm.mp hw
  calc ‖w‖ = ‖w - z + z‖ := by congr 1; ring
    _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ ((R + 1 : ℕ) : ℝ) := by rw [hdist]; push_cast; linarith

theorem bakerBlock_hasse_norm_le_two_pow_radius (h a m R S : ℕ) (hS : 0 < S)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖(hasseDeriv m (bakerBlock h a)).eval₂ (Rat.castHom ℂ) z‖ ≤
      (2 : ℝ) ^ ((R + S + h) * (a / h) + (R + S + a % h)) / (S : ℝ) ^ m := by
  rw [eval₂_eq_eval_map, ← hasseDeriv_map]
  apply polynomial_hasse_norm_le_circle_bound_radius _ _ _ _ _ (by exact_mod_cast hS)
  intro w hw
  rw [← eval₂_eq_eval_map]
  apply bakerBlock_norm_le_two_pow
  have hdist : ‖w - z‖ = (S : ℝ) := mem_sphere_iff_norm.mp hw
  calc ‖w‖ = ‖w - z + z‖ := by congr 1; ring
    _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ ((R + S : ℕ) : ℝ) := by rw [hdist]; push_cast; linarith

theorem bakerBlock_hasse_norm_le_uniform {h a L T : ℕ} (hh : 0 < h)
    (ha : a < h * (L + 1)) (m : ℕ) (z : ℂ) (hz : ‖z‖ ≤ (T * h : ℕ)) :
    ‖(hasseDeriv m (bakerBlock h a)).eval₂ (Rat.castHom ℂ) z‖ ≤
      (2 : ℝ) ^ (h * (T + 2) * (L + 1)) := by
  rw [eval₂_eq_eval_map, ← hasseDeriv_map]
  apply polynomial_hasse_norm_le_circle_bound
  intro w hw
  rw [← eval₂_eq_eval_map]
  have hdist : ‖w - z‖ = 1 := mem_sphere_iff_norm.mp hw
  have hwBound : ‖w‖ ≤ ((T + 1) * h : ℕ) := by
    have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
    calc ‖w‖ = ‖w - z + z‖ := by congr 1; ring
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ _ := by rw [hdist]; push_cast at hz ⊢; nlinarith
  simpa only [Nat.add_assoc] using (bakerBlock_norm_le_uniform hh ha w hwBound)

end HadamardMultibase
