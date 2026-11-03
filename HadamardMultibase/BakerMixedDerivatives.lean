/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerPerturbation
public import HadamardMultibase.BakerAuxiliaryGrowth
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

@[expose] public section

/-! # Analytic mixed auxiliary functions and their derivatives

Differentiating on the diagonal raises one of the two mixed indices. The
recurrence controls univariate jets using the rectangular comparison system.
-/

namespace HadamardMultibase

open Polynomial

theorem derivative_hasseDeriv_succ (P : ℚ[X]) (u : ℕ) :
    (hasseDeriv u P).derivative = (u + 1) • hasseDeriv (u + 1) P := by
  have he := congrArg (fun T : ℚ[X] →ₗ[ℚ] ℚ[X] => T P) (hasseDeriv_comp (R := ℚ) 1 u)
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, hasseDeriv_one,
    Nat.choose_one_right, Nat.add_comm] using he

theorem hassePolynomial_eval_hasDerivAt (P : ℚ[X]) (u : ℕ) (z : ℂ) :
    HasDerivAt (fun w => (hasseDeriv u P).eval₂ (Rat.castHom ℂ) w)
      ((u + 1 : ℕ) * (hasseDeriv (u + 1) P).eval₂ (Rat.castHom ℂ) z) z := by
  simpa [eval₂_eq_eval_map, derivative_map, derivative_hasseDeriv_succ, nsmul_eq_mul] using
    ((hasseDeriv u P).map (Rat.castHom ℂ)).hasDerivAt z

noncomputable def bakerMixedComplexValue {n : ℕ} (h u v : ℕ) (β : ℝ) (a : ℕ)
    (c : Fin n → ℤ) (d lam mu : Fin n → ℕ) (z : ℂ) : ℂ :=
  ∑ j, (c j : ℂ) * (hasseDeriv u (bakerBlock h (d j))).eval₂ (Rat.castHom ℂ) z *
    (((lam j : ℝ) + (mu j : ℝ) * β : ℝ) : ℂ) ^ v *
      Complex.exp (((((lam j : ℝ) + (mu j : ℝ) * β) * Real.log a : ℝ) : ℂ) * z)

theorem bakerMixedComplex_hasDerivAt {n : ℕ} (h u v : ℕ) (β : ℝ) (a : ℕ)
    (c : Fin n → ℤ) (d lam mu : Fin n → ℕ) (z : ℂ) :
    HasDerivAt (bakerMixedComplexValue h u v β a c d lam mu)
      ((u + 1 : ℕ) * bakerMixedComplexValue h (u + 1) v β a c d lam mu z +
        (Real.log a : ℂ) * bakerMixedComplexValue h u (v + 1) β a c d lam mu z) z := by
  classical
  have hj (j : Fin n) :=
    (((hassePolynomial_eval_hasDerivAt (bakerBlock h (d j)) u z).const_mul (c j : ℂ)).mul_const
      ((((lam j : ℝ) + (mu j : ℝ) * β : ℝ) : ℂ) ^ v)).mul
        (((hasDerivAt_id z).const_mul
          (((((lam j : ℝ) + (mu j : ℝ) * β) * Real.log a : ℝ) : ℂ))).cexp)
  convert HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hj j) using 1
  · rfl
  · simp only [bakerMixedComplexValue, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Complex.ofReal_mul, pow_succ, id_eq, mul_one]
    ring

theorem bakerMixedComplex_differentiable {n : ℕ} (h u v : ℕ) (β : ℝ) (a : ℕ)
    (c : Fin n → ℤ) (d lam mu : Fin n → ℕ) :
    Differentiable ℂ (bakerMixedComplexValue h u v β a c d lam mu) :=
  fun z => (bakerMixedComplex_hasDerivAt h u v β a c d lam mu z).differentiableAt

theorem bakerMixedComplex_deriv {n : ℕ} (h u v : ℕ) (β : ℝ) (a : ℕ)
    (c : Fin n → ℤ) (d lam mu : Fin n → ℕ) :
    deriv (bakerMixedComplexValue h u v β a c d lam mu) =
      fun z => (u + 1 : ℕ) * bakerMixedComplexValue h (u + 1) v β a c d lam mu z +
        (Real.log a : ℂ) * bakerMixedComplexValue h u (v + 1) β a c d lam mu z := by
  funext z
  exact (bakerMixedComplex_hasDerivAt h u v β a c d lam mu z).deriv

theorem bakerMixedComplex_eval_real {n : ℕ} (h u v : ℕ) (β : ℝ) (a : ℕ)
    (c : Fin n → ℤ) (d lam mu : Fin n → ℕ) (x : ℝ) :
    bakerMixedComplexValue h u v β a c d lam mu (x : ℂ) =
      ((bakerMixedRealValue h u v β a c d lam mu x : ℝ) : ℂ) := by
  unfold bakerMixedComplexValue bakerMixedRealValue
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  rw [ratPolynomial_eval_complex_real]
  simp only [eval₂_eq_eval_map]

theorem bakerMixedComplex_iteratedDeriv_bound {n K : ℕ} (h : ℕ) (β : ℝ) (a : ℕ)
    (c : Fin n → ℤ) (d lam mu : Fin n → ℕ) (z : ℂ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hvalues : ∀ i j : ℕ, i + j ≤ K → ‖bakerMixedComplexValue h i j β a c d lam mu z‖ ≤ ε)
    (r u v : ℕ) (hbudget : u + v + r ≤ K) :
    ‖iteratedDeriv r (bakerMixedComplexValue h u v β a c d lam mu) z‖ ≤
      ((K : ℝ) + |Real.log a|) ^ r * ε := by
  induction r generalizing u v with
  | zero => simpa using hvalues u v (by omega)
  | succ r ih =>
    have hfirst := ih (u + 1) v (by omega)
    have hsecond := ih u (v + 1) (by omega)
    have hc1 : ContDiffAt ℂ r
        (fun w => ((u + 1 : ℕ) : ℂ) * bakerMixedComplexValue h (u + 1) v β a c d lam mu w) z :=
      ((bakerMixedComplex_differentiable h (u + 1) v β a c d lam mu).const_mul _).contDiff.contDiffAt
    have hc2 : ContDiffAt ℂ r
        (fun w => (Real.log a : ℂ) * bakerMixedComplexValue h u (v + 1) β a c d lam mu w) z :=
      ((bakerMixedComplex_differentiable h u (v + 1) β a c d lam mu).const_mul _).contDiff.contDiffAt
    rw [iteratedDeriv_succ', bakerMixedComplex_deriv,
      iteratedDeriv_fun_add hc1 hc2, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
    calc ‖((u + 1 : ℕ) : ℂ) * iteratedDeriv r
            (bakerMixedComplexValue h (u + 1) v β a c d lam mu) z +
          (Real.log a : ℂ) * iteratedDeriv r
            (bakerMixedComplexValue h u (v + 1) β a c d lam mu) z‖
        ≤ ((u + 1 : ℕ) : ℝ) * (((K : ℝ) + |Real.log a|) ^ r * ε) +
            |Real.log a| * (((K : ℝ) + |Real.log a|) ^ r * ε) := by
          apply (norm_add_le _ _).trans
          simp only [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
          exact add_le_add (mul_le_mul_of_nonneg_left hfirst (by positivity))
            (mul_le_mul_of_nonneg_left hsecond (abs_nonneg _))
      _ ≤ ((K : ℝ) + |Real.log a|) ^ (r + 1) * ε := by
        have huK : ((u + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast (show u + 1 ≤ K by omega)
        have hp : 0 ≤ ((K : ℝ) + |Real.log a|) ^ r * ε := by positivity
        have he := mul_le_mul_of_nonneg_right huK hp
        rw [pow_succ]
        nlinarith [he]

end HadamardMultibase
