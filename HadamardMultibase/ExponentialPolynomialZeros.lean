/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import HadamardMultibase.ExponentialPolynomialDegree
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic

@[expose] public section

/-!
# Ordered zeros under differentiation

Rolle's theorem produces an ordered family of zeros of the derivative, one
in each gap between consecutive zeros. Applying it after an exponential
change of weight gives the corresponding step for the operator D - a.
Degree descent then gives the complete real exponential-polynomial zero count.
-/

namespace HadamardMultibase

theorem exists_ordered_derivative_zeros {n : ℕ} {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : ∀ t, HasDerivAt f (g t) t)
    (x : Fin (n + 1) → ℝ) (hx : StrictMono x) (hz : ∀ i, f (x i) = 0) :
    ∃ y : Fin n → ℝ, StrictMono y ∧
      (∀ i, x i.castSucc < y i ∧ y i < x i.succ) ∧ (∀ i, g (y i) = 0) := by
  have hgap (i : Fin n) : ∃ t, t ∈ Set.Ioo (x i.castSucc) (x i.succ) ∧ g t = 0 := by
    apply exists_hasDerivAt_eq_zero
    · exact hx (by simp)
    · exact hf.continuousOn
    · rw [hz, hz]
    · intro t _; exact hg t
  choose y hy hgy using hgap
  refine ⟨y, ?_, hy, hgy⟩
  intro i j hij
  have hindices : i.succ ≤ j.castSucc := by
    change i.val + 1 ≤ j.val
    exact hij
  exact (hy i).2.trans_le ((hx.monotone hindices).trans (hy j).1.le)

theorem hasDerivAt_exp_weight (a : ℝ) {f : ℝ → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) :
    HasDerivAt (fun x => Real.exp (-a * x) * f x)
      (Real.exp (-a * t) * (deriv f t - a * f t)) t := by
  have he := (Real.hasDerivAt_exp (-a * t)).comp t ((hasDerivAt_id t).const_mul (-a))
  convert he.mul hf.hasDerivAt using 1
  · rfl
  · dsimp [Function.comp_def]
    ring

theorem exists_ordered_expDifferential_zeros {n : ℕ} (a : ℝ) {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hz : ∀ i, f (x i) = 0) :
    ∃ y : Fin n → ℝ, StrictMono y ∧
      (∀ i, x i.castSucc < y i ∧ y i < x i.succ) ∧
      (∀ i, deriv f (y i) - a * f (y i) = 0) := by
  have hfc := hf.continuous
  have hw : Continuous (fun t => Real.exp (-a * t) * f t) := by fun_prop
  obtain ⟨y, hy, hgap, hzero⟩ := exists_ordered_derivative_zeros hw
    (fun t => hasDerivAt_exp_weight a (hf t)) x hx (by intro i; rw [hz i, mul_zero])
  refine ⟨y, hy, hgap, ?_⟩
  intro i
  exact (mul_eq_zero.mp (hzero i)).resolve_left (Real.exp_ne_zero _)

open Polynomial

noncomputable def exponentialPolynomialEval {ι : Type*} [Fintype ι]
    (ω : ι → ℝ) (P : ι → ℝ[X]) (x : ℝ) : ℝ :=
  ∑ i, (P i).eval x * Real.exp (ω i * x)

theorem exponentialPolynomial_hasDerivAt {ι : Type*} [Fintype ι]
    (ω : ι → ℝ) (P : ι → ℝ[X]) (x : ℝ) :
    HasDerivAt (exponentialPolynomialEval ω P)
      (exponentialPolynomialEval ω (fun i => polynomialExpDifferential (ω i) (P i)) x) x := by
  classical
  have hi (i : ι) := (P i).hasDerivAt x |>.mul
    (((hasDerivAt_id x).const_mul (ω i)).exp)
  convert HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i) using 1
  · rfl
  · apply Finset.sum_congr rfl
    intro i _
    simp only [polynomialExpDifferential, eval_add, eval_mul, eval_C, id_eq]
    ring

theorem exponentialPolynomial_differentiable {ι : Type*} [Fintype ι]
    (ω : ι → ℝ) (P : ι → ℝ[X]) : Differentiable ℝ (exponentialPolynomialEval ω P) :=
  fun x => (exponentialPolynomial_hasDerivAt ω P x).differentiableAt

theorem exponentialPolynomial_expDifferential_eval {ι : Type*} [Fintype ι]
    (ω : ι → ℝ) (P : ι → ℝ[X]) (a x : ℝ) :
    deriv (exponentialPolynomialEval ω P) x - a * exponentialPolynomialEval ω P x =
      exponentialPolynomialEval ω (fun i => polynomialExpDifferential (ω i - a) (P i)) x := by
  classical
  rw [(exponentialPolynomial_hasDerivAt ω P x).deriv]
  simp only [exponentialPolynomialEval, polynomialExpDifferential, eval_add, eval_mul, eval_C]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A family of polynomial coefficients at distinct real frequencies is zero
if its exponential sum has as many ordered zeros as its total dimension.
The proof uses weighted Rolle and induction on that dimension. -/
theorem exponentialPolynomial_eq_zero_of_ordered_zeros {ι : Type*} [Fintype ι]
    (ω : ι → ℝ) (hω : Function.Injective ω) (P : ι → ℝ[X])
    (x : Fin (exponentialPolynomialDimension P) → ℝ) (hx : StrictMono x)
    (hz : ∀ k, exponentialPolynomialEval ω P (x k) = 0) : ∀ i, P i = 0 := by
  classical
  by_cases hp : ∀ i, P i = 0
  · exact hp
  push Not at hp
  obtain ⟨j, hj⟩ := hp
  let Q : ι → ℝ[X] := fun i => polynomialExpDifferential (ω i - ω j) (P i)
  have hdim : exponentialPolynomialDimension Q < exponentialPolynomialDimension P :=
    exponentialPolynomialDimension_descent ω P j hj
  have hcount : exponentialPolynomialDimension Q + 1 ≤ exponentialPolynomialDimension P := hdim
  let xx : Fin (exponentialPolynomialDimension Q + 1) → ℝ := fun k => x (Fin.castLE hcount k)
  have hxx : StrictMono xx := by intro k l hkl; exact hx hkl
  obtain ⟨y, hy, _, hzero⟩ := exists_ordered_expDifferential_zeros (ω j)
    (exponentialPolynomial_differentiable ω P) xx hxx (fun k => hz (Fin.castLE hcount k))
  have hyzero : ∀ k, exponentialPolynomialEval ω Q (y k) = 0 := by
    intro k
    rw [← exponentialPolynomial_expDifferential_eval]
    exact hzero k
  have hQ : ∀ i, Q i = 0 :=
    exponentialPolynomial_eq_zero_of_ordered_zeros ω hω Q y hy hyzero
  have hothers (i : ι) (hi : i ≠ j) : P i = 0 := by
    apply (polynomialExpDifferential_eq_zero_iff (sub_ne_zero.mpr (hω.ne hi)) (P i)).mp
    exact hQ i
  have hd : (P j).derivative = 0 := by simpa [Q] using hQ j
  have hc := eq_C_of_derivative_eq_zero hd
  have hpos : 0 < exponentialPolynomialDimension P := lt_of_le_of_lt (Nat.zero_le _) hdim
  have hnode := hz ⟨0, hpos⟩
  have hsingle : exponentialPolynomialEval ω P (x ⟨0, hpos⟩) =
      (P j).eval (x ⟨0, hpos⟩) * Real.exp (ω j * x ⟨0, hpos⟩) := by
    apply Finset.sum_eq_single j
    · intro i _ hi
      rw [hothers i hi, eval_zero, zero_mul]
    · simp
  rw [hsingle, hc, eval_C] at hnode
  have hcoeff : (P j).coeff 0 = 0 :=
    (mul_eq_zero.mp hnode).resolve_right (Real.exp_ne_zero _)
  exact False.elim (hj (by rw [hc, hcoeff, C_0]))
termination_by exponentialPolynomialDimension P

/-- The number of distinct real zeros is strictly smaller than the sum of
one plus the degrees of the nonzero polynomial coefficients. -/
theorem exponentialPolynomial_ordered_zero_bound {ι : Type*} [Fintype ι]
    (ω : ι → ℝ) (hω : Function.Injective ω) (P : ι → ℝ[X])
    (hP : ∃ i, P i ≠ 0) {N : ℕ} (x : Fin N → ℝ) (hx : StrictMono x)
    (hz : ∀ k, exponentialPolynomialEval ω P (x k) = 0) :
    N < exponentialPolynomialDimension P := by
  by_contra h
  have hn : exponentialPolynomialDimension P ≤ N := Nat.le_of_not_gt h
  have heq := exponentialPolynomial_eq_zero_of_ordered_zeros ω hω P
    (fun k => x (Fin.castLE hn k)) (by intro i j hij; exact hx hij)
    (fun k => hz (Fin.castLE hn k))
  obtain ⟨i, hi⟩ := hP
  exact hi (heq i)

theorem exponentialPolynomial_finset_zero_bound {ι : Type*} [Fintype ι]
    (ω : ι → ℝ) (hω : Function.Injective ω) (P : ι → ℝ[X])
    (hP : ∃ i, P i ≠ 0) (S : Finset ℝ)
    (hS : ∀ x ∈ S, exponentialPolynomialEval ω P x = 0) :
    S.card < exponentialPolynomialDimension P := by
  exact exponentialPolynomial_ordered_zero_bound ω hω P hP
    (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).strictMono
    (fun i => hS _ (S.orderEmbOfFin_mem rfl i))

end HadamardMultibase
