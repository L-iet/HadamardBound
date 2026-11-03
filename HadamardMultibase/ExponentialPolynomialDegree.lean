/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Tactic

@[expose] public section

/-! # Degree descent for real exponential polynomials

The operator D-a sends P(X) exp(b X) to
(P'(X) + (b-a)P(X)) exp(b X). It decreases the polynomial dimension
at b=a and cannot increase it at any other frequency.
-/

namespace HadamardMultibase

open Polynomial

noncomputable def polynomialDimension (P : ℝ[X]) : ℕ :=
  if P = 0 then 0 else P.natDegree + 1

@[simp] theorem polynomialDimension_zero : polynomialDimension 0 = 0 := by
  simp [polynomialDimension]

theorem polynomialDimension_pos_iff (P : ℝ[X]) :
    0 < polynomialDimension P ↔ P ≠ 0 := by
  by_cases h : P = 0 <;> simp [polynomialDimension, h]

theorem polynomialDimension_eq_zero_iff (P : ℝ[X]) :
    polynomialDimension P = 0 ↔ P = 0 := by
  by_cases h : P = 0 <;> simp [polynomialDimension, h]

theorem polynomialDimension_derivative_lt {P : ℝ[X]} (hP : P ≠ 0) :
    polynomialDimension P.derivative < polynomialDimension P := by
  by_cases hd : P.derivative = 0
  · simp [polynomialDimension, hP, hd]
  · simp only [polynomialDimension, ite_eq_right hP, ite_eq_right hd]
    have hn : P.natDegree ≠ 0 := Polynomial.derivative_ne_zero.mp hd
    exact Nat.add_lt_add_right (natDegree_derivative_lt hn) 1

noncomputable def polynomialExpDifferential (c : ℝ) (P : ℝ[X]) : ℝ[X] :=
  P.derivative + C c * P

@[simp] theorem polynomialExpDifferential_zero (c : ℝ) :
    polynomialExpDifferential c 0 = 0 := by
  simp [polynomialExpDifferential]

@[simp] theorem polynomialExpDifferential_zero_frequency (P : ℝ[X]) :
    polynomialExpDifferential 0 P = P.derivative := by
  simp [polynomialExpDifferential]

theorem polynomialDimension_expDifferential_le (c : ℝ) (P : ℝ[X]) :
    polynomialDimension (polynomialExpDifferential c P) ≤ polynomialDimension P := by
  by_cases hP : P = 0
  · simp [hP]
  by_cases hQ : polynomialExpDifferential c P = 0
  · simp [polynomialDimension, hP, hQ]
  simp only [polynomialDimension, ite_eq_right hP, ite_eq_right hQ]
  apply Nat.add_le_add_right
  exact natDegree_add_le_of_degree_le (natDegree_derivative_le P |>.trans (Nat.sub_le _ _))
    (natDegree_C_mul_le c P)

theorem polynomialExpDifferential_eq_zero_iff {c : ℝ} (hc : c ≠ 0) (P : ℝ[X]) :
    polynomialExpDifferential c P = 0 ↔ P = 0 := by
  refine ⟨?_, fun h => by simp [h]⟩
  intro h
  by_contra hP
  have heq : P.derivative = -(C c * P) := by
    exact eq_neg_of_add_eq_zero_left h
  have hdeg := degree_derivative_lt hP
  rw [heq, degree_neg, degree_C_mul hc] at hdeg
  exact (lt_irrefl _ hdeg)

noncomputable def exponentialPolynomialDimension {ι : Type*} [Fintype ι]
    (P : ι → ℝ[X]) : ℕ := ∑ i, polynomialDimension (P i)

theorem exponentialPolynomialDimension_eq_zero_iff {ι : Type*} [Fintype ι]
    (P : ι → ℝ[X]) : exponentialPolynomialDimension P = 0 ↔ ∀ i, P i = 0 := by
  classical
  simp [exponentialPolynomialDimension, Finset.sum_eq_zero_iff,
    polynomialDimension_eq_zero_iff]

theorem exponentialPolynomialDimension_descent {ι : Type*} [Fintype ι]
    (ω : ι → ℝ) (P : ι → ℝ[X]) (j : ι) (hj : P j ≠ 0) :
    exponentialPolynomialDimension (fun i => polynomialExpDifferential (ω i - ω j) (P i)) <
      exponentialPolynomialDimension P := by
  classical
  apply Finset.sum_lt_sum
  · intro i _
    exact polynomialDimension_expDifferential_le _ _
  · refine ⟨j, Finset.mem_univ j, ?_⟩
    simpa using polynomialDimension_derivative_lt hj

end HadamardMultibase
