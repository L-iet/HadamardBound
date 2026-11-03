/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerPolynomials
public import HadamardMultibase.ExponentialPolynomialZeros
public import HadamardMultibase.LogIndependence
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

/-! # Nonvanishing and a zero bound for block auxiliary functions

A nonzero coefficient array gives a nonzero polynomial at some frequency,
because the block polynomials have successive degrees. The real zero-count
theorem therefore applies with an explicit dimension bound.
-/

namespace HadamardMultibase

open Polynomial

noncomputable def bakerRealBlockSequence (h : ℕ) : Polynomial.Sequence ℝ where
  elems' d := (bakerBlock h d).map (Rat.castHom ℝ)
  degree_eq' d := by
    rw [degree_map, degree_eq_natDegree (bakerBlock_ne_zero h d), bakerBlock_natDegree]

theorem bakerRealBlock_linearIndependent (h : ℕ) :
    LinearIndependent ℝ (fun d => (bakerBlock h d).map (Rat.castHom ℝ)) :=
  (bakerRealBlockSequence h).linearIndependent

noncomputable def bakerAuxiliaryPolynomial {D : ℕ} (h : ℕ) (c : Fin D → ℝ) : ℝ[X] :=
  ∑ d, c d • (bakerBlock h d.val).map (Rat.castHom ℝ)

theorem bakerAuxiliaryPolynomial_eq_zero_iff {D : ℕ} (h : ℕ) (c : Fin D → ℝ) :
    bakerAuxiliaryPolynomial h c = 0 ↔ ∀ d, c d = 0 := by
  classical
  refine ⟨?_, ?_⟩
  · exact (Fintype.linearIndependent_iff.mp
      ((bakerRealBlock_linearIndependent h).comp Fin.val Fin.val_injective)) c
  · intro hc
    simp [bakerAuxiliaryPolynomial, hc]

theorem bakerAuxiliaryPolynomial_dimension_le {D : ℕ} (h : ℕ) (c : Fin D → ℝ) :
    polynomialDimension (bakerAuxiliaryPolynomial h c) ≤ D := by
  classical
  by_cases hD : D = 0
  · subst D
    simp [bakerAuxiliaryPolynomial]
  by_cases hp : bakerAuxiliaryPolynomial h c = 0
  · simp [hp]
  have hdeg : (bakerAuxiliaryPolynomial h c).natDegree ≤ D - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro d _
    apply (natDegree_smul_le _ _).trans
    rw [natDegree_map, bakerBlock_natDegree]
    exact Nat.le_sub_one_of_lt d.isLt
  simp only [polynomialDimension, ite_eq_right hp]
  omega

theorem bakerAuxiliary_nonzero_polynomial {ι : Type*} [Fintype ι] {D : ℕ}
    (h : ℕ) (c : ι → Fin D → ℝ) (hc : ∃ i d, c i d ≠ 0) :
    ∃ i, bakerAuxiliaryPolynomial h (c i) ≠ 0 := by
  obtain ⟨i, d, hd⟩ := hc
  exact ⟨i, fun hp => hd ((bakerAuxiliaryPolynomial_eq_zero_iff h (c i)).mp hp d)⟩

theorem bakerAuxiliary_zero_bound {ι : Type*} [Fintype ι] {D : ℕ}
    (h : ℕ) (ω : ι → ℝ) (hω : Function.Injective ω)
    (c : ι → Fin D → ℝ) (hc : ∃ i d, c i d ≠ 0) (S : Finset ℝ)
    (hS : ∀ x ∈ S,
      exponentialPolynomialEval ω (fun i => bakerAuxiliaryPolynomial h (c i)) x = 0) :
    S.card < Fintype.card ι * D := by
  classical
  apply (exponentialPolynomial_finset_zero_bound ω hω _
    (bakerAuxiliary_nonzero_polynomial h c hc) S hS).trans_le
  calc exponentialPolynomialDimension (fun i => bakerAuxiliaryPolynomial h (c i))
      ≤ ∑ _i : ι, D := Finset.sum_le_sum (fun i _ => bakerAuxiliaryPolynomial_dimension_le h (c i))
    _ = _ := by simp

theorem irrational_frequency_injective {α β : ℝ} (hα : α ≠ 0)
    (hirr : Irrational (β / α)) :
    Function.Injective (fun e : ℕ × ℕ => (e.1 : ℝ) * α + (e.2 : ℝ) * β) := by
  intro e f heq
  change (e.1 : ℝ) * α + (e.2 : ℝ) * β = (f.1 : ℝ) * α + (f.2 : ℝ) * β at heq
  have hsecond : e.2 = f.2 := by
    by_contra hne
    have hden : ((e.2 : ℤ) - f.2 : ℤ) ≠ 0 := by omega
    have hdenR : ((e.2 : ℤ) - f.2 : ℝ) ≠ 0 := by exact_mod_cast hden
    apply hirr.ne_rational ((f.1 : ℤ) - e.1) ((e.2 : ℤ) - f.2)
    push_cast at hdenR ⊢
    apply (eq_div_iff hdenR).mpr
    apply (mul_right_cancel₀ hα)
    calc (β / α * ((e.2 : ℝ) - f.2)) * α = β * ((e.2 : ℝ) - f.2) := by field_simp
      _ = ((f.1 : ℝ) - e.1) * α := by nlinarith
  have hfirst : e.1 = f.1 := by
    have : ((e.1 : ℝ) - (f.1 : ℝ)) * α = 0 := by rw [hsecond] at heq; nlinarith
    have : (e.1 : ℝ) = (f.1 : ℝ) := sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hα)
    exact_mod_cast this
  exact Prod.ext hfirst hsecond

/-- A nonzero block auxiliary function cannot vanish at every positive integer
up to its dimension bound. This is the final zero-count contradiction used
after analytic extrapolation supplies a sufficiently long grid of zeros. -/
theorem bakerAuxiliary_integer_nonzero {ι : Type*} [Fintype ι] {D T : ℕ}
    (h : ℕ) (ω : ι → ℝ) (hω : Function.Injective ω)
    (c : ι → Fin D → ℝ) (hc : ∃ i d, c i d ≠ 0)
    (hT : Fintype.card ι * D ≤ T) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ T ∧
      exponentialPolynomialEval ω (fun i => bakerAuxiliaryPolynomial h (c i)) l ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hz (k : Fin T) :
      exponentialPolynomialEval ω (fun i => bakerAuxiliaryPolynomial h (c i)) (k.val + 1 : ℕ) = 0 :=
    hn (k.val + 1) (by omega) (by omega)
  have hcount := exponentialPolynomial_ordered_zero_bound ω hω _
    (bakerAuxiliary_nonzero_polynomial h c hc)
    (fun k : Fin T => ((k.val + 1 : ℕ) : ℝ))
    (by
      intro i j hij
      change (((i.val + 1 : ℕ) : ℝ)) < (((j.val + 1 : ℕ) : ℝ))
      exact Nat.cast_lt.mpr (by omega)) hz
  have hdim : exponentialPolynomialDimension (fun i => bakerAuxiliaryPolynomial h (c i)) ≤
      Fintype.card ι * D := by
    calc exponentialPolynomialDimension (fun i => bakerAuxiliaryPolynomial h (c i))
        ≤ ∑ _i : ι, D := Finset.sum_le_sum (fun i _ => bakerAuxiliaryPolynomial_dimension_le h (c i))
      _ = _ := by simp
  omega

end HadamardMultibase
