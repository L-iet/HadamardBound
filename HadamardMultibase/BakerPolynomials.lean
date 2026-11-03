/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Binomial
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.Tactic

@[expose] public section

/-!
# Integer-valued auxiliary polynomials

The ordinary binomial polynomial is `Δ_n(X) = (X+1)⋯(X+n)/n!`.
For a positive block size `h`, write a degree index `a = qh+r` and use
`Δ_h(X)^q Δ_r(X)`. This separates the degree from the denominator block size,
as in the classical auxiliary-polynomial approach to logarithmic forms.

All results in this module are proved from mathlib. No transcendence estimate
is imported.
-/

namespace HadamardMultibase

open Polynomial

noncomputable def bakerDelta (n : ℕ) : ℚ[X] :=
  Ring.multichoose (X + 1 : ℚ[X]) n

@[simp] theorem bakerDelta_zero : bakerDelta 0 = 1 := by
  simp [bakerDelta]

@[simp] theorem bakerDelta_one : bakerDelta 1 = X + 1 := by
  simp [bakerDelta]

theorem bakerDelta_comp (n : ℕ) (P : ℚ[X]) :
    (bakerDelta n).comp P = Ring.multichoose (P + 1) n := by
  simpa [bakerDelta] using Ring.map_multichoose (compRingHom P) (X + 1) n

theorem bakerDelta_eval (n : ℕ) (z : ℚ) :
    (bakerDelta n).eval z = Ring.multichoose (z + 1) n := by
  simpa [bakerDelta] using Ring.map_multichoose (evalRingHom z) (X + 1) n

theorem bakerDelta_pascal (n : ℕ) (P : ℚ[X]) :
    (bakerDelta (n + 1)).comp (P + 1) =
      (bakerDelta (n + 1)).comp P + (bakerDelta n).comp (P + 1) := by
  simp only [bakerDelta_comp]
  exact Ring.multichoose_succ_succ (P + 1) n

/-- Integer values are obtained without clearing a factorial-sized denominator. -/
theorem bakerDelta_eval_int (n : ℕ) (z : ℤ) :
    (bakerDelta n).eval (z : ℚ) = (Ring.multichoose (z + 1) n : ℤ) := by
  rw [bakerDelta_eval]
  simpa using (Ring.map_multichoose (Int.castRingHom ℚ) (z + 1) n).symm

theorem bakerDelta_integerValued (n : ℕ) (z : ℤ) :
    ∃ v : ℤ, (bakerDelta n).eval (z : ℚ) = (v : ℚ) :=
  ⟨Ring.multichoose (z + 1) n, bakerDelta_eval_int n z⟩

theorem bakerDelta_nsmul_succ (n : ℕ) :
    (n + 1) • bakerDelta (n + 1) = bakerDelta n * (X + (n + 1 : ℚ[X])) := by
  apply nsmul_right_injective (Nat.factorial_ne_zero n)
  calc n.factorial • ((n + 1) • bakerDelta (n + 1))
      = (n + 1).factorial • bakerDelta (n + 1) := by
        rw [smul_smul, Nat.factorial, Nat.mul_comm n.factorial]
    _ = (ascPochhammer ℕ (n + 1)).smeval (X + 1 : ℚ[X]) :=
      Ring.factorial_nsmul_multichoose_eq_ascPochhammer _ _
    _ = (ascPochhammer ℕ n).smeval (X + 1 : ℚ[X]) * (X + (n + 1 : ℚ[X])) := by
      rw [ascPochhammer_succ_right, smeval_mul]
      simp only [smeval_add, smeval_X, smeval_natCast]
      congr 1
      ring
    _ = n.factorial • (bakerDelta n * (X + (n + 1 : ℚ[X]))) := by
      rw [← Ring.factorial_nsmul_multichoose_eq_ascPochhammer]
      simp only [nsmul_eq_mul, mul_assoc, bakerDelta]

theorem bakerDelta_succ (n : ℕ) :
    bakerDelta (n + 1) = bakerDelta n * (C ((n + 1 : ℚ)⁻¹) * X + 1) := by
  have hn : (n + 1 : ℚ) ≠ 0 := by positivity
  have hlin : (n + 1 : ℚ[X]) * (C ((n + 1 : ℚ)⁻¹) * X + 1) =
      X + (n + 1 : ℚ[X]) := by
    have hc : (n + 1 : ℚ[X]) * C ((n + 1 : ℚ)⁻¹) = 1 := by
      simpa using congrArg (C : ℚ →+* ℚ[X]) (mul_inv_cancel₀ hn)
    linear_combination X * hc
  apply nsmul_right_injective (Nat.succ_ne_zero n)
  change (n + 1) • bakerDelta (n + 1) =
    (n + 1) • (bakerDelta n * (C ((n + 1 : ℚ)⁻¹) * X + 1))
  rw [bakerDelta_nsmul_succ, nsmul_eq_mul]
  rw [mul_left_comm, Nat.cast_add, Nat.cast_one, hlin]

theorem bakerDelta_ne_zero (n : ℕ) : bakerDelta n ≠ 0 := by
  intro h
  have he := congrArg (eval (0 : ℚ)) h
  have hone : (bakerDelta n).eval 0 = 1 := by
    rw [bakerDelta_eval]
    simp
  rw [hone, eval_zero] at he
  exact one_ne_zero he

theorem bakerDelta_natDegree (n : ℕ) : (bakerDelta n).natDegree = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hd : (C ((n + 1 : ℚ)⁻¹) * X + 1 : ℚ[X]).natDegree = 1 := by
      rw [← C_1, natDegree_add_C, natDegree_C_mul_X _ (inv_ne_zero (by positivity))]
    have hn : (C ((n + 1 : ℚ)⁻¹) * X + 1 : ℚ[X]) ≠ 0 := by
      exact ne_zero_of_natDegree_gt (show 0 <
        (C ((n + 1 : ℚ)⁻¹) * X + 1 : ℚ[X]).natDegree by rw [hd]; decide)
    rw [bakerDelta_succ, natDegree_mul (bakerDelta_ne_zero n) hn, ih, hd]

/-- Degree-indexed block polynomials. The useful parameter regime is `0 < h`;
the definition itself is total, using the natural quotient and remainder. -/
noncomputable def bakerBlock (h a : ℕ) : ℚ[X] :=
  bakerDelta h ^ (a / h) * bakerDelta (a % h)

@[simp] theorem bakerBlock_zero (h : ℕ) : bakerBlock h 0 = 1 := by
  simp [bakerBlock]

theorem bakerBlock_of_lt {h a : ℕ} (ha : a < h) :
    bakerBlock h a = bakerDelta a := by
  simp [bakerBlock, Nat.div_eq_of_lt ha, Nat.mod_eq_of_lt ha]

theorem bakerBlock_integerValued (h a : ℕ) (z : ℤ) :
    ∃ v : ℤ, (bakerBlock h a).eval (z : ℚ) = (v : ℚ) := by
  obtain ⟨u, hu⟩ := bakerDelta_integerValued h z
  obtain ⟨v, hv⟩ := bakerDelta_integerValued (a % h) z
  refine ⟨u ^ (a / h) * v, ?_⟩
  simp only [bakerBlock, eval_mul, eval_pow, hu, hv, Int.cast_mul, Int.cast_pow]

theorem bakerBlock_ne_zero (h a : ℕ) : bakerBlock h a ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (bakerDelta_ne_zero _)) (bakerDelta_ne_zero _)

theorem bakerBlock_natDegree (h a : ℕ) :
    (bakerBlock h a).natDegree = a := by
  rw [bakerBlock, natDegree_mul (pow_ne_zero _ (bakerDelta_ne_zero _))
    (bakerDelta_ne_zero _), natDegree_pow, bakerDelta_natDegree, bakerDelta_natDegree]
  simpa only [Nat.mul_comm] using Nat.div_add_mod a h

/-- The block family spans every finite degree range through Mathlib's
polynomial-sequence basis theorem. -/
noncomputable def bakerBlockSequence (h : ℕ) : Polynomial.Sequence ℚ where
  elems' := bakerBlock h
  degree_eq' a := by
    rw [degree_eq_natDegree (bakerBlock_ne_zero h a), bakerBlock_natDegree]

theorem bakerBlock_linearIndependent (h : ℕ) : LinearIndependent ℚ (bakerBlock h) := by
  exact (bakerBlockSequence h).linearIndependent

end HadamardMultibase
