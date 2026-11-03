/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerComparisonGrowth
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

/-! # Perturbing logarithmic frequencies

At integer nodes, replacing the true logarithm ratio by p/q changes each
arithmetic comparison entry by an exponential factor. The error is bounded
explicitly in the coefficient height, entry bound and logarithmic defect.
-/

namespace HadamardMultibase

theorem log_frequency_exp_factor {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (β : ℝ) (lam mu l : ℕ) :
    Real.exp (((lam : ℝ) + (mu : ℝ) * β) * Real.log a * l) =
      (a : ℝ) ^ (lam * l) * (b : ℝ) ^ (mu * l) *
        Real.exp ((mu * l : ℕ) * (β * Real.log a - Real.log b)) := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have he : ((lam : ℝ) + (mu : ℝ) * β) * Real.log a * l =
      ((lam * l : ℕ) : ℝ) * Real.log a + ((mu * l : ℕ) : ℝ) * Real.log b +
        ((mu * l : ℕ) : ℝ) * (β * Real.log a - Real.log b) := by push_cast; ring
  rw [he, Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log haR, Real.exp_log hbR]

noncomputable def bakerMixedRealValue {n : ℕ} (h u v : ℕ) (β : ℝ) (a : ℕ)
    (c : Fin n → ℤ) (d lam mu : Fin n → ℕ) (x : ℝ) : ℝ :=
  ∑ j, (c j : ℝ) * (Polynomial.hasseDeriv u (bakerBlock h (d j))).eval₂ (Rat.castHom ℝ) x *
    ((lam j : ℝ) + (mu j : ℝ) * β) ^ v *
      Real.exp (((lam j : ℝ) + (mu j : ℝ) * β) * Real.log a * x)

theorem bakerMixedRealValue_at_integer {n : ℕ} {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h u v l q : ℕ) (p : ℤ) (c : Fin n → ℤ) (d lam mu : Fin n → ℕ) :
    bakerMixedRealValue h u v ((p : ℝ) / q) a c d lam mu l =
      ∑ j, (c j : ℝ) * ((bakerComparisonValue h (d j) u v l (lam j) (mu j) p q a b : ℚ) : ℝ) *
        Real.exp ((mu j * l : ℕ) * (((p : ℝ) / q) * Real.log a - Real.log b)) := by
  unfold bakerMixedRealValue
  apply Finset.sum_congr rfl
  intro j _
  rw [log_frequency_exp_factor ha hb]
  have heval : (Polynomial.hasseDeriv u (bakerBlock h (d j))).eval₂ (Rat.castHom ℝ) (l : ℝ) =
      (((Polynomial.hasseDeriv u (bakerBlock h (d j))).eval (l : ℚ) : ℚ) : ℝ) := by simp
  rw [heval]
  simp only [bakerComparisonValue, Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_intCast, mul_div_assoc]
  ring

theorem finite_exp_perturbation_bound {n : ℕ} (A t : Fin n → ℝ)
    {H T : ℝ} (hH : 0 ≤ H) (_hT : 0 ≤ T) (hT1 : T ≤ 1)
    (hA : ∀ j, |A j| ≤ H) (ht : ∀ j, |t j| ≤ T) :
    |(∑ j, A j * Real.exp (t j)) - ∑ j, A j| ≤ 2 * (n : ℝ) * H * T := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ j, (A j * Real.exp (t j) - A j)|
      ≤ ∑ j, |A j * Real.exp (t j) - A j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, 2 * H * T := by
      apply Finset.sum_le_sum
      intro j _
      have he : A j * Real.exp (t j) - A j = A j * (Real.exp (t j) - 1) := by ring
      rw [he, abs_mul]
      have hexp := Real.abs_exp_sub_one_le ((ht j).trans hT1)
      have hexp' : |Real.exp (t j) - 1| ≤ 2 * T := hexp.trans (by linarith [ht j])
      have hmul := mul_le_mul (hA j) hexp' (abs_nonneg _) hH
      nlinarith [hmul]
    _ = _ := by simp; ring

theorem bakerMixedRealValue_comparison_error {n : ℕ} {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h u v l q L : ℕ) (p : ℤ) (c : Fin n → ℤ) (d lam mu : Fin n → ℕ)
    (H B : ℝ) (hH : 0 ≤ H) (hB : 0 ≤ B) (hc : ∀ j, |(c j : ℝ)| ≤ H)
    (hentry : ∀ j, |((bakerComparisonValue h (d j) u v l (lam j) (mu j) p q a b : ℚ) : ℝ)| ≤ B)
    (hmu : ∀ j, mu j ≤ L)
    (hsmall : ((L * l : ℕ) : ℝ) * |((p : ℝ) / q) * Real.log a - Real.log b| ≤ 1) :
    |bakerMixedRealValue h u v ((p : ℝ) / q) a c d lam mu l -
      ∑ j, (c j : ℝ) * ((bakerComparisonValue h (d j) u v l (lam j) (mu j) p q a b : ℚ) : ℝ)| ≤
      2 * (n : ℝ) * H * B * ((L * l : ℕ) : ℝ) *
        |((p : ℝ) / q) * Real.log a - Real.log b| := by
  rw [bakerMixedRealValue_at_integer ha hb]
  let η := ((p : ℝ) / q) * Real.log a - Real.log b
  have hA (j) : |(c j : ℝ) *
      ((bakerComparisonValue h (d j) u v l (lam j) (mu j) p q a b : ℚ) : ℝ)| ≤ H * B := by
    rw [abs_mul]
    exact mul_le_mul (hc j) (hentry j) (abs_nonneg _) hH
  have ht (j) : |((mu j * l : ℕ) : ℝ) * η| ≤ ((L * l : ℕ) : ℝ) * |η| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.mul_le_mul_right l (hmu j)) (abs_nonneg _)
  have he := finite_exp_perturbation_bound
    (fun j => (c j : ℝ) * ((bakerComparisonValue h (d j) u v l (lam j) (mu j) p q a b : ℚ) : ℝ))
    (fun j => ((mu j * l : ℕ) : ℝ) * η) (mul_nonneg hH hB) (by positivity) hsmall hA ht
  simpa only [η, mul_assoc] using he

end HadamardMultibase
