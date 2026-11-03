/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.NonLiouvilleSeparation
public import HadamardMultibase.LogIndependence

@[expose] public section

/-!
# Classical logarithmic forms: the elementary reduction

This module proves the
exact reduction from a polynomial bound on two real logarithmic forms to the
rotation separation needed by the sparse-representation proof.

`PolynomialLinearFormBound` is a proposition, not an axiom or a proved instance.
Proving it for the required logarithms is a separate mathematical obligation.
Qualitative nonvanishing, or an exponential-in-height lower bound, does not
discharge that obligation.
-/

namespace HadamardMultibase

/-- A polynomial lower bound with the elementary coefficient height
`k + |j| + 1`. The constants are chosen before either coefficient. -/
def PolynomialLinearFormBound (x y : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ ν : ℕ, ∀ k : ℕ, 0 < k → ∀ j : ℤ,
    (k : ℝ) * x - (j : ℝ) * y ≠ 0 →
      c ≤ |(k : ℝ) * x - (j : ℝ) * y| *
        ((k : ℝ) + |(j : ℝ)| + 1) ^ ν

theorem linear_form_eq_denominator_mul {x y : ℝ} (hy : y ≠ 0)
    (k : ℕ) (j : ℤ) :
    (k : ℝ) * x - (j : ℝ) * y = y * ((k : ℝ) * (x / y) - (j : ℝ)) := by
  field_simp

/-- Irrationality is used only to ensure that the form is not zero. -/
theorem linear_form_ne_zero_of_irrational {x y : ℝ} (hy : y ≠ 0)
    (hirr : Irrational (x / y)) {k : ℕ} (hk : 0 < k) (j : ℤ) :
    (k : ℝ) * x - (j : ℝ) * y ≠ 0 := by
  rw [linear_form_eq_denominator_mul hy]
  apply mul_ne_zero hy
  intro h
  have hkR : (k : ℝ) ≠ 0 := by positivity
  have heq : x / y = (j : ℝ) / (k : ℝ) := by
    apply (eq_div_iff hkR).mpr
    nlinarith
  exact hirr.ne_rational j k heq

/-- Near a rational approximation, numerator height is at most a fixed
multiple of denominator height. This is why coefficient-height bounds suffice. -/
theorem coefficient_height_le_of_small_error {α : ℝ} {k : ℕ} (hk : 0 < k)
    {j : ℤ} (hsmall : |(k : ℝ) * α - (j : ℝ)| < 1) :
    (k : ℝ) + |(j : ℝ)| + 1 ≤ (|α| + 3) * (k : ℝ) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have habs : |(j : ℝ)| ≤ |(k : ℝ) * α| + |(k : ℝ) * α - (j : ℝ)| := by
    calc |(j : ℝ)| = |(k : ℝ) * α - ((k : ℝ) * α - (j : ℝ))| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k)] at habs
  nlinarith

/-- The elementary transfer loses constants, but no asymptotic strength.
There is no invocation of a logarithm-ratio theorem in this proof. -/
theorem polynomialRotationSeparation_of_linearFormBound {x y : ℝ}
    (hy : y ≠ 0) (hirr : Irrational (x / y))
    (hbound : PolynomialLinearFormBound x y) :
    PolynomialRotationSeparation (x / y) := by
  obtain ⟨c, hc, ν, hbound⟩ := hbound
  let R : ℝ := |x / y| + 3
  have hR : 0 < R := by dsimp [R]; positivity
  have hden : 0 < |y| * R ^ ν := mul_pos (abs_pos.mpr hy) (pow_pos hR _)
  refine ⟨min 1 (c / (|y| * R ^ ν)), lt_min (by norm_num) (div_pos hc hden), ν, ?_⟩
  intro k hk j
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (1 : ℝ) ≤ (k : ℝ) ^ ν := one_le_pow₀ hk1
  by_cases hlarge : 1 ≤ |(k : ℝ) * (x / y) - (j : ℝ)|
  · exact (min_le_left _ _).trans (one_le_mul_of_one_le_of_one_le hlarge hkp)
  have hheight := coefficient_height_le_of_small_error hk (lt_of_not_ge hlarge)
  have hform := hbound k hk j (linear_form_ne_zero_of_irrational hy hirr hk j)
  rw [linear_form_eq_denominator_mul hy, abs_mul] at hform
  have hscaled : c ≤ (|y| * R ^ ν) *
      (|(k : ℝ) * (x / y) - (j : ℝ)| * (k : ℝ) ^ ν) := by
    calc c ≤ |y| * |(k : ℝ) * (x / y) - (j : ℝ)| *
        ((k : ℝ) + |(j : ℝ)| + 1) ^ ν := hform
      _ ≤ |y| * |(k : ℝ) * (x / y) - (j : ℝ)| * (R * (k : ℝ)) ^ ν := by
        gcongr
      _ = _ := by rw [mul_pow]; ring
  exact (min_le_right _ _).trans ((div_le_iff₀ hden).mpr (by nlinarith [hscaled]))

/-- The logarithm-ratio non-Liouville endpoint follows once the classical
polynomial bound has actually been proved. This is intentionally conditional. -/
theorem not_liouville_of_linearFormBound {x y : ℝ} (hy : y ≠ 0)
    (hirr : Irrational (x / y)) (hbound : PolynomialLinearFormBound x y) :
    ¬Liouville (x / y) :=
  (polynomialRotationSeparation_of_linearFormBound hy hirr hbound).not_liouville

end HadamardMultibase
