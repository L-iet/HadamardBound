/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerMixedDerivatives
public import HadamardMultibase.BakerExponentialEstimates

@[expose] public section

/-! # Derivative data from a rectangle of mixed values -/
namespace HadamardMultibase
open Filter

theorem bakerMixed_rectangular_jet_bound {n k : ℕ} (hk : 0 < k)
    (h : ℕ) (β : ℝ) (a : ℕ) (c : Fin n → ℤ) (d lam mu : Fin n → ℕ)
    (z : ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hvalues : ∀ i j : ℕ, i < 4 * k → j < 4 * k →
      ‖bakerMixedComplexValue h i j β a c d lam mu z‖ ≤ ε)
    (u v r : ℕ) (hu : u < k) (hv : v < k) (hr : r < 2 * k) :
    ‖iteratedDeriv r (bakerMixedComplexValue h u v β a c d lam mu) z‖ /
        (r.factorial : ℝ) ≤
      ((4 * k : ℕ) + |Real.log a|) ^ (4 * k) * ε := by
  have htri : ∀ i j : ℕ, i + j ≤ 4 * k - 1 →
      ‖bakerMixedComplexValue h i j β a c d lam mu z‖ ≤ ε := by
    intro i j hij
    exact hvalues i j (by omega) (by omega)
  have hb := bakerMixedComplex_iteratedDeriv_bound h β a c d lam mu z hε htri
    r u v (by omega)
  have hbase : (1 : ℝ) ≤ ((4 * k : ℕ) : ℝ) + |Real.log a| := by
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast
    linarith [abs_nonneg (Real.log (a : ℝ))]
  have hmono : (((4 * k - 1 : ℕ) : ℝ) + |Real.log a|) ^ r ≤
      (((4 * k : ℕ) : ℝ) + |Real.log a|) ^ (4 * k) := by
    apply (pow_le_pow_left₀ (by positivity) (show
      (((4 * k - 1 : ℕ) : ℝ) + |Real.log a|) ≤
        (((4 * k : ℕ) : ℝ) + |Real.log a|) by
          gcongr; exact Nat.sub_le _ _) r).trans
    exact pow_le_pow_right₀ hbase (by omega)
  have hfac : (1 : ℝ) ≤ r.factorial := by exact_mod_cast Nat.factorial_pos r
  calc _ ≤ ‖iteratedDeriv r (bakerMixedComplexValue h u v β a c d lam mu) z‖ :=
      div_le_self (norm_nonneg _) hfac
    _ ≤ _ := hb.trans (mul_le_mul_of_nonneg_right hmono hε)

theorem eventually_bakerMixed_rectangular_jets {k : ℕ} (hk : 0 < k) (a : ℕ) :
    ∀ᶠ h : ℕ in atTop, ∀ n : ℕ, ∀ β : ℝ, ∀ c : Fin n → ℤ,
      ∀ d lam mu : Fin n → ℕ, ∀ z : ℂ, ∀ E : ℝ,
      (∀ i j : ℕ, i < 4 * k → j < 4 * k →
        ‖bakerMixedComplexValue h i j β a c d lam mu z‖ ≤ Real.exp (-E * h)) →
      ∀ u v r : ℕ, u < k → v < k → r < 2 * k →
      ‖iteratedDeriv r (bakerMixedComplexValue h u v β a c d lam mu) z‖ /
        (r.factorial : ℝ) ≤ Real.exp ((1 - E) * h) := by
  filter_upwards [eventually_nat_const_mul_pow_le_exp
    ((((4 * k : ℕ) : ℝ) + |Real.log a|) ^ (4 * k)) 0
      (show (0 : ℝ) < 1 by norm_num)] with h hh
  intro n β c d lam mu z E hvalues u v r hu hv hr
  have hb := bakerMixed_rectangular_jet_bound hk h β a c d lam mu z
    (Real.exp_pos _).le hvalues u v r hu hv hr
  apply hb.trans
  calc
    _ ≤ Real.exp (h : ℝ) * Real.exp (-E * h) := by
      gcongr
      simpa using hh
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end HadamardMultibase
