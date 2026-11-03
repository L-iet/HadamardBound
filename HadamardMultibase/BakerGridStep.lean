/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerRectangularJets

@[expose] public section

/-! # One analytic extrapolation step for the mixed auxiliary family -/
namespace HadamardMultibase
open Filter

theorem eventually_bakerMixed_grid_step {k s t w : ℕ}
    (hk : 0 < k) (hs : 0 < s) (hst : s ≤ t) (htw : t < w)
    (a : ℕ) (A E : ℝ) :
    ∀ᶠ h : ℕ in atTop, ∀ n : ℕ, ∀ β : ℝ, ∀ c : Fin n → ℤ,
      ∀ d lam mu : Fin n → ℕ,
      (∀ u v : ℕ, u < 4 * k → v < 4 * k → ∀ l : ℕ,
        1 ≤ l → l ≤ s * h →
        ‖bakerMixedComplexValue h u v β a c d lam mu l‖ ≤ Real.exp (-E * h)) →
      (∀ u v : ℕ, u < k → v < k →
        ∀ z ∈ Metric.sphere 0 ((w * h : ℕ) : ℝ),
          ‖bakerMixedComplexValue h u v β a c d lam mu z‖ ≤ Real.exp (A * h)) →
      ∀ u v : ℕ, u < k → v < k → ∀ z : ℂ, ‖z‖ ≤ ((t * h : ℕ) : ℝ) →
      ‖bakerMixedComplexValue h u v β a c d lam mu z‖ ≤
        Real.exp ((-E + 2 + 4 * (k : ℝ) * ((t : ℝ) + s)) * h) +
          Real.exp ((A + ((2 * k * s : ℕ) : ℝ) *
            Real.log (((t : ℝ) + s) / ((w : ℝ) - t)) + 1) * h) := by
  filter_upwards [eventually_bakerMixed_rectangular_jets hk a,
    eventually_baker_grid_extrapolation_exp (k := 2 * k) (by omega) hs hst htw A (E - 1)]
    with h hjets hgrid
  intro n β c d lam mu hvalues hboundary u v hu hv z hz
  have hf : DiffContOnCl ℂ (bakerMixedComplexValue h u v β a c d lam mu)
      (Metric.ball 0 ((w * h : ℕ) : ℝ)) :=
    (bakerMixedComplex_differentiable h u v β a c d lam mu).diffContOnCl
  have hj : ∀ l : ℕ, 1 ≤ l → l ≤ s * h → ∀ r : ℕ, r < 2 * k →
      ‖iteratedDeriv r (bakerMixedComplexValue h u v β a c d lam mu) l‖ /
        (r.factorial : ℝ) ≤ Real.exp (-(E - 1) * h) := by
    intro l hl hlmax r hr
    have he := hjets n β c d lam mu (l : ℂ) E
      (fun i j hi hj => hvalues i j hi hj l hl hlmax) u v r hu hv hr
    convert he using 1; congr 1; ring
  have hb := hgrid (bakerMixedComplexValue h u v β a c d lam mu)
    hf (hboundary u v hu hv) hj z hz
  convert hb using 1; push_cast; congr 2; ring

end HadamardMultibase
