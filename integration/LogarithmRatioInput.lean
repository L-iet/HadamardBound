module

public import HadamardMultibase.PowerMonoidRepresentation
public import HadamardMultibase.GeneralIndependence
public import integration.FiniteApproximationAdapter
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
public import QuadraticPi.RationalLogRatioTheorem
public import QuadraticPi.ExponentConverse

@[expose] public section

/-! Sparse representations and generator separation from the verified
rational-logarithm-ratio theorem in arXiv:2610.28079v1. The external endpoint
and all five adapters have passed local compilation and axiom audits. -/

namespace HadamardMultibase

open Filter

theorem not_liouville_log_ratio_of_irrational (a b : ℚ)
    (ha : 0 < (a : ℝ)) (hb : 0 < (b : ℝ)) (hlogb : Real.log (b : ℝ) ≠ 0)
    (hirr : Irrational (Real.log (a : ℝ) / Real.log (b : ℝ))) :
    ¬Liouville (Real.log (a : ℝ) / Real.log (b : ℝ)) := by
  apply not_liouville_of_finite_good hirr
  exact QuadraticPi.rationalLogRatio_finite_good a b ha hb hlogb
    (QuadraticPi.TwoLogCharacterCenters.noPowerRelation_of_irrational_log_ratio hlogb hirr)
    4 (by norm_num)

theorem not_liouville_log_ten_div_log_two : ¬Liouville (Real.log 10 / Real.log 2) := by
  have hlog₂ : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  simpa only [Rat.cast_ofNat] using not_liouville_log_ratio_of_irrational (10 : ℚ) (2 : ℚ)
    (by norm_num) (by norm_num) (by simpa using hlog₂) (by simpa using irrational_log_ten_div_log_two)

theorem sparseRepresentationBound : SparseRepresentationBound :=
  sparseRepresentationBound_of_not_liouville not_liouville_log_ten_div_log_two

theorem IndependentBases.log_ratio_separation {r : ℕ} {b : Fin r → ℕ}
    (hind : IndependentBases b) (hb : ∀ i, 2 ≤ b i)
    {i₀ i₁ : Fin r} (hne : i₀ ≠ i₁) :
    PolynomialRotationSeparation (Real.log (b i₁ : ℝ) / Real.log (b i₀ : ℝ)) := by
  have hirr := hind.irrational_log_ratio hb hne
  have hp : (0 : ℝ) < b i₀ := by exact_mod_cast (show 0 < b i₀ by have := hb i₀; omega)
  have hq : (0 : ℝ) < b i₁ := by exact_mod_cast (show 0 < b i₁ by have := hb i₁; omega)
  have hlogp : Real.log (b i₀ : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < b i₀ by have := hb i₀; omega))).ne'
  apply polynomialRotationSeparation_of_not_liouville hirr
  simpa only [Rat.cast_natCast] using not_liouville_log_ratio_of_irrational
    (b i₁ : ℚ) (b i₀ : ℚ) (by simpa using hq) (by simpa using hp)
    (by simpa using hlogp) (by simpa using hirr)

end HadamardMultibase
