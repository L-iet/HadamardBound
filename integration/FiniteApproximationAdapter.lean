module

public import HadamardMultibase.NonLiouvilleSeparation
public import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
public import QuadraticPi.ExponentConverse

@[expose] public section

namespace HadamardMultibase

open Filter

/-- Connect the supplement's finite set of reduced good fractions to
mathlib's Liouville predicate. This uses only its elementary exponent modules. -/
theorem not_liouville_of_finite_good {x : ℝ} (hx : Irrational x)
    (hfinite : (QuadraticPi.GoodRationalApproximations x 4).Finite) : ¬Liouville x := by
  intro hL
  apply hfinite.not_infinite
  apply QuadraticPi.infinite_good_of_unbounded_denominator_approximations hx (by norm_num)
  intro N
  obtain ⟨q, hq, p, _, herr⟩ :=
    ((eventually_ge_atTop (max N 2)).and_frequently (hL.frequently_exists_num 4)).exists
  refine ⟨p, q, (le_max_left _ _).trans hq, ?_⟩
  rw [Real.rpow_neg (Nat.cast_nonneg q), Real.rpow_ofNat]
  simpa only [one_div] using herr

end HadamardMultibase
