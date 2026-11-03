module

public import HadamardMultibase.ApproximationFromSeparation
public import HadamardMultibase.CoveringLower

@[expose] public section

namespace HadamardMultibase

open Filter

theorem DistinctSum.sumOfAtMost {S : Set ℕ} {n : ℕ} {s : Finset ℕ}
    (hs : DistinctSum S n s) : SumOfAtMost S s.card n := by
  classical
  exact ⟨s.toList, by simp, by simpa using hs.1, by simpa using hs.2⟩

/-- The general covering lower bound reduced to polynomial separation for
one pair of generators. Representation and positivity remain explicit. -/
theorem coveringNumber_lower_of_separation {S : Set ℕ} {p q : ℕ}
    (hpos : ∀ a ∈ S, 0 < a)
    (hrep : ∀ n : ℕ, ∃ s : Finset ℕ, DistinctSum S n s)
    (hmissing : ∀ m, HasMissing S m)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hmem : ∀ l m : ℕ, p ^ l * q ^ m ∈ S)
    (hsep : PolynomialRotationSeparation (Real.log (q : ℝ) / Real.log (p : ℝ))) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      Real.exp (c * m * Real.log m) ≤ (coveringNumber S m (hmissing m) : ℝ) := by
  have h1 : 1 ∈ S := by simpa using hmem 0 0
  obtain ⟨K, hK, hbound⟩ := sparse_bound_of_separation hpos hrep hp hq hmem hsep
  apply coveringNumber_lower_of_representation h1 hmissing hK
  refine ⟨3, ?_⟩
  intro n hn
  obtain ⟨s, hs, hcard⟩ := hbound n (by omega)
  exact ⟨s.card, hs.sumOfAtMost, hcard⟩

end HadamardMultibase
