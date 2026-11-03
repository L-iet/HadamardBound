module

public import HadamardMultibase.Turyn
public import HadamardMultibase.CraigenTransfer
public import HadamardMultibase.Gaps
public import HadamardMultibase.MultiBase

@[expose] public section

namespace HadamardMultibase

/-! User-facing results with the Golay-family and Craigen inputs discharged.
The remaining sparse-representation hypothesis is visible in every main result. -/

/-- Every odd multiplier admits a Hadamard order after scaling by a power of two. -/
theorem odd_hasExponent {p : ℕ} (hp : Odd p) : HasExponent p :=
  hasExponent_odd craigenTransfer hp

theorem main_bound (hS : SparseRepresentationBound) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ p : ℕ, N ≤ p → Odd p →
      ∃ t : ℕ, HadamardOrder (2 ^ t * p) ∧ (t : ℝ) ≤ C * logScale p :=
  main_bound_of_inputs golayFamily craigenTransfer hS

theorem tau_bound (hS : SparseRepresentationBound) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ p : ℕ, N ≤ p → Odd p →
      ∀ h : HasExponent p, (tau p h : ℝ) ≤ C * logScale p :=
  tau_bound_of_inputs golayFamily craigenTransfer hS

theorem quantitative_gap_bound (hS : SparseRepresentationBound) :
    ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      ∃ d : ℕ, HadamardGapBound x d ∧ (d : ℝ) ≤ Real.exp (D * logScale x) :=
  quantitative_gap_bound_of_inputs golayFamily craigenTransfer hS

theorem subpolynomial_gap_bound (hS : SparseRepresentationBound)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      ∃ d : ℕ, HadamardGapBound x d ∧ (d : ℝ) ≤ (x : ℝ) ^ ε :=
  subpolynomial_gap_bound_of_inputs golayFamily craigenTransfer hS hε

end HadamardMultibase

