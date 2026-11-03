module

public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!+# Independent statement surface

For all sufficiently large odd natural numbers p, there is a real Hadamard
matrix of order 2^t*p with t <= C*log(p)/log(log(p)), for one absolute C > 0.
The parameter p ranges over all odd integers, not only primes. The five further
claims record the least exponent, distinct sparse Golay-length representations,
quantitative and subpolynomial gaps, and flat orthogonal matrices.

This file imports only mathlib. Its six deliberate statement holes belong to
the challenge, not the proof development. Solution.lean does not import it.
Comparator checks the same named declarations and their reached definitions
against the independently compiled proof environment.

The covering and condition-number results are proved in the development but
are not among this first submission's compared declarations. See
paper/ALIGNMENT.md for the scope, proof route and manuscript corrections.
-/

@[expose] public section

namespace HadamardMultibase

/-- A positive order admitting an integer matrix with entries ±1 and orthogonal
rows. Mathlib's IsHadamard also records the equivalent column identity. -/
def HadamardOrder (n : ℕ) : Prop :=
  0 < n ∧ ∃ H : Matrix (Fin n) (Fin n) ℤ, H.IsHadamard

/-- Existence is required before taking the least power-of-two exponent. -/
def HasExponent (p : ℕ) : Prop := ∃ t : ℕ, HadamardOrder (2 ^ t * p)

/-- The least exponent, with no default value for an empty existence set. -/
noncomputable def tau (p : ℕ) (h : HasExponent p) : ℕ := by
  classical
  exact Nat.find h

/-- Natural logarithms; the conclusions only use this at sufficiently large p. -/
noncomputable def logScale (n : ℕ) : ℝ := Real.log n / Real.log (Real.log n)

/-- The multiplicative alphabet of binary Golay lengths 2^a*10^b. -/
def golayMonoid₂ : Set ℕ := {n | ∃ a b : ℕ, n = 2 ^ a * 10 ^ b}

/-- Distinct summands, expressed as a finite set with exactly the requested sum. -/
def SparseDecomposition (q : ℕ) (s : Finset ℕ) : Prop :=
  (∀ n ∈ s, n ∈ golayMonoid₂) ∧ ∑ n ∈ s, n = q

/-- A uniform bound for every q > 2; finite initial cases are included. -/
def SparseRepresentationBound : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ q : ℕ, 2 < q →
    ∃ s : Finset ℕ, SparseDecomposition q s ∧ (s.card : ℝ) ≤ K * logScale q

/-- Every natural starting point up to x has a strictly larger Hadamard order
within d. This avoids negative real starting points and enumeration choices. -/
def HadamardGapBound (x d : ℕ) : Prop :=
  ∀ y : ℕ, y ≤ x → ∃ h : ℕ, HadamardOrder h ∧ y < h ∧ h ≤ y + d

/-- The sparse representation input is a proved conclusion, not an assumption. -/
theorem sparseRepresentationBound : SparseRepresentationBound := by
  sorry

namespace Complete

/-- The main Hadamard existence bound, uniform over all sufficiently large odd p. -/
theorem main_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ p : ℕ, N ≤ p → Odd p →
      ∃ t : ℕ, HadamardOrder (2 ^ t * p) ∧ (t : ℝ) ≤ C * logScale p := by
  sorry

/-- The same bound for the least admissible exponent, with existence witnessed
by main_bound, so this statement is not an empty implication. -/
theorem tau_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ p : ℕ, N ≤ p → Odd p →
      ∀ h : HasExponent p, (tau p h : ℝ) ≤ C * logScale p := by
  sorry

/-- A uniform bound on all Hadamard gaps with starting point at most x. -/
theorem quantitative_gap_bound :
    ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      ∃ d : ℕ, HadamardGapBound x d ∧ (d : ℝ) ≤ Real.exp (D * logScale x) := by
  sorry

/-- For every positive epsilon, the preceding gap bound is eventually <= x^epsilon. -/
theorem subpolynomial_gap_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      ∃ d : ℕ, HadamardGapBound x d ∧ (d : ℝ) ≤ (x : ℝ) ^ ε := by
  sorry

/-- The manuscript's flatness estimate in its corrected positive-denominator
range. The original claim for every epsilon > 0 is not asserted. -/
theorem flat_orthogonal_bound {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ M : Matrix (Fin n) (Fin n) ℝ, M.transpose * M = 1 ∧
        ∀ i j, |M i j| ≤ 1 / (Real.sqrt n - (n : ℝ) ^ ε) := by
  sorry

end Complete
end HadamardMultibase
