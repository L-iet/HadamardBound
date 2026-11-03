/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.LogarithmSeparation
public import HadamardMultibase.Results
public import HadamardMultibase.OptimalConditionNumber
public import HadamardMultibase.GeneralIndependence
public import HadamardMultibase.CoveringUpper

@[expose] public section

/-! # Unconditional final results

The logarithmic separation input is proved from mathlib in this project.
These endpoints have no sparse-representation or Diophantine hypotheses.
-/
namespace HadamardMultibase

theorem sparseRepresentationBound : SparseRepresentationBound :=
  sparseRepresentationBound_of_not_liouville
    (not_liouville_log_ratio (by norm_num : 2 ≤ (2 : ℕ)) (by norm_num : 2 ≤ (10 : ℕ))
      irrational_log_ten_div_log_two)

namespace Complete

theorem main_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ p : ℕ, N ≤ p → Odd p →
      ∃ t : ℕ, HadamardOrder (2 ^ t * p) ∧ (t : ℝ) ≤ C * logScale p :=
  HadamardMultibase.main_bound sparseRepresentationBound

theorem tau_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ p : ℕ, N ≤ p → Odd p →
      ∀ h : HasExponent p, (tau p h : ℝ) ≤ C * logScale p :=
  HadamardMultibase.tau_bound sparseRepresentationBound

theorem quantitative_gap_bound :
    ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      ∃ d : ℕ, HadamardGapBound x d ∧ (d : ℝ) ≤ Real.exp (D * logScale x) :=
  HadamardMultibase.quantitative_gap_bound sparseRepresentationBound

theorem subpolynomial_gap_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      ∃ d : ℕ, HadamardGapBound x d ∧ (d : ℝ) ≤ (x : ℝ) ^ ε :=
  HadamardMultibase.subpolynomial_gap_bound sparseRepresentationBound hε

theorem flat_orthogonal_bound {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ M : Matrix (Fin n) (Fin n) ℝ, M.transpose * M = 1 ∧
        ∀ i j, |M i j| ≤ 1 / (Real.sqrt n - (n : ℝ) ^ ε) :=
  HadamardMultibase.flat_orthogonal_bound sparseRepresentationBound hε hεhalf

theorem approximateHadamard_bound {α : ℝ} (hα : 0 < α) (hαquarter : α < 1 / 4) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ A : Matrix (Fin n) (Fin n) ℝ, (∀ i j, A i j = 1 ∨ A i j = -1) ∧
        matrixConditionNumber A ≤ ENNReal.ofReal (1 + (n : ℝ) ^ (-α)) :=
  HadamardMultibase.approximateHadamard_bound sparseRepresentationBound hα hαquarter

theorem approximateHadamard_condition_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ A : Matrix (Fin n) (Fin n) ℝ, (∀ i j, A i j = 1 ∨ A i j = -1) ∧
        matrixConditionNumber A ≤ ENNReal.ofReal (1 + (n : ℝ) ^ (-1 / 4 + δ)) :=
  HadamardMultibase.approximateHadamard_condition_bound sparseRepresentationBound hδ

theorem optimalConditionNumber_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      optimalConditionNumber n ≤ ENNReal.ofReal (1 + (n : ℝ) ^ (-1 / 4 + δ)) :=
  HadamardMultibase.optimalConditionNumber_bound sparseRepresentationBound hδ

theorem powerMonoid_sparse_bound {r : ℕ} {b : Fin r → ℕ}
    (hb : ∀ i, 2 ≤ b i) (hind : IndependentBases b)
    {i₀ i₁ : Fin r} (hi₀ : b i₀ = 2) (hne : i₀ ≠ i₁) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 < n →
      ∃ s : Finset ℕ, DistinctSum (powerMonoid b) n s ∧ (s.card : ℝ) ≤ K * logScale n := by
  apply powerMonoid_sparse_bound_of_separation hb hi₀
  have hirr := hind.irrational_log_ratio hb hne
  rw [hi₀] at hirr
  exact polynomialRotationSeparation_log_ratio (by norm_num : 2 ≤ (2 : ℕ)) (hb i₁) hirr

theorem powerMonoid_covering_lower {r : ℕ} {b : Fin r → ℕ}
    (hb : ∀ i, 2 ≤ b i) (hind : IndependentBases b)
    {i₀ i₁ : Fin r} (hi₀ : b i₀ = 2) (hne : i₀ ≠ i₁) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in Filter.atTop,
      Real.exp (c * m * Real.log m) ≤
        (coveringNumber (powerMonoid b) m (hasMissing_powerMonoid hb m) : ℝ) := by
  apply powerMonoid_covering_lower_of_separation hb hi₀
  have hirr := hind.irrational_log_ratio hb hne
  rw [hi₀] at hirr
  exact polynomialRotationSeparation_log_ratio (by norm_num : 2 ≤ (2 : ℕ)) (hb i₁) hirr

theorem golayCoveringNumber₃_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in Filter.atTop,
      Real.exp (c * m * Real.log m) ≤ (golayCoveringNumber₃ m : ℝ) := by
  have h := powerMonoid_covering_lower (b := ![2, 10, 26]) (by decide)
    independentBases_two_ten_twentySix (i₀ := 0) (i₁ := 1) (by decide) (by decide)
  simpa [powerMonoid_two_ten_twentySix, golayCoveringNumber₃] using h

theorem golayCoveringNumber₃_two_sided :
    ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η → ∀ᶠ m : ℕ in Filter.atTop,
      Real.exp (c * m * Real.log m) ≤ (golayCoveringNumber₃ m : ℝ) ∧
      (golayCoveringNumber₃ m : ℝ) ≤ Real.exp ((2 + η) * m * Real.log m) := by
  obtain ⟨c, hc, hlower⟩ := golayCoveringNumber₃_lower
  exact ⟨c, hc, fun η hη => hlower.and (golayCoveringNumber₃_upper hη)⟩

end Complete
end HadamardMultibase
