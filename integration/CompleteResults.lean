module

public import HadamardMultibase
public import integration.LogarithmRatioInput

@[expose] public section

/-! Unconditional endpoints for the manuscript's Hadamard, gap, covering and
approximate-Hadamard bounds. All construction and Diophantine inputs are
discharged. The flat-matrix bound uses its meaningful range `0 < ε < 1/2`. -/

namespace HadamardMultibase.Complete

open Filter

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

theorem covering_bounds {r : ℕ} {b : Fin r → ℕ}
    (hb : ∀ i, 2 ≤ b i) (hr : 2 ≤ r) (hind : IndependentBases b)
    {i₀ : Fin r} (hi₀ : b i₀ = 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η → ∀ᶠ m : ℕ in atTop,
      Real.exp (c * m * Real.log m) ≤
        (coveringNumber (powerMonoid b) m (hasMissing_powerMonoid hb m) : ℝ) ∧
      (coveringNumber (powerMonoid b) m (hasMissing_powerMonoid hb m) : ℝ) ≤
        Real.exp (((r : ℝ) - 1 + η) * m * Real.log m) := by
  let : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  obtain ⟨i₁, hne⟩ := exists_ne i₀
  have hsep : PolynomialRotationSeparation (Real.log (b i₁ : ℝ) / Real.log 2) := by
    simpa [hi₀] using hind.log_ratio_separation hb hne.symm
  obtain ⟨c, hc, hlower⟩ := powerMonoid_covering_lower_of_separation hb hi₀ hsep
  refine ⟨c, hc, ?_⟩
  intro η hη
  filter_upwards [hlower, coveringNumber_upper hb hr hη] with m hl hu
  exact ⟨hl, hu⟩

theorem golay_covering_bounds :
    ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η → ∀ᶠ m : ℕ in atTop,
      Real.exp (c * m * Real.log m) ≤ (golayCoveringNumber₃ m : ℝ) ∧
      (golayCoveringNumber₃ m : ℝ) ≤ Real.exp ((2 + η) * m * Real.log m) := by
  obtain ⟨c, hc, hlower⟩ := golayCoveringNumber₃_lower sparseRepresentationBound
  refine ⟨c, hc, ?_⟩
  intro η hη
  filter_upwards [hlower, golayCoveringNumber₃_upper hη] with m hl hu
  exact ⟨hl, hu⟩

theorem flat_orthogonal_bound {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ M : Matrix (Fin n) (Fin n) ℝ, M.transpose * M = 1 ∧
        ∀ i j, |M i j| ≤ 1 / (Real.sqrt n - (n : ℝ) ^ ε) :=
  HadamardMultibase.flat_orthogonal_bound sparseRepresentationBound hε hεhalf

theorem approximateHadamard_condition_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ A : Matrix (Fin n) (Fin n) ℝ, (∀ i j, A i j = 1 ∨ A i j = -1) ∧
        matrixConditionNumber A ≤ ENNReal.ofReal (1 + (n : ℝ) ^ (-1 / 4 + δ)) :=
  HadamardMultibase.approximateHadamard_condition_bound sparseRepresentationBound hδ

theorem optimalConditionNumber_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      optimalConditionNumber n ≤ ENNReal.ofReal (1 + (n : ℝ) ^ (-1 / 4 + δ)) :=
  HadamardMultibase.optimalConditionNumber_bound sparseRepresentationBound hδ

end HadamardMultibase.Complete
