module

public import HadamardMultibase.SparseGreedy
public import HadamardMultibase.ClippedLogScale

@[expose] public section

namespace HadamardMultibase

open Filter

/-- The quantitative approximation step needed by the greedy algorithm. -/
def PolynomialRemainderApproximation (S : Set ℕ) : Prop :=
  ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ n : ℕ in atTop,
    ∃ b ∈ S, b ≤ n ∧ ((n - b : ℕ) : ℝ) ≤ shrinkingRemainder C κ n

/-- A polynomial saving in the logarithm gives an eventual sparse bound.
All finite initial representations and the distinctness of the greedy sums
are included in the proof. -/
theorem eventual_sparse_bound_of_approximation {S : Set ℕ}
    (hpos : ∀ a ∈ S, 0 < a)
    (hrep : ∀ n : ℕ, ∃ s : Finset ℕ, DistinctSum S n s)
    (happrox : PolynomialRemainderApproximation S) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∃ s : Finset ℕ, DistinctSum S n s ∧ (s.card : ℝ) ≤ K * logScale n := by
  obtain ⟨C, κ, hC, hκ, happ⟩ := happrox
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp eventually_logScale_threshold
  let N := max N₀ 1
  have hN : 0 < N := by dsimp [N]; omega
  have hlogN : Real.exp 1 ≤ Real.log (N : ℝ) := hN₀ N (le_max_left _ _)
  have hscale : 0 < logScale N := logScaleReal_pos hlogN
  have hevent : ∀ᶠ n : ℕ in atTop,
      N ≤ n ∧ (shrinkingRemainder C κ n < (n : ℝ) / 2) ∧
      (∀ r : ℕ, (r : ℝ) ≤ shrinkingRemainder C κ n →
        clippedLogScale N r ≤ logScale n - κ / 4) ∧
      ∃ b ∈ S, b ≤ n ∧ ((n - b : ℕ) : ℝ) ≤ shrinkingRemainder C κ n := by
    filter_upwards [eventually_ge_atTop N, eventually_shrinkingRemainder_lt_half hκ,
      eventually_clippedLogScale_drop hN hlogN hC hκ, happ] with n hn hhalf hdrop ha
    exact ⟨hn, hhalf, hdrop, ha⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  let K : ℝ := max (4 / κ) ((T : ℝ) / logScale N + 1)
  have hK₁ : 4 / κ ≤ K := le_max_left _ _
  have hK₂ : (T : ℝ) / logScale N + 1 ≤ K := le_max_right _ _
  have hK : 0 < K := lt_of_lt_of_le (div_pos (by norm_num) hκ) hK₁
  have hunit : 1 ≤ K * (κ / 4) := by
    have h := (div_le_iff₀ hκ).mp hK₁
    nlinarith
  have hbasebudget : (T : ℝ) ≤ K * logScale N := by
    have h := (div_le_iff₀ hscale).mp (show (T : ℝ) / logScale N ≤ K by linarith)
    exact h
  have hall := greedy_distinct_sum (S := S) (fun n => K * clippedLogScale N n) T
    (by
      intro n hn
      obtain ⟨s, hs⟩ := hrep n
      refine ⟨s, hs, ?_⟩
      calc
        (s.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hs.card_le hpos
        _ ≤ T := by exact_mod_cast hn
        _ ≤ K * logScale N := hbasebudget
        _ ≤ K * clippedLogScale N n :=
          mul_le_mul_of_nonneg_left (clippedLogScale_lower hN hlogN n) hK.le)
    (by
      intro n hn
      obtain ⟨hnN, hhalf, hdrop, b, hbS, hbn, hres⟩ := hT n (by omega)
      have hsum : ((n - b : ℕ) : ℝ) + (b : ℝ) = (n : ℝ) := by
        exact_mod_cast (Nat.sub_add_cancel hbn)
      have hsmall : n - b < b := by
        have : ((n - b : ℕ) : ℝ) < (b : ℝ) := by linarith
        exact_mod_cast this
      refine ⟨b, hbS, by omega, hbn, hsmall, ?_⟩
      have hd := mul_le_mul_of_nonneg_left (hdrop (n - b) hres) hK.le
      rw [clippedLogScale_eq hnN]
      nlinarith)
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  simpa only [clippedLogScale_eq hn] using hall n

/-- Absorb the finitely many initial cases into the multiplicative constant. -/
theorem sparse_bound_of_eventual {S : Set ℕ}
    (hpos : ∀ a ∈ S, 0 < a)
    (hrep : ∀ n : ℕ, ∃ s : Finset ℕ, DistinctSum S n s)
    (hevent : ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      ∃ s : Finset ℕ, DistinctSum S n s ∧ (s.card : ℝ) ≤ K * logScale n) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 < n →
      ∃ s : Finset ℕ, DistinctSum S n s ∧ (s.card : ℝ) ≤ K * logScale n := by
  classical
  obtain ⟨K, hK, hevent⟩ := hevent
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevent
  let small := (Finset.range M).filter (fun q => 2 < q)
  let E : ℝ := ∑ q ∈ small, (q : ℝ) / logScale q
  have hterm : ∀ q ∈ small, 0 ≤ (q : ℝ) / logScale q := by
    intro q hq
    exact div_nonneg (Nat.cast_nonneg q)
      (logScale_pos_of_gt_two (Finset.mem_filter.mp hq).2).le
  have hE : 0 ≤ E := Finset.sum_nonneg hterm
  refine ⟨K + E + 1, by linarith, ?_⟩
  intro n hn
  have hscale := logScale_pos_of_gt_two hn
  by_cases hnM : M ≤ n
  · obtain ⟨s, hs, hb⟩ := hM n hnM
    refine ⟨s, hs, hb.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith) hscale.le
  · obtain ⟨s, hs⟩ := hrep n
    have hmem : n ∈ small := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hn⟩
    have hratio : (n : ℝ) / logScale n ≤ E :=
      Finset.single_le_sum (f := fun q : ℕ => (q : ℝ) / logScale q) hterm hmem
    have hnE : (n : ℝ) ≤ E * logScale n := (div_le_iff₀ hscale).mp hratio
    refine ⟨s, hs, ?_⟩
    have hcard : (s.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hs.card_le hpos
    have hmul := mul_le_mul_of_nonneg_right (show E ≤ K + E + 1 by linarith) hscale.le
    exact hcard.trans (hnE.trans hmul)

theorem sparse_bound_of_approximation {S : Set ℕ}
    (hpos : ∀ a ∈ S, 0 < a)
    (hrep : ∀ n : ℕ, ∃ s : Finset ℕ, DistinctSum S n s)
    (happrox : PolynomialRemainderApproximation S) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 < n →
      ∃ s : Finset ℕ, DistinctSum S n s ∧ (s.card : ℝ) ≤ K * logScale n :=
  sparse_bound_of_eventual hpos hrep
    (eventual_sparse_bound_of_approximation hpos hrep happrox)

theorem sparseRepresentationBound_of_approximation
    (happrox : PolynomialRemainderApproximation golayMonoid₂) :
    SparseRepresentationBound := by
  exact sparse_bound_of_approximation (fun a ha => golayMonoid₂_pos ha)
    exists_sparseDecomposition happrox

end HadamardMultibase
