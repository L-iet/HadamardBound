module

public import HadamardMultibase.WalkVarianceProducts

@[expose] public section

namespace HadamardMultibase

/-- A finite weighted covering bound: choose one lift for each nonzero term.
The decoding map makes those choices injective. -/
theorem sum_le_sum_of_weighted_lifts {A B : Type*} [Fintype A] [Fintype B]
    (a : A → ℝ) (b : B → ℝ) (decode : B → A) (hb : ∀ y, 0 ≤ b y)
    (hlift : ∀ x, a x ≠ 0 → ∃ y, decode y = x ∧ a x ≤ b y) :
    ∑ x, a x ≤ ∑ y, b y := by
  classical
  let S := {x : A // a x ≠ 0}
  choose lift hdecode hbound using (fun x : S => hlift x.val x.property)
  have hinj : Function.Injective lift := by
    intro x y hxy
    apply Subtype.ext
    exact (hdecode x).symm.trans ((congrArg decode hxy).trans (hdecode y))
  have hzero : (∑ x : {x : A // ¬a x ≠ 0}, a x) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact not_ne_iff.mp x.property
  have hsum : (∑ x : S, a x) = ∑ x : A, a x := by
    have h := Fintype.sum_subtype_add_sum_subtype (fun x : A => a x ≠ 0) a
    simpa only [hzero, add_zero] using h
  rw [← hsum]
  apply Finset.sum_le_sum_of_injOn lift hinj.injOn (Finset.subset_univ _)
  · intro x _
    exact hbound x
  · intro y _ _
    exact hb y

/-- Quantitative weighted walk bound. It uses singleton cancellation,
discovery-pattern counting, and the row-sum bound on tree variances. -/
theorem sum_wordMomentMajorant_histories_le
    {V τ : Type*} [Fintype V] [DecidableEq V] [Fintype τ] [DecidableEq τ]
    (label : V → V → τ)
    (hlabel : ∀ a b c d, label a b = label c d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c))
    {μ : τ → ℝ} (hμ : ∀ a, |μ a| ≤ 1) {v : ℝ} (hv : 1 ≤ v)
    (hrow : ∀ x, ∑ y, (1 - (μ (label x y)) ^ 2) ≤ v)
    (n k : ℕ) (hnk : n ≤ 2 * k) :
    (∑ w : Fin (n + 1) → V, wordMomentMajorant μ (historyEdgeWord label w)) ≤
      (2 : ℝ) ^ n * (((n + 1) ^ n : ℕ) : ℝ) * (Fintype.card V : ℝ) * v ^ k := by
  classical
  let W : V → V → ℝ := fun x y => 1 - (μ (label x y)) ^ 2
  let P := {p : WalkPattern n // (walkPatternData p).fresh ≤ k}
  let B := Σ p : P, Fin ((walkPatternData p.val).fresh + 1) → V
  let cost : B → ℝ := fun b => (2 : ℝ) ^ n *
    increasingTreeWeight W (walkPatternData b.1.val).tree b.2
  let decode : B → (Fin (n + 1) → V) := fun b => realizeWalkPattern b.1.val b.2
  have hW : ∀ x y, 0 ≤ W x y := fun x y => roundingVariance_nonneg (hμ (label x y))
  have hcost : ∀ b, 0 ≤ cost b := fun b =>
    mul_nonneg (by positivity) (increasingTreeWeight_nonneg hW _ _)
  have hcover : ∀ w : Fin (n + 1) → V,
      wordMomentMajorant μ (historyEdgeWord label w) ≠ 0 →
      ∃ b : B, decode b = w ∧ wordMomentMajorant μ (historyEdgeWord label w) ≤ cost b := by
    intro w hw
    have hno : ∀ a, wordMultiplicity (historyEdgeWord label w) a ≠ 1 := by
      by_contra hn
      exact hw (by simp [wordMomentMajorant, hn])
    obtain ⟨p, f, hf, hrealize, hcount⟩ := exists_bounded_walkPattern_realization label hlabel w hno
    have hpk : (walkPatternData p).fresh ≤ k := by omega
    refine ⟨⟨⟨p, hpk⟩, f⟩, hrealize, ?_⟩
    have h := wordMomentMajorant_le_pattern_tree label hlabel hμ p hf
    simpa only [hrealize] using h
  have hsum := sum_le_sum_of_weighted_lifts
    (fun w => wordMomentMajorant μ (historyEdgeWord label w)) cost decode hcost hcover
  have hcostsum : (∑ b : B, cost b) = (2 : ℝ) ^ n *
      ∑ p ∈ boundedWalkPatterns n k,
        ∑ f : Fin ((walkPatternData p).fresh + 1) → V, increasingTreeWeight W (walkPatternData p).tree f := by
    change (∑ b : Σ p : P, Fin ((walkPatternData p.val).fresh + 1) → V, cost b) = _
    rw [Fintype.sum_sigma]
    simp only [cost]
    simp_rw [← Finset.mul_sum]
    congr 1
    exact (Finset.sum_subtype (boundedWalkPatterns n k)
      (by intro p; simp [boundedWalkPatterns])
      (fun p => ∑ f : Fin ((walkPatternData p).fresh + 1) → V,
        increasingTreeWeight W (walkPatternData p).tree f)).symm
  apply hsum.trans
  rw [hcostsum]
  have hbound := sum_bounded_pattern_tree_weights_le hW hv hrow n k
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound (show 0 ≤ (2 : ℝ) ^ n by positivity)

end HadamardMultibase
