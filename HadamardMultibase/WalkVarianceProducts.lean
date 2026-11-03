module

public import HadamardMultibase.WalkTreeLabels

@[expose] public section

namespace HadamardMultibase

theorem roundingVariance_nonneg {μ : ℝ} (hμ : |μ| ≤ 1) : 0 ≤ 1 - μ ^ 2 := by
  have h := abs_le.mp hμ
  nlinarith [mul_nonneg (show 0 ≤ 1 - μ by linarith) (show 0 ≤ 1 + μ by linarith)]

theorem roundingVariance_le_one (μ : ℝ) : 1 - μ ^ 2 ≤ 1 := by nlinarith [sq_nonneg μ]

theorem wordMultiplicity_ne_zero_iff {ι τ : Type*} [Fintype τ] [DecidableEq ι]
    (word : τ → ι) (i : ι) : wordMultiplicity word i ≠ 0 ↔ i ∈ Finset.univ.image word := by
  classical
  rw [← Nat.pos_iff_ne_zero, wordMultiplicity, Finset.card_pos]
  constructor
  · rintro ⟨t, ht⟩
    exact Finset.mem_image.mpr ⟨t, (Finset.mem_filter.mp ht).1, (Finset.mem_filter.mp ht).2⟩
  · intro hi
    obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hi
    exact ⟨t, Finset.mem_filter.mpr ⟨ht, hti⟩⟩

noncomputable def wordVarianceProduct {ι τ : Type*} [Fintype τ] [DecidableEq ι]
    (μ : ι → ℝ) (word : τ → ι) : ℝ :=
  ∏ i ∈ Finset.univ.image word, (1 - (μ i) ^ 2)

theorem wordMomentMajorant_le_varianceProduct
    {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]
    {μ : ι → ℝ} (hμ : ∀ i, |μ i| ≤ 1) (word : τ → ι) :
    wordMomentMajorant μ word ≤ (2 : ℝ) ^ Fintype.card τ * wordVarianceProduct μ word := by
  classical
  have hprod : (∏ i, if wordMultiplicity word i = 0 then (1 : ℝ) else 1 - (μ i) ^ 2) =
      wordVarianceProduct μ word := by
    unfold wordVarianceProduct
    calc
      _ = ∏ i ∈ Finset.univ.image word,
          if wordMultiplicity word i = 0 then (1 : ℝ) else 1 - (μ i) ^ 2 := by
        symm
        apply Finset.prod_subset (Finset.subset_univ _)
        intro i _ hi
        have hz : wordMultiplicity word i = 0 := by
          by_contra hz
          exact hi ((wordMultiplicity_ne_zero_iff word i).mp hz)
        rw [ite_eq_left hz]
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [ite_eq_right ((wordMultiplicity_ne_zero_iff word i).mpr hi)]
  unfold wordMomentMajorant
  split_ifs with hno
  · calc
      _ ≤ ∏ i, (2 : ℝ) ^ wordMultiplicity word i *
          (if wordMultiplicity word i = 0 then 1 else 1 - (μ i) ^ 2) := by
        apply Finset.prod_le_prod₀
        · intro i _
          split_ifs <;> positivity [roundingVariance_nonneg (hμ i)]
        · intro i _
          by_cases hi : wordMultiplicity word i = 0
          · simp [hi]
          · simp only [ite_eq_right hi]
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le _ _))
              (roundingVariance_nonneg (hμ i))
      _ = (2 : ℝ) ^ (∑ i, wordMultiplicity word i) * wordVarianceProduct μ word := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hprod]
      _ = _ := by rw [sum_wordMultiplicity]
  · exact mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => roundingVariance_nonneg (hμ i)))

/-- Dropping non-tree variance factors only increases the product. -/
theorem wordVarianceProduct_le_treeWeight
    {V τ : Type*} [DecidableEq τ] (label : V → V → τ)
    (hlabel : ∀ a b c d, label a b = label c d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c))
    {μ : τ → ℝ} (hμ : ∀ a, |μ a| ≤ 1) {n : ℕ} (p : WalkPattern n)
    {f : Fin ((walkPatternData p).fresh + 1) → V} (hf : Function.Injective f) :
    wordVarianceProduct μ (historyEdgeWord label (realizeWalkPattern p f)) ≤
      increasingTreeWeight (fun x y => 1 - (μ (label x y)) ^ 2) (walkPatternData p).tree f := by
  classical
  unfold wordVarianceProduct
  calc
    _ ≤ ∏ a ∈ Finset.univ.image (treeEdgeWord label (walkPatternData p).tree f), (1 - (μ a) ^ 2) :=
      Finset.prod_le_prod_of_subset_of_le_one₀ (treeEdgeWord_support_subset_history label p f)
        (fun a _ => roundingVariance_nonneg (hμ a)) (fun a _ _ => roundingVariance_le_one (μ a))
    _ = ∏ e, (1 - (μ (treeEdgeWord label (walkPatternData p).tree f e)) ^ 2) := by
      rw [Finset.prod_image (by
        intro a _ b _ hab
        exact treeEdgeWord_injective label hlabel (walkPatternData p).tree hf hab)]
    _ = _ := (increasingTreeWeight_eq_prod_edges
      (fun x y => 1 - (μ (label x y)) ^ 2) (walkPatternData p).tree f).symm

theorem wordMomentMajorant_le_pattern_tree
    {V τ : Type*} [DecidableEq τ] [Fintype τ] (label : V → V → τ)
    (hlabel : ∀ a b c d, label a b = label c d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c))
    {μ : τ → ℝ} (hμ : ∀ a, |μ a| ≤ 1) {n : ℕ} (p : WalkPattern n)
    {f : Fin ((walkPatternData p).fresh + 1) → V} (hf : Function.Injective f) :
    wordMomentMajorant μ (historyEdgeWord label (realizeWalkPattern p f)) ≤
      (2 : ℝ) ^ n *
        increasingTreeWeight (fun x y => 1 - (μ (label x y)) ^ 2) (walkPatternData p).tree f := by
  have h := wordMomentMajorant_le_varianceProduct hμ
    (historyEdgeWord label (realizeWalkPattern p f))
  rw [Fintype.card_fin] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (wordVarianceProduct_le_treeWeight label hlabel hμ p hf) (by positivity))

noncomputable def boundedWalkPatterns (n k : ℕ) : Finset (WalkPattern n) := by
  classical
  exact Finset.univ.filter (fun p => (walkPatternData p).fresh ≤ k)

/-- Sum over all bounded discovery patterns and all discovery-vertex labels.
This is the numerical tree estimate used after encoding surviving walks. -/
theorem sum_bounded_pattern_tree_weights_le {V : Type*} [Fintype V] [DecidableEq V]
    {W : V → V → ℝ} (hW : ∀ x y, 0 ≤ W x y) {v : ℝ} (hv : 1 ≤ v)
    (hrow : ∀ x, ∑ y, W x y ≤ v) (n k : ℕ) :
    (∑ p ∈ boundedWalkPatterns n k,
      ∑ f : Fin ((walkPatternData p).fresh + 1) → V,
        increasingTreeWeight W (walkPatternData p).tree f) ≤
      (((n + 1) ^ n : ℕ) : ℝ) * (Fintype.card V : ℝ) * v ^ k := by
  classical
  have hv0 : 0 ≤ v := by linarith
  have hcard : (boundedWalkPatterns n k).card ≤ (n + 1) ^ n :=
    (Finset.card_filter_le _ _).trans (card_walkPattern_le n)
  calc
    _ ≤ ∑ _p ∈ boundedWalkPatterns n k, (Fintype.card V : ℝ) * v ^ k := by
      apply Finset.sum_le_sum
      intro p hp
      have hpk : (walkPatternData p).fresh ≤ k := (Finset.mem_filter.mp hp).2
      exact (sum_increasingTreeWeight_le hW hv0 hrow (walkPatternData p).tree).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hv hpk) (Nat.cast_nonneg _))
    _ = ((boundedWalkPatterns n k).card : ℝ) * ((Fintype.card V : ℝ) * v ^ k) := by simp
    _ ≤ _ := by
      have hcardR : ((boundedWalkPatterns n k).card : ℝ) ≤ (((n + 1) ^ n : ℕ) : ℝ) :=
        Nat.cast_le.mpr hcard
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcardR
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hv0 _))

end HadamardMultibase
