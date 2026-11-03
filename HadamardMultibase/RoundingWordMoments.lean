module

public import HadamardMultibase.RoundingMoments

@[expose] public section

namespace HadamardMultibase

def wordMultiplicity {ι τ : Type*} [Fintype τ] [DecidableEq ι]
    (word : τ → ι) (i : ι) : ℕ := (Finset.univ.filter (fun t => word t = i)).card

theorem sum_wordMultiplicity {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]
    (word : τ → ι) : ∑ i, wordMultiplicity word i = Fintype.card τ := by
  classical
  have h := Finset.sum_fiberwise' (Finset.univ : Finset τ) word (fun _ : ι => (1 : ℕ))
  simpa [wordMultiplicity] using h

/-- A nonzero centered moment can use at most half as many distinct random
coordinates as there are factors. -/
theorem word_support_card_le_half {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]
    (word : τ → ι) (hno : ∀ i, wordMultiplicity word i ≠ 1) :
    2 * (Finset.univ.image word).card ≤ Fintype.card τ := by
  classical
  calc
    _ = ∑ _i ∈ Finset.univ.image word, (2 : ℕ) := by simp [mul_comm]
    _ ≤ ∑ i ∈ Finset.univ.image word, wordMultiplicity word i := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hi
      have hpos : 0 < wordMultiplicity word i :=
        Finset.card_pos.mpr ⟨t, by simp [ht]⟩
      have hne := hno i
      omega
    _ ≤ ∑ i, wordMultiplicity word i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    _ = _ := sum_wordMultiplicity word

/-- Group the factors of a word by coordinate, preserving all repetitions. -/
theorem word_product_eq_product_multiplicities
    {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]
    (word : τ → ι) (x : ι → ℝ) :
    (∏ t, x (word t)) = ∏ i, x i ^ wordMultiplicity word i := by
  classical
  have h := Finset.prod_fiberwise' (Finset.univ : Finset τ) word x
  simpa only [Finset.prod_const, wordMultiplicity] using h.symm

theorem roundingWeight_word_moment_factorization
    {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]
    (μ : ι → ℝ) (word : τ → ι) :
    (∑ ω : ι → Bool, roundingWeight μ ω *
      (∏ t, (roundingSign (ω (word t)) - μ (word t)))) =
    ∏ i, ∑ b : Bool, roundingProbability (μ i) b *
      (roundingSign b - μ i) ^ wordMultiplicity word i := by
  have hregroup (ω : ι → Bool) :=
    word_product_eq_product_multiplicities word (fun i => roundingSign (ω i) - μ i)
  simp_rw [hregroup]
  exact roundingWeight_moment_factorization μ
    (fun i b => (roundingSign b - μ i) ^ wordMultiplicity word i)

theorem roundingWeight_word_moment_zero
    {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]
    (μ : ι → ℝ) (word : τ → ι) {i : ι} (hi : wordMultiplicity word i = 1) :
    (∑ ω : ι → Bool, roundingWeight μ ω *
      (∏ t, (roundingSign (ω (word t)) - μ (word t)))) = 0 := by
  rw [roundingWeight_word_moment_factorization]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa only [hi, pow_one] using roundingSign_centered_mean (μ i)

/-- A variance-sensitive bound for a word with no singleton coordinates.
The factors for unused coordinates are one. -/
theorem roundingWeight_word_moment_bound
    {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]
    {μ : ι → ℝ} (hμ : ∀ i, |μ i| ≤ 1) (word : τ → ι)
    (hno : ∀ i, wordMultiplicity word i ≠ 1) :
    |∑ ω : ι → Bool, roundingWeight μ ω *
      (∏ t, (roundingSign (ω (word t)) - μ (word t)))| ≤
      ∏ i, if wordMultiplicity word i = 0 then 1 else
        (2 : ℝ) ^ (wordMultiplicity word i - 2) * (1 - (μ i) ^ 2) := by
  rw [roundingWeight_word_moment_factorization, Finset.abs_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
  intro i _
  by_cases hi : wordMultiplicity word i = 0
  · rw [ite_eq_left hi]
    simp only [hi, pow_zero, mul_one, roundingProbability_sum, abs_one, le_refl]
  · rw [ite_eq_right hi]
    exact roundingSign_moment_bound (hμ i) (by have := hno i; omega)

/-- Non-surviving words contribute zero; all remaining variance factors are
kept explicit for the combinatorial walk estimate. -/
noncomputable def wordMomentMajorant
    {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]
    (μ : ι → ℝ) (word : τ → ι) : ℝ := by
  classical
  exact if ∀ i, wordMultiplicity word i ≠ 1 then
    ∏ i, if wordMultiplicity word i = 0 then 1 else
      (2 : ℝ) ^ (wordMultiplicity word i - 2) * (1 - (μ i) ^ 2)
    else 0

theorem roundingWeight_word_moment_le_majorant
    {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]
    {μ : ι → ℝ} (hμ : ∀ i, |μ i| ≤ 1) (word : τ → ι) :
    |∑ ω : ι → Bool, roundingWeight μ ω *
      (∏ t, (roundingSign (ω (word t)) - μ (word t)))| ≤ wordMomentMajorant μ word := by
  classical
  unfold wordMomentMajorant
  split_ifs with hno
  · exact roundingWeight_word_moment_bound hμ word hno
  · push Not at hno
    obtain ⟨i, hi⟩ := hno
    rw [roundingWeight_word_moment_zero μ word hi, abs_zero]

end HadamardMultibase
