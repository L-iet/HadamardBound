module

public import HadamardMultibase.FiniteRounding

@[expose] public section

namespace HadamardMultibase

theorem roundingSign_centered_mean (μ : ℝ) :
    ∑ b : Bool, roundingProbability μ b * (roundingSign b - μ) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    roundingSign_mean, roundingProbability_sum, one_mul, sub_self]

/-- A centered product vanishes if any independent coordinate occurs once.
This is the cancellation used in trace-moment concentration proofs. -/
theorem roundingWeight_centered_moment_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → ℝ) (e : ι → ℕ) {i : ι} (hi : e i = 1) :
    ∑ ω : ι → Bool, roundingWeight μ ω *
      (∏ j, (roundingSign (ω j) - μ j) ^ e j) = 0 := by
  rw [roundingWeight_moment_factorization μ (fun j b => (roundingSign b - μ j) ^ e j)]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa only [hi, pow_one] using roundingSign_centered_mean (μ i)

/-- Higher centered moments retain the small variance factor. -/
theorem roundingSign_moment_bound {μ : ℝ} (hμ : |μ| ≤ 1) {k : ℕ} (hk : 2 ≤ k) :
    |∑ b : Bool, roundingProbability μ b * (roundingSign b - μ) ^ k| ≤
      (2 : ℝ) ^ (k - 2) * (1 - μ ^ 2) := by
  have hp (b : Bool) : |roundingSign b - μ| ^ k ≤
      (2 : ℝ) ^ (k - 2) * (roundingSign b - μ) ^ 2 := by
    rw [show k = (k - 2) + 2 by omega, pow_add, sq_abs]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg _) (roundingSign_error_le hμ b) _) (sq_nonneg _)
  calc
    _ ≤ ∑ b : Bool, |roundingProbability μ b * (roundingSign b - μ) ^ k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ b : Bool, roundingProbability μ b * |roundingSign b - μ| ^ k := by
      apply Finset.sum_congr rfl
      intro b _
      rw [abs_mul, abs_of_nonneg (roundingProbability_nonneg hμ b), abs_pow]
    _ ≤ ∑ b : Bool, roundingProbability μ b *
        ((2 : ℝ) ^ (k - 2) * (roundingSign b - μ) ^ 2) :=
      Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hp b)
        (roundingProbability_nonneg hμ b))
    _ = (2 : ℝ) ^ (k - 2) *
        (∑ b : Bool, roundingProbability μ b * (roundingSign b - μ) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [roundingSign_variance]

end HadamardMultibase
