module

public import HadamardMultibase.MatrixWalkExpansion
public import HadamardMultibase.RoundingWordMoments

@[expose] public section

namespace HadamardMultibase

open Matrix
open scoped Matrix.Norms.L2Operator

variable {ι τ : Type*} [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ]

/-- The coordinate assigned to each edge of a walk. Labels need not be
injective: symmetric matrix entries may share one random coordinate. -/
def matrixPathWord (label : ι → ι → τ) {k : ℕ} (i j : ι) (f : Fin k → ι) :
    Fin (k + 1) → τ := fun t =>
  label (Fin.cons (α := fun _ : Fin (k + 1) => ι) i f t)
    (Fin.snoc (α := fun _ : Fin (k + 1) => ι) f j t)

/-- A deterministic mask times independent centered coordinates. The mask
allows structurally zero blocks in a symmetric dilation. -/
noncomputable def centeredLabelMatrix (μ : τ → ℝ) (label : ι → ι → τ)
    (mask : Matrix ι ι ℝ) (ω : τ → Bool) : Matrix ι ι ℝ :=
  fun i j => mask i j * (roundingSign (ω (label i j)) - μ (label i j))

omit [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ] in
theorem matrixPathWeight_centered_factorization (μ : τ → ℝ) (label : ι → ι → τ)
    (mask : Matrix ι ι ℝ) (ω : τ → Bool) {k : ℕ} (i j : ι) (f : Fin k → ι) :
    matrixPathWeight (centeredLabelMatrix μ label mask ω) i j f =
      matrixPathWeight mask i j f *
        ∏ t, (roundingSign (ω (matrixPathWord label i j f t)) - μ (matrixPathWord label i j f t)) := by
  exact Finset.prod_mul_distrib

omit [Fintype ι] [DecidableEq ι] in
theorem roundingWeight_path_moment_factorization (μ : τ → ℝ) (label : ι → ι → τ)
    (mask : Matrix ι ι ℝ) {k : ℕ} (i j : ι) (f : Fin k → ι) :
    (∑ ω : τ → Bool, roundingWeight μ ω *
      matrixPathWeight (centeredLabelMatrix μ label mask ω) i j f) =
    matrixPathWeight mask i j f *
      ∏ a, ∑ b : Bool, roundingProbability (μ a) b *
        (roundingSign b - μ a) ^ wordMultiplicity (matrixPathWord label i j f) a := by
  simp_rw [matrixPathWeight_centered_factorization]
  calc
    _ = matrixPathWeight mask i j f * (∑ ω : τ → Bool, roundingWeight μ ω *
        ∏ t, (roundingSign (ω (matrixPathWord label i j f t)) - μ (matrixPathWord label i j f t))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = _ := by rw [roundingWeight_word_moment_factorization]

omit [Fintype ι] [DecidableEq ι] in
theorem roundingWeight_path_moment_zero (μ : τ → ℝ) (label : ι → ι → τ)
    (mask : Matrix ι ι ℝ) {k : ℕ} (i j : ι) (f : Fin k → ι) {a : τ}
    (ha : wordMultiplicity (matrixPathWord label i j f) a = 1) :
    (∑ ω : τ → Bool, roundingWeight μ ω *
      matrixPathWeight (centeredLabelMatrix μ label mask ω) i j f) = 0 := by
  rw [roundingWeight_path_moment_factorization]
  have hzero : (∏ a, ∑ b : Bool, roundingProbability (μ a) b *
      (roundingSign b - μ a) ^ wordMultiplicity (matrixPathWord label i j f) a) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    simpa only [ha, pow_one] using roundingSign_centered_mean (μ a)
  rw [hzero, mul_zero]

/-- Exact expected trace expansion. Each walk is weighted by a product of
scalar centered moments, grouped according to its random-coordinate labels. -/
theorem roundingWeight_trace_pow_expansion (μ : τ → ℝ) (label : ι → ι → τ)
    (mask : Matrix ι ι ℝ) (k : ℕ) :
    (∑ ω : τ → Bool, roundingWeight μ ω *
      Matrix.trace ((centeredLabelMatrix μ label mask ω) ^ (k + 1))) =
    ∑ i : ι, ∑ f : Fin k → ι, matrixPathWeight mask i i f *
      ∏ a, ∑ b : Bool, roundingProbability (μ a) b *
        (roundingSign b - μ a) ^ wordMultiplicity (matrixPathWord label i i f) a := by
  simp_rw [matrix_trace_pow_walk_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  exact roundingWeight_path_moment_factorization μ label mask i i f

omit [Fintype ι] [DecidableEq ι] in
theorem roundingWeight_path_moment_bound {μ : τ → ℝ} (hμ : ∀ a, |μ a| ≤ 1)
    (label : ι → ι → τ) (mask : Matrix ι ι ℝ) {k : ℕ} (i j : ι) (f : Fin k → ι)
    (hno : ∀ a, wordMultiplicity (matrixPathWord label i j f) a ≠ 1) :
    |∑ ω : τ → Bool, roundingWeight μ ω *
      matrixPathWeight (centeredLabelMatrix μ label mask ω) i j f| ≤
    |matrixPathWeight mask i j f| *
      ∏ a, if wordMultiplicity (matrixPathWord label i j f) a = 0 then 1 else
        (2 : ℝ) ^ (wordMultiplicity (matrixPathWord label i j f) a - 2) * (1 - (μ a) ^ 2) := by
  have h := roundingWeight_word_moment_bound hμ (matrixPathWord label i j f) hno
  rw [roundingWeight_word_moment_factorization] at h
  rw [roundingWeight_path_moment_factorization, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

omit [Fintype ι] [DecidableEq ι] in
theorem roundingWeight_path_moment_le_majorant {μ : τ → ℝ} (hμ : ∀ a, |μ a| ≤ 1)
    (label : ι → ι → τ) (mask : Matrix ι ι ℝ) {k : ℕ} (i j : ι) (f : Fin k → ι) :
    |∑ ω : τ → Bool, roundingWeight μ ω *
      matrixPathWeight (centeredLabelMatrix μ label mask ω) i j f| ≤
    |matrixPathWeight mask i j f| * wordMomentMajorant μ (matrixPathWord label i j f) := by
  have h := roundingWeight_word_moment_le_majorant hμ (matrixPathWord label i j f)
  rw [roundingWeight_word_moment_factorization] at h
  rw [roundingWeight_path_moment_factorization, abs_mul]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- Reduction of expected traces to a deterministic weighted walk sum. -/
theorem roundingWeight_trace_pow_le_walk_sum {μ : τ → ℝ} (hμ : ∀ a, |μ a| ≤ 1)
    (label : ι → ι → τ) (mask : Matrix ι ι ℝ) (k : ℕ) :
    |∑ ω : τ → Bool, roundingWeight μ ω *
      Matrix.trace ((centeredLabelMatrix μ label mask ω) ^ (k + 1))| ≤
    ∑ i : ι, ∑ f : Fin k → ι,
      |matrixPathWeight mask i i f| * wordMomentMajorant μ (matrixPathWord label i i f) := by
  have hexpand : (∑ ω : τ → Bool, roundingWeight μ ω *
      Matrix.trace ((centeredLabelMatrix μ label mask ω) ^ (k + 1))) =
      ∑ i : ι, ∑ f : Fin k → ι, ∑ ω : τ → Bool, roundingWeight μ ω *
        matrixPathWeight (centeredLabelMatrix μ label mask ω) i i f := by
    simp_rw [matrix_trace_pow_walk_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  rw [hexpand]
  calc
    _ ≤ ∑ i : ι, |∑ f : Fin k → ι, ∑ ω : τ → Bool, roundingWeight μ ω *
        matrixPathWeight (centeredLabelMatrix μ label mask ω) i i f| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : ι, ∑ f : Fin k → ι, |∑ ω : τ → Bool, roundingWeight μ ω *
        matrixPathWeight (centeredLabelMatrix μ label mask ω) i i f| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun f _ =>
      roundingWeight_path_moment_le_majorant hμ label mask i i f))

/-- A symmetric rounding admits a sample controlled by the deterministic
walk majorant. Concentration now reduces to bounding that finite walk sum. -/
theorem exists_rounding_norm_pow_le_walk_sum [Nonempty ι]
    {μ : τ → ℝ} (hμ : ∀ a, |μ a| ≤ 1) (label : ι → ι → τ)
    (mask : Matrix ι ι ℝ)
    (hsym : ∀ ω : τ → Bool, (centeredLabelMatrix μ label mask ω)ᵀ =
      centeredLabelMatrix μ label mask ω) {k : ℕ} (hk : 0 < k) :
    ∃ ω : τ → Bool, ‖centeredLabelMatrix μ label mask ω‖ ^ (2 * k) ≤
      ∑ i : ι, ∑ f : Fin (2 * k - 1) → ι,
        |matrixPathWeight mask i i f| * wordMomentMajorant μ (matrixPathWord label i i f) := by
  obtain ⟨ω, hω⟩ := exists_rounding_le_expectation hμ
    (fun ω => ‖centeredLabelMatrix μ label mask ω‖ ^ (2 * k))
  refine ⟨ω, hω.trans ?_⟩
  calc
    _ ≤ ∑ η : τ → Bool, roundingWeight μ η *
        Matrix.trace ((centeredLabelMatrix μ label mask η) ^ (2 * k)) := by
      apply Finset.sum_le_sum
      intro η _
      exact mul_le_mul_of_nonneg_left (symmetric_norm_even_pow_le_trace (hsym η) k)
        (roundingWeight_nonneg hμ η)
    _ ≤ |∑ η : τ → Bool, roundingWeight μ η *
        Matrix.trace ((centeredLabelMatrix μ label mask η) ^ (2 * k))| := le_abs_self _
    _ ≤ _ := by
      have h := roundingWeight_trace_pow_le_walk_sum hμ label mask (2 * k - 1)
      simpa only [show 2 * k - 1 + 1 = 2 * k by omega] using h

end HadamardMultibase
