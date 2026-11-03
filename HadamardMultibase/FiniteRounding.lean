module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic

@[expose] public section

namespace HadamardMultibase

def roundingSign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def roundingProbability (μ : ℝ) (b : Bool) : ℝ :=
  if b then (1 + μ) / 2 else (1 - μ) / 2

theorem roundingProbability_nonneg {μ : ℝ} (hμ : |μ| ≤ 1) (b : Bool) :
    0 ≤ roundingProbability μ b := by
  have h := abs_le.mp hμ
  cases b <;> dsimp [roundingProbability] <;> linarith

theorem roundingProbability_sum (μ : ℝ) : ∑ b : Bool, roundingProbability μ b = 1 := by
  simp [roundingProbability]
  ring

theorem roundingSign_mean (μ : ℝ) :
    ∑ b : Bool, roundingProbability μ b * roundingSign b = μ := by
  simp [roundingProbability, roundingSign]
  ring

theorem roundingSign_variance (μ : ℝ) :
    ∑ b : Bool, roundingProbability μ b * (roundingSign b - μ) ^ 2 = 1 - μ ^ 2 := by
  simp [roundingProbability, roundingSign]
  ring

theorem roundingSign_error_le {μ : ℝ} (hμ : |μ| ≤ 1) (b : Bool) :
    |roundingSign b - μ| ≤ 2 := by
  have h := abs_le.mp hμ
  cases b <;> dsimp [roundingSign] <;> apply abs_le.mpr <;> constructor <;> linarith

/-- A finite product probability distribution for independent rounding.
Keeping expectations as finite sums makes all statements exact. -/
noncomputable def roundingWeight {ι : Type*} [Fintype ι] (μ : ι → ℝ) (ω : ι → Bool) : ℝ :=
  ∏ i, roundingProbability (μ i) (ω i)

theorem roundingWeight_nonneg {ι : Type*} [Fintype ι] {μ : ι → ℝ}
    (hμ : ∀ i, |μ i| ≤ 1) (ω : ι → Bool) : 0 ≤ roundingWeight μ ω :=
  Finset.prod_nonneg (fun i _ => roundingProbability_nonneg (hμ i) (ω i))

theorem roundingWeight_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : ι → ℝ) :
    ∑ ω : ι → Bool, roundingWeight μ ω = 1 := by
  classical
  simp only [roundingWeight]
  rw [← Fintype.prod_sum]
  calc
    _ = ∏ _i : ι, (1 : ℝ) := by
      apply Finset.prod_congr rfl
      intro i _
      exact roundingProbability_sum (μ i)
    _ = 1 := by simp

/-- Factorization of every mixed moment is the independence property needed
by the later matrix concentration argument. -/
theorem roundingWeight_moment_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → ℝ) (f : ι → Bool → ℝ) :
    ∑ ω : ι → Bool, roundingWeight μ ω * (∏ i, f i (ω i)) =
      ∏ i, ∑ b : Bool, roundingProbability (μ i) b * f i b := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ω _
  exact (Finset.prod_mul_distrib).symm

theorem roundingWeight_coordinate_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → ℝ) (i : ι) (f : Bool → ℝ) :
    ∑ ω : ι → Bool, roundingWeight μ ω * f (ω i) =
      ∑ b : Bool, roundingProbability (μ i) b * f b := by
  classical
  have h := roundingWeight_moment_factorization μ (fun j b => if j = i then f b else 1)
  have hprod (ω : ι → Bool) : (∏ j, if j = i then f (ω j) else 1) = f (ω i) := by simp
  simp only [hprod] at h
  rw [h]
  have hinner (j : ι) :
      (∑ b : Bool, roundingProbability (μ j) b * (if j = i then f b else 1)) =
        if j = i then (∑ b : Bool, roundingProbability (μ j) b * f b) else 1 := by
    by_cases hji : j = i
    · simp only [ite_eq_left hji]
    · simp only [ite_eq_right hji, mul_one]
      exact roundingProbability_sum (μ j)
  simp_rw [hinner]
  simp

theorem roundingWeight_coordinate_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → ℝ) (i : ι) :
    ∑ ω : ι → Bool, roundingWeight μ ω * roundingSign (ω i) = μ i := by
  rw [roundingWeight_coordinate_expectation, roundingSign_mean]

theorem roundingWeight_centered_mean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → ℝ) (i : ι) :
    ∑ ω : ι → Bool, roundingWeight μ ω * (roundingSign (ω i) - μ i) = 0 := by
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    roundingWeight_coordinate_mean, roundingWeight_sum, one_mul, sub_self]

theorem roundingWeight_coordinate_variance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → ℝ) (i : ι) :
    ∑ ω : ι → Bool, roundingWeight μ ω * (roundingSign (ω i) - μ i) ^ 2 = 1 - (μ i) ^ 2 := by
  exact (roundingWeight_coordinate_expectation μ i (fun b => (roundingSign b - μ i) ^ 2)).trans
    (roundingSign_variance (μ i))

/-- A sample no worse than the finite expectation always exists. -/
theorem exists_rounding_le_expectation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : ι → ℝ} (hμ : ∀ i, |μ i| ≤ 1) (f : (ι → Bool) → ℝ) :
    ∃ ω : ι → Bool, f ω ≤ ∑ η : ι → Bool, roundingWeight μ η * f η := by
  classical
  obtain ⟨ω, _, hω⟩ := (Finset.univ : Finset (ι → Bool)).exists_min_image f (by simp)
  refine ⟨ω, ?_⟩
  calc
    f ω = ∑ η : ι → Bool, roundingWeight μ η * f ω := by
      rw [← Finset.sum_mul, roundingWeight_sum, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun η hη =>
      mul_le_mul_of_nonneg_left (hω η hη) (roundingWeight_nonneg hμ η))

end HadamardMultibase
