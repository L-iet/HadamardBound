module

public import HadamardMultibase.FiniteRounding
public import HadamardMultibase.MatrixSpectralPerturbation

@[expose] public section

namespace HadamardMultibase

open Matrix

def roundedMatrix {n : ℕ} (ω : (Fin n × Fin n) → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => roundingSign (ω (i, j))

theorem roundedMatrix_sign {n : ℕ} (ω : (Fin n × Fin n) → Bool) (i j : Fin n) :
    roundedMatrix ω i j = 1 ∨ roundedMatrix ω i j = -1 := by
  cases h : ω (i, j) <;> simp [roundedMatrix, roundingSign, h]

theorem roundedMatrix_mean {n : ℕ} (μ : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ∑ ω : (Fin n × Fin n) → Bool,
      roundingWeight (fun p => μ p.1 p.2) ω * roundedMatrix ω i j = μ i j :=
  roundingWeight_coordinate_mean _ (i, j)

theorem orthogonal_row_sum_sq {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Qᵀ * Q = 1) (i : Fin n) : ∑ j, (Q i j) ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i)
    (mul_eq_one_comm.mp hQ)
  simpa only [mul_apply, transpose_apply, one_apply_eq, pow_two] using h

theorem orthogonal_col_sum_sq {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Qᵀ * Q = 1) (j : Fin n) : ∑ i, (Q i j) ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M j j) hQ
  simpa only [mul_apply, transpose_apply, one_apply_eq, pow_two] using h

/-- Each row has exactly the variance parameter used in matrix concentration. -/
theorem rounding_row_variance {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Qᵀ * Q = 1) (u : ℝ) (i : Fin n) :
    ∑ j, (1 - (Q i j / u) ^ 2) = n - 1 / u ^ 2 := by
  simp only [Finset.sum_sub_distrib, div_pow, ← Finset.sum_div]
  rw [orthogonal_row_sum_sq hQ i]
  simp

theorem rounding_col_variance {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Qᵀ * Q = 1) (u : ℝ) (j : Fin n) :
    ∑ i, (1 - (Q i j / u) ^ 2) = n - 1 / u ^ 2 := by
  simp only [Finset.sum_sub_distrib, div_pow, ← Finset.sum_div]
  rw [orthogonal_col_sum_sq hQ j]
  simp

end HadamardMultibase
