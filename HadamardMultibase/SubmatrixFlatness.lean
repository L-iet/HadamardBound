module

public import HadamardMultibase.SubmatrixOrthogonalization
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

namespace HadamardMultibase

open Matrix
open scoped Matrix.Norms.Operator NNReal

theorem abs_matrix_mul_le_of_row_bound
    {ι κ ν : Type*} [Fintype κ]
    {A : Matrix ι κ ℝ} {B : Matrix κ ν ℝ} {a b : ℝ}
    (hb : 0 ≤ b) (hA : ∀ i, ∑ j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b)
    (i : ι) (j : ν) : |(A * B) i j| ≤ a * b := by
  calc
    _ ≤ ∑ k, |A i k * B k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, |A i k| * b := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hB k j) (abs_nonneg _)
    _ = (∑ k, |A i k|) * b := (Finset.sum_mul _ _ _).symm
    _ ≤ a * b := mul_le_mul_of_nonneg_right (hA i) hb

theorem matrix_row_abs_sum_le_norm
    {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) (i : ι) :
    ∑ j, |A i j| ≤ ‖A‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h := Finset.le_sup (f := fun i : ι => ∑ j : κ, ‖A i j‖₊) (Finset.mem_univ i)
  have h' := NNReal.coe_le_coe.mpr h
  simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using h'

theorem matrix_norm_le_of_row_abs_sum
    {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hA : ∀ i, ∑ j, |A i j| ≤ a) : ‖A‖ ≤ a := by
  rw [Matrix.linfty_opNorm_def]
  change (((Finset.univ : Finset ι).sup fun i => ∑ j : κ, ‖A i j‖₊ : ℝ≥0) : ℝ) ≤ a
  suffices h : (Finset.univ : Finset ι).sup (fun i => ∑ j : κ, ‖A i j‖₊) ≤
      (⟨a, ha⟩ : ℝ≥0) by exact_mod_cast h
  apply Finset.sup_le
  intro i _
  apply NNReal.coe_le_coe.mp
  change ((∑ j : κ, ‖A i j‖₊ : ℝ≥0) : ℝ) ≤ a
  simpa only [NNReal.coe_sum, coe_nnnorm, Real.norm_eq_abs] using hA i

/-- The inverse norm estimate follows directly from J = 1 + AJ once
invertibility has been established by the Neumann criterion. -/
theorem matrix_inverse_one_sub_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : ‖A‖ < 1) :
    IsUnit (1 - A) ∧ ‖(1 - A)⁻¹‖ ≤ 1 / (1 - ‖A‖) := by
  have hu := isUnit_one_sub_of_norm_lt_one hA
  refine ⟨hu, ?_⟩
  have heq : (1 - A) * (1 - A)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((1 - A).isUnit_iff_isUnit_det.mp hu)
  have heq' : (1 - A)⁻¹ = 1 + A * (1 - A)⁻¹ := by
    rw [Matrix.sub_mul, Matrix.one_mul] at heq
    calc
      _ = ((1 - A)⁻¹ - A * (1 - A)⁻¹) + A * (1 - A)⁻¹ := by abel
      _ = _ := by rw [heq]
  have hn : ‖(1 - A)⁻¹‖ ≤ 1 + ‖A‖ * ‖(1 - A)⁻¹‖ := by
    calc
      _ = ‖1 + A * (1 - A)⁻¹‖ := congrArg norm heq'
      _ ≤ ‖(1 : Matrix ι ι ℝ)‖ + ‖A * (1 - A)⁻¹‖ := norm_add_le _ _
      _ ≤ 1 + ‖A‖ * ‖(1 - A)⁻¹‖ := by rw [norm_one]; gcongr; exact norm_mul_le _ _
  apply (le_div_iff₀ (by linarith : 0 < 1 - ‖A‖)).mpr
  nlinarith

/-- Flatness after removing a small block. This strengthens the Hadamard
specialization: only orthogonality and a common bound on entries are needed. -/
theorem submatrix_flatness
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [Nonempty ι]
    (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) (C : Matrix κ ι ℝ) (D : Matrix κ κ ℝ)
    (horth : (fromBlocks A B C D)ᵀ * fromBlocks A B C D = 1)
    {s : ℝ} (hs : 0 < s) (hk : (Fintype.card ι : ℝ) < s)
    (hA : ∀ i j, |A i j| ≤ 1 / s) (hB : ∀ i j, |B i j| ≤ 1 / s)
    (hC : ∀ i j, |C i j| ≤ 1 / s) (hD : ∀ i j, |D i j| ≤ 1 / s) :
    ∃ M : Matrix κ κ ℝ, Mᵀ * M = 1 ∧
      ∀ i j, |M i j| ≤ 1 / (s - Fintype.card ι) := by
  let k : ℝ := Fintype.card ι
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hratio : k / s < 1 := (div_lt_one hs).mpr hk
  have hrowA : ∀ i, ∑ j, |A i j| ≤ k / s := by
    intro i
    calc
      _ ≤ ∑ j : ι, 1 / s := Finset.sum_le_sum (fun j _ => hA i j)
      _ = _ := by simp [k, div_eq_mul_inv]
  have hnormA : ‖A‖ ≤ k / s := matrix_norm_le_of_row_abs_sum A (by positivity) hrowA
  obtain ⟨hinv, hnormJ⟩ := matrix_inverse_one_sub_norm_le A (hnormA.trans_lt hratio)
  have hJ : ‖(1 - A)⁻¹‖ ≤ 1 / (1 - k / s) := by
    exact hnormJ.trans (one_div_le_one_div_of_le (by linarith) (by linarith))
  have hJB : ∀ i j, |((1 - A)⁻¹ * B) i j| ≤ ‖(1 - A)⁻¹‖ * (1 / s) := by
    intro i j
    exact abs_matrix_mul_le_of_row_bound (by positivity)
      (matrix_row_abs_sum_le_norm _) hB i j
  have hrowC : ∀ i, ∑ j, |C i j| ≤ k / s := by
    intro i
    calc
      _ ≤ ∑ j : ι, 1 / s := Finset.sum_le_sum (fun j _ => hC i j)
      _ = _ := by simp [k, div_eq_mul_inv]
  refine ⟨D + C * (1 - A)⁻¹ * B, submatrix_orthogonalization A B C D horth hinv, ?_⟩
  intro i j
  have hcorr : |(C * (1 - A)⁻¹ * B) i j| ≤
      (k / s) * (‖(1 - A)⁻¹‖ * (1 / s)) := by
    rw [Matrix.mul_assoc]
    exact abs_matrix_mul_le_of_row_bound (by positivity) hrowC hJB i j
  calc
    _ ≤ |D i j| + |(C * (1 - A)⁻¹ * B) i j| := abs_add_le _ _
    _ ≤ 1 / s + (k / s) * (‖(1 - A)⁻¹‖ * (1 / s)) := add_le_add (hD i j) hcorr
    _ ≤ 1 / s + (k / s) * ((1 / (1 - k / s)) * (1 / s)) := by gcongr
    _ = 1 / (s - k) := by
      have hsk : s - k ≠ 0 := by linarith
      have hr : 1 - k / s ≠ 0 := by linarith
      field_simp
      ring

end HadamardMultibase
