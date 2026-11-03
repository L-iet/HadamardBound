module

public import HadamardMultibase.MomentNormBound
public import HadamardMultibase.SymmetricDilation
public import HadamardMultibase.RoundingVariance
public import Mathlib.Data.Sym.Card

@[expose] public section

namespace HadamardMultibase

open Matrix
open scoped Matrix.Norms.L2Operator

abbrev DilationIndex (n : ℕ) := Fin n ⊕ Fin n

noncomputable def dilationMean {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (u : ℝ) :
    DilationIndex n → DilationIndex n → ℝ
  | Sum.inl _, Sum.inl _ => 1
  | Sum.inr _, Sum.inr _ => 1
  | Sum.inl i, Sum.inr j => Q i j / u
  | Sum.inr j, Sum.inl i => Q i j / u

theorem dilationMean_symmetric {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (u : ℝ)
    (a b : DilationIndex n) : dilationMean Q u a b = dilationMean Q u b a := by
  cases a <;> cases b <;> rfl

noncomputable def dilationPairMean {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (u : ℝ) :
    Sym2 (DilationIndex n) → ℝ :=
  Sym2.lift ⟨dilationMean Q u, dilationMean_symmetric Q u⟩

@[simp] theorem dilationPairMean_mk {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (u : ℝ)
    (a b : DilationIndex n) : dilationPairMean Q u s(a, b) = dilationMean Q u a b := rfl

theorem dilationPairMean_abs_le {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ} {u : ℝ}
    (hu : 0 < u) (hQ : ∀ i j, |Q i j| ≤ u) (a : Sym2 (DilationIndex n)) :
    |dilationPairMean Q u a| ≤ 1 := by
  have habs (i j : Fin n) : |Q i j / u| ≤ 1 := by
    rw [abs_div, abs_of_pos hu]
    exact (div_le_one hu).mpr (hQ i j)
  induction a using Sym2.ind with
  | _ a b =>
    rw [dilationPairMean_mk]
    cases a <;> cases b <;> simp [dilationMean, habs]

theorem dilationPairMean_variance_row {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Qᵀ * Q = 1) (u : ℝ) (a : DilationIndex n) :
    ∑ b : DilationIndex n, (1 - (dilationPairMean Q u s(a, b)) ^ 2) = n - 1 / u ^ 2 := by
  cases a with
  | inl i => simpa [Fintype.sum_sum_type, dilationMean] using rounding_row_variance hQ u i
  | inr j => simpa [Fintype.sum_sum_type, dilationMean] using rounding_col_variance hQ u j

def dilationMask {n : ℕ} : Matrix (DilationIndex n) (DilationIndex n) ℝ
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => 0
  | Sum.inl _, Sum.inr _ => 1
  | Sum.inr _, Sum.inl _ => 1

def dilationRoundedMatrix {n : ℕ} (ω : Sym2 (DilationIndex n) → Bool) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => roundingSign (ω s(Sum.inl i, Sum.inr j))

theorem dilationRoundedMatrix_sign {n : ℕ} (ω : Sym2 (DilationIndex n) → Bool) (i j : Fin n) :
    dilationRoundedMatrix ω i j = 1 ∨ dilationRoundedMatrix ω i j = -1 := by
  cases h : ω s(Sum.inl i, Sum.inr j) <;> simp [dilationRoundedMatrix, roundingSign, h]

theorem centeredLabelMatrix_dilation {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (u : ℝ)
    (ω : Sym2 (DilationIndex n) → Bool) :
    centeredLabelMatrix (dilationPairMean Q u) Sym2.mk dilationMask ω =
      symmetricDilation (dilationRoundedMatrix ω - u⁻¹ • Q) := by
  ext a b
  cases a <;> cases b <;>
    simp [centeredLabelMatrix, dilationMean, dilationMask, symmetricDilation,
      dilationRoundedMatrix, Matrix.smul_apply, div_eq_mul_inv, mul_comm, Sym2.eq_swap]

/-- Rounding a flat orthogonal matrix to signs with an explicitly controlled
Euclidean operator-norm error. -/
theorem exists_sign_rounding_error_bound {n : ℕ} (hn : 0 < n)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ * Q = 1)
    {u : ℝ} (hu : 0 < u) (hentry : ∀ i j, |Q i j| ≤ u) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, (∀ i j, A i j = 1 ∨ A i j = -1) ∧
      ‖A - u⁻¹ • Q‖ ≤ 4 * (2 * (concentrationMomentOrder (2 * n) : ℝ) + 1) *
        Real.sqrt (max 1 ((n : ℝ) - 1 / u ^ 2)) := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hlabel : ∀ a b c d : DilationIndex n, s(a, b) = s(c, d) →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := fun _ _ _ _ => Sym2.eq_iff.mp
  have hmask (a b : DilationIndex n) : |dilationMask a b| ≤ 1 := by
    cases a <;> cases b <;> norm_num [dilationMask]
  have hsym (ω : Sym2 (DilationIndex n) → Bool) :
      (centeredLabelMatrix (dilationPairMean Q u) Sym2.mk dilationMask ω)ᵀ =
        centeredLabelMatrix (dilationPairMean Q u) Sym2.mk dilationMask ω := by
    rw [centeredLabelMatrix_dilation]
    exact symmetricDilation_transpose _
  obtain ⟨ω, hω⟩ := exists_rounding_norm_bound (V := DilationIndex n) Sym2.mk hlabel
    (dilationPairMean_abs_le hu hentry) (le_max_left 1 ((n : ℝ) - 1 / u ^ 2))
    (fun a => (dilationPairMean_variance_row hQ u a).le.trans (le_max_right _ _))
    dilationMask hmask hsym
  refine ⟨dilationRoundedMatrix ω, dilationRoundedMatrix_sign ω, ?_⟩
  have hcard : Fintype.card (DilationIndex n) = 2 * n := by simp [DilationIndex]; omega
  rw [centeredLabelMatrix_dilation, hcard] at hω
  exact (norm_le_symmetricDilation _).trans hω

end HadamardMultibase
