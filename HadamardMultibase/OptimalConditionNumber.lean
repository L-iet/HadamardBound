module

public import HadamardMultibase.ApproximateHadamard

@[expose] public section

namespace HadamardMultibase

open scoped ENNReal

def SignMatrix (n : ℕ) :=
  {A : Matrix (Fin n) (Fin n) ℝ // ∀ i j, A i j = 1 ∨ A i j = -1}

instance signMatrixNonempty (n : ℕ) : Nonempty (SignMatrix n) :=
  ⟨⟨fun _ _ => 1, fun _ _ => Or.inl rfl⟩⟩

instance signMatrixFinite (n : ℕ) : Finite (SignMatrix n) := by
  classical
  let f : Matrix (Fin n) (Fin n) Bool → SignMatrix n := fun b =>
    ⟨fun i j => if b i j then 1 else -1, by intro i j; cases h : b i j <;> simp [h]⟩
  apply Finite.of_surjective f
  intro A
  refine ⟨fun i j => decide (A.val i j = 1), ?_⟩
  apply Subtype.ext
  ext i j
  rcases A.property i j with h | h <;> norm_num [f, h]

/-- The paper's best sign-matrix condition number, taking values in [1,∞]
for positive orders. The infimum is attained because the sign matrices form
a finite nonempty set. -/
noncomputable def optimalConditionNumber (n : ℕ) : ℝ≥0∞ :=
  ⨅ A : SignMatrix n, matrixConditionNumber A.val

theorem optimalConditionNumber_le (n : ℕ) (A : SignMatrix n) :
    optimalConditionNumber n ≤ matrixConditionNumber A.val := iInf_le _ A

theorem optimalConditionNumber_attained (n : ℕ) :
    ∃ A : SignMatrix n, optimalConditionNumber n = matrixConditionNumber A.val := by
  classical
  let : Fintype (SignMatrix n) := Fintype.ofFinite _
  obtain ⟨A, _, hA⟩ := (Finset.univ : Finset (SignMatrix n)).exists_min_image
    (fun A => matrixConditionNumber A.val) (by simp)
  refine ⟨A, le_antisymm (optimalConditionNumber_le n A) ?_⟩
  exact le_iInf (fun B => hA B (Finset.mem_univ B))

/-- The approximate-Hadamard corollary in the exact κ(n) notation. -/
theorem optimalConditionNumber_bound (hS : SparseRepresentationBound)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      optimalConditionNumber n ≤ ENNReal.ofReal (1 + (n : ℝ) ^ (-1 / 4 + δ)) := by
  obtain ⟨N, hN⟩ := approximateHadamard_condition_bound hS hδ
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨A, hsign, hcond⟩ := hN n hn
  exact (optimalConditionNumber_le n ⟨A, hsign⟩).trans hcond

end HadamardMultibase
