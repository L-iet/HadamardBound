module

public import HadamardMultibase.CraigenBlock

@[expose] public section

namespace HadamardMultibase

open Matrix

/-- A real signed permutation matrix, recorded by its row permutation and signs. -/
def IsSignedPermutation {ι : Type*} [DecidableEq ι] (A : Matrix ι ι ℤ) : Prop :=
  ∃ e : Equiv.Perm ι, ∃ ε : ι → ℤ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
    ∀ i j, A i j = if e i = j then ε i else 0

theorem IsSignedPermutation.neg {ι : Type*} [DecidableEq ι] {A : Matrix ι ι ℤ}
    (hA : IsSignedPermutation A) : IsSignedPermutation (-A) := by
  obtain ⟨e, ε, hε, hA⟩ := hA
  refine ⟨e, -ε, ?_, ?_⟩
  · intro i
    obtain h | h := hε i <;> simp [h]
  · intro i j
    simp only [Matrix.neg_apply, hA]
    split_ifs <;> simp

theorem IsSignedPermutation.transpose {ι : Type*} [DecidableEq ι] {A : Matrix ι ι ℤ}
    (hA : IsSignedPermutation A) : IsSignedPermutation Aᵀ := by
  obtain ⟨e, ε, hε, hA⟩ := hA
  refine ⟨e.symm, fun i => ε (e.symm i), fun i => hε _, ?_⟩
  intro i j
  by_cases h : e.symm i = j
  · subst j
    simp [Matrix.transpose_apply, hA]
  · have he : e j ≠ i := by
      intro he
      apply h
      simpa using (congrArg e.symm he).symm
    simp [Matrix.transpose_apply, hA, h, he]

theorem IsSignedPermutation.conjTranspose {ι : Type*} [DecidableEq ι] {A : Matrix ι ι ℤ}
    (hA : IsSignedPermutation A) : IsSignedPermutation Aᴴ := by
  simpa using hA.transpose

theorem signedPermutation_one (ι : Type*) [DecidableEq ι] :
    IsSignedPermutation (1 : Matrix ι ι ℤ) := by
  refine ⟨Equiv.refl ι, fun _ => 1, fun _ => Or.inl rfl, ?_⟩
  intro i j
  simp only [Matrix.one_apply, Equiv.refl_apply]
  split_ifs <;> simp_all

theorem IsSignedPermutation.mul {ι : Type*} [DecidableEq ι] [Fintype ι] {A B : Matrix ι ι ℤ}
    (hA : IsSignedPermutation A) (hB : IsSignedPermutation B) :
    IsSignedPermutation (A * B) := by
  classical
  obtain ⟨e, ε, hε, hA⟩ := hA
  obtain ⟨f, η, hη, hB⟩ := hB
  refine ⟨e.trans f, fun i => ε i * η (e i), ?_, ?_⟩
  · intro i
    obtain he | he := hε i <;> obtain hf | hf := hη (e i) <;> simp [he, hf]
  · intro i j
    simp only [Matrix.mul_apply, hA, ite_mul, zero_mul]
    simp [hB, mul_ite]
    rfl

theorem IsSignedPermutation.blockDiagonal {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {A : Matrix ι ι ℤ} {B : Matrix κ κ ℤ}
    (hA : IsSignedPermutation A) (hB : IsSignedPermutation B) :
    IsSignedPermutation (Matrix.fromBlocks A 0 0 B) := by
  obtain ⟨e, ε, hε, hA⟩ := hA
  obtain ⟨f, η, hη, hB⟩ := hB
  refine ⟨Equiv.sumCongr e f, Sum.elim ε η, ?_, ?_⟩
  · intro i
    cases i with
    | inl i => exact hε i
    | inr i => exact hη i
  · intro i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, hA, hB]

theorem IsSignedPermutation.blockAntiDiagonal {ι : Type*} [DecidableEq ι]
    {A B : Matrix ι ι ℤ}
    (hA : IsSignedPermutation A) (hB : IsSignedPermutation B) :
    IsSignedPermutation (Matrix.fromBlocks (0 : Matrix ι ι ℤ) A B 0) := by
  obtain ⟨e, ε, hε, hA⟩ := hA
  obtain ⟨f, η, hη, hB⟩ := hB
  refine ⟨(Equiv.sumCongr e f).trans (Equiv.sumComm ι ι), Sum.elim ε η, ?_, ?_⟩
  · intro i
    cases i with
    | inl i => exact hε i
    | inr i => exact hη i
  · intro i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks, hA, hB, Equiv.sumComm_apply]

theorem IsSignedPermutation.ne_zero {ι : Type*} [DecidableEq ι] [Nonempty ι] {A : Matrix ι ι ℤ}
    (hA : IsSignedPermutation A) : A ≠ 0 := by
  obtain ⟨e, ε, hε, hA⟩ := hA
  intro hzero
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hi : ε i = 0 := by simpa [hA] using congrArg (fun M : Matrix ι ι ℤ => M i (e i)) hzero
  obtain h | h := hε i <;> omega

theorem IsSignedPermutation.mul_conjTranspose {ι : Type*} [DecidableEq ι] [Fintype ι]
    {A : Matrix ι ι ℤ} (hA : IsSignedPermutation A) : A * Aᴴ = 1 := by
  obtain ⟨e, ε, hε, hA⟩ := hA
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, hA]
  simp only [ite_mul, zero_mul]
  by_cases hij : i = j
  · subst j
    obtain h | h := hε i <;> simp [h]
  · have he : e j ≠ e i := fun h => hij (e.injective h).symm
    simp [he, hij]

/-- Multiplying a binary matrix by a signed permutation only permutes/negates rows. -/
theorem IsSignedPermutation.binary_mul {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype ι]
    {A : Matrix ι ι ℤ} (hA : IsSignedPermutation A) (H : Matrix ι κ ℤ)
    (hH : ∀ i j, H i j = 1 ∨ H i j = -1) :
    ∀ i j, (A * H) i j = 1 ∨ (A * H) i j = -1 := by
  classical
  obtain ⟨e, ε, hε, hA⟩ := hA
  intro i j
  have hentry : (A * H) i j = ε i * H (e i) j := by
    simp [Matrix.mul_apply, hA, ite_mul]
  rw [hentry]
  obtain he | he := hε i <;> obtain hh | hh := hH (e i) j <;> simp [he, hh]

end HadamardMultibase
