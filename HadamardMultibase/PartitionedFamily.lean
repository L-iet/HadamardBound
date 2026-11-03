module

public import HadamardMultibase.PeriodicGolay

@[expose] public section

namespace HadamardMultibase

open Matrix

noncomputable def partitionPolynomial {I D G : Type*} [DecidableEq I] [Fintype D]
    [AddCommGroup G] (owner : D → I) (loc : D ≃ G) (σ : D → ℤ) (i : I) :
    AddMonoidAlgebra ℚ G :=
  ∑ d, if owner d = i then AddMonoidAlgebra.single (loc d) (σ d : ℚ) else 0

def partitionSequence {I D G : Type*} [DecidableEq I]
    (owner : D → I) (loc : D ≃ G) (σ : D → ℤ) (i : I) (x : G) : ℤ :=
  if owner (loc.symm x) = i then σ (loc.symm x) else 0

theorem partitionPolynomial_coeff_at {I D G : Type*} [DecidableEq I] [Fintype D]
    [DecidableEq D] [DecidableEq G] [AddCommGroup G]
    (owner : D → I) (loc : D ≃ G) (σ : D → ℤ) (i : I) (d : D) :
    (partitionPolynomial owner loc σ i).coeff (loc d) =
      if owner d = i then (σ d : ℚ) else 0 := by
  unfold partitionPolynomial
  simp only [AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  rw [Finset.sum_eq_single d]
  · split_ifs <;> simp
  · intro t _ htd
    have hloc : loc t ≠ loc d := fun h => htd (loc.injective h)
    split_ifs <;> simp [hloc]
  · simp

theorem partitionPolynomial_coeff {I D G : Type*} [DecidableEq I] [Fintype D]
    [DecidableEq D] [DecidableEq G] [AddCommGroup G]
    (owner : D → I) (loc : D ≃ G) (σ : D → ℤ) (i : I) (x : G) :
    (partitionPolynomial owner loc σ i).coeff x = (partitionSequence owner loc σ i x : ℚ) := by
  have h := partitionPolynomial_coeff_at owner loc σ i (loc.symm x)
  simpa [partitionSequence, Int.cast_ite] using h

theorem partitionSequence_ternary {I D G : Type*} [DecidableEq I]
    (owner : D → I) (loc : D ≃ G) (σ : D → ℤ) (hσ : ∀ d, σ d = 1 ∨ σ d = -1) :
    ∀ i x, partitionSequence owner loc σ i x = 0 ∨
      partitionSequence owner loc σ i x = 1 ∨ partitionSequence owner loc σ i x = -1 := by
  intro i x
  unfold partitionSequence
  split_ifs
  · exact Or.inr (hσ _)
  · exact Or.inl rfl

theorem partitionSequence_eq_zero {I D G : Type*} [DecidableEq I]
    (owner : D → I) (loc : D ≃ G) (σ : D → ℤ) (hσ : ∀ d, σ d = 1 ∨ σ d = -1)
    (i : I) (x : G) : partitionSequence owner loc σ i x = 0 ↔ owner (loc.symm x) ≠ i := by
  have hne : σ (loc.symm x) ≠ 0 := by obtain h | h := hσ (loc.symm x) <;> omega
  by_cases h : owner (loc.symm x) = i <;> simp [partitionSequence, h, hne]

theorem partitionSequence_full {I D G : Type*} [DecidableEq I]
    (owner : D → I) (loc : D ≃ G) (σ : D → ℤ) (hσ : ∀ d, σ d = 1 ∨ σ d = -1) :
    ∀ x, ∃ i, partitionSequence owner loc σ i x ≠ 0 := by
  intro x
  refine ⟨owner (loc.symm x), ?_⟩
  intro hzero
  exact ((partitionSequence_eq_zero owner loc σ hσ _ x).mp hzero) rfl

theorem partitionSequence_disjoint {I D G : Type*} [DecidableEq I]
    (owner : D → I) (loc : D ≃ G) (σ : D → ℤ) (hσ : ∀ d, σ d = 1 ∨ σ d = -1) :
    ∀ i j, i ≠ j → ∀ x, partitionSequence owner loc σ i x = 0 ∨
      partitionSequence owner loc σ j x = 0 := by
  intro i j hij x
  by_cases h : owner (loc.symm x) = i
  · right
    apply (partitionSequence_eq_zero owner loc σ hσ j x).mpr
    exact fun hj => hij (h.symm.trans hj)
  · exact Or.inl ((partitionSequence_eq_zero owner loc σ hσ i x).mpr h)

theorem partitionSequence_quasisymmetric {I D G : Type*} [DecidableEq I] [Neg G]
    (owner : D → I) (loc : D ≃ G) (σ : D → ℤ) (hσ : ∀ d, σ d = 1 ∨ σ d = -1)
    (mirror : D → D) (howner : ∀ d, owner (mirror d) = owner d)
    (hloc : ∀ d, loc (mirror d) = -(loc d)) :
    ∀ i x, partitionSequence owner loc σ i x = 0 ↔ partitionSequence owner loc σ i (-x) = 0 := by
  intro i x
  rw [partitionSequence_eq_zero owner loc σ hσ, partitionSequence_eq_zero owner loc σ hσ]
  have hinv : loc.symm (-x) = mirror (loc.symm x) := by
    apply loc.injective
    rw [loc.apply_symm_apply, hloc, loc.apply_symm_apply]
  rw [hinv, howner]

theorem partitionSequence_gram {I D G : Type*} [Fintype I] [DecidableEq I]
    [Fintype D] [DecidableEq D] [Fintype G] [DecidableEq G] [AddCommGroup G]
    (owner : D → I) (loc : D ≃ G) (σ : D → ℤ)
    (h : ∑ i, periodicEnergy (partitionPolynomial owner loc σ i) =
      (Fintype.card G : AddMonoidAlgebra ℚ G)) :
    (∑ i, circulant (partitionSequence owner loc σ i) *
      (circulant (partitionSequence owner loc σ i))ᴴ) = (Fintype.card G : Matrix G G ℤ) := by
  have hQ := periodic_gram_sum (partitionPolynomial owner loc σ) h
  ext x y
  have he := congrArg (fun M : Matrix G G ℚ => M x y) hQ
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    periodicMatrix_apply, partitionPolynomial_coeff, Matrix.natCast_apply] at he
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    Matrix.circulant_apply, Matrix.natCast_apply]
  exact_mod_cast he

theorem hadamardOrder_of_partition {I D G : Type*} [Fintype I] [DecidableEq I]
    [Fintype D] [DecidableEq D] [Fintype G] [DecidableEq G] [AddCommGroup G]
    (n : ℕ) (hcard : Fintype.card I = n + 1)
    (owner : D → I) (loc : D ≃ G) (σ : D → ℤ) (hσ : ∀ d, σ d = 1 ∨ σ d = -1)
    (mirror : D → D) (howner : ∀ d, owner (mirror d) = owner d)
    (hloc : ∀ d, loc (mirror d) = -(loc d))
    (henergy : ∑ i, periodicEnergy (partitionPolynomial owner loc σ i) =
      (Fintype.card G : AddMonoidAlgebra ℚ G)) :
    HadamardOrder (Fintype.card G * 2 ^ n) := by
  let e : Fin (n + 1) ≃ I := Fintype.equivOfCardEq (by simp [hcard])
  apply hadamardOrder_of_supplementary_sequences n
    (fun i => partitionSequence owner loc σ (e i))
  · exact fun i => partitionSequence_ternary owner loc σ hσ (e i)
  · exact fun i => partitionSequence_quasisymmetric owner loc σ hσ mirror howner hloc (e i)
  · intro i j hij
    exact partitionSequence_disjoint owner loc σ hσ (e i) (e j) (fun h => hij (e.injective h))
  · intro x
    obtain ⟨i, hi⟩ := partitionSequence_full owner loc σ hσ x
    exact ⟨e.symm i, by simpa using hi⟩
  · have hsum := e.sum_comp (fun i : I =>
      circulant (partitionSequence owner loc σ i) * (circulant (partitionSequence owner loc σ i))ᴴ)
    exact hsum.trans (partitionSequence_gram owner loc σ henergy)

end HadamardMultibase
