module

public import HadamardMultibase.GolayPolynomial

@[expose] public section

namespace HadamardMultibase

open scoped LaurentPolynomial

theorem sequenceLaurent_add {n : ℕ} (A B : Fin n → ℤ) :
    sequenceLaurent (A + B) = sequenceLaurent A + sequenceLaurent B := by
  simp [sequenceLaurent, AddMonoidAlgebra.single_add, Finset.sum_add_distrib]

theorem sequenceLaurent_sub {n : ℕ} (A B : Fin n → ℤ) :
    sequenceLaurent (A - B) = sequenceLaurent A - sequenceLaurent B := by
  simp [sequenceLaurent, AddMonoidAlgebra.single_sub, Finset.sum_sub_distrib]

theorem sequenceLaurent_double {n : ℕ} (A : Fin n → ℤ) :
    sequenceLaurent (fun i => 2 * A i) = 2 * sequenceLaurent A := by
  have heq : (fun i => 2 * A i) = A + A := by ext i; simp [two_mul]
  rw [heq, sequenceLaurent_add, two_mul]

def reverseSequence {n : ℕ} (A : Fin n → ℤ) : Fin n → ℤ := fun i => A i.rev

theorem sequenceLaurent_reverse {n : ℕ} (A : Fin n → ℤ) :
    sequenceLaurent (reverseSequence A) =
      LaurentPolynomial.invert (sequenceLaurent A) * LaurentPolynomial.T (n - 1 : ℤ) := by
  let e : Fin n ≃ Fin n :=
    { toFun := Fin.rev, invFun := Fin.rev, left_inv := Fin.rev_rev, right_inv := Fin.rev_rev }
  have he := Equiv.sum_comp e
    (fun i : Fin n => (AddMonoidAlgebra.single (i.val : ℤ)
      (reverseSequence A i : ℚ) : ℚ[T;T⁻¹]))
  rw [sequenceLaurent, ← he]
  simp only [sequenceLaurent, map_sum, laurent_invert_single, Finset.sum_mul,
    LaurentPolynomial.T, AddMonoidAlgebra.single_mul_single, mul_one]
  apply Finset.sum_congr rfl
  intro i _
  have hi := i.isLt
  have hindex : ((e i).val : ℤ) = -(i.val : ℤ) + (n - 1 : ℤ) := by
    dsimp [e]
    omega
  have hcoeff : reverseSequence A (e i) = A i := by
    change A i.rev.rev = A i
    rw [Fin.rev_rev]
  rw [hindex, hcoeff]

/-- Substitute T^m for T. -/
noncomputable def laurentDilate (m : ℕ) : ℚ[T;T⁻¹] →+* ℚ[T;T⁻¹] :=
  AddMonoidAlgebra.mapDomainRingHom ℚ
    { toFun := fun k => (m : ℤ) * k
      map_zero' := by simp
      map_add' := by intros; simp [mul_add] }

theorem laurentDilate_single (m : ℕ) (k : ℤ) (a : ℚ) :
    laurentDilate m (AddMonoidAlgebra.single k a) =
      AddMonoidAlgebra.single ((m : ℤ) * k) a := by
  change AddMonoidAlgebra.mapDomain (fun k => (m : ℤ) * k)
    (AddMonoidAlgebra.single k a) = _
  exact AddMonoidAlgebra.mapDomain_single

theorem laurentDilate_C (m : ℕ) (a : ℚ) :
    laurentDilate m (LaurentPolynomial.C a) = LaurentPolynomial.C a := by
  change laurentDilate m (AddMonoidAlgebra.single 0 a) = AddMonoidAlgebra.single 0 a
  rw [laurentDilate_single, mul_zero]

theorem laurentDilate_T (m : ℕ) (k : ℤ) :
    laurentDilate m (LaurentPolynomial.T k) = LaurentPolynomial.T ((m : ℤ) * k) :=
  laurentDilate_single m k 1

theorem laurentDilate_invert (m : ℕ) (p : ℚ[T;T⁻¹]) :
    laurentDilate m (LaurentPolynomial.invert p) =
      LaurentPolynomial.invert (laurentDilate m p) := by
  have h : ((laurentDilate m).comp LaurentPolynomial.invert.toRingHom).toAddMonoidHom =
      (LaurentPolynomial.invert.toRingHom.comp (laurentDilate m)).toAddMonoidHom := by
    apply AddMonoidAlgebra.addMonoidHom_ext
    intro k a
    change laurentDilate m (LaurentPolynomial.invert (AddMonoidAlgebra.single k a)) =
      LaurentPolynomial.invert (laurentDilate m (AddMonoidAlgebra.single k a))
    rw [laurent_invert_single, laurentDilate_single, laurentDilate_single, laurent_invert_single]
    congr 1
    ring
  exact DFunLike.congr_fun h p

theorem laurentEnergy_dilate (m : ℕ) (p : ℚ[T;T⁻¹]) :
    laurentEnergy (laurentDilate m p) = laurentDilate m (laurentEnergy p) := by
  simp [laurentEnergy, map_mul, laurentDilate_invert]

/-- The low digit indexes A; the high digit indexes C. -/
def tensorSequence {m n : ℕ} (A : Fin m → ℤ) (C : Fin n → ℤ) : Fin (n * m) → ℤ :=
  fun k => A (finProdFinEquiv.symm k).2 * C (finProdFinEquiv.symm k).1

private theorem productIndex_val {m n : ℕ} (i : Fin n) (j : Fin m) :
    ((finProdFinEquiv (i, j)).val : ℤ) = (j.val : ℤ) + (m : ℤ) * i.val := by
  change ((j.val + m * i.val : ℕ) : ℤ) = _
  push_cast
  rfl

theorem sequenceLaurent_tensor {m n : ℕ} (A : Fin m → ℤ) (C : Fin n → ℤ) :
    sequenceLaurent (tensorSequence A C) =
      sequenceLaurent A * laurentDilate m (sequenceLaurent C) := by
  have he := Equiv.sum_comp (finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m))
    (fun i : Fin (n * m) => (AddMonoidAlgebra.single (i.val : ℤ)
      (tensorSequence A C i : ℚ) : ℚ[T;T⁻¹]))
  rw [sequenceLaurent, ← he]
  simp only [tensorSequence, Equiv.symm_apply_apply, Fintype.sum_prod_type, productIndex_val,
    Int.cast_mul,
    sequenceLaurent, map_sum, laurentDilate_single, Finset.sum_mul, Finset.mul_sum,
    AddMonoidAlgebra.single_mul_single]

end HadamardMultibase
