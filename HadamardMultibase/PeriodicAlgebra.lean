module

public import HadamardMultibase.CraigenHadamard
public import HadamardMultibase.GolayPolynomial
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

@[expose] public section

namespace HadamardMultibase

open Matrix
open scoped LaurentPolynomial

noncomputable def periodicReverse {G : Type*} [AddCommGroup G] :
    AddMonoidAlgebra ℚ G ≃ₐ[ℚ] AddMonoidAlgebra ℚ G :=
  AddMonoidAlgebra.domCongr ℚ ℚ (AddEquiv.neg G)

@[simp] theorem periodicReverse_coeff {G : Type*} [AddCommGroup G]
    (p : AddMonoidAlgebra ℚ G) (x : G) : (periodicReverse p).coeff x = p.coeff (-x) := by
  simp [periodicReverse]

@[simp] theorem periodicReverse_reverse {G : Type*} [AddCommGroup G]
    (p : AddMonoidAlgebra ℚ G) : periodicReverse (periodicReverse p) = p := by
  ext x
  simp

@[simp] theorem periodicReverse_single {G : Type*} [AddCommGroup G] (x : G) (a : ℚ) :
    periodicReverse (AddMonoidAlgebra.single x a) = AddMonoidAlgebra.single (-x) a := by
  simp [periodicReverse]

/-- The regular representation of a finite additive group, as a circulant matrix. -/
noncomputable def periodicMatrix {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G] :
    AddMonoidAlgebra ℚ G →+* Matrix G G ℚ where
  toFun p := circulant (fun x => p.coeff x)
  map_zero' := by ext i j; simp
  map_one' := by
    ext i j
    simp [circulant_apply, Matrix.one_apply, AddMonoidAlgebra.one_def,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, sub_eq_zero, eq_comm]
  map_add' p q := by ext i j; simp
  map_mul' p q := by
    change circulant (fun x => (p * q).coeff x) =
      circulant (fun x => p.coeff x) * circulant (fun x => q.coeff x)
    rw [Matrix.circulant_mul]
    apply congrArg Matrix.circulant
    funext x
    change (p * q).coeff x = ∑ y, p.coeff (x - y) * q.coeff y
    rw [AddMonoidAlgebra.coeff_mul_apply_right]
    simpa only [sub_eq_add_neg] using
      Finsupp.sum_fintype q.coeff (fun y a => p.coeff (x - y) * a) (fun _ => mul_zero _)

theorem periodicMatrix_apply {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (p : AddMonoidAlgebra ℚ G) (i j : G) : periodicMatrix p i j = p.coeff (i - j) := rfl

theorem periodicMatrix_reverse {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (p : AddMonoidAlgebra ℚ G) : periodicMatrix (periodicReverse p) = (periodicMatrix p)ᴴ := by
  ext i j
  simp only [periodicMatrix_apply, periodicReverse_coeff, Matrix.conjTranspose_apply,
    star_trivial, neg_sub]

noncomputable def periodicEmbedding {G : Type*} [AddCommGroup G] (e : ℤ →+ G) :
    ℚ[T;T⁻¹] →+* AddMonoidAlgebra ℚ G := AddMonoidAlgebra.mapDomainRingHom ℚ e

theorem periodicEmbedding_single {G : Type*} [AddCommGroup G] (e : ℤ →+ G) (k : ℤ) (a : ℚ) :
    periodicEmbedding e (AddMonoidAlgebra.single k a) = AddMonoidAlgebra.single (e k) a := by
  change AddMonoidAlgebra.mapDomain e (AddMonoidAlgebra.single k a) = _
  exact AddMonoidAlgebra.mapDomain_single

theorem periodicEmbedding_reverse {G : Type*} [AddCommGroup G] (e : ℤ →+ G) (p : ℚ[T;T⁻¹]) :
    periodicEmbedding e (LaurentPolynomial.invert p) = periodicReverse (periodicEmbedding e p) := by
  have h : ((periodicEmbedding e).comp LaurentPolynomial.invert.toRingHom).toAddMonoidHom =
      (periodicReverse.toRingHom.comp (periodicEmbedding e)).toAddMonoidHom := by
    apply AddMonoidAlgebra.addMonoidHom_ext
    intro k a
    change periodicEmbedding e (LaurentPolynomial.invert (AddMonoidAlgebra.single k a)) =
      periodicReverse (periodicEmbedding e (AddMonoidAlgebra.single k a))
    rw [laurent_invert_single, periodicEmbedding_single, periodicEmbedding_single,
      periodicReverse_single, map_neg]
  exact DFunLike.congr_fun h p

noncomputable def periodicEnergy {G : Type*} [AddCommGroup G]
    (p : AddMonoidAlgebra ℚ G) : AddMonoidAlgebra ℚ G := p * periodicReverse p

theorem IsGolayPair.periodicEnergy_eq {G : Type*} [AddCommGroup G] (e : ℤ →+ G)
    {n : ℕ} {A B : Fin n → ℤ} (h : IsGolayPair A B) :
    periodicEnergy (periodicEmbedding e (sequenceLaurent A)) +
      periodicEnergy (periodicEmbedding e (sequenceLaurent B)) =
      AddMonoidAlgebra.single 0 (2 * n : ℚ) := by
  have hsrc := h.laurentEnergy_eq
  rw [← LaurentPolynomial.single_eq_C] at hsrc
  have hp := congrArg (periodicEmbedding e) hsrc
  simp only [map_add, laurentEnergy, map_mul, periodicEmbedding_reverse,
    periodicEmbedding_single, map_zero] at hp
  exact hp

/-- Reflect-and-swap cancels every cross term between a pair of separated blocks. -/
theorem periodic_reflect_pair_energy {G : Type*} [AddCommGroup G]
    (p q : AddMonoidAlgebra ℚ G) :
    periodicEnergy (p + periodicReverse q) + periodicEnergy (q - periodicReverse p) =
      2 * (periodicEnergy p + periodicEnergy q) := by
  simp only [periodicEnergy, map_add, map_sub, periodicReverse_reverse]
  ring

end HadamardMultibase
