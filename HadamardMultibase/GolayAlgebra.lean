module

public import HadamardMultibase.GolaySeeds
public import Mathlib.Algebra.Polynomial.Laurent

@[expose] public section

namespace HadamardMultibase

/-- The algebraic identity behind Turyn multiplication. This is independent
of sequence indexing: the involution may be Laurent-polynomial inversion. -/
theorem turyn_numerator_identity {R : Type*} [CommRing R] [StarRing R]
    (a b c d t : R) (ht : t * star t = 1) :
    ((a + b) * c + (a - b) * star d * t) *
        star ((a + b) * c + (a - b) * star d * t) +
      ((a + b) * d - (a - b) * star c * t) *
        star ((a + b) * d - (a - b) * star c * t) =
      2 * (a * star a + b * star b) * (c * star c + d * star d) := by
  simp only [star_add, star_sub, star_mul, star_star]
  calc
    _ = ((a + b) * (star a + star b) +
        (a - b) * (star a - star b) * (t * star t)) *
        (c * star c + d * star d) := by ring
    _ = _ := by rw [ht]; ring

open scoped LaurentPolynomial

/-- Polynomial energy, whose nonconstant coefficients encode correlation. -/
noncomputable def laurentEnergy (p : ℚ[T;T⁻¹]) : ℚ[T;T⁻¹] :=
  p * LaurentPolynomial.invert p

@[simp] theorem laurent_invert_invert (p : ℚ[T;T⁻¹]) :
    LaurentPolynomial.invert (LaurentPolynomial.invert p) = p :=
  LaurentPolynomial.involutive_invert p

/-- Laurent inversion preserves the energy. -/
theorem laurentEnergy_invert (p : ℚ[T;T⁻¹]) :
    laurentEnergy (LaurentPolynomial.invert p) = laurentEnergy p := by
  simp [laurentEnergy, mul_comm]

/-- The reversal shift has energy one, including at length one. -/
theorem laurentEnergy_T (k : ℤ) :
    laurentEnergy (LaurentPolynomial.T k : ℚ[T;T⁻¹]) = 1 := by
  unfold laurentEnergy
  rw [LaurentPolynomial.invert_T, ← LaurentPolynomial.T_add, add_neg_cancel,
    LaurentPolynomial.T_zero]

/-- Energy is multiplicative in the commutative Laurent ring. -/
theorem laurentEnergy_mul (p q : ℚ[T;T⁻¹]) :
    laurentEnergy (p * q) = laurentEnergy p * laurentEnergy q := by
  simp only [laurentEnergy, map_mul]
  ring

/-- An unnormalized Turyn multiplication identity using Laurent inversion.
Sequence coefficients are divided by two when constructing the binary pair. -/
theorem laurent_turyn_identity (a b c d : ℚ[T;T⁻¹]) (k : ℤ) :
    laurentEnergy ((a + b) * c + (a - b) * LaurentPolynomial.invert d *
        LaurentPolynomial.T k) +
      laurentEnergy ((a + b) * d - (a - b) * LaurentPolynomial.invert c *
        LaurentPolynomial.T k) =
      2 * (laurentEnergy a + laurentEnergy b) *
        (laurentEnergy c + laurentEnergy d) := by
  simp only [laurentEnergy, map_add, map_sub, map_mul,
    laurent_invert_invert, LaurentPolynomial.invert_T]
  have ht : (LaurentPolynomial.T k : ℚ[T;T⁻¹]) * LaurentPolynomial.T (-k) = 1 := by
    rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
  calc
    _ = ((a + b) * (LaurentPolynomial.invert a + LaurentPolynomial.invert b) +
        (a - b) * (LaurentPolynomial.invert a - LaurentPolynomial.invert b) *
        (LaurentPolynomial.T k * LaurentPolynomial.T (-k))) *
        (c * LaurentPolynomial.invert c + d * LaurentPolynomial.invert d) := by ring
    _ = _ := by rw [ht]; ring

/-- Turyn's identity after splitting the first pair into its disjoint halves. -/
theorem laurent_turyn_parts_identity (e f c d : ℚ[T;T⁻¹]) (k : ℤ) :
    laurentEnergy (e * c + f * LaurentPolynomial.invert d * LaurentPolynomial.T k) +
      laurentEnergy (e * d - f * LaurentPolynomial.invert c * LaurentPolynomial.T k) =
      (laurentEnergy e + laurentEnergy f) * (laurentEnergy c + laurentEnergy d) := by
  simp only [laurentEnergy, map_add, map_sub, map_mul,
    laurent_invert_invert, LaurentPolynomial.invert_T]
  have ht : (LaurentPolynomial.T k : ℚ[T;T⁻¹]) * LaurentPolynomial.T (-k) = 1 := by
    rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
  calc
    _ = (e * LaurentPolynomial.invert e +
        f * LaurentPolynomial.invert f * (LaurentPolynomial.T k * LaurentPolynomial.T (-k))) *
        (c * LaurentPolynomial.invert c + d * LaurentPolynomial.invert d) := by ring
    _ = _ := by rw [ht]; ring

end HadamardMultibase
