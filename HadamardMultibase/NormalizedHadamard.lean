module

public import HadamardMultibase.Basic
public import HadamardMultibase.SubmatrixFlatness
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

namespace HadamardMultibase

open Matrix

noncomputable def normalizedHadamard {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℤ) : Matrix ι ι ℝ :=
  (Real.sqrt (Fintype.card ι : ℝ))⁻¹ • H.map (Int.castRingHom ℝ)

theorem normalizedHadamard_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {H : Matrix ι ι ℤ} (hH : H.IsHadamard) :
    (normalizedHadamard H)ᵀ * normalizedHadamard H = 1 := by
  have hZ : Hᵀ * H = (Fintype.card ι : ℤ) • (1 : Matrix ι ι ℤ) := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hH.conjTranspose_mul
  have hR : (H.map (Int.castRingHom ℝ))ᵀ * H.map (Int.castRingHom ℝ) =
      (Fintype.card ι : ℝ) • (1 : Matrix ι ι ℝ) := by
    ext i j
    have h := congrArg (fun M : Matrix ι ι ℤ => M i j) hZ
    simp only [mul_apply, transpose_apply, Matrix.smul_apply, one_apply, smul_eq_mul,
      Matrix.map_apply, Int.coe_castRingHom] at h ⊢
    exact_mod_cast h
  have hs : 0 < Real.sqrt (Fintype.card ι : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hsq := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ Fintype.card ι)
  have hc : (Real.sqrt (Fintype.card ι : ℝ))⁻¹ *
      ((Real.sqrt (Fintype.card ι : ℝ))⁻¹ * (Fintype.card ι : ℝ)) = 1 := by
    field_simp
    nlinarith
  simp only [normalizedHadamard, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hR, smul_smul]
  rw [hc, one_smul]

theorem normalizedHadamard_abs_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℤ} (hH : H.IsHadamard) (i j : ι) :
    |normalizedHadamard H i j| = 1 / Real.sqrt (Fintype.card ι : ℝ) := by
  rcases Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem i j) with h | h
  · simp [normalizedHadamard, Matrix.map_apply, Matrix.smul_apply, h, abs_of_nonneg (Real.sqrt_nonneg _)]
  · simp [normalizedHadamard, Matrix.map_apply, Matrix.smul_apply, h, abs_of_nonneg (Real.sqrt_nonneg _)]

end HadamardMultibase
