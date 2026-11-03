module

public import HadamardMultibase.RotationMesh

@[expose] public section

namespace HadamardMultibase

/-- A polynomial lower bound on nonzero integer linear forms in `1, α`.
For logarithms of algebraic numbers this is a consequence of a quantitative
linear-forms theorem; it is an explicit hypothesis here, not an axiom. -/
def PolynomialRotationSeparation (α : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ ν : ℕ, ∀ k : ℕ, 0 < k → ∀ j : ℤ,
    c ≤ |(k : ℝ) * α - (j : ℝ)| * (k : ℝ) ^ ν

/-- Dirichlet's theorem and a polynomial separation bound give a one-sided
mesh with a polynomially bounded index. This avoids discrepancy theory. -/
theorem quantitative_rotation_mesh {α c : ℝ} {ν : ℕ} (hc : 0 < c)
    (hsep : ∀ k : ℕ, 0 < k → ∀ j : ℤ,
      c ≤ |(k : ℝ) * α - (j : ℝ)| * (k : ℝ) ^ ν)
    {Q : ℕ} (hQ : 0 < Q) {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    ∃ m : ℕ, ∃ z : ℤ,
      (m : ℝ) ≤ (Q : ℝ) ^ (ν + 1) / c ∧
      0 ≤ (m : ℝ) * α + (z : ℝ) ∧
      x - 1 / ((Q : ℝ) + 1) ≤ (m : ℝ) * α + (z : ℝ) ∧
      (m : ℝ) * α + (z : ℝ) ≤ x := by
  obtain ⟨k, hk, hkQ, hreturn⟩ := Real.exists_nat_abs_mul_sub_round_le α hQ
  let j : ℤ := round ((k : ℝ) * α)
  have hsepK := hsep k hk j
  have hd : (k : ℝ) * α - (j : ℝ) ≠ 0 := by
    intro heq
    rw [heq, abs_zero, zero_mul] at hsepK
    linarith
  obtain ⟨m, z, hindex, hy0, hyl, hyu⟩ := rotation_mesh_of_small_return hd hx hx1
  have hkQR : (k : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hkQ
  have hpow : (k : ℝ) ^ ν ≤ (Q : ℝ) ^ ν := by gcongr
  have hsepQ : c ≤ |(k : ℝ) * α - (j : ℝ)| * (Q : ℝ) ^ ν :=
    hsepK.trans (mul_le_mul_of_nonneg_left hpow (abs_nonneg _))
  have hm₁ := mul_le_mul_of_nonneg_left hsepQ (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hm₂ := mul_le_mul_of_nonneg_right (hindex.trans hkQR)
    (show (0 : ℝ) ≤ (Q : ℝ) ^ ν by positivity)
  have hm : (m : ℝ) * c ≤ (Q : ℝ) ^ (ν + 1) := by
    calc
      (m : ℝ) * c ≤ ((m : ℝ) * |(k : ℝ) * α - (j : ℝ)|) * (Q : ℝ) ^ ν := by
        simpa only [mul_assoc] using hm₁
      _ ≤ (Q : ℝ) * (Q : ℝ) ^ ν := hm₂
      _ = (Q : ℝ) ^ (ν + 1) := by rw [pow_succ]; ring
  refine ⟨m, z, (le_div_iff₀ hc).mpr hm, hy0, ?_, hyu⟩
  change |(k : ℝ) * α - (j : ℝ)| ≤ 1 / ((Q : ℝ) + 1) at hreturn
  linarith

/-- Lift the fractional mesh to nonnegative combinations of two positive
generators. The size condition ensures that the integer coefficient is natural. -/
theorem nonnegative_log_mesh {α c : ℝ} {ν : ℕ} (hα : 0 < α) (hc : 0 < c)
    (hsep : ∀ k : ℕ, 0 < k → ∀ j : ℤ,
      c ≤ |(k : ℝ) * α - (j : ℝ)| * (k : ℝ) ^ ν)
    {Q : ℕ} (hQ : 0 < Q) {t : ℝ}
    (ht : 1 + α * ((Q : ℝ) ^ (ν + 1) / c) ≤ t) :
    ∃ l m : ℕ, t - 1 / ((Q : ℝ) + 1) ≤ (l : ℝ) + (m : ℝ) * α ∧
      (l : ℝ) + (m : ℝ) * α ≤ t := by
  obtain ⟨m, z, hm, hy0, hyl, hyu⟩ :=
    quantitative_rotation_mesh hc hsep hQ (Int.fract_nonneg t) (Int.fract_lt_one t)
  have hmα := mul_le_mul_of_nonneg_right hm hα.le
  have hfloor := Int.lt_floor_add_one t
  have hnonnegR : (0 : ℝ) ≤ (⌊t⌋ : ℤ) + (z : ℝ) := by
    linarith
  have hnonneg : (0 : ℤ) ≤ ⌊t⌋ + z := by exact_mod_cast hnonnegR
  let l := (⌊t⌋ + z).toNat
  have hl : (l : ℝ) = (⌊t⌋ : ℤ) + (z : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hnonneg)
  refine ⟨l, m, ?_, ?_⟩
  · rw [hl]
    change t - (⌊t⌋ : ℤ) - 1 / ((Q : ℝ) + 1) ≤ (m : ℝ) * α + (z : ℝ) at hyl
    linarith
  · rw [hl]
    change (m : ℝ) * α + (z : ℝ) ≤ t - (⌊t⌋ : ℤ) at hyu
    linarith

end HadamardMultibase
