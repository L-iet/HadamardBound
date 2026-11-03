module

public import HadamardMultibase.QuantitativeRotation
public import Mathlib.NumberTheory.Transcendental.Liouville.Basic

@[expose] public section

namespace HadamardMultibase

/-- For an irrational number, failure of Liouville approximation provides
the uniform separation required by the rotation argument, including denominator one. -/
theorem polynomialRotationSeparation_of_not_liouville {α : ℝ}
    (hα : Irrational α) (hL : ¬Liouville α) : PolynomialRotationSeparation α := by
  classical
  unfold Liouville at hL
  push Not at hL
  obtain ⟨ν, hν⟩ := hL
  let δ : ℝ := |α - (round α : ℤ)|
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr (hα.ne_int _))
  refine ⟨min 1 δ, lt_min (by norm_num) hδ, ν, ?_⟩
  intro k hk j
  by_cases hk1 : k = 1
  · subst k
    simpa only [Nat.cast_one, one_mul, one_pow, mul_one] using
      (min_le_right (1 : ℝ) δ).trans (round_le α j)
  · have hk2 : 1 < k := by omega
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hpow : (0 : ℝ) < (k : ℝ) ^ ν := by positivity
    have hbad : 1 / (k : ℝ) ^ ν ≤ |α - (j : ℝ) / (k : ℝ)| := by
      exact hν j (k : ℤ) (by exact_mod_cast hk2) (hα.ne_rational j k)
    have hprod : 1 ≤ |α - (j : ℝ) / (k : ℝ)| * (k : ℝ) ^ ν := by
      exact (div_le_iff₀ hpow).mp hbad
    have hscaled := mul_le_mul_of_nonneg_left hprod hkR.le
    have heq : |(k : ℝ) * α - (j : ℝ)| =
        (k : ℝ) * |α - (j : ℝ) / (k : ℝ)| := by
      calc
        _ = |(k : ℝ) * (α - (j : ℝ) / (k : ℝ))| := by
          congr 1
          field_simp
        _ = _ := by rw [abs_mul, abs_of_pos hkR]
    have hkone : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    calc
      min 1 δ ≤ 1 := min_le_left _ _
      _ ≤ (k : ℝ) := hkone
      _ ≤ |(k : ℝ) * α - (j : ℝ)| * (k : ℝ) ^ ν := by
        rw [heq]
        simpa only [mul_one, mul_assoc] using hscaled

theorem PolynomialRotationSeparation.irrational {α : ℝ}
    (h : PolynomialRotationSeparation α) : Irrational α := by
  obtain ⟨c, hc, ν, hsep⟩ := h
  rintro ⟨q, rfl⟩
  have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hzero : (q.den : ℝ) * (q : ℝ) - (q.num : ℝ) = 0 := by
    rw [Rat.cast_def]
    field_simp
    ring
  have hbad := hsep q.den q.pos q.num
  rw [hzero, abs_zero, zero_mul] at hbad
  linarith

theorem PolynomialRotationSeparation.not_liouville {α : ℝ}
    (h : PolynomialRotationSeparation α) : ¬Liouville α := by
  obtain ⟨c, hc, ν, hsep⟩ := h
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / c)
  have htwo : (1 : ℝ) < c * (2 : ℝ) ^ M := by
    have hpow : (M : ℝ) < (2 : ℝ) ^ M := by exact_mod_cast M.lt_two_pow_self
    have h := (div_lt_iff₀ hc).mp (hM.trans hpow)
    nlinarith
  intro hL
  obtain ⟨a, b, hb, _, hsmall⟩ := hL (ν + M + 1)
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hb0 : (0 : ℝ) < b := by linarith
  let k : ℕ := b.toNat
  have hkInt : (k : ℤ) = b := Int.toNat_of_nonneg (by omega)
  have hk : 0 < k := by omega
  have hkR : (k : ℝ) = (b : ℝ) := by exact_mod_cast hkInt
  have hbad := hsep k hk a
  rw [hkR] at hbad
  have heq : |(b : ℝ) * α - (a : ℝ)| = |α - (a : ℝ) / (b : ℝ)| * (b : ℝ) := by
    calc
      _ = |(α - (a : ℝ) / (b : ℝ)) * (b : ℝ)| := by
        congr 1
        field_simp
      _ = _ := by rw [abs_mul, abs_of_pos hb0]
  rw [heq] at hbad
  have hpow : (2 : ℝ) ^ M ≤ (b : ℝ) ^ M := by
    have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast (show (2 : ℤ) ≤ b by omega)
    gcongr
  have hlarge : 1 < c * (b : ℝ) ^ M :=
    htwo.trans_le (mul_le_mul_of_nonneg_left hpow hc.le)
  have hscaled := mul_le_mul_of_nonneg_right hbad (show (0 : ℝ) ≤ (b : ℝ) ^ M by positivity)
  have hsmallprod := (lt_div_iff₀ (show (0 : ℝ) < (b : ℝ) ^ (ν + M + 1) by positivity)).mp hsmall
  have hfactor : (|α - (a : ℝ) / (b : ℝ)| * (b : ℝ) * (b : ℝ) ^ ν) * (b : ℝ) ^ M =
      |α - (a : ℝ) / (b : ℝ)| * (b : ℝ) ^ (ν + M + 1) := by
    rw [pow_add, pow_add, pow_one]
    ring
  rw [← hfactor] at hsmallprod
  linarith

theorem polynomialRotationSeparation_iff {α : ℝ} :
    PolynomialRotationSeparation α ↔ Irrational α ∧ ¬Liouville α :=
  ⟨fun h => ⟨h.irrational, h.not_liouville⟩,
    fun h => polynomialRotationSeparation_of_not_liouville h.1 h.2⟩

end HadamardMultibase
