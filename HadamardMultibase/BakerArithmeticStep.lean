/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerUniformPerturbation
public import HadamardMultibase.BakerGridStep
public import HadamardMultibase.BakerUniformGrowth

@[expose] public section

/-! # Exact arithmetic propagation of the vanishing grid -/
namespace HadamardMultibase
open Filter

theorem bakerIndexedMixed_comparison_cast (h L u v l : ℕ) (p : ℤ) (q a b : ℕ)
    (c : Fin (bakerColumnCount h L) → ℤ) :
    ‖bakerIndexedMixed h L u v ((p : ℝ) / q) a c l -
      (((bakerIndexedComparison h L u v l p q a b c : ℚ) : ℝ) : ℂ)‖ =
      |bakerMixedRealValue h u v ((p : ℝ) / q) a c
          (bakerColumnDegree h L) (bakerColumnLam h L) (bakerColumnMu h L) l -
        ∑ j, (c j : ℝ) * ((bakerComparisonValue h (bakerColumnDegree h L j) u v l
          (bakerColumnLam h L j) (bakerColumnMu h L j) p q a b : ℚ) : ℝ)| := by
  unfold bakerIndexedMixed
  rw [show (l : ℂ) = ((l : ℝ) : ℂ) by simp, bakerMixedComplex_eval_real, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  simp only [bakerIndexedComparison, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast]

theorem three_exp_margin {h : ℕ} (hh : 1 ≤ h) (D : ℝ) :
    3 * Real.exp ((-D - 2) * h) < Real.exp (-D * h) := by
  have he : (3 : ℝ) < Real.exp 2 := by
    have hx := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)
    linarith
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have he' : (3 : ℝ) < Real.exp (2 * (h : ℝ)) :=
    he.trans_le (Real.exp_le_exp.mpr (by linarith))
  calc
    _ < Real.exp (2 * (h : ℝ)) * Real.exp ((-D - 2) * h) :=
      mul_lt_mul_of_pos_right he' (Real.exp_pos _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

noncomputable def bakerMixedCircleRate (L w a : ℕ) (Γ C : ℝ) : ℝ :=
  C + 2 * ((L : ℝ) + 1) * Real.log 2 + 1 +
    (((L : ℝ) + 1) * Real.log 2 + Γ * |Real.log a|) * w

noncomputable def bakerComparisonZeroRate (K : ℕ) : ℝ := (Real.log 4 + 5) * K

theorem eventually_baker_comparison_grid_step {L S K k s t w a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hk : 0 < k) (hs : 0 < s)
    (hst : s ≤ t) (htw : t < w) (htS : t ≤ S) (hbudget : 4 * k ≤ K)
    {Γ : ℝ} (hΓ : 1 ≤ Γ) (C A : ℝ)
    (hA : 1 ≤ A)
    (hdata : C + bakerGridEntryRate L S a b + 1 - A + 2 +
      4 * (k : ℝ) * ((t : ℝ) + s) ≤ -bakerComparisonZeroRate K - 2)
    (hcontour : bakerMixedCircleRate L w a Γ C + ((2 * k * s : ℕ) : ℝ) *
      Real.log (((t : ℝ) + s) / ((w : ℝ) - t)) + 1 ≤ -bakerComparisonZeroRate K - 2) :
    ∀ᶠ h : ℕ in atTop, ∀ p : ℤ, ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp h →
      ∀ c : Fin (bakerColumnCount h L) → ℤ,
      (∀ j, |(c j : ℝ)| ≤ Real.exp (C * h)) →
      (∀ j, |(bakerColumnLam h L j : ℝ) + (bakerColumnMu h L j : ℝ) * p / q| ≤ Γ) →
      |((p : ℝ) / q) * Real.log a - Real.log b| ≤ Real.exp (-A * h) →
      (∀ u v : ℕ, u < 4 * k → v < 4 * k → ∀ l : ℕ,
        1 ≤ l → l ≤ s * h → bakerIndexedComparison h L u v l p q a b c = 0) →
      ∀ u v : ℕ, u < k → v < k → ∀ l : ℕ, 1 ≤ l → l ≤ t * h →
        bakerIndexedComparison h L u v l p q a b c = 0 := by
  let E : ℝ := A - (C + bakerGridEntryRate L S a b + 1)
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_baker_grid_perturbation (L := L) (S := S) (K := K) (J := (L + 1)^3)
      ha hb hΓ C,
    eventually_bakerMixed_growth (L := L) (K := K) (J := (L + 1)^3) hΓ a C,
    eventually_bakerMixed_grid_step hk hs hst htw a (bakerMixedCircleRate L w a Γ C) E]
    with h hh hpert hgrowth hstep
  intro p q hq hqheight c hc hgamma hdef hzero u v hu hv l hl hlt
  have hcount : bakerColumnCount h L ≤ (L + 1)^3 * h := by
    rw [bakerColumnCount_eq, Nat.mul_comm]
  have herror (i j x : ℕ) (hj : j ≤ K) (hx : x ≤ S * h) :
      ‖bakerIndexedMixed h L i j ((p : ℝ) / q) a c x -
        (((bakerIndexedComparison h L i j x p q a b c : ℚ) : ℝ) : ℂ)‖ ≤
        Real.exp (-E * h) := by
    rw [bakerIndexedMixed_comparison_cast]
    have he := hpert (bakerColumnCount h L) hcount
      (bakerColumnDegree h L) (bakerColumnLam h L) (bakerColumnMu h L)
      (bakerColumnDegree_lt h L) (bakerColumnLam_le h L) (bakerColumnMu_le h L)
      i j x hj hx p q c hc hgamma A hA hdef
    convert he using 1; congr 1; dsimp [E]; ring
  have hvalues (i j : ℕ) (hi : i < 4 * k) (hj : j < 4 * k)
      (x : ℕ) (hx : 1 ≤ x) (hxs : x ≤ s * h) :
      ‖bakerMixedComplexValue h i j ((p : ℝ) / q) a c
        (bakerColumnDegree h L) (bakerColumnLam h L) (bakerColumnMu h L) x‖ ≤
          Real.exp (-E * h) := by
    have he := herror i j x (by omega)
      (hxs.trans (Nat.mul_le_mul_right h (hst.trans htS)))
    rw [hzero i j hi hj x hx hxs, Rat.cast_zero, Complex.ofReal_zero, sub_zero] at he
    exact he
  have hboundary (i j : ℕ) (hi : i < k) (hj : j < k)
      (z : ℂ) (hz : z ∈ Metric.sphere 0 ((w * h : ℕ) : ℝ)) :
      ‖bakerMixedComplexValue h i j ((p : ℝ) / q) a c
        (bakerColumnDegree h L) (bakerColumnLam h L) (bakerColumnMu h L) z‖ ≤
          Real.exp (bakerMixedCircleRate L w a Γ C * h) := by
    have hnz : ‖z‖ ≤ ((w * h : ℕ) : ℝ) := by
      simpa only [Metric.mem_sphere, dist_zero_right] using (show dist z 0 ≤ _ from le_of_eq hz)
    have he := hgrowth (bakerColumnCount h L) hcount
      (bakerColumnDegree h L) (bakerColumnLam h L) (bakerColumnMu h L)
      (bakerColumnDegree_lt h L) i j (by omega) ((p : ℝ) / q) c hc
      (fun x => by simpa [mul_div_assoc] using hgamma x) w z hnz
    convert he using 1; congr 1; dsimp [bakerMixedCircleRate]; push_cast; ring
  have hlz : ‖(l : ℂ)‖ ≤ ((t * h : ℕ) : ℝ) := by
    rw [Complex.norm_natCast]
    exact_mod_cast hlt
  have hnew := hstep (bakerColumnCount h L) ((p : ℝ) / q) c
    (bakerColumnDegree h L) (bakerColumnLam h L) (bakerColumnMu h L)
    hvalues hboundary u v hu hv (l : ℂ) hlz
  let D := bakerComparisonZeroRate K
  have hr1 : -E + 2 + 4 * (k : ℝ) * ((t : ℝ) + s) ≤ -D - 2 := by
    dsimp [E, D]
    linarith [hdata]
  have hFnorm : ‖bakerIndexedMixed h L u v ((p : ℝ) / q) a c l‖ ≤
      2 * Real.exp ((-D - 2) * h) := by
    apply hnew.trans
    have h1 := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hr1 (Nat.cast_nonneg h))
    have h2 := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcontour (Nat.cast_nonneg h))
    linarith
  have herrnew := herror u v l (by omega)
    (hlt.trans (Nat.mul_le_mul_right h htS))
  have hE : -E ≤ -D - 2 := by
    have hpos : 0 ≤ 2 + 4 * (k : ℝ) * ((t : ℝ) + s) := by positivity
    linarith [hr1]
  have herrornew : ‖bakerIndexedMixed h L u v ((p : ℝ) / q) a c l -
      (((bakerIndexedComparison h L u v l p q a b c : ℚ) : ℝ) : ℂ)‖ ≤
      Real.exp ((-D - 2) * h) :=
    herrnew.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hE (Nat.cast_nonneg h)))
  apply bakerIndexedComparison_eq_zero_of_exp_small (K := K) (by omega) hq hqheight L u v l
    (by omega) (by omega) p a b c
  have hnorm := norm_sub_le (bakerIndexedMixed h L u v ((p : ℝ) / q) a c l)
    (bakerIndexedMixed h L u v ((p : ℝ) / q) a c l -
      (((bakerIndexedComparison h L u v l p q a b c : ℚ) : ℝ) : ℂ))
  simp only [sub_sub_cancel, Complex.norm_real, Real.norm_eq_abs] at hnorm
  have hsum : |((bakerIndexedComparison h L u v l p q a b c : ℚ) : ℝ)| ≤
      3 * Real.exp ((-D - 2) * h) := by linarith
  simpa only [D, bakerComparisonZeroRate, neg_mul] using
    hsum.trans_lt (three_exp_margin hh D)

end HadamardMultibase
