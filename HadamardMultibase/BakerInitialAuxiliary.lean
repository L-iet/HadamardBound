/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerIndexing
public import HadamardMultibase.BakerUniformGrowth

@[expose] public section

/-! # Construction of the initial bounded auxiliary vector

The unknowns run over all block degrees and both frequency indices. The
initial rational equations vanish exactly, and the coefficient bound is
exponential in h with a rate independent of the varying rational slope.
-/

namespace HadamardMultibase

open Filter

theorem bakerInitialHeightRate_nonneg {K L a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    0 ≤ bakerInitialHeightRate K L a b := by
  have hab : (1 : ℝ) ≤ ((a * b : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ a * b by simpa using Nat.mul_le_mul ha hb)
  have hlog := Real.log_nonneg hab
  have hlog2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have hlog4 := Real.log_pos (show (1 : ℝ) < 4 by norm_num)
  unfold bakerInitialHeightRate
  positivity

theorem eventually_kernel_ceiling_height (C : ℝ) (hC : 0 ≤ C) (J : ℕ) :
    ∀ᶠ h : ℕ in atTop, ∀ n : ℕ, n ≤ J * h →
      ((2 * n * ⌈Real.exp (C * h)⌉₊ + 1 : ℕ) : ℝ) ≤ Real.exp ((C + 1) * h) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_nat_const_mul_pow_le_exp (4 * (J : ℝ) + 1) 1
      (show (0 : ℝ) < 1 by norm_num)] with h hh hp
  intro n hn
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hnR : (n : ℝ) ≤ (J : ℝ) * h := by exact_mod_cast hn
  have hexp : 1 ≤ Real.exp (C * h) := Real.one_le_exp (by positivity)
  have hceil : (⌈Real.exp (C * h)⌉₊ : ℝ) ≤ 2 * Real.exp (C * h) := by
    have he := (Nat.ceil_lt_add_one (Real.exp_pos (C * h)).le).le
    linarith
  have hpoly : 4 * (J : ℝ) * h + 1 ≤ Real.exp (h : ℝ) := by
    calc 4 * (J : ℝ) * h + 1 ≤ (4 * (J : ℝ) + 1) * h := by nlinarith
      _ ≤ _ := by simpa only [pow_one, one_mul] using hp
  calc ((2 * n * ⌈Real.exp (C * h)⌉₊ + 1 : ℕ) : ℝ)
      ≤ 4 * (J : ℝ) * h * Real.exp (C * h) + 1 := by push_cast; nlinarith [hceil]
    _ ≤ (4 * (J : ℝ) * h + 1) * Real.exp (C * h) := by nlinarith [hexp]
    _ ≤ Real.exp (h : ℝ) * Real.exp (C * h) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem eventually_exists_initial_baker_auxiliary {K L a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hdim : 2 * K ^ 2 ≤ (L + 1) ^ 3)
    {Γ : ℝ} (hΓ : 1 ≤ Γ) :
    ∀ᶠ h : ℕ in atTop, ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp h →
      ∀ p : ℤ,
      (∀ j : Fin (bakerColumnCount h L),
        |(bakerColumnLam h L j : ℝ) + (bakerColumnMu h L j : ℝ) * p / q| ≤ Γ) →
      ∃ c : Fin (bakerColumnCount h L) → ℤ, c ≠ 0 ∧
        (∀ j, |(c j : ℝ)| ≤ Real.exp ((bakerInitialHeightRate K L a b + 1) * h)) ∧
        ∀ l u v : ℕ, 1 ≤ l → l ≤ h → u < K → v < K →
          bakerIndexedComparison h L u v l p q a b c = 0 := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_bakerComparison_cleared_height (K := K) (L := L) ha hb hΓ,
    eventually_kernel_ceiling_height (bakerInitialHeightRate K L a b)
      (bakerInitialHeightRate_nonneg ha hb) ((L + 1) ^ 3)] with h hh hclear hcoef
  intro q hq hheight p hgamma
  have hhpos : 0 < h := by omega
  let rowEquiv := Fintype.equivFin (BakerRow h K)
  let iu : Fin (bakerRowCount h K) → ℕ := fun r => (rowEquiv.symm r).2.1.val
  let iv : Fin (bakerRowCount h K) → ℕ := fun r => (rowEquiv.symm r).2.2.val
  let il : Fin (bakerRowCount h K) → ℕ := fun r => (rowEquiv.symm r).1.val + 1
  let M : ℕ := ⌈Real.exp (bakerInitialHeightRate K L a b * h)⌉₊
  have hcols : bakerColumnCount h L ≤ (L + 1) ^ 3 * h := by
    rw [bakerColumnCount_eq, Nat.mul_comm]
  have hpos : 0 < bakerColumnCount h L := by rw [bakerColumnCount_eq]; positivity
  have hmn : 2 * bakerRowCount h K ≤ bakerColumnCount h L := by
    rw [bakerRowCount_eq, bakerColumnCount_eq]
    have he := Nat.mul_le_mul_left h hdim
    nlinarith [he]
  have hmatrix (r : Fin (bakerRowCount h K)) (j : Fin (bakerColumnCount h L)) :
      |((Nat.lcmUpto h ^ iu r * q ^ iv r : ℕ) : ℚ) *
        bakerComparisonValue h (bakerColumnDegree h L j) (iu r) (iv r) (il r)
          (bakerColumnLam h L j) (bakerColumnMu h L j) p q a b| ≤ (M : ℚ) := by
    have hilu : il r ≤ h := by have he := (rowEquiv.symm r).1.isLt; dsimp [il]; omega
    have hiu : iu r ≤ K := by have he := (rowEquiv.symm r).2.1.isLt; dsimp [iu]; omega
    have hiv : iv r ≤ K := by have he := (rowEquiv.symm r).2.2.isLt; dsimp [iv]; omega
    have he := hclear q hheight (bakerColumnDegree h L j) (il r) (iu r) (iv r)
      (bakerColumnLam h L j) (bakerColumnMu h L j) (bakerColumnDegree_lt h L j) hilu
      hiu hiv (bakerColumnLam_le h L j) (bakerColumnMu_le h L j) p (hgamma j)
    have he' := he.trans (Nat.le_ceil (Real.exp (bakerInitialHeightRate K L a b * h)))
    exact_mod_cast he'
  obtain ⟨c, hc, hbound, hzero⟩ := exists_bounded_baker_comparison_kernel hhpos hq hpos hmn
    (bakerColumnDegree h L) (bakerColumnLam h L) (bakerColumnMu h L) iu iv il p a b hmatrix
  refine ⟨c, hc, ?_, ?_⟩
  · intro j
    have hj : |(c j : ℝ)| ≤ ((2 * bakerColumnCount h L * M + 1 : ℕ) : ℝ) := by
      exact_mod_cast hbound j
    exact hj.trans (hcoef _ hcols)
  · intro l u v hl hlh hu hv
    let r : BakerRow h K := (⟨l - 1, by omega⟩, ⟨u, hu⟩, ⟨v, hv⟩)
    have he := hzero (rowEquiv r)
    have hlprev : l - 1 + 1 = l := by omega
    simpa [bakerIndexedComparison, iu, iv, il, r, hlprev] using he

end HadamardMultibase
