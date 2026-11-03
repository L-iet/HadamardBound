module

public import HadamardMultibase.Asymptotics

@[expose] public section

namespace HadamardMultibase

/-- Every starting point up to x has a Hadamard order in the next d positions.
This avoids needing an enumeration of all Hadamard orders. -/
def HadamardGapBound (x d : ℕ) : Prop :=
  ∀ y : ℕ, y ≤ x → ∃ h : ℕ, HadamardOrder h ∧ y < h ∧ h ≤ y + d

theorem exists_odd_grid_point (d y : ℕ) (hd : 0 < d) :
    ∃ q : ℕ, Odd q ∧ y < d * q ∧ d * q ≤ y + 2 * d ∧ q ≤ y + 2 := by
  let k := y / d
  let q := k + 1 + k % 2
  have hk : d * k ≤ y := Nat.mul_div_le y d
  have hy : y < d * k + d := by
    have hmod := Nat.mod_lt y hd
    have hdiv := Nat.mod_add_div y d
    dsimp [k]
    nlinarith
  have hmod₂ := Nat.mod_lt k (by omega : 0 < 2)
  have hdiv₂ := Nat.mod_add_div k 2
  have hq : k + 1 ≤ q ∧ q ≤ k + 2 := by dsimp [q]; omega
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · refine ⟨k / 2 + k % 2, ?_⟩
    dsimp [q]
    omega
  · nlinarith
  · nlinarith
  · have hky : k ≤ y := Nat.div_le_self y d
    omega

/-- The finite grid argument behind the gap theorem. -/
theorem gapBound_of_uniform_exponent {x T : ℕ} (hx : 2 ≤ x)
    (hT : ∀ q : ℕ, Odd q → q ≤ 2 * x → HadamardOrder (2 ^ T * q)) :
    HadamardGapBound x (2 ^ (T + 1)) := by
  intro y hy
  obtain ⟨q, hq, hlow, hupp, hqy⟩ :=
    exists_odd_grid_point (2 ^ T) y (by positivity)
  refine ⟨2 ^ T * q, hT q hq (by omega), hlow, ?_⟩
  simpa [pow_succ, mul_comm] using hupp

/-- Consecutive-order gaps satisfy any pointwise gap bound at their left endpoint. -/
theorem consecutive_gap_le {x d a b : ℕ} (hgap : HadamardGapBound x d)
    (ha : a ≤ x) (hconsecutive : ∀ h : ℕ, HadamardOrder h → a < h → b ≤ h) :
    b ≤ a + d := by
  obtain ⟨h, hh, hah, hhd⟩ := hgap a ha
  exact (hconsecutive h hh hah).trans hhd

/-- Absorb all small odd multipliers into a finite maximum, and use a common
exponent for every odd multiplier below x. -/
theorem uniform_exponent_bound_of_inputs (hG : GolayFamily) (hC : CraigenTransfer)
    (hS : SparseRepresentationBound) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      ∃ T : ℕ, (T : ℝ) ≤ C * logScale x ∧
        ∀ q : ℕ, Odd q → q ≤ x → HadamardOrder (2 ^ T * q) := by
  classical
  obtain ⟨C, hCpos, N₁, hmain⟩ := main_bound_of_inputs hG hC hS
  obtain ⟨N₂, hlog⟩ := Filter.eventually_atTop.mp eventually_logScale_threshold
  let N := max N₁ (max N₂ 3)
  let B := (Finset.range N).sup (fun q =>
    if h : Odd q then tau q (hasExponent_odd hC h) else 0)
  refine ⟨B + C + 1, by positivity, N, ?_⟩
  intro x hx
  have hNx : N₂ ≤ x := by dsimp [N] at hx; omega
  have hxlog := hlog x hNx
  have hxscale : 1 ≤ logScale x := one_le_logScaleReal hxlog
  have hscale0 : 0 ≤ logScale x := by linarith
  let T := max B ⌈C * logScale x⌉₊
  have hceil : (⌈C * logScale x⌉₊ : ℝ) ≤ C * logScale x + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hCpos.le hscale0)).le
  refine ⟨T, ?_, ?_⟩
  · dsimp [T]
    rw [Nat.cast_max]
    apply max_le
    · nlinarith [show (0 : ℝ) ≤ B by positivity]
    · nlinarith
  · intro q hodd hqx
    apply hadamardOrder_atExponent_ge (hasExponent_odd hC hodd)
    by_cases hqN : q < N
    · have hB : tau q (hasExponent_odd hC hodd) ≤ B := by
        have h := Finset.le_sup (f := fun q =>
          if h : Odd q then tau q (hasExponent_odd hC h) else 0) (Finset.mem_range.mpr hqN)
        simpa only [dite_eq_left hodd] using h
      exact hB.trans (le_max_left _ _)
    · have hqN₁ : N₁ ≤ q := by dsimp [N] at hqN; omega
      have hqN₂ : N₂ ≤ q := by dsimp [N] at hqN; omega
      have hqpos : (0 : ℝ) < q := by dsimp [N] at hqN; exact_mod_cast (by omega : 0 < q)
      have hscale : logScale q ≤ logScale x :=
        logScaleReal_mono hqpos (hlog q hqN₂) (by exact_mod_cast hqx)
      obtain ⟨t, ht, htb⟩ := hmain q hqN₁ hodd
      have htau : (tau q (hasExponent_odd hC hodd) : ℝ) ≤ C * logScale x := by
        have hle : (tau q (hasExponent_odd hC hodd) : ℝ) ≤ t := by
          exact_mod_cast tau_le (hasExponent_odd hC hodd) ht
        nlinarith
      have hceil_lower : C * logScale x ≤ (⌈C * logScale x⌉₊ : ℝ) := Nat.le_ceil _
      have hnat : tau q (hasExponent_odd hC hodd) ≤ ⌈C * logScale x⌉₊ := by
        exact_mod_cast htau.trans hceil_lower
      exact hnat.trans (le_max_right _ _)

theorem logScale_double_le {x : ℕ} (hx : 2 ≤ x)
    (hlog : Real.exp 1 ≤ Real.log (x : ℝ)) : logScale (2 * x) ≤ 2 * logScale x := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hx₂ : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  have hlogpos : 0 < Real.log (x : ℝ) := by linarith
  have hden : 0 < Real.log (Real.log (x : ℝ)) := Real.log_pos (by linarith)
  have hlogmul : Real.log (2 * (x : ℝ)) = Real.log 2 + Real.log x :=
    Real.log_mul (by norm_num) hxpos.ne'
  have hlog₂ : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog₂x : Real.log 2 ≤ Real.log (x : ℝ) := Real.log_le_log (by norm_num) hx₂
  have hdenle : Real.log (Real.log (x : ℝ)) ≤ Real.log (Real.log (2 * (x : ℝ))) :=
    Real.log_le_log hlogpos (by linarith)
  change Real.log ((2 * x : ℕ) : ℝ) / Real.log (Real.log ((2 * x : ℕ) : ℝ)) ≤ _
  push_cast
  calc
    _ ≤ Real.log (2 * (x : ℝ)) / Real.log (Real.log (x : ℝ)) :=
      div_le_div_of_nonneg_left (by linarith) hden hdenle
    _ ≤ (2 * Real.log (x : ℝ)) / Real.log (Real.log (x : ℝ)) :=
      div_le_div_of_nonneg_right (by linarith) hden.le
    _ = _ := by unfold logScale; ring

/-- The manuscript's quantitative gap rate. The two deep external ingredients
remain hypotheses; uniformization and the grid/analytic deduction are proved. -/
theorem quantitative_gap_bound_of_inputs (hG : GolayFamily) (hC : CraigenTransfer)
    (hS : SparseRepresentationBound) :
    ∃ D : ℝ, 0 < D ∧ ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      ∃ d : ℕ, HadamardGapBound x d ∧ (d : ℝ) ≤ Real.exp (D * logScale x) := by
  obtain ⟨C, hCpos, N₁, huniform⟩ := uniform_exponent_bound_of_inputs hG hC hS
  obtain ⟨N₂, hlog⟩ := Filter.eventually_atTop.mp eventually_logScale_threshold
  have hlog₂ : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  refine ⟨(2 * C + 1) * Real.log 2, by positivity, max N₁ (max N₂ 2), ?_⟩
  intro x hx
  have hx₂ : 2 ≤ x := by omega
  have hxlog := hlog x (by omega)
  obtain ⟨T, hT, horders⟩ := huniform (2 * x) (by omega)
  refine ⟨2 ^ (T + 1), gapBound_of_uniform_exponent hx₂ horders, ?_⟩
  have hdouble := logScale_double_le hx₂ hxlog
  have hscale : 1 ≤ logScale x := one_le_logScaleReal hxlog
  have hdouble' := mul_le_mul_of_nonneg_left hdouble hCpos.le
  have htexp : (T : ℝ) + 1 ≤ (2 * C + 1) * logScale x := by nlinarith
  have heq : ((2 ^ (T + 1) : ℕ) : ℝ) = Real.exp (((T + 1 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    push_cast
    rfl
  rw [heq]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right htexp hlog₂.le
  push_cast
  nlinarith

theorem subpolynomial_gap_bound_of_inputs (hG : GolayFamily) (hC : CraigenTransfer)
    (hS : SparseRepresentationBound) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ x : ℕ, N ≤ x →
      ∃ d : ℕ, HadamardGapBound x d ∧ (d : ℝ) ≤ (x : ℝ) ^ ε := by
  obtain ⟨D, hD, N₁, hgap⟩ := quantitative_gap_bound_of_inputs hG hC hS
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, logScale n / Real.log n < ε / D :=
    tendsto_logScale_div_log.eventually (gt_mem_nhds (div_pos hε hD))
  obtain ⟨N₂, hsmall⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨max N₁ (max N₂ 2), ?_⟩
  intro x hx
  obtain ⟨d, hd, hdb⟩ := hgap x (by omega)
  refine ⟨d, hd, hdb.trans ?_⟩
  have hx₂ : 2 ≤ x := by omega
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < x))
  have hs := (div_lt_iff₀ hlogpos).mp (hsmall x (by omega))
  have hscale : D * logScale x ≤ ε * Real.log x := by
    calc
      _ ≤ D * (ε / D * Real.log x) := mul_le_mul_of_nonneg_left hs.le hD.le
      _ = _ := by field_simp
  rw [Real.rpow_def_of_pos hxpos]
  apply Real.exp_le_exp.mpr
  nlinarith

end HadamardMultibase
