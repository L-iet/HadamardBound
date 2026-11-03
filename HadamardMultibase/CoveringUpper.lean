module

public import HadamardMultibase.CoveringEstimates

@[expose] public section

namespace HadamardMultibase

open Filter
open scoped Topology

/-- Rounding an exponential upward costs at most log 2 in its logarithm. -/
theorem log_ceil_exp_bounds {x : ℝ} (hx : 0 ≤ x) :
    x ≤ Real.log (⌈Real.exp x⌉₊ : ℝ) ∧
      Real.log (⌈Real.exp x⌉₊ : ℝ) ≤ x + Real.log 2 := by
  have he : 1 ≤ Real.exp x := Real.one_le_exp_iff.mpr hx
  have hc := Nat.le_ceil (Real.exp x)
  have hround := Nat.ceil_lt_add_one (Real.exp_pos x).le
  constructor
  · simpa using Real.log_le_log (Real.exp_pos x) hc
  · have hle : (⌈Real.exp x⌉₊ : ℝ) ≤ 2 * Real.exp x := by linarith
    have h := Real.log_le_log ((Real.exp_pos x).trans_le hc) hle
    simpa [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero x),
      Real.log_exp, add_comm] using h

/-- Sharp covering upper bound for any finite set of bases at least two.
Independence is unnecessary for this half of the covering theorem. -/
theorem coveringNumber_upper_ceil {r : ℕ} {b : Fin r → ℕ}
    (hb : ∀ i, 2 ≤ b i) (hr : 2 ≤ r) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      coveringNumber (powerMonoid b) m (hasMissing_powerMonoid hb m) ≤
        ⌈Real.exp (((r : ℝ) - 1 + η) * m * Real.log m)⌉₊ := by
  classical
  let A : ℝ := (r : ℝ) - 1 + η
  have hA : 0 < A := by
    dsimp [A]
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    linarith
  let N : ℕ → ℕ := fun m => ⌈Real.exp (A * m * Real.log m)⌉₊
  let C : ℝ := (2 / Real.log 2) ^ r * (A + 1) ^ r
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hcount : ∀ᶠ m : ℕ in atTop,
      ((truncatedMonoid b (N m)).card : ℝ) ≤ C * ((m : ℝ) * Real.log m) ^ r := by
    filter_upwards [hlog, eventually_ge_atTop (1 : ℕ)] with m hlm hm
    change 1 ≤ Real.log (m : ℝ) at hlm
    have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hx : 0 ≤ A * m * Real.log m := by positivity
    have hbounds := log_ceil_exp_bounds hx
    have hlog₂ : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hnlog : Real.log (N m) ≤ (A + 1) * ((m : ℝ) * Real.log m) := by
      change Real.log (⌈Real.exp (A * m * Real.log m)⌉₊ : ℝ) ≤ _
      nlinarith [hbounds.2]
    have hn : 2 ≤ N m := by
      have hexp : 1 < Real.exp (A * m * Real.log m) :=
        Real.one_lt_exp_iff.mpr (by positivity)
      have hc := Nat.le_ceil (Real.exp (A * m * Real.log m))
      have : (1 : ℝ) < N m := hexp.trans_le hc
      exact_mod_cast this
    calc
      _ ≤ (2 / Real.log 2) ^ r * (Real.log (N m)) ^ r :=
        truncatedMonoid_card_le_log_power hb hn
      _ ≤ (2 / Real.log 2) ^ r * ((A + 1) * ((m : ℝ) * Real.log m)) ^ r := by
        gcongr
      _ = _ := by dsimp [C]; rw [mul_pow]; ring
  have hentropy := eventually_log_choose_lt (u := fun m => (truncatedMonoid b (N m)).card)
    (by omega : 0 < r) hC (half_pos hη) hcount
  filter_upwards [hentropy, hlog, eventually_ge_atTop (1 : ℕ)] with m hent hlm hm
  change 1 ≤ Real.log (m : ℝ) at hlm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlpos : 0 < Real.log (m : ℝ) := by linarith
  have hbounds := log_ceil_exp_bounds (show 0 ≤ A * m * Real.log m by positivity)
  have hlt : Real.log ((((truncatedMonoid b (N m)).card + m).choose m : ℕ) : ℝ) <
      Real.log (N m) := by
    apply hent.trans
    apply lt_of_lt_of_le _ hbounds.1
    dsimp [A]
    nlinarith [mul_pos hmpos hlpos]
  have hchoosepos : (0 : ℝ) <
      (((truncatedMonoid b (N m)).card + m).choose m : ℕ) := by
    exact_mod_cast Nat.choose_pos (by omega : m ≤ (truncatedMonoid b (N m)).card + m)
  have hnpos : (0 : ℝ) < N m :=
    (Real.exp_pos _).trans_le (Nat.le_ceil _)
  have hnat : ((truncatedMonoid b (N m)).card + m).choose m < N m := by
    exact_mod_cast (Real.log_lt_log_iff hchoosepos hnpos).mp hlt
  obtain ⟨n, hn, hnN, hnot⟩ := exists_missing_powerMonoid_of_count hb hnat
  exact (coveringNumber_le_of_missing _ (by omega) hnot).trans hnN

/-- The upper half of the manuscript's covering theorem, with the o(1)
expressed as an arbitrary positive η. -/
theorem coveringNumber_upper {r : ℕ} {b : Fin r → ℕ}
    (hb : ∀ i, 2 ≤ b i) (hr : 2 ≤ r) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      (coveringNumber (powerMonoid b) m (hasMissing_powerMonoid hb m) : ℝ) ≤
        Real.exp (((r : ℝ) - 1 + η) * m * Real.log m) := by
  have hc := coveringNumber_upper_ceil hb hr (half_pos hη)
  have hl := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (max 1 (2 * Real.log 2 / η))
  filter_upwards [hc, hl, eventually_ge_atTop (1 : ℕ)] with m hcm hlm hm
  change max 1 (2 * Real.log 2 / η) ≤ Real.log (m : ℝ) at hlm
  have hlog : 1 ≤ Real.log (m : ℝ) := (le_max_left _ _).trans hlm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hA : 0 < (r : ℝ) - 1 + η / 2 := by linarith
  have hx : 0 ≤ ((r : ℝ) - 1 + η / 2) * m * Real.log m := by positivity
  have hround := (log_ceil_exp_bounds hx).2
  have he := (div_le_iff₀ hη).mp ((le_max_right _ _).trans hlm)
  have hlogbound : Real.log
      (⌈Real.exp (((r : ℝ) - 1 + η / 2) * m * Real.log m)⌉₊ : ℝ) ≤
        ((r : ℝ) - 1 + η) * m * Real.log m := by
    have hmul : Real.log (m : ℝ) ≤ m * Real.log m := by nlinarith
    have := mul_le_mul_of_nonneg_left hmul hη.le
    nlinarith
  have hpos : (0 : ℝ) <
      ⌈Real.exp (((r : ℝ) - 1 + η / 2) * m * Real.log m)⌉₊ :=
    (Real.exp_pos _).trans_le (Nat.le_ceil _)
  have hfinal := Real.exp_le_exp.mpr hlogbound
  rw [Real.exp_log hpos] at hfinal
  exact (Nat.cast_le.mpr hcm).trans hfinal

theorem golayCoveringNumber₃_upper {η : ℝ} (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop, (golayCoveringNumber₃ m : ℝ) ≤
      Real.exp ((2 + η) * m * Real.log m) := by
  have h := coveringNumber_upper (b := ![2, 10, 26]) (by decide) (by decide) hη
  simpa [powerMonoid_two_ten_twentySix, golayCoveringNumber₃,
    show (3 : ℝ) - 1 = 2 by norm_num] using h

end HadamardMultibase
