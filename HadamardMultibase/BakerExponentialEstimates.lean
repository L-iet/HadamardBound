/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerGridExtrapolation
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-! # Exponential estimates with a varying grid scale

Fixed polynomial factors are absorbed by increasing the lower threshold on h.
The exponential rates themselves remain explicit, so that the parameter
choice cannot accidentally introduce a height-dependent constant.
-/

namespace HadamardMultibase

open Filter

theorem eventually_nat_const_mul_pow_le_exp (C : ℝ) (r : ℕ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ h : ℕ in atTop, C * (h : ℝ) ^ r ≤ Real.exp (b * (h : ℝ)) := by
  have ho := (isLittleO_pow_exp_pos_mul_atTop r hb).const_mul_left C
  have he := ho.def (show (0 : ℝ) < 1 by norm_num)
  have hn := tendsto_natCast_atTop_atTop.eventually he
  filter_upwards [hn] with h hh
  have hh' : |C * (h : ℝ) ^ r| ≤ Real.exp (b * (h : ℝ)) := by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul] using hh
  exact (le_abs_self _).trans hh'

theorem eventually_grid_data_prefactor {k s t : ℕ} :
    ∀ᶠ h : ℕ in atTop,
      ((k * (s * h) : ℕ) : ℝ) *
        (1 + 2 * (k : ℝ) * (((t * h : ℕ) : ℝ) + (s * h : ℕ))) ^ (k - 1) ≤
      Real.exp (h : ℝ) := by
  let B : ℝ := 2 * (k : ℝ) * ((t : ℝ) + s)
  let C : ℝ := (k : ℝ) * s * (1 + B) ^ (k - 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_nat_const_mul_pow_le_exp C k (show (0 : ℝ) < 1 by norm_num)] with h hh he
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hlin : 1 + B * (h : ℝ) ≤ (1 + B) * h := by nlinarith
  have hp : (1 + B * (h : ℝ)) ^ (k - 1) ≤ ((1 + B) * h) ^ (k - 1) :=
    pow_le_pow_left₀ (by positivity) hlin _
  by_cases hk0 : k = 0
  · simpa [hk0] using (Real.exp_pos (h : ℝ)).le
  · have heq : k - 1 + 1 = k := by omega
    have hpow : (h : ℝ) ^ k = (h : ℝ) ^ (k - 1) * h := by
      conv_lhs => rw [← heq, pow_succ]
    calc ((k * (s * h) : ℕ) : ℝ) *
          (1 + 2 * (k : ℝ) * (((t * h : ℕ) : ℝ) + (s * h : ℕ))) ^ (k - 1)
        = (k : ℝ) * s * h * (1 + B * (h : ℝ)) ^ (k - 1) := by dsimp [B]; push_cast; ring
      _ ≤ (k : ℝ) * s * h * (((1 + B) * h) ^ (k - 1)) := by gcongr
      _ = C * (h : ℝ) ^ k := by
        rw [mul_pow, hpow]
        dsimp [C]
        ring
      _ ≤ Real.exp (h : ℝ) := by simpa only [one_mul] using he

theorem geometric_cauchy_remainder_eq_exp {k s t w h : ℕ}
    (hh : 0 < h) (hs : 0 < s) (_hst : s ≤ t) (htw : t < w) (A : ℝ) :
    (((t * h : ℕ) : ℝ) + ((s * h : ℕ) : ℝ)) ^ (k * (s * h)) *
        (((w * h : ℕ) : ℝ) * Real.exp (A * h) /
          (((w * h : ℕ) : ℝ) - ((t * h : ℕ) : ℝ)) ^ (k * (s * h) + 1)) =
      ((w : ℝ) / ((w : ℝ) - t)) *
        Real.exp ((A + ((k * s : ℕ) : ℝ) *
          Real.log (((t : ℝ) + s) / ((w : ℝ) - t))) * h) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hden : (0 : ℝ) < (w : ℝ) - t := by
    have he : (t : ℝ) < w := by exact_mod_cast htw
    linarith
  have hnum : (0 : ℝ) < (t : ℝ) + s := by
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    positivity
  have hratio : (0 : ℝ) < ((t : ℝ) + s) / ((w : ℝ) - t) := div_pos hnum hden
  let m := k * (s * h)
  have heq : (((t * h : ℕ) : ℝ) + ((s * h : ℕ) : ℝ)) ^ m *
      (((w * h : ℕ) : ℝ) * Real.exp (A * h) /
        (((w * h : ℕ) : ℝ) - ((t * h : ℕ) : ℝ)) ^ (m + 1)) =
      ((w : ℝ) / ((w : ℝ) - t)) * Real.exp (A * h) *
        (((t : ℝ) + s) / ((w : ℝ) - t)) ^ m := by
    push_cast
    rw [show (t : ℝ) * h + (s : ℝ) * h = ((t : ℝ) + s) * h by ring,
      show (w : ℝ) * h - (t : ℝ) * h = ((w : ℝ) - t) * h by ring,
      pow_succ, mul_pow, mul_pow, div_pow]
    field_simp
  rw [heq, ← Real.exp_log (pow_pos hratio m), Real.log_pow, mul_assoc, ← Real.exp_add]
  congr 2
  dsimp [m]
  push_cast
  ring

theorem eventually_baker_grid_extrapolation_exp {k s t w : ℕ}
    (hk : 0 < k) (hs : 0 < s) (hst : s ≤ t) (htw : t < w) (A E : ℝ) :
    ∀ᶠ h : ℕ in atTop, ∀ f : ℂ → ℂ,
      DiffContOnCl ℂ f (Metric.ball 0 ((w * h : ℕ) : ℝ)) →
      (∀ z ∈ Metric.sphere 0 ((w * h : ℕ) : ℝ), ‖f z‖ ≤ Real.exp (A * h)) →
      (∀ l : ℕ, 1 ≤ l → l ≤ s * h → ∀ u : ℕ, u < k →
        ‖iteratedDeriv u f (l : ℂ)‖ / (u.factorial : ℝ) ≤ Real.exp (-E * h)) →
      ∀ z : ℂ, ‖z‖ ≤ ((t * h : ℕ) : ℝ) →
        ‖f z‖ ≤ Real.exp ((-E + 1 + 2 * (k : ℝ) * ((t : ℝ) + s)) * h) +
          Real.exp ((A + ((k * s : ℕ) : ℝ) *
            Real.log (((t : ℝ) + s) / ((w : ℝ) - t)) + 1) * h) := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_grid_data_prefactor (k := k) (s := s) (t := t),
    eventually_nat_const_mul_pow_le_exp ((w : ℝ) / ((w : ℝ) - t)) 0
      (show (0 : ℝ) < 1 by norm_num)] with h hh hdata hrem
  intro f hf hboundary hjet z hz
  have hhpos : 0 < h := by omega
  have hstR : ((s * h : ℕ) : ℝ) ≤ ((t * h : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_le_mul_right h hst
  have htwR : ((t * h : ℕ) : ℝ) < ((w * h : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_lt_mul_of_pos_right htw hhpos
  have hb := baker_grid_extrapolation hk hstR htwR
    (Real.exp_pos (-E * h)).le (Real.exp_pos (A * h)).le hf hboundary hjet z hz
  apply hb.trans
  apply add_le_add
  · calc ((k * (s * h) : ℕ) : ℝ) * Real.exp (-E * h) *
          (1 + 2 * (k : ℝ) * (((t * h : ℕ) : ℝ) + ((s * h : ℕ) : ℝ))) ^ (k - 1) *
          Real.exp (2 * (k : ℝ) * (((t * h : ℕ) : ℝ) + ((s * h : ℕ) : ℝ)))
        = Real.exp (-E * h) *
          (((k * (s * h) : ℕ) : ℝ) *
            (1 + 2 * (k : ℝ) * (((t * h : ℕ) : ℝ) + ((s * h : ℕ) : ℝ))) ^ (k - 1)) *
          Real.exp (2 * (k : ℝ) * (((t * h : ℕ) : ℝ) + ((s * h : ℕ) : ℝ))) := by ring
      _ ≤ Real.exp (-E * h) * Real.exp (h : ℝ) *
          Real.exp (2 * (k : ℝ) * (((t * h : ℕ) : ℝ) + ((s * h : ℕ) : ℝ))) := by gcongr
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        push_cast
        ring
  · rw [geometric_cauchy_remainder_eq_exp hhpos hs hst htw]
    have hconst : (w : ℝ) / ((w : ℝ) - t) ≤ Real.exp (h : ℝ) := by simpa using hrem
    calc (w : ℝ) / ((w : ℝ) - t) *
          Real.exp ((A + ((k * s : ℕ) : ℝ) * Real.log (((t : ℝ) + s) / ((w : ℝ) - t))) * h)
        ≤ Real.exp (h : ℝ) *
          Real.exp ((A + ((k * s : ℕ) : ℝ) * Real.log (((t : ℝ) + s) / ((w : ℝ) - t))) * h) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

end HadamardMultibase
