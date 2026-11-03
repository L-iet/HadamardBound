/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerPolynomials
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

/-!
# Growth bounds for the auxiliary block polynomials

On a complex disk of integral radius R the ordinary binomial polynomial is
bounded by choose(R+n,n). Grouping into blocks then gives an exponential bound
linear in the block size, with no extra log(block size) factor.
-/

namespace HadamardMultibase

open Polynomial

theorem bakerDelta_norm_le_choose (n R : ℕ) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖(bakerDelta n).eval₂ (Rat.castHom ℂ) z‖ ≤ ((R + n).choose n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : ((n + 1 : ℕ) : ℂ) * (bakerDelta (n + 1)).eval₂ (Rat.castHom ℂ) z =
        (bakerDelta n).eval₂ (Rat.castHom ℂ) z * (z + (n + 1 : ℕ)) := by
      have h := congrArg (Polynomial.eval₂ (Rat.castHom ℂ) z) (bakerDelta_nsmul_succ n)
      simpa [nsmul_eq_mul] using h
    have hn := congrArg norm he
    simp only [norm_mul, Complex.norm_natCast] at hn
    have hlin : ‖z + (n + 1 : ℕ)‖ ≤ (R + n + 1 : ℕ) := by
      calc ‖z + (n + 1 : ℕ)‖ ≤ ‖z‖ + ‖((n + 1 : ℕ) : ℂ)‖ := norm_add_le _ _
        _ ≤ _ := by
          have hnorm : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
            simpa using Complex.norm_natCast (n + 1)
          simp only [Nat.cast_add, Nat.cast_one]
          rw [hnorm]
          linarith
    have hc : ((R + n + 1).choose (n + 1) : ℝ) * (n + 1 : ℕ) =
        (R + n + 1 : ℕ) * ((R + n).choose n : ℝ) := by
      exact_mod_cast (Nat.add_one_mul_choose_eq (R + n) n).symm
    have hbound := mul_le_mul ih hlin (norm_nonneg _) (by positivity)
    rw [← hn] at hbound
    have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hcast : R + (n + 1) = R + n + 1 := by omega
    rw [hcast]
    nlinarith

theorem bakerDelta_norm_le_two_pow (n R : ℕ) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖(bakerDelta n).eval₂ (Rat.castHom ℂ) z‖ ≤ (2 : ℝ) ^ (R + n) := by
  apply (bakerDelta_norm_le_choose n R z hz).trans
  exact_mod_cast Nat.choose_le_two_pow (R + n) n

theorem bakerBlock_norm_le_two_pow (h a R : ℕ) (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖(bakerBlock h a).eval₂ (Rat.castHom ℂ) z‖ ≤
      (2 : ℝ) ^ ((R + h) * (a / h) + (R + a % h)) := by
  simp only [bakerBlock, eval₂_mul, eval₂_pow, norm_mul, norm_pow]
  rw [pow_add, pow_mul]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (bakerDelta_norm_le_two_pow h R z hz) _)
    (bakerDelta_norm_le_two_pow (a % h) R z hz) (norm_nonneg _) (by positivity)

theorem bakerBlock_norm_le_uniform {h a L T : ℕ} (hh : 0 < h)
    (ha : a < h * (L + 1)) (z : ℂ) (hz : ‖z‖ ≤ (T * h : ℕ)) :
    ‖(bakerBlock h a).eval₂ (Rat.castHom ℂ) z‖ ≤
      (2 : ℝ) ^ (h * (T + 1) * (L + 1)) := by
  apply (bakerBlock_norm_le_two_pow h a (T * h) z hz).trans
  apply pow_le_pow_right₀ (by norm_num)
  have hq : a / h ≤ L := by
    have := (Nat.div_lt_iff_lt_mul hh).mpr (by simpa [Nat.mul_comm] using ha)
    omega
  have hr := Nat.mod_lt a hh
  calc (T * h + h) * (a / h) + (T * h + a % h)
      ≤ (T * h + h) * (a / h + 1) := by nlinarith
    _ ≤ (T * h + h) * (L + 1) := Nat.mul_le_mul_left _ (Nat.add_le_add_right hq 1)
    _ = h * (T + 1) * (L + 1) := by ring

end HadamardMultibase
