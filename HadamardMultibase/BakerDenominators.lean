/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerPolynomials
public import Mathlib.Algebra.Polynomial.Lifts

@[expose] public section

/-!
# Common denominators independent of the degree index

If every integer from 1 through h divides D, substituting z + D X in a block
polynomial produces integer coefficients, for every integer z. Reading a
Taylor coefficient then clears its divided derivative by D^m, independently
of the block polynomial's degree. No transcendence estimate is assumed.
-/

namespace HadamardMultibase

open Polynomial

theorem bakerDelta_scaled_zero_lift {h : ℕ} {D : ℤ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ h → (j : ℤ) ∣ D) :
    ∃ P : ℤ[X], P.map (Int.castRingHom ℚ) =
      (bakerDelta h).comp (C (D : ℚ) * X) := by
  induction h with
  | zero => exact ⟨1, by simp⟩
  | succ h ih =>
    obtain ⟨P, hP⟩ := ih (fun j hj hjh => hD j hj (by omega))
    obtain ⟨d, hd⟩ := hD (h + 1) (by omega) (by omega)
    refine ⟨P * (C d * X + 1), ?_⟩
    have hquot : (h + 1 : ℚ)⁻¹ * D = d := by
      rw [hd]
      push_cast
      field_simp
    rw [Polynomial.map_mul, hP, bakerDelta_succ, mul_comp]
    congr 1
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, map_X, Polynomial.map_one, add_comp,
      mul_comp, C_comp, X_comp, one_comp]
    rw [← mul_assoc, ← map_mul, hquot]
    simp

theorem bakerDelta_scaled_translate_lift {h : ℕ} {D : ℤ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ h → (j : ℤ) ∣ D) (z : ℤ) :
    ∃ P : ℤ[X], P.map (Int.castRingHom ℚ) =
      (bakerDelta h).comp (C (z : ℚ) + C (D : ℚ) * X) := by
  induction h generalizing z with
  | zero => exact ⟨1, by simp⟩
  | succ h ih =>
    have lower (z : ℤ) := ih (fun j hj hjh => hD j hj (by omega)) z
    have pascal (z : ℤ) :
        (bakerDelta (h + 1)).comp (C ((z + 1 : ℤ) : ℚ) + C (D : ℚ) * X) =
          (bakerDelta (h + 1)).comp (C (z : ℚ) + C (D : ℚ) * X) +
          (bakerDelta h).comp (C ((z + 1 : ℤ) : ℚ) + C (D : ℚ) * X) := by
      have shift : C ((z + 1 : ℤ) : ℚ) + C (D : ℚ) * X =
          (C (z : ℚ) + C (D : ℚ) * X) + 1 := by
        simp only [Int.cast_add, Int.cast_one, map_add, map_one]
        ring
      simpa only [shift] using bakerDelta_pascal h (C (z : ℚ) + C (D : ℚ) * X)
    induction z using Int.induction_on with
    | zero => simpa using bakerDelta_scaled_zero_lift hD
    | succ n hn =>
      obtain ⟨P, hP⟩ := hn
      obtain ⟨Q, hQ⟩ := lower ((n : ℤ) + 1)
      refine ⟨P + Q, ?_⟩
      rw [Polynomial.map_add, hP, hQ, ← pascal]
    | pred n hn =>
      obtain ⟨P, hP⟩ := hn
      obtain ⟨Q, hQ⟩ := lower (-(n : ℤ))
      refine ⟨P - Q, ?_⟩
      have h := pascal (-(n : ℤ) - 1)
      rw [sub_add_cancel] at h
      rw [Polynomial.map_sub, hP, hQ]
      exact (eq_sub_of_add_eq h.symm).symm

theorem bakerBlock_scaled_translate_lift {h : ℕ} (hh : 0 < h) {D : ℤ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ h → (j : ℤ) ∣ D) (a : ℕ) (z : ℤ) :
    ∃ P : ℤ[X], P.map (Int.castRingHom ℚ) =
      (bakerBlock h a).comp (C (z : ℚ) + C (D : ℚ) * X) := by
  obtain ⟨P, hP⟩ := bakerDelta_scaled_translate_lift hD z
  obtain ⟨Q, hQ⟩ := bakerDelta_scaled_translate_lift
    (fun j hj hjr => hD j hj (hjr.trans (Nat.le_of_lt (Nat.mod_lt a hh)))) z
  refine ⟨P ^ (a / h) * Q, ?_⟩
  simp only [Polynomial.map_mul, Polynomial.map_pow, hP, hQ, bakerBlock, mul_comp, pow_comp]

theorem bakerBlock_hasse_integer {h : ℕ} (hh : 0 < h) {D : ℤ}
    (hD : ∀ j : ℕ, 1 ≤ j → j ≤ h → (j : ℤ) ∣ D) (a m : ℕ) (z : ℤ) :
    ∃ v : ℤ, (D : ℚ) ^ m * (hasseDeriv m (bakerBlock h a)).eval (z : ℚ) = v := by
  obtain ⟨P, hP⟩ := bakerBlock_scaled_translate_lift hh hD a z
  refine ⟨P.coeff m, ?_⟩
  have hc := congrArg (fun Q : ℚ[X] => Q.coeff m) hP
  have hcomp : (bakerBlock h a).comp (C (z : ℚ) + C (D : ℚ) * X) =
      (taylor (z : ℚ) (bakerBlock h a)).comp (C (D : ℚ) * X) := by
    simp only [taylor_apply, comp_assoc, add_comp, X_comp, C_comp]
    congr 1
    ring
  rw [hcomp, coeff_map, comp_C_mul_X_coeff, taylor_coeff] at hc
  simpa only [eq_intCast, mul_comm] using hc.symm

end HadamardMultibase
