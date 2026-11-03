module

public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.Tactic

@[expose] public section

namespace HadamardMultibase

/-- A small nonzero return of a rotation gives a one-sided mesh. The bound
on the index is recorded without division, for later quantitative estimates. -/
theorem rotation_mesh_of_small_return {α : ℝ} {k : ℕ} {j : ℤ}
    (hd : (k : ℝ) * α - (j : ℝ) ≠ 0) {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    ∃ m : ℕ, ∃ z : ℤ,
      (m : ℝ) * |(k : ℝ) * α - (j : ℝ)| ≤ (k : ℝ) ∧
      0 ≤ (m : ℝ) * α + (z : ℝ) ∧
      x - |(k : ℝ) * α - (j : ℝ)| ≤ (m : ℝ) * α + (z : ℝ) ∧
      (m : ℝ) * α + (z : ℝ) ≤ x := by
  let d := (k : ℝ) * α - (j : ℝ)
  have hd' : d ≠ 0 := hd
  have habs : 0 < |d| := abs_pos.mpr hd'
  by_cases hnear : x ≤ |d|
  · refine ⟨0, 0, ?_, ?_, ?_, ?_⟩ <;> simp only [Nat.cast_zero, Int.cast_zero, zero_mul, zero_add]
    · exact Nat.cast_nonneg k
    · exact le_rfl
    · exact sub_nonpos.mpr hnear
    · exact hx
  · have hfar : |d| < x := lt_of_not_ge hnear
    rcases lt_or_gt_of_ne hd' with hneg | hpos
    · let l : ℕ := ⌈(1 - x) / (-d)⌉₊
      have hdpos : 0 < -d := by linarith
      have harg : 0 ≤ (1 - x) / (-d) := div_nonneg (by linarith) hdpos.le
      have hceil := Nat.le_ceil ((1 - x) / (-d))
      have hceil' := Nat.ceil_lt_add_one harg
      change (1 - x) / (-d) ≤ (l : ℝ) at hceil
      change (l : ℝ) < (1 - x) / (-d) + 1 at hceil'
      have hlower : 1 - x ≤ (l : ℝ) * (-d) := (div_le_iff₀ hdpos).mp hceil
      have hupper : (l : ℝ) * (-d) < 1 - x + (-d) := by
        have h := (mul_lt_mul_iff_left₀ hdpos).mpr hceil'
        rw [add_mul, div_mul_cancel₀ _ hdpos.ne', one_mul] at h
        nlinarith
      have hdabs : |d| = -d := abs_of_neg hneg
      have hlone : (l : ℝ) * (-d) ≤ 1 := by rw [hdabs] at hfar; linarith
      have hmul := mul_le_mul_of_nonneg_left hlone (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      have heq : ((k * l : ℕ) : ℝ) * α + ((1 - (l : ℤ) * j : ℤ) : ℝ) =
          1 - (l : ℝ) * (-d) := by dsimp [d]; push_cast; ring
      refine ⟨k * l, 1 - (l : ℤ) * j, ?_, ?_, ?_, ?_⟩
      · change ((k * l : ℕ) : ℝ) * |d| ≤ (k : ℝ)
        rw [Nat.cast_mul, hdabs]
        nlinarith
      · rw [heq]; linarith
      · change x - |d| ≤ _
        rw [heq, hdabs]; linarith
      · rw [heq]; linarith
    · let l : ℕ := ⌊x / d⌋₊
      have harg : 0 ≤ x / d := div_nonneg hx hpos.le
      have hfloor := Nat.floor_le harg
      have hfloor' := Nat.lt_floor_add_one (x / d)
      change (l : ℝ) ≤ x / d at hfloor
      change x / d < (l : ℝ) + 1 at hfloor'
      have hupper : (l : ℝ) * d ≤ x := (le_div_iff₀ hpos).mp hfloor
      have hlower : x < ((l : ℝ) + 1) * d := (div_lt_iff₀ hpos).mp hfloor'
      have hlone : (l : ℝ) * d ≤ 1 := by linarith
      have hmul := mul_le_mul_of_nonneg_left hlone (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
      have heq : ((k * l : ℕ) : ℝ) * α + ((-(l : ℤ) * j : ℤ) : ℝ) = (l : ℝ) * d := by
        dsimp [d]; push_cast; ring
      refine ⟨k * l, -(l : ℤ) * j, ?_, ?_, ?_, ?_⟩
      · change ((k * l : ℕ) : ℝ) * |d| ≤ (k : ℝ)
        rw [Nat.cast_mul, abs_of_pos hpos]
        nlinarith
      · rw [heq]; positivity
      · change x - |d| ≤ _
        rw [heq, abs_of_pos hpos]; linarith
      · rw [heq]; exact hupper

end HadamardMultibase
