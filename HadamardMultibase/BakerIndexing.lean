/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerInitialHeight
public import HadamardMultibase.RationalAuxiliaryKernel

@[expose] public section

/-! # Indices for the auxiliary coefficient vector and initial equations -/

namespace HadamardMultibase

abbrev BakerColumn (h L : ℕ) := Fin (h * (L + 1)) × (Fin (L + 1) × Fin (L + 1))
abbrev BakerRow (h K : ℕ) := Fin h × (Fin K × Fin K)

def bakerColumnCount (h L : ℕ) : ℕ := Fintype.card (BakerColumn h L)
def bakerRowCount (h K : ℕ) : ℕ := Fintype.card (BakerRow h K)

theorem bakerColumnCount_eq (h L : ℕ) : bakerColumnCount h L = h * (L + 1) ^ 3 := by
  simp [bakerColumnCount, BakerColumn, Fintype.card_prod, pow_succ]; ring

theorem bakerRowCount_eq (h K : ℕ) : bakerRowCount h K = h * K ^ 2 := by
  simp [bakerRowCount, BakerRow, Fintype.card_prod, pow_two]

noncomputable def bakerColumnEquiv (h L : ℕ) : BakerColumn h L ≃ Fin (bakerColumnCount h L) :=
  Fintype.equivFin _

noncomputable def bakerColumnDegree (h L : ℕ) (j : Fin (bakerColumnCount h L)) : ℕ :=
  ((bakerColumnEquiv h L).symm j).1.val

noncomputable def bakerColumnLam (h L : ℕ) (j : Fin (bakerColumnCount h L)) : ℕ :=
  ((bakerColumnEquiv h L).symm j).2.1.val

noncomputable def bakerColumnMu (h L : ℕ) (j : Fin (bakerColumnCount h L)) : ℕ :=
  ((bakerColumnEquiv h L).symm j).2.2.val

theorem bakerColumnDegree_lt (h L : ℕ) (j : Fin (bakerColumnCount h L)) :
    bakerColumnDegree h L j < h * (L + 1) := ((bakerColumnEquiv h L).symm j).1.isLt

theorem bakerColumnLam_le (h L : ℕ) (j : Fin (bakerColumnCount h L)) :
    bakerColumnLam h L j ≤ L := by
  have he := ((bakerColumnEquiv h L).symm j).2.1.isLt
  exact Nat.le_of_lt_succ he

theorem bakerColumnMu_le (h L : ℕ) (j : Fin (bakerColumnCount h L)) :
    bakerColumnMu h L j ≤ L := by
  have he := ((bakerColumnEquiv h L).symm j).2.2.isLt
  exact Nat.le_of_lt_succ he

noncomputable def bakerIndexedMixed (h L u v : ℕ) (β : ℝ) (a : ℕ)
    (c : Fin (bakerColumnCount h L) → ℤ) : ℂ → ℂ :=
  bakerMixedComplexValue h u v β a c (bakerColumnDegree h L) (bakerColumnLam h L) (bakerColumnMu h L)

noncomputable def bakerIndexedComparison (h L u v l : ℕ) (p : ℤ) (q a b : ℕ)
    (c : Fin (bakerColumnCount h L) → ℤ) : ℚ :=
  ∑ j, (c j : ℚ) * bakerComparisonValue h (bakerColumnDegree h L j) u v l
    (bakerColumnLam h L j) (bakerColumnMu h L j) p q a b

theorem bakerIndexedComparison_integer_multiple {h q : ℕ} (hh : 0 < h) (hq : 0 < q)
    (L u v l : ℕ) (p : ℤ) (a b : ℕ) (c : Fin (bakerColumnCount h L) → ℤ) :
    HasIntegerMultiple (Nat.lcmUpto h ^ u * q ^ v) (bakerIndexedComparison h L u v l p q a b c) := by
  apply bakerComparison_sum_integer_multiple hh hq Finset.univ c
    (bakerColumnDegree h L) (bakerColumnLam h L) (bakerColumnMu h L) u v l p a b

theorem bakerIndexedComparison_eq_zero_of_exp_small {h q K : ℕ}
    (hh : 0 < h) (hq : 0 < q) (hheight : (q : ℝ) ≤ Real.exp h)
    (L u v l : ℕ) (hu : u ≤ K) (hv : v ≤ K) (p : ℤ) (a b : ℕ)
    (c : Fin (bakerColumnCount h L) → ℤ)
    (hsmall : |((bakerIndexedComparison h L u v l p q a b c : ℚ) : ℝ)| <
      Real.exp (-((Real.log 4 + 5) * (K : ℝ) * (h : ℝ)))) :
    bakerIndexedComparison h L u v l p q a b c = 0 := by
  apply rat_eq_zero_of_small_abs (mul_pos (pow_pos (Nat.lcmUpto_pos h) u) (pow_pos hq v))
    (bakerIndexedComparison_integer_multiple hh hq L u v l p a b c)
  apply hsmall.trans_le
  rw [Real.exp_neg, ← one_div]
  apply one_div_le_one_div_of_le (by
    have hp := mul_pos (pow_pos (Nat.lcmUpto_pos h) u) (pow_pos hq v)
    exact_mod_cast hp)
  exact baker_comparison_denominator_exp_bound hheight hu hv

end HadamardMultibase
