/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerIndexing
public import HadamardMultibase.GeneralIndependence

@[expose] public section

/-! # The exact zero-grid contradiction

The zeroth comparison sum has the true integer logarithmic frequencies.
Reindexing its nonzero coefficient vector into block polynomials lets the
checked exponential-polynomial zero count exclude a grid of sufficient size.
-/

namespace HadamardMultibase

noncomputable def bakerGroupedCoefficients (h L : ℕ)
    (c : Fin (bakerColumnCount h L) → ℤ)
    (freq : Fin (L + 1) × Fin (L + 1)) (d : Fin (h * (L + 1))) : ℝ :=
  (c (bakerColumnEquiv h L (d, freq)) : ℝ)

noncomputable def bakerTrueFrequency (a b L : ℕ) (freq : Fin (L + 1) × Fin (L + 1)) : ℝ :=
  (freq.1.val : ℝ) * Real.log a + (freq.2.val : ℝ) * Real.log b

theorem bakerTrueFrequency_injective {a b : ℕ} (ha : 2 ≤ a)
    (hirr : Irrational (Real.log (b : ℝ) / Real.log (a : ℝ))) (L : ℕ) :
    Function.Injective (bakerTrueFrequency a b L) := by
  have hloga : Real.log (a : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < a by omega))).ne'
  intro i j he
  have hp : (i.1.val, i.2.val) = (j.1.val, j.2.val) :=
    irrational_frequency_injective hloga hirr he
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst hp)
  · exact Fin.ext (congrArg Prod.snd hp)

theorem bakerGroupedCoefficients_ne_zero {h L : ℕ}
    (c : Fin (bakerColumnCount h L) → ℤ) (hc : c ≠ 0) :
    ∃ freq d, bakerGroupedCoefficients h L c freq d ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  apply hc
  funext j
  let col := (bakerColumnEquiv h L).symm j
  have he := hn col.2 col.1
  dsimp [bakerGroupedCoefficients, col] at he
  simp only [Prod.mk.eta, Equiv.apply_symm_apply] at he
  simpa using (show c j = 0 by exact_mod_cast he)

theorem true_log_frequency_exp {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (lam mu l : ℕ) :
    Real.exp (((lam : ℝ) * Real.log a + (mu : ℝ) * Real.log b) * l) =
      (a : ℝ) ^ (lam * l) * (b : ℝ) ^ (mu * l) := by
  have he : ((lam : ℝ) * Real.log a + (mu : ℝ) * Real.log b) * l =
      ((lam * l : ℕ) : ℝ) * Real.log a + ((mu * l : ℕ) : ℝ) * Real.log b := by push_cast; ring
  rw [he, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (by exact_mod_cast ha : (0 : ℝ) < a),
    Real.exp_log (by exact_mod_cast hb : (0 : ℝ) < b)]

theorem bakerIndexedComparison_zero_eq_auxiliary {h L a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (c : Fin (bakerColumnCount h L) → ℤ) (l q : ℕ) (p : ℤ) :
    ((bakerIndexedComparison h L 0 0 l p q a b c : ℚ) : ℝ) =
      exponentialPolynomialEval (bakerTrueFrequency a b L)
        (fun freq => bakerAuxiliaryPolynomial h (bakerGroupedCoefficients h L c freq)) l := by
  classical
  simp only [bakerIndexedComparison, Rat.cast_sum, Rat.cast_mul]
  rw [← Equiv.sum_comp (bakerColumnEquiv h L)]
  simp only [bakerColumnDegree, bakerColumnLam, bakerColumnMu, Equiv.symm_apply_apply,
    bakerComparisonValue, Polynomial.hasseDeriv_zero, LinearMap.id_apply, pow_zero,
    mul_one, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
  rw [Fintype.sum_prod_type]
  unfold exponentialPolynomialEval bakerAuxiliaryPolynomial bakerGroupedCoefficients
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro freq _
  apply Finset.sum_congr rfl
  intro d _
  rw [bakerTrueFrequency, true_log_frequency_exp ha hb]
  have heval : (((bakerBlock h d.val).eval (l : ℚ) : ℚ) : ℝ) =
      ((bakerBlock h d.val).map (Rat.castHom ℝ)).eval (l : ℝ) := by
    simp [← Polynomial.eval₂_eq_eval_map]
  rw [heval]
  push_cast
  ring

theorem bakerIndexedComparison_zero_grid_impossible {h L a b T : ℕ}
    (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hirr : Irrational (Real.log (b : ℝ) / Real.log (a : ℝ)))
    (c : Fin (bakerColumnCount h L) → ℤ) (hc : c ≠ 0)
    (hT : bakerColumnCount h L ≤ T) (p : ℤ) (q : ℕ)
    (hzero : ∀ l : ℕ, 1 ≤ l → l ≤ T → bakerIndexedComparison h L 0 0 l p q a b c = 0) : False := by
  classical
  have hdim : Fintype.card (Fin (L + 1) × Fin (L + 1)) * (h * (L + 1)) ≤ T := by
    simpa [bakerColumnCount, BakerColumn, Fintype.card_prod, mul_comm, mul_left_comm, mul_assoc] using hT
  obtain ⟨l, hl, hlT, hne⟩ := bakerAuxiliary_integer_nonzero h (bakerTrueFrequency a b L)
    (bakerTrueFrequency_injective ha hirr L) (bakerGroupedCoefficients h L c)
    (bakerGroupedCoefficients_ne_zero c hc) hdim
  apply hne
  rw [← bakerIndexedComparison_zero_eq_auxiliary (show 0 < a by omega) (show 0 < b by omega) c l q p,
    hzero l hl hlT, Rat.cast_zero]

end HadamardMultibase
