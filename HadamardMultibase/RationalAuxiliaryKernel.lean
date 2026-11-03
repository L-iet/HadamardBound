/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BoundedIntegerKernel
public import HadamardMultibase.BakerComparisonValues

@[expose] public section

/-! # Bounded auxiliary coefficients for rational comparison systems

Row-wise denominator certificates convert the rational comparison equations
to a bounded integer matrix. Finite-box pigeonhole then provides a nonzero
integer coefficient vector with explicit height and exact rational vanishing.
-/

namespace HadamardMultibase

theorem exists_bounded_rational_kernel {m n M : ℕ} (hn : 0 < n) (hmn : 2 * m ≤ n)
    (A : Fin m → Fin n → ℚ) (D : Fin m → ℕ) (hD : ∀ i, 0 < D i)
    (hint : ∀ i j, HasIntegerMultiple (D i) (A i j))
    (hA : ∀ i j, |(D i : ℚ) * A i j| ≤ (M : ℚ)) :
    ∃ c : Fin n → ℤ, c ≠ 0 ∧ (∀ j, |c j| ≤ (2 * n * M + 1 : ℕ)) ∧
      ∀ i, ∑ j, A i j * (c j : ℚ) = 0 := by
  classical
  choose B hB using hint
  have hbound (i) (j) : |B i j| ≤ (M : ℤ) := by
    have h := hA i j
    rw [hB i j] at h
    exact_mod_cast h
  obtain ⟨c, hc, hcBound, hcZero⟩ :=
    exists_bounded_integer_kernel_of_twice_rows_le hn hmn B hbound
  refine ⟨c, hc, hcBound, ?_⟩
  intro i
  have hcleared : (D i : ℚ) * (∑ j, A i j * (c j : ℚ)) = 0 := by
    calc (D i : ℚ) * (∑ j, A i j * (c j : ℚ))
        = ∑ j, (D i : ℚ) * A i j * (c j : ℚ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = ∑ j, (B i j : ℚ) * (c j : ℚ) := by simp only [hB]
      _ = ((∑ j, B i j * c j : ℤ) : ℚ) := by push_cast; rfl
      _ = 0 := by rw [hcZero i, Int.cast_zero]
  exact (mul_eq_zero.mp hcleared).resolve_left (by exact_mod_cast (hD i).ne')

theorem exists_bounded_baker_comparison_kernel {m n M h q : ℕ}
    (hh : 0 < h) (hq : 0 < q) (hn : 0 < n) (hmn : 2 * m ≤ n)
    (d lam mu : Fin n → ℕ) (u v l : Fin m → ℕ) (p : ℤ) (a b : ℕ)
    (hA : ∀ i j,
      |((Nat.lcmUpto h ^ u i * q ^ v i : ℕ) : ℚ) *
        bakerComparisonValue h (d j) (u i) (v i) (l i) (lam j) (mu j) p q a b| ≤ M) :
    ∃ c : Fin n → ℤ, c ≠ 0 ∧ (∀ j, |c j| ≤ (2 * n * M + 1 : ℕ)) ∧
      ∀ i, ∑ j, (c j : ℚ) *
        bakerComparisonValue h (d j) (u i) (v i) (l i) (lam j) (mu j) p q a b = 0 := by
  obtain ⟨c, hc, hbound, hzero⟩ := exists_bounded_rational_kernel hn hmn
    (fun i j => bakerComparisonValue h (d j) (u i) (v i) (l i) (lam j) (mu j) p q a b)
    (fun i => Nat.lcmUpto h ^ u i * q ^ v i)
    (fun i => mul_pos (pow_pos (Nat.lcmUpto_pos h) _) (pow_pos hq _))
    (fun i j => bakerComparison_integer_multiple hh hq (d j) (u i) (v i) (l i)
      (lam j) (mu j) p a b) hA
  exact ⟨c, hc, hbound, fun i => by simpa only [mul_comm] using hzero i⟩

theorem exists_bounded_rational_kernel_fintype {ι κ : Type*} [Fintype ι] [Fintype κ]
    {M : ℕ} (hn : 0 < Fintype.card κ) (hmn : 2 * Fintype.card ι ≤ Fintype.card κ)
    (A : ι → κ → ℚ) (D : ι → ℕ) (hD : ∀ i, 0 < D i)
    (hint : ∀ i j, HasIntegerMultiple (D i) (A i j))
    (hA : ∀ i j, |(D i : ℚ) * A i j| ≤ (M : ℚ)) :
    ∃ c : κ → ℤ, c ≠ 0 ∧ (∀ j, |c j| ≤ (2 * Fintype.card κ * M + 1 : ℕ)) ∧
      ∀ i, ∑ j, A i j * (c j : ℚ) = 0 := by
  classical
  let ei := Fintype.equivFin ι
  let ej := Fintype.equivFin κ
  obtain ⟨v, hv, hvBound, hvZero⟩ := exists_bounded_rational_kernel hn hmn
    (fun i j => A (ei.symm i) (ej.symm j)) (fun i => D (ei.symm i))
    (fun i => hD _) (fun i j => hint _ _) (fun i j => hA _ _)
  refine ⟨fun j => v (ej j), ?_, fun j => hvBound _, ?_⟩
  · intro hc
    apply hv
    funext j
    have he := congrFun hc (ej.symm j)
    simpa using he
  · intro i
    have he := hvZero (ei i)
    simp only [Equiv.symm_apply_apply] at he
    rw [← Equiv.sum_comp ej] at he
    simpa using he

end HadamardMultibase
