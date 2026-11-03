module

public import HadamardMultibase.MatrixTraceMoments
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace HadamardMultibase

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Weight of a walk with fixed endpoints and k intermediate vertices. -/
noncomputable def matrixPathWeight (A : Matrix ι ι ℝ) {k : ℕ}
    (i j : ι) (f : Fin k → ι) : ℝ :=
  ∏ t : Fin (k + 1),
    A (Fin.cons (α := fun _ : Fin (k + 1) => ι) i f t)
      (Fin.snoc (α := fun _ : Fin (k + 1) => ι) f j t)

omit [Fintype ι] [DecidableEq ι] in
theorem matrixPathWeight_cons (A : Matrix ι ι ℝ) {k : ℕ}
    (i a j : ι) (f : Fin k → ι) :
    matrixPathWeight A i j (Fin.cons a f) = A i a * matrixPathWeight A a j f := by
  unfold matrixPathWeight
  rw [← Fin.cons_snoc_eq_snoc_cons, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- Entrywise walk expansion, with no restrictions on repeated vertices. -/
theorem matrix_pow_entry_walk_sum (A : Matrix ι ι ℝ) (k : ℕ) (i j : ι) :
    (A ^ (k + 1)) i j = ∑ f : Fin k → ι, matrixPathWeight A i j f := by
  induction k generalizing i j with
  | zero =>
    simp [matrixPathWeight]
    rw [show (0 : Fin 1) = Fin.last 0 by rfl, Fin.snoc_last]
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih, Finset.mul_sum]
    calc
      _ = ∑ p : ι × (Fin k → ι), matrixPathWeight A i j (Fin.cons p.1 p.2) := by
        rw [Fintype.sum_prod_type]
        simp only [matrixPathWeight_cons]
      _ = _ := (Fin.consEquiv (fun _ : Fin (k + 1) => ι)).sum_comp
        (fun f => matrixPathWeight A i j f)

theorem matrix_trace_pow_walk_sum (A : Matrix ι ι ℝ) (k : ℕ) :
    Matrix.trace (A ^ (k + 1)) = ∑ i : ι, ∑ f : Fin k → ι, matrixPathWeight A i i f := by
  simp only [Matrix.trace, Matrix.diag, matrix_pow_entry_walk_sum]

end HadamardMultibase
