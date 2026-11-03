module

public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-! Definitions corresponding to the introduction and sparse-decomposition section of the note.
Integer coefficients ensure that mathlib's unitary-entry condition means precisely ±1.
Positive order is required explicitly to exclude the empty matrix.
-/

@[expose] public section

namespace HadamardMultibase

def HadamardOrder (n : ℕ) : Prop :=
  0 < n ∧ ∃ H : Matrix (Fin n) (Fin n) ℤ, H.IsHadamard

theorem hadamardOrder_one : HadamardOrder 1 := by
  refine ⟨by omega, !![(1 : ℤ)], ?_⟩
  constructor
  · intro i j
    fin_cases i
    fin_cases j
    norm_num [Unitary.mem_iff]
  · ext i j
    fin_cases i
    fin_cases j
    norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply]
  · ext i j
    fin_cases i
    fin_cases j
    norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem HadamardOrder.mul {m n : ℕ} (hm : HadamardOrder m) (hn : HadamardOrder n) :
    HadamardOrder (m * n) := by
  obtain ⟨hm, A, hA⟩ := hm
  obtain ⟨hn, B, hB⟩ := hn
  refine ⟨Nat.mul_pos hm hn,
    Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kronecker A B), ?_⟩
  exact (hA.kronecker hB).reindex finProdFinEquiv finProdFinEquiv

theorem hadamardOrder_two : HadamardOrder 2 := by
  refine ⟨by omega, !![(1 : ℤ), 1; 1, -1], ?_⟩
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Unitary.mem_iff]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]

theorem HadamardOrder.double {n : ℕ} (hn : HadamardOrder n) : HadamardOrder (2 * n) :=
  hadamardOrder_two.mul hn

theorem HadamardOrder.two_pow_mul {n : ℕ} (hn : HadamardOrder n) (k : ℕ) :
    HadamardOrder (2 ^ k * n) := by
  induction k with
  | zero => simpa using hn
  | succ k ih => simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using ih.double

theorem hadamardOrder_two_pow (k : ℕ) : HadamardOrder (2 ^ k) := by
  simpa using hadamardOrder_one.two_pow_mul k

theorem HadamardOrder.four_dvd {n : ℕ} (h : HadamardOrder n) (hn : 2 < n) :
    4 ∣ n := by
  obtain ⟨_, H, hH⟩ := h
  simpa using hH.four_dvd_card (by simpa using hn)

/-- Avoid assigning a spurious minimum when existence has not yet been established. -/
def HasExponent (p : ℕ) : Prop := ∃ t : ℕ, HadamardOrder (2 ^ t * p)

noncomputable def tau (p : ℕ) (h : HasExponent p) : ℕ := by
  classical
  exact Nat.find h

theorem tau_spec {p : ℕ} (h : HasExponent p) : HadamardOrder (2 ^ tau p h * p) := by
  classical
  exact Nat.find_spec h

theorem tau_le {p t : ℕ} (h : HasExponent p) (ht : HadamardOrder (2 ^ t * p)) :
    tau p h ≤ t := by
  classical
  exact Nat.find_min' h ht

def golayMonoid₂ : Set ℕ := {n | ∃ a b : ℕ, n = 2 ^ a * 10 ^ b}

def golayMonoid₃ : Set ℕ := {n | ∃ a b c : ℕ, n = 2 ^ a * 10 ^ b * 26 ^ c}

theorem golayMonoid₂_subset : golayMonoid₂ ⊆ golayMonoid₃ := by
  rintro n ⟨a, b, rfl⟩
  exact ⟨a, b, 0, by simp⟩

theorem golayMonoid₂_pos {n : ℕ} (hn : n ∈ golayMonoid₂) : 0 < n := by
  obtain ⟨a, b, rfl⟩ := hn
  positivity

/-- Repetitions are allowed in the covering problem. -/
def SumOfAtMost (S : Set ℕ) (m n : ℕ) : Prop :=
  ∃ l : List ℕ, l.length ≤ m ∧ (∀ x ∈ l, x ∈ S) ∧ l.sum = n

/-- A 0/1 multi-base expansion: distinct natural-number summands. -/
def SparseDecomposition (q : ℕ) (s : Finset ℕ) : Prop :=
  (∀ n ∈ s, n ∈ golayMonoid₂) ∧ ∑ n ∈ s, n = q

noncomputable def logScale (n : ℕ) : ℝ := Real.log n / Real.log (Real.log n)

/-- The precise specialized input required from Krenn--Suppakitpaisarn--Wagner.
This is a proposition, not an axiom or a claim that the input has been proved. -/
def SparseRepresentationBound : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ q : ℕ, 2 < q →
    ∃ s : Finset ℕ, SparseDecomposition q s ∧ (s.card : ℝ) ≤ K * logScale q

end HadamardMultibase
