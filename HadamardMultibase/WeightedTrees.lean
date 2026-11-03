module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic

@[expose] public section

namespace HadamardMultibase

/-- A rooted tree built by adding each new vertex to an earlier parent.
The parameter is its number of edges. -/
inductive IncreasingTree : ℕ → Type
  | root : IncreasingTree 0
  | attach {n : ℕ} (tree : IncreasingTree n) (parent : Fin (n + 1)) : IncreasingTree (n + 1)

/-- Edges are oriented from each earlier parent to its newly added child. -/
def increasingTreeEdges : {n : ℕ} → IncreasingTree n → Fin n → Fin (n + 1) × Fin (n + 1)
  | 0, .root, e => Fin.elim0 e
  | n + 1, .attach tree parent, e =>
      Fin.snoc (α := fun _ : Fin (n + 1) => Fin (n + 2) × Fin (n + 2))
        (fun j => ((increasingTreeEdges tree j).1.castSucc, (increasingTreeEdges tree j).2.castSucc))
        (parent.castSucc, Fin.last (n + 1)) e

@[simp] theorem increasingTreeEdges_last {n : ℕ} (tree : IncreasingTree n)
    (parent : Fin (n + 1)) :
    increasingTreeEdges (.attach tree parent) (Fin.last n) =
      (parent.castSucc, Fin.last (n + 1)) := by
  change Fin.snoc (α := fun _ : Fin (n + 1) => Fin (n + 2) × Fin (n + 2))
    (fun j => ((increasingTreeEdges tree j).1.castSucc, (increasingTreeEdges tree j).2.castSucc))
    (parent.castSucc, Fin.last (n + 1)) (Fin.last n) = _
  rw [Fin.snoc_last]

@[simp] theorem increasingTreeEdges_castSucc {n : ℕ} (tree : IncreasingTree n)
    (parent : Fin (n + 1)) (e : Fin n) :
    increasingTreeEdges (.attach tree parent) e.castSucc =
      ((increasingTreeEdges tree e).1.castSucc, (increasingTreeEdges tree e).2.castSucc) := by
  change Fin.snoc (α := fun _ : Fin (n + 1) => Fin (n + 2) × Fin (n + 2))
    (fun j => ((increasingTreeEdges tree j).1.castSucc, (increasingTreeEdges tree j).2.castSucc))
    (parent.castSucc, Fin.last (n + 1)) e.castSucc = _
  rw [Fin.snoc_castSucc]

theorem increasingTreeEdges_parent_le_child {n : ℕ} (tree : IncreasingTree n) (e : Fin n) :
    (increasingTreeEdges tree e).1.val ≤ e.val ∧
      (increasingTreeEdges tree e).2.val = e.val + 1 := by
  induction tree with
  | root => exact Fin.elim0 e
  | @attach n tree parent ih =>
    refine Fin.lastCases ?_ (fun e => ?_) e
    · simp only [increasingTreeEdges_last, Fin.val_last, Fin.val_castSucc]
      have hp := parent.isLt
      constructor
      · omega
      · trivial
    · simpa only [increasingTreeEdges_castSucc, Fin.val_castSucc] using ih e

noncomputable def increasingTreeWeight {V : Type*} (W : V → V → ℝ) :
    {n : ℕ} → IncreasingTree n → (Fin (n + 1) → V) → ℝ
  | _, .root, _ => 1
  | n + 1, .attach tree parent, f =>
      increasingTreeWeight W tree (Fin.init f) * W (f parent.castSucc) (f (Fin.last (n + 1)))

theorem increasingTreeWeight_attach_snoc {V : Type*} (W : V → V → ℝ)
    {n : ℕ} (tree : IncreasingTree n) (parent : Fin (n + 1))
    (f : Fin (n + 1) → V) (x : V) :
    increasingTreeWeight W (.attach tree parent)
      (Fin.snoc (α := fun _ : Fin (n + 2) => V) f x) =
      increasingTreeWeight W tree f * W (f parent) x := by
  simp [increasingTreeWeight]

theorem increasingTreeWeight_nonneg {V : Type*} {W : V → V → ℝ}
    (hW : ∀ x y, 0 ≤ W x y) {n : ℕ} (tree : IncreasingTree n)
    (f : Fin (n + 1) → V) : 0 ≤ increasingTreeWeight W tree f := by
  induction tree with
  | root => norm_num [increasingTreeWeight]
  | attach tree parent ih =>
    exact mul_nonneg (ih (Fin.init f)) (hW _ _)

/-- Summing nonnegative tree weights costs at most one row-sum factor per
edge and one free choice of root. No symmetry or independence is required. -/
theorem sum_increasingTreeWeight_le {V : Type*} [Fintype V] [DecidableEq V]
    {W : V → V → ℝ} (hW : ∀ x y, 0 ≤ W x y) {v : ℝ} (hv : 0 ≤ v)
    (hrow : ∀ x, ∑ y, W x y ≤ v) {n : ℕ} (tree : IncreasingTree n) :
    (∑ f : Fin (n + 1) → V, increasingTreeWeight W tree f) ≤
      (Fintype.card V : ℝ) * v ^ n := by
  classical
  induction tree with
  | root => simp [increasingTreeWeight]
  | @attach n tree parent ih =>
    calc
      _ = ∑ p : V × (Fin (n + 1) → V),
          increasingTreeWeight W (.attach tree parent) (Fin.snoc p.2 p.1) :=
        ((Fin.snocEquiv (fun _ : Fin (n + 2) => V)).sum_comp
          (fun f => increasingTreeWeight W (.attach tree parent) f)).symm
      _ = ∑ f : Fin (n + 1) → V, ∑ x : V, increasingTreeWeight W tree f * W (f parent) x := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        simp only [increasingTreeWeight_attach_snoc]
      _ ≤ ∑ f : Fin (n + 1) → V, increasingTreeWeight W tree f * v := by
        apply Finset.sum_le_sum
        intro f _
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hrow _) (increasingTreeWeight_nonneg hW tree f)
      _ = (∑ f : Fin (n + 1) → V, increasingTreeWeight W tree f) * v :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ ((Fintype.card V : ℝ) * v ^ n) * v := mul_le_mul_of_nonneg_right ih hv
      _ = _ := by rw [pow_succ]; ring

theorem increasingTreeWeight_eq_prod_edges {V : Type*} (W : V → V → ℝ)
    {n : ℕ} (tree : IncreasingTree n) (f : Fin (n + 1) → V) :
    increasingTreeWeight W tree f =
      ∏ e : Fin n, W (f (increasingTreeEdges tree e).1) (f (increasingTreeEdges tree e).2) := by
  induction tree with
  | root => simp [increasingTreeWeight]
  | attach tree parent ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [increasingTreeEdges_last, increasingTreeEdges_castSucc]
    change increasingTreeWeight W tree (Fin.init f) * _ = _
    rw [ih]
    rfl

end HadamardMultibase
