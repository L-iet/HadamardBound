module

public import HadamardMultibase.WeightedTrees

@[expose] public section

namespace HadamardMultibase

/-- Each step either discovers a fresh vertex or revisits an earlier position. -/
inductive WalkPattern : ℕ → Type
  | start : WalkPattern 0
  | fresh {n : ℕ} (p : WalkPattern n) : WalkPattern (n + 1)
  | revisit {n : ℕ} (p : WalkPattern n) (reference : Fin (n + 1)) : WalkPattern (n + 1)

def walkPatternZeroEquiv : WalkPattern 0 ≃ Unit where
  toFun _ := ()
  invFun _ := .start
  left_inv p := by cases p; rfl
  right_inv _ := rfl

def walkPatternSuccEquiv (n : ℕ) :
    WalkPattern (n + 1) ≃ WalkPattern n ⊕ (WalkPattern n × Fin (n + 1)) where
  toFun
    | .fresh p => Sum.inl p
    | .revisit p r => Sum.inr (p, r)
  invFun
    | Sum.inl p => .fresh p
    | Sum.inr (p, r) => .revisit p r
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with p | ⟨p, r⟩ <;> rfl

instance walkPatternFintype : (n : ℕ) → Fintype (WalkPattern n)
  | 0 => Fintype.ofEquiv Unit walkPatternZeroEquiv.symm
  | n + 1 => by
      letI := walkPatternFintype n
      exact Fintype.ofEquiv (WalkPattern n ⊕ (WalkPattern n × Fin (n + 1)))
        (walkPatternSuccEquiv n).symm

instance walkPatternDecidableEq : (n : ℕ) → DecidableEq (WalkPattern n)
  | 0 => fun p q => isTrue (by cases p; cases q; rfl)
  | n + 1 => by
      letI := walkPatternDecidableEq n
      exact (walkPatternSuccEquiv n).injective.decidableEq

theorem card_walkPattern_le (n : ℕ) : Fintype.card (WalkPattern n) ≤ (n + 1) ^ n := by
  induction n with
  | zero =>
    rw [Fintype.card_congr walkPatternZeroEquiv]
    simp
  | succ n ih =>
    rw [Fintype.card_congr (walkPatternSuccEquiv n), Fintype.card_sum,
      Fintype.card_prod, Fintype.card_fin]
    have hcard : Fintype.card (WalkPattern n) + Fintype.card (WalkPattern n) * (n + 1) =
        Fintype.card (WalkPattern n) * (n + 2) := by ring
    rw [hcard]
    calc
      _ ≤ (n + 1) ^ n * (n + 2) := Nat.mul_le_mul_right _ ih
      _ ≤ (n + 2) ^ n * (n + 2) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
      _ = _ := by rw [pow_succ]

/-- The discovery tree and the vertex indices described by a reference code. -/
structure WalkPatternData (n : ℕ) where
  fresh : ℕ
  tree : IncreasingTree fresh
  vertex : Fin (n + 1) → Fin (fresh + 1)

noncomputable abbrev walkPatternData : {n : ℕ} → WalkPattern n → WalkPatternData n
  | 0, .start => ⟨0, .root, fun _ => 0⟩
  | n + 1, .fresh p =>
      let d := walkPatternData p
      ⟨d.fresh + 1, .attach d.tree (d.vertex (Fin.last n)),
        Fin.snoc (fun i => (d.vertex i).castSucc) (Fin.last (d.fresh + 1))⟩
  | _n + 1, .revisit p r =>
      let d := walkPatternData p
      ⟨d.fresh, d.tree, Fin.snoc d.vertex (d.vertex r)⟩

theorem walkPattern_fresh_le {n : ℕ} (p : WalkPattern n) : (walkPatternData p).fresh ≤ n := by
  induction p with
  | start => change 0 ≤ 0; omega
  | @fresh n p ih =>
    change (walkPatternData p).fresh + 1 ≤ n + 1
    exact Nat.succ_le_succ ih
  | revisit p r ih => exact ih.trans (Nat.le_succ _)

/-- Assign actual vertex labels to the discovery vertices of a pattern. -/
noncomputable def realizeWalkPattern {V : Type*} {n : ℕ} (p : WalkPattern n)
    (f : Fin ((walkPatternData p).fresh + 1) → V) : Fin (n + 1) → V :=
  fun i => f ((walkPatternData p).vertex i)

@[simp] theorem walkPattern_fresh_vertex_last {n : ℕ} (p : WalkPattern n) :
    (walkPatternData (.fresh p)).vertex (Fin.last (n + 1)) =
      Fin.last ((walkPatternData p).fresh + 1) := by
  change Fin.snoc (α := fun _ : Fin (n + 2) => Fin ((walkPatternData p).fresh + 2))
    (fun i => ((walkPatternData p).vertex i).castSucc)
    (Fin.last ((walkPatternData p).fresh + 1)) (Fin.last (n + 1)) = _
  rw [Fin.snoc_last]

@[simp] theorem walkPattern_fresh_vertex_castSucc {n : ℕ} (p : WalkPattern n) (i : Fin (n + 1)) :
    (walkPatternData (.fresh p)).vertex i.castSucc = ((walkPatternData p).vertex i).castSucc := by
  change Fin.snoc (α := fun _ : Fin (n + 2) => Fin ((walkPatternData p).fresh + 2))
    (fun i => ((walkPatternData p).vertex i).castSucc)
    (Fin.last ((walkPatternData p).fresh + 1)) i.castSucc = _
  rw [Fin.snoc_castSucc]

@[simp] theorem walkPattern_revisit_vertex_last {n : ℕ} (p : WalkPattern n) (r : Fin (n + 1)) :
    (walkPatternData (.revisit p r)).vertex (Fin.last (n + 1)) = (walkPatternData p).vertex r := by
  change Fin.snoc (α := fun _ : Fin (n + 2) => Fin ((walkPatternData p).fresh + 1))
    (walkPatternData p).vertex ((walkPatternData p).vertex r) (Fin.last (n + 1)) = _
  rw [Fin.snoc_last]

@[simp] theorem walkPattern_revisit_vertex_castSucc {n : ℕ} (p : WalkPattern n)
    (r i : Fin (n + 1)) :
    (walkPatternData (.revisit p r)).vertex i.castSucc = (walkPatternData p).vertex i := by
  change Fin.snoc (α := fun _ : Fin (n + 2) => Fin ((walkPatternData p).fresh + 1))
    (walkPatternData p).vertex ((walkPatternData p).vertex r) i.castSucc = _
  rw [Fin.snoc_castSucc]

theorem walkPattern_vertex_surjective {n : ℕ} (p : WalkPattern n) :
    Function.Surjective (walkPatternData p).vertex := by
  induction p with
  | start =>
    intro j
    fin_cases j
    exact ⟨0, rfl⟩
  | @fresh n p ih =>
    intro j
    change Fin ((walkPatternData p).fresh + 2) at j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · exact ⟨Fin.last (n + 1), walkPattern_fresh_vertex_last p⟩
    · obtain ⟨i, hi⟩ := ih j
      refine ⟨i.castSucc, ?_⟩
      rw [walkPattern_fresh_vertex_castSucc]
      exact congrArg Fin.castSucc hi
  | @revisit n p r ih =>
    intro j
    obtain ⟨i, hi⟩ := ih j
    refine ⟨i.castSucc, ?_⟩
    rw [walkPattern_revisit_vertex_castSucc]
    exact hi

theorem realizeWalkPattern_fresh {V : Type*} {n : ℕ} (p : WalkPattern n)
    (f : Fin ((walkPatternData p).fresh + 1) → V) (x : V) :
    realizeWalkPattern (.fresh p)
      (Fin.snoc (α := fun _ : Fin ((walkPatternData p).fresh + 2) => V) f x) =
      Fin.snoc (α := fun _ : Fin (n + 2) => V) (realizeWalkPattern p f) x := by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [realizeWalkPattern]
  · simp [realizeWalkPattern]

theorem realizeWalkPattern_revisit {V : Type*} {n : ℕ} (p : WalkPattern n)
    (r : Fin (n + 1)) (f : Fin ((walkPatternData p).fresh + 1) → V) :
    realizeWalkPattern (.revisit p r) f =
      Fin.snoc (α := fun _ : Fin (n + 2) => V) (realizeWalkPattern p f)
        (realizeWalkPattern p f r) := by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [realizeWalkPattern]
  · simp [realizeWalkPattern]

/-- Every vertex history has a discovery code with distinct labels on its
discovery vertices. Thus no vertex histories are lost in pattern counting. -/
theorem exists_injective_walkPattern_realization {V : Type*} {n : ℕ}
    (w : Fin (n + 1) → V) :
    ∃ p : WalkPattern n, ∃ f : Fin ((walkPatternData p).fresh + 1) → V,
      Function.Injective f ∧ realizeWalkPattern p f = w := by
  classical
  induction n with
  | zero =>
    refine ⟨.start, (fun _ : Fin 1 => w 0), ?_, ?_⟩
    · intro i j _
      apply Fin.ext
      have hi : i.val < 1 := i.isLt
      have hj : j.val < 1 := j.isLt
      omega
    · ext i
      fin_cases i
      rfl
  | succ n ih =>
    obtain ⟨p, f, hf, hw⟩ := ih (Fin.init w)
    by_cases hold : ∃ i : Fin (n + 1), Fin.init w i = w (Fin.last (n + 1))
    · obtain ⟨r, hr⟩ := hold
      refine ⟨.revisit p r, f, hf, ?_⟩
      rw [realizeWalkPattern_revisit, hw, hr, Fin.snoc_init_self]
    · have hnew : w (Fin.last (n + 1)) ∉ Set.range f := by
        rintro ⟨a, ha⟩
        obtain ⟨i, hi⟩ := walkPattern_vertex_surjective p a
        apply hold
        refine ⟨i, ?_⟩
        have h := congrFun hw i
        change f ((walkPatternData p).vertex i) = Fin.init w i at h
        rw [hi] at h
        exact h.symm.trans ha
      refine ⟨.fresh p, Fin.snoc (α := fun _ : Fin ((walkPatternData p).fresh + 2) => V)
        f (w (Fin.last (n + 1))),
        Fin.snoc_injective_of_injective hf hnew, ?_⟩
      rw [realizeWalkPattern_fresh p f, hw, Fin.snoc_init_self]

end HadamardMultibase
