module

public import HadamardMultibase.WalkEdgeCounting

@[expose] public section

namespace HadamardMultibase

def treeEdgeWord {V τ : Type*} (label : V → V → τ) {n : ℕ}
    (tree : IncreasingTree n) (f : Fin (n + 1) → V) : Fin n → τ :=
  fun e => label (f (increasingTreeEdges tree e).1) (f (increasingTreeEdges tree e).2)

/-- Distinct discovery-tree edges have distinct faithful unordered labels. -/
theorem treeEdgeWord_injective {V τ : Type*} (label : V → V → τ)
    (hlabel : ∀ a b c d, label a b = label c d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c))
    {n : ℕ} (tree : IncreasingTree n) {f : Fin (n + 1) → V}
    (hf : Function.Injective f) : Function.Injective (treeEdgeWord label tree f) := by
  intro e g heq
  have he := increasingTreeEdges_parent_le_child tree e
  have hg := increasingTreeEdges_parent_le_child tree g
  change label (f (increasingTreeEdges tree e).1) (f (increasingTreeEdges tree e).2) =
    label (f (increasingTreeEdges tree g).1) (f (increasingTreeEdges tree g).2) at heq
  rcases hlabel _ _ _ _ heq with ⟨_, hchild⟩ | ⟨h₁, h₂⟩
  · have h := congrArg Fin.val (hf hchild)
    apply Fin.ext
    omega
  · have h₁' := congrArg Fin.val (hf h₁)
    have h₂' := congrArg Fin.val (hf h₂)
    omega

theorem treeEdgeWord_attach {V τ : Type*} (label : V → V → τ) {n : ℕ}
    (tree : IncreasingTree n) (parent : Fin (n + 1)) (f : Fin (n + 2) → V) :
    treeEdgeWord label (.attach tree parent) f =
      Fin.snoc (α := fun _ : Fin (n + 1) => τ) (treeEdgeWord label tree (Fin.init f))
        (label (f parent.castSucc) (f (Fin.last (n + 1)))) := by
  ext e
  refine Fin.lastCases ?_ (fun e => ?_) e
  · simp [treeEdgeWord]
  · simp [treeEdgeWord, Fin.init]

theorem realizeWalkPattern_fresh_general {V : Type*} {n : ℕ} (p : WalkPattern n)
    (f : Fin ((walkPatternData p).fresh + 2) → V) :
    realizeWalkPattern (.fresh p) f =
      Fin.snoc (α := fun _ : Fin (n + 2) => V) (realizeWalkPattern p (Fin.init f))
        (f (Fin.last ((walkPatternData p).fresh + 1))) := by
  conv_lhs => rw [← Fin.snoc_init_self f]
  exact realizeWalkPattern_fresh p (Fin.init f) _

/-- The discovery tree uses only edges actually traversed by the history. -/
theorem treeEdgeWord_support_subset_history {V τ : Type*} [DecidableEq τ]
    (label : V → V → τ) {n : ℕ} (p : WalkPattern n)
    (f : Fin ((walkPatternData p).fresh + 1) → V) :
    Finset.univ.image (treeEdgeWord label (walkPatternData p).tree f) ⊆
      Finset.univ.image (historyEdgeWord label (realizeWalkPattern p f)) := by
  classical
  induction p with
  | start => simp
  | fresh p ih =>
    change Fin ((walkPatternData p).fresh + 2) → V at f
    change (Finset.univ : Finset (Fin ((walkPatternData p).fresh + 1))).image (treeEdgeWord label
      (.attach (walkPatternData p).tree ((walkPatternData p).vertex (Fin.last _))) f) ⊆ _
    rw [treeEdgeWord_attach, image_univ_snoc, realizeWalkPattern_fresh_general,
      historyEdgeWord_snoc, image_univ_snoc]
    apply Finset.insert_subset_insert
    exact ih (Fin.init f)
  | revisit p r ih =>
    change Fin ((walkPatternData p).fresh + 1) → V at f
    change (Finset.univ : Finset (Fin (walkPatternData p).fresh)).image
      (treeEdgeWord label (walkPatternData p).tree f) ⊆ _
    rw [realizeWalkPattern_revisit, historyEdgeWord_snoc, image_univ_snoc]
    exact (ih f).trans (Finset.subset_insert _ _)

end HadamardMultibase
