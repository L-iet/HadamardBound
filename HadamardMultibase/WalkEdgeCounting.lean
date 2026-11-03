module

public import HadamardMultibase.WalkPatterns
public import HadamardMultibase.RoundingWordMoments
public import HadamardMultibase.RoundingWalkMoments

@[expose] public section

namespace HadamardMultibase

theorem image_univ_snoc {V : Type*} [DecidableEq V] {n : ℕ}
    (w : Fin n → V) (x : V) :
    Finset.univ.image (Fin.snoc (α := fun _ : Fin (n + 1) => V) w x) =
      insert x (Finset.univ.image w) := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
    revert hi
    refine Fin.lastCases ?_ (fun i => ?_) i
    · intro hi
      simp only [Fin.snoc_last] at hi
      exact Finset.mem_insert.mpr (Or.inl hi.symm)
    · intro hi
      simp only [Fin.snoc_castSucc] at hi
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩))
  · intro ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact Finset.mem_image.mpr ⟨Fin.last n, Finset.mem_univ _, Fin.snoc_last _ _⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, by simpa using hi⟩

theorem image_realizeWalkPattern {V : Type*} [DecidableEq V] {n : ℕ}
    (p : WalkPattern n) (f : Fin ((walkPatternData p).fresh + 1) → V) :
    Finset.univ.image (realizeWalkPattern p f) = Finset.univ.image f := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨(walkPatternData p).vertex i, Finset.mem_univ _, hi⟩
  · intro hx
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
    obtain ⟨i, hi⟩ := walkPattern_vertex_surjective p a
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by simpa [realizeWalkPattern, hi] using ha⟩

theorem card_image_realizeWalkPattern {V : Type*} [DecidableEq V] {n : ℕ}
    (p : WalkPattern n) {f : Fin ((walkPatternData p).fresh + 1) → V}
    (hf : Function.Injective f) :
    (Finset.univ.image (realizeWalkPattern p f)).card = (walkPatternData p).fresh + 1 := by
  rw [image_realizeWalkPattern, Finset.card_image_of_injective _ hf, Finset.card_univ,
    Fintype.card_fin]

def historyEdgeWord {V τ : Type*} (label : V → V → τ) {n : ℕ}
    (w : Fin (n + 1) → V) : Fin n → τ := fun t => label (w t.castSucc) (w t.succ)

theorem historyEdgeWord_snoc {V τ : Type*} (label : V → V → τ) {n : ℕ}
    (w : Fin (n + 1) → V) (x : V) :
    historyEdgeWord label (Fin.snoc (α := fun _ : Fin (n + 2) => V) w x) =
      Fin.snoc (α := fun _ : Fin (n + 1) => τ) (historyEdgeWord label w)
        (label (w (Fin.last n)) x) := by
  ext t
  refine Fin.lastCases ?_ (fun t => ?_) t
  · simp only [historyEdgeWord, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
  · simp only [historyEdgeWord, Fin.snoc_castSucc]
    rw [show t.castSucc.succ = t.succ.castSucc by rfl, Fin.snoc_castSucc]

/-- Every newly visited vertex requires a new unordered edge label. -/
theorem history_vertices_card_le_edges_add_one
    {V τ : Type*} [DecidableEq V] [DecidableEq τ] (label : V → V → τ)
    (hlabel : ∀ a b c d, label a b = label c d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c))
    {n : ℕ} (w : Fin (n + 1) → V) :
    (Finset.univ.image w).card ≤ (Finset.univ.image (historyEdgeWord label w)).card + 1 := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    let u := Fin.init w
    let x := w (Fin.last (n + 1))
    have hw : Fin.snoc (α := fun _ : Fin (n + 2) => V) u x = w := Fin.snoc_init_self w
    rw [← hw, historyEdgeWord_snoc, image_univ_snoc, image_univ_snoc]
    have hi := ih u
    by_cases hx : x ∈ Finset.univ.image u
    · rw [Finset.insert_eq_of_mem hx]
      exact hi.trans (Nat.add_le_add_right
        (Finset.card_le_card (Finset.subset_insert _ _)) _)
    · have hedge : label (u (Fin.last n)) x ∉ Finset.univ.image (historyEdgeWord label u) := by
        intro he
        obtain ⟨t, _, ht⟩ := Finset.mem_image.mp he
        change label (u t.castSucc) (u t.succ) = label (u (Fin.last n)) x at ht
        have h := hlabel _ _ _ _ ht.symm
        rcases h with ⟨_, hx'⟩ | ⟨_, hx'⟩
        · exact hx (Finset.mem_image.mpr ⟨t.succ, Finset.mem_univ _, hx'.symm⟩)
        · exact hx (Finset.mem_image.mpr ⟨t.castSucc, Finset.mem_univ _, hx'.symm⟩)
      rw [Finset.card_insert_of_notMem hx, Finset.card_insert_of_notMem hedge]
      omega

theorem walkPattern_fresh_le_edge_support
    {V τ : Type*} [DecidableEq V] [DecidableEq τ] (label : V → V → τ)
    (hlabel : ∀ a b c d, label a b = label c d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c))
    {n : ℕ} (p : WalkPattern n) {f : Fin ((walkPatternData p).fresh + 1) → V}
    (hf : Function.Injective f) :
    (walkPatternData p).fresh ≤
      (Finset.univ.image (historyEdgeWord label (realizeWalkPattern p f))).card := by
  have h := history_vertices_card_le_edges_add_one label hlabel (realizeWalkPattern p f)
  rw [card_image_realizeWalkPattern p hf] at h
  omega

/-- Singleton cancellation bounds discovery vertices, not just edge labels. -/
theorem walkPattern_fresh_le_half
    {V τ : Type*} [DecidableEq V] [Fintype τ] [DecidableEq τ] (label : V → V → τ)
    (hlabel : ∀ a b c d, label a b = label c d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c))
    {n : ℕ} (p : WalkPattern n) {f : Fin ((walkPatternData p).fresh + 1) → V}
    (hf : Function.Injective f)
    (hno : ∀ a, wordMultiplicity (historyEdgeWord label (realizeWalkPattern p f)) a ≠ 1) :
    2 * (walkPatternData p).fresh ≤ n := by
  have hvertices := walkPattern_fresh_le_edge_support label hlabel p hf
  have hedge := word_support_card_le_half (historyEdgeWord label (realizeWalkPattern p f)) hno
  rw [Fintype.card_fin] at hedge
  omega

theorem exists_bounded_walkPattern_realization
    {V τ : Type*} [DecidableEq V] [Fintype τ] [DecidableEq τ] (label : V → V → τ)
    (hlabel : ∀ a b c d, label a b = label c d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c))
    {n : ℕ} (w : Fin (n + 1) → V)
    (hno : ∀ a, wordMultiplicity (historyEdgeWord label w) a ≠ 1) :
    ∃ p : WalkPattern n, ∃ f : Fin ((walkPatternData p).fresh + 1) → V,
      Function.Injective f ∧ realizeWalkPattern p f = w ∧ 2 * (walkPatternData p).fresh ≤ n := by
  obtain ⟨p, f, hf, hw⟩ := exists_injective_walkPattern_realization w
  refine ⟨p, f, hf, hw, ?_⟩
  apply walkPattern_fresh_le_half label hlabel p hf
  simpa only [hw] using hno

theorem historyEdgeWord_closed_path {V τ : Type*} (label : V → V → τ) {k : ℕ}
    (i : V) (f : Fin k → V) :
    historyEdgeWord label
      (Fin.snoc (α := fun _ : Fin (k + 2) => V) (Fin.cons i f) i) =
      matrixPathWord label i i f := by
  ext t
  simp only [historyEdgeWord, matrixPathWord, Fin.snoc_castSucc]
  rw [← Fin.cons_snoc_eq_snoc_cons, Fin.cons_succ]

end HadamardMultibase
