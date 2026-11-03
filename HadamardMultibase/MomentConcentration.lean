module

public import HadamardMultibase.WalkSumBound

@[expose] public section

namespace HadamardMultibase

open Matrix
open scoped Matrix.Norms.L2Operator

theorem wordMomentMajorant_nonneg
    {ι τ : Type*} [Fintype ι] [Fintype τ] [DecidableEq ι]
    {μ : ι → ℝ} (hμ : ∀ i, |μ i| ≤ 1) (word : τ → ι) :
    0 ≤ wordMomentMajorant μ word :=
  (abs_nonneg _).trans (roundingWeight_word_moment_le_majorant hμ word)

theorem sum_closed_walk_majorants_le_histories
    {V τ : Type*} [Fintype V] [DecidableEq V] [Fintype τ] [DecidableEq τ]
    {μ : τ → ℝ} (hμ : ∀ a, |μ a| ≤ 1) (label : V → V → τ) (k : ℕ) :
    (∑ i : V, ∑ f : Fin k → V, wordMomentMajorant μ (matrixPathWord label i i f)) ≤
      ∑ w : Fin (k + 2) → V, wordMomentMajorant μ (historyEdgeWord label w) := by
  classical
  let encode : V × (Fin k → V) → (Fin (k + 2) → V) :=
    fun p => Fin.snoc (α := fun _ : Fin (k + 2) => V) (Fin.cons p.1 p.2) p.1
  have hinj : Function.Injective encode := by
    intro a b hab
    have h := congrArg Fin.init hab
    change Fin.init (Fin.snoc (α := fun _ : Fin (k + 2) => V) (Fin.cons a.1 a.2) a.1) =
      Fin.init (Fin.snoc (α := fun _ : Fin (k + 2) => V) (Fin.cons b.1 b.2) b.1) at h
    simp only [Fin.init_snoc] at h
    apply Prod.ext
    · simpa only [Fin.cons_zero] using congrFun h 0
    · simpa only [Fin.tail_cons] using congrArg Fin.tail h
  have hsum : (∑ i : V, ∑ f : Fin k → V, wordMomentMajorant μ (matrixPathWord label i i f)) =
      ∑ p : V × (Fin k → V), wordMomentMajorant μ (matrixPathWord label p.1 p.1 p.2) :=
    (Fintype.sum_prod_type (fun p : V × (Fin k → V) =>
      wordMomentMajorant μ (matrixPathWord label p.1 p.1 p.2))).symm
  rw [hsum]
  apply Finset.sum_le_sum_of_injOn encode hinj.injOn (Finset.subset_univ _)
  · intro p _
    exact (congrArg (wordMomentMajorant μ) (historyEdgeWord_closed_path label p.1 p.2)).symm.le
  · intro w _ _
    exact wordMomentMajorant_nonneg hμ _

/-- A finite moment concentration bound for independent centered coordinates
with a variance row bound. This weaker logarithmic-loss alternative to matrix
Bernstein suffices for every strict power exponent in the application. -/
theorem exists_rounding_norm_moment_bound
    {V τ : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype τ] [DecidableEq τ]
    (label : V → V → τ)
    (hlabel : ∀ a b c d, label a b = label c d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c))
    {μ : τ → ℝ} (hμ : ∀ a, |μ a| ≤ 1) {v : ℝ} (hv : 1 ≤ v)
    (hrow : ∀ x, ∑ y, (1 - (μ (label x y)) ^ 2) ≤ v)
    (mask : Matrix V V ℝ) (hmask : ∀ i j, |mask i j| ≤ 1)
    (hsym : ∀ ω : τ → Bool, (centeredLabelMatrix μ label mask ω)ᵀ =
      centeredLabelMatrix μ label mask ω) {k : ℕ} (hk : 0 < k) :
    ∃ ω : τ → Bool, ‖centeredLabelMatrix μ label mask ω‖ ^ (2 * k) ≤
      (2 : ℝ) ^ (2 * k) * (((2 * k + 1) ^ (2 * k) : ℕ) : ℝ) *
        (Fintype.card V : ℝ) * v ^ k := by
  obtain ⟨ω, hω⟩ := exists_rounding_norm_pow_le_walk_sum hμ label mask hsym hk
  refine ⟨ω, hω.trans ?_⟩
  have hpathmask (i : V) (f : Fin (2 * k - 1) → V) : |matrixPathWeight mask i i f| ≤ 1 := by
    rw [matrixPathWeight, Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => hmask _ _)
  calc
    _ ≤ ∑ i : V, ∑ f : Fin (2 * k - 1) → V, wordMomentMajorant μ (matrixPathWord label i i f) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro f _
      exact mul_le_of_le_one_left (wordMomentMajorant_nonneg hμ _) (hpathmask i f)
    _ ≤ ∑ w : Fin (2 * k - 1 + 2) → V, wordMomentMajorant μ (historyEdgeWord label w) :=
      sum_closed_walk_majorants_le_histories hμ label (2 * k - 1)
    _ ≤ _ := by
      have h := sum_wordMomentMajorant_histories_le label hlabel hμ hv hrow
        (2 * k - 1 + 1) k (by omega)
      conv at h => rhs; rw [show 2 * k - 1 + 1 = 2 * k by omega]
      exact h

end HadamardMultibase
