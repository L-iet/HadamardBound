module

public import HadamardMultibase.CraigenScalar
public import HadamardMultibase.CoefficientSpace

@[expose] public section

namespace HadamardMultibase

open Matrix

/-- Merge n+1 disjoint quasisymmetric ternary sequences. The coefficient
dimension is exactly 2^n, and their scalar Gram matrices add without loss. -/
theorem merge_ternary_family {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (n : ℕ) : ∀ (s : Fin (n + 1) → G → ℤ),
      (∀ i x, s i x = 0 ∨ s i x = 1 ∨ s i x = -1) →
      (∀ i x, s i x = 0 ↔ s i (-x) = 0) →
      (∀ i j, i ≠ j → ∀ x, s i x = 0 ∨ s j x = 0) →
      ∃ f : G → Matrix (CoeffSpace n) (CoeffSpace n) ℤ,
        (∀ x, SignedOrZero (f x)) ∧
        (∀ x, f x = 0 ↔ ∀ i, s i x = 0) ∧
        (∀ x, f x = 0 ↔ f (-x) = 0) ∧
        ((circulant f)ᴴ * circulant f = circulant f * (circulant f)ᴴ) ∧
        circulant f * (circulant f)ᴴ =
          scalarLift G (CoeffSpace n) (∑ i, circulant (s i) * (circulant (s i))ᴴ) := by
  induction n with
  | zero =>
    intro s htern hsym _
    refine ⟨fun x => (s 0 x : Matrix (CoeffSpace 0) (CoeffSpace 0) ℤ), ?_, ?_, ?_, ?_, ?_⟩
    · exact fun x => scalarMatrix_signedOrZero (htern 0 x)
    · intro x
      rw [scalarMatrix_eq_zero_iff]
      simp
    · intro x
      rw [scalarMatrix_eq_zero_iff, scalarMatrix_eq_zero_iff]
      exact hsym 0 x
    · exact scalar_circulant_normal (s 0)
    · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
      rw [← scalarLift_circulant, ← scalarLift_conjTranspose, ← map_mul]
  | succ n ih =>
    intro s htern hsym hdisj
    obtain ⟨f, hf, hsupport, hfsym, hfnormal, hfenergy⟩ :=
      ih (fun i => s i.succ) (fun i => htern i.succ) (fun i => hsym i.succ)
        (fun i j hij => hdisj i.succ j.succ (by intro h; exact hij (Fin.succ_inj.mp h)))
    let g : G → Matrix (CoeffSpace n) (CoeffSpace n) ℤ :=
      fun x => (s 0 x : Matrix (CoeffSpace n) (CoeffSpace n) ℤ)
    have hgzero (x : G) : g x = 0 ↔ s 0 x = 0 := scalarMatrix_eq_zero_iff _
    have hg (x : G) : SignedOrZero (g x) := scalarMatrix_signedOrZero (htern 0 x)
    have hgsym (x : G) : g x = 0 ↔ g (-x) = 0 := by
      rw [hgzero, hgzero]
      exact hsym 0 x
    have hfgdisj : ∀ x, f x = 0 ∨ g x = 0 := by
      intro x
      by_cases hx : s 0 x = 0
      · exact Or.inr ((hgzero x).mpr hx)
      · apply Or.inl
        apply (hsupport x).mpr
        intro i
        exact (hdisj i.succ 0 (Fin.succ_ne_zero i) x).resolve_right hx
    have hgnormal : (circulant g)ᴴ * circulant g = circulant g * (circulant g)ᴴ :=
      scalar_circulant_normal (s 0)
    have hfg : Commute (circulant f) (circulant g) := circulant_commute_integer f (s 0)
    have hstarfg : Commute (circulant f)ᴴ (circulant g) := by
      rw [Matrix.conjTranspose_circulant]
      exact circulant_commute_integer _ (s 0)
    refine ⟨mergeSequence f g, mergeSequence_signedOrZero f g hf hg hfsym hgsym hfgdisj,
      ?_, mergeSequence_quasisymmetric f g hfsym hgsym, ?_, ?_⟩
    · intro x
      rw [mergeSequence_eq_zero f g hfsym hgsym, hsupport, hgzero]
      constructor
      · rintro ⟨htail, hzero⟩ i
        exact Fin.cases hzero htail i
      · intro hall
        exact ⟨fun i => hall i.succ, hall 0⟩
    · rw [← coefficientMerge_circulant]
      exact coefficientMerge_normal (circulant f) (circulant g) hfg hstarfg hfnormal hgnormal
    · have hgenergy : circulant g * (circulant g)ᴴ =
          scalarLift G (CoeffSpace n) (circulant (s 0) * (circulant (s 0))ᴴ) := by
        rw [← scalarLift_circulant, ← scalarLift_conjTranspose, ← map_mul]
      have hadded : circulant f * (circulant f)ᴴ + circulant g * (circulant g)ᴴ =
          scalarLift G (CoeffSpace n)
            ((∑ i : Fin (n + 1), circulant (s i.succ) * (circulant (s i.succ))ᴴ) +
              circulant (s 0) * (circulant (s 0))ᴴ) := by
        rw [hfenergy, hgenergy, ← map_add]
      rw [← coefficientMerge_circulant]
      calc
        _ = scalarLift G (CoeffSpace n ⊕ CoeffSpace n)
            ((∑ i : Fin (n + 1), circulant (s i.succ) * (circulant (s i.succ))ᴴ) +
              circulant (s 0) * (circulant (s 0))ᴴ) :=
          coefficientMerge_scalar_energy (circulant f) (circulant g) _ hfg hfnormal hgnormal hadded
        _ = _ := by
          congr 1
          conv_rhs => rw [Fin.sum_univ_succ]
          exact add_comm _ _

end HadamardMultibase
