module

public import HadamardMultibase.CraigenInduction

@[expose] public section

namespace HadamardMultibase

open Matrix

/-- Replace every signed-permutation block by its product with a Sylvester
Hadamard matrix. The resulting matrix is binary and has the required Gram matrix. -/
theorem hadamardOrder_of_signed_blocks {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Nonempty ι] [Nonempty κ]
    (A : Matrix ι ι (Matrix κ κ ℤ))
    (hA : ∀ i j, IsSignedPermutation (A i j))
    (hGram : A * Aᴴ = (Fintype.card ι : Matrix ι ι (Matrix κ κ ℤ)))
    (H : Matrix κ κ ℤ) (hH : H.IsHadamard) :
    HadamardOrder (Fintype.card ι * Fintype.card κ) := by
  let D : Matrix ι ι (Matrix κ κ ℤ) := Matrix.diagonal (fun _ => H)
  let K := A * D
  let M := Matrix.comp ι ι κ κ ℤ K
  have hHGram : H * Hᴴ = (Fintype.card κ : Matrix κ κ ℤ) := by
    simpa only [Nat.cast_smul_eq_nsmul, nsmul_one] using hH.mul_conjTranspose
  have hDGram : D * Dᴴ = (Fintype.card κ : Matrix ι ι (Matrix κ κ ℤ)) := by
    dsimp [D]
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    simp only [Pi.star_apply, star_eq_conjTranspose, hHGram]
    exact Matrix.diagonal_natCast _
  have hKGram : K * Kᴴ =
      ((Fintype.card κ * Fintype.card ι : ℕ) : Matrix ι ι (Matrix κ κ ℤ)) := by
    change (A * D) * (A * D)ᴴ = _
    rw [Matrix.conjTranspose_mul]
    calc
      _ = A * (D * Dᴴ) * Aᴴ := by noncomm_ring
      _ = A * (Fintype.card κ : Matrix ι ι (Matrix κ κ ℤ)) * Aᴴ := by rw [hDGram]
      _ = (Fintype.card κ : Matrix ι ι (Matrix κ κ ℤ)) * (A * Aᴴ) := by
        noncomm_ring [(Nat.commute_cast A (Fintype.card κ)).eq]
      _ = _ := by rw [hGram, Nat.cast_mul]
  have hMGram : M * Mᴴ =
      ((Fintype.card κ * Fintype.card ι : ℕ) : Matrix (ι × κ) (ι × κ) ℤ) := by
    dsimp only [M]
    rw [← matrix_comp_conjTranspose]
    change (Matrix.compRingEquiv ι κ ℤ K) * (Matrix.compRingEquiv ι κ ℤ Kᴴ) = _
    rw [← map_mul, hKGram, map_natCast]
  have hM : M.IsHadamard := by
    apply Matrix.IsHadamard.of_mul_conjTranspose
    · rintro ⟨i, a⟩ ⟨j, b⟩
      apply Unitary.mem_iff_eq_one_or_eq_neg_one.mpr
      have hbinary := (hA i j).binary_mul H (fun a b =>
        Unitary.mem_iff_eq_one_or_eq_neg_one.mp (hH.apply_mem a b))
      have hentry : M (i, a) (j, b) = (A i j * H) a b := by
        simp [M, K, D, Matrix.comp_apply, Matrix.mul_diagonal]
      rw [hentry]
      exact hbinary a b
    · rw [Nat.cast_smul_eq_nsmul, nsmul_one]
      simpa only [Fintype.card_prod, Nat.mul_comm] using hMGram
    · apply isRegular_iff_ne_zero.mpr
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card (ι × κ) ≠ 0)
  simpa only [Fintype.card_prod] using hadamardOrder_of_index M hM

/-- Craigen's supplementary-sequence construction, in a direct matrix form.
This is Corollary 3.8 of Livinskyi's thesis, with n+1 input sequences. -/
theorem hadamardOrder_of_supplementary_sequences {G : Type*} [Fintype G]
    [DecidableEq G] [AddCommGroup G] (n : ℕ) (s : Fin (n + 1) → G → ℤ)
    (htern : ∀ i x, s i x = 0 ∨ s i x = 1 ∨ s i x = -1)
    (hsym : ∀ i x, s i x = 0 ↔ s i (-x) = 0)
    (hdisj : ∀ i j, i ≠ j → ∀ x, s i x = 0 ∨ s j x = 0)
    (hfull : ∀ x, ∃ i, s i x ≠ 0)
    (hGram : (∑ i, circulant (s i) * (circulant (s i))ᴴ) =
      (Fintype.card G : Matrix G G ℤ)) :
    HadamardOrder (Fintype.card G * 2 ^ n) := by
  obtain ⟨f, hf, hsupport, _, _, hfGram⟩ := merge_ternary_family n s htern hsym hdisj
  obtain ⟨H, hH⟩ := exists_hadamard_coeffSpace n
  have hblocks : ∀ i j, IsSignedPermutation (circulant f i j) := by
    intro i j
    have hne : f (i - j) ≠ 0 := by
      intro hz
      obtain ⟨k, hk⟩ := hfull (i - j)
      exact hk ((hsupport (i - j)).mp hz k)
    exact (hf (i - j)).resolve_left hne
  have henergy : circulant f * (circulant f)ᴴ =
      (Fintype.card G : Matrix G G (Matrix (CoeffSpace n) (CoeffSpace n) ℤ)) := by
    rw [hfGram, hGram, map_natCast]
  simpa only [card_coeffSpace] using hadamardOrder_of_signed_blocks (circulant f) hblocks henergy H hH

end HadamardMultibase
