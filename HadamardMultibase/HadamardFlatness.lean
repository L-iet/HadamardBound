module

public import HadamardMultibase.NormalizedHadamard
public import HadamardMultibase.Results

@[expose] public section

namespace HadamardMultibase

open Matrix

/-- A nearby larger Hadamard matrix gives a flat orthogonal matrix of the
desired order, with the exact finite-dimensional bound. -/
theorem flat_orthogonal_of_hadamardOrder {m n : ℕ} (hH : HadamardOrder m)
    (hnm : n < m) (hk : ((m - n : ℕ) : ℝ) < Real.sqrt m) :
    ∃ M : Matrix (Fin n) (Fin n) ℝ, Mᵀ * M = 1 ∧
      ∀ i j, |M i j| ≤ 1 / (Real.sqrt m - (m - n : ℕ)) := by
  classical
  obtain ⟨hm, H, hH⟩ := hH
  let : Nonempty (Fin (m - n)) := ⟨⟨0, by omega⟩⟩
  let e : (Fin (m - n) ⊕ Fin n) ≃ Fin m :=
    finSumFinEquiv.trans (finCongr (by omega))
  let H' : Matrix (Fin (m - n) ⊕ Fin n) (Fin (m - n) ⊕ Fin n) ℤ :=
    reindex e.symm e.symm H
  have hH' : H'.IsHadamard := hH.reindex e.symm e.symm
  let Q := normalizedHadamard H'
  have hcard : Fintype.card (Fin (m - n) ⊕ Fin n) = m := by simp; omega
  have horth : Qᵀ * Q = 1 := normalizedHadamard_orthogonal hH'
  have hentry : ∀ i j, |Q i j| ≤ 1 / Real.sqrt (m : ℝ) := by
    intro i j
    have h := normalizedHadamard_abs_entry hH' i j
    rw [hcard] at h
    exact h.le
  have hs : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hblockorth :
      (fromBlocks Q.toBlocks₁₁ Q.toBlocks₁₂ Q.toBlocks₂₁ Q.toBlocks₂₂)ᵀ *
      fromBlocks Q.toBlocks₁₁ Q.toBlocks₁₂ Q.toBlocks₂₁ Q.toBlocks₂₂ = 1 := by
    rw [fromBlocks_toBlocks]
    exact horth
  have h := submatrix_flatness Q.toBlocks₁₁ Q.toBlocks₁₂ Q.toBlocks₂₁ Q.toBlocks₂₂
    hblockorth hs (by simpa using hk)
    (fun i j => hentry (Sum.inl i) (Sum.inl j))
    (fun i j => hentry (Sum.inl i) (Sum.inr j))
    (fun i j => hentry (Sum.inr i) (Sum.inl j))
    (fun i j => hentry (Sum.inr i) (Sum.inr j))
  simpa only [Fintype.card_fin] using h

/-- Flat orthogonal matrices from the subpolynomial Hadamard gap bound.
The range ε<1/2 is necessary for the displayed positive denominator. -/
theorem flat_orthogonal_bound (hS : SparseRepresentationBound)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ M : Matrix (Fin n) (Fin n) ℝ, Mᵀ * M = 1 ∧
        ∀ i j, |M i j| ≤ 1 / (Real.sqrt n - (n : ℝ) ^ ε) := by
  obtain ⟨N, hN⟩ := subpolynomial_gap_bound hS hε
  refine ⟨max N 2, ?_⟩
  intro n hn
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  obtain ⟨d, hd, hdbound⟩ := hN n hnN
  obtain ⟨m, hm, hnm, hmd⟩ := hd n le_rfl
  have hpow : (n : ℝ) ^ ε < Real.sqrt (n : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (show 1 < n by omega)) hεhalf
  have hk : ((m - n : ℕ) : ℝ) ≤ (n : ℝ) ^ ε := by
    have hkd : m - n ≤ d := by omega
    exact (Nat.cast_le.mpr hkd).trans hdbound
  have hsqrt : Real.sqrt (n : ℝ) ≤ Real.sqrt (m : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hnm.le)
  obtain ⟨M, hM, hentries⟩ := flat_orthogonal_of_hadamardOrder hm hnm
    (hk.trans_lt (hpow.trans_le hsqrt))
  refine ⟨M, hM, ?_⟩
  intro i j
  apply (hentries i j).trans
  apply one_div_le_one_div_of_le (by linarith : 0 < Real.sqrt (n : ℝ) - (n : ℝ) ^ ε)
  linarith

end HadamardMultibase
