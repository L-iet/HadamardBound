module

public import HadamardMultibase.Covering

@[expose] public section

namespace HadamardMultibase

def powerProduct {r : ℕ} (b e : Fin r → ℕ) : ℕ := ∏ i, b i ^ e i

def powerMonoid {r : ℕ} (b : Fin r → ℕ) : Set ℕ := Set.range (powerProduct b)

noncomputable def truncatedMonoid {r : ℕ} (b : Fin r → ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (N + 1)).filter (fun x => x ∈ powerMonoid b)

theorem mem_truncatedMonoid {r : ℕ} (b : Fin r → ℕ) (N x : ℕ) :
    x ∈ truncatedMonoid b N ↔ x ≤ N ∧ x ∈ powerMonoid b := by
  classical
  simp [truncatedMonoid]

theorem powerProduct_pos {r : ℕ} {b : Fin r → ℕ} (hb : ∀ i, 2 ≤ b i)
    (e : Fin r → ℕ) : 0 < powerProduct b e := by
  apply Finset.prod_pos
  intro i _
  exact pow_pos (by have := hb i; omega) _

theorem zero_notMem_truncatedMonoid {r : ℕ} {b : Fin r → ℕ}
    (hb : ∀ i, 2 ≤ b i) (N : ℕ) : 0 ∉ truncatedMonoid b N := by
  rw [mem_truncatedMonoid]
  rintro ⟨_, e, he⟩
  have h := powerProduct_pos hb e
  omega

theorem exponent_le_log {r : ℕ} {b : Fin r → ℕ} (hb : ∀ i, 2 ≤ b i)
    {e : Fin r → ℕ} {N : ℕ} (he : powerProduct b e ≤ N) (i : Fin r) :
    e i ≤ Nat.log 2 N := by
  have hle : b i ^ e i ≤ powerProduct b e := by
    apply Finset.single_le_prod (fun j _ => ?_) (Finset.mem_univ i)
    have h := pow_pos (show 0 < b j by have := hb j; omega) (e j)
    omega
  have hpow : 2 ^ e i ≤ b i ^ e i := Nat.pow_le_pow_left (hb i) _
  exact Nat.le_log_of_pow_le (by omega) (hpow.trans (hle.trans he))

/-- Elementary finite exponent-box bound. Independence is not needed here. -/
theorem truncatedMonoid_card_le {r : ℕ} {b : Fin r → ℕ} (hb : ∀ i, 2 ≤ b i)
    (N : ℕ) : (truncatedMonoid b N).card ≤ (Nat.log 2 N + 1) ^ r := by
  classical
  let f : (Fin r → Fin (Nat.log 2 N + 1)) → ℕ :=
    fun e => powerProduct b (fun i => (e i).val)
  have hsub : truncatedMonoid b N ⊆ Finset.univ.image f := by
    intro x hx
    obtain ⟨hxN, e, rfl⟩ := (mem_truncatedMonoid b N x).mp hx
    let e' : Fin r → Fin (Nat.log 2 N + 1) :=
      fun i => ⟨e i, Nat.lt_succ_of_le (exponent_le_log hb hxN i)⟩
    exact Finset.mem_image.mpr ⟨e', Finset.mem_univ _, rfl⟩
  calc
    _ ≤ (Finset.univ.image f).card := Finset.card_le_card hsub
    _ ≤ Fintype.card (Fin r → Fin (Nat.log 2 N + 1)) := Finset.card_image_le
    _ = _ := by simp

theorem exists_missing_powerMonoid_of_count {r : ℕ} {b : Fin r → ℕ}
    (hb : ∀ i, 2 ≤ b i) {m N : ℕ}
    (hcount : ((truncatedMonoid b N).card + m).choose m < N) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ N ∧ ¬ SumOfAtMost (powerMonoid b) m n :=
  exists_missing_of_count
    (fun x hx hxN => (mem_truncatedMonoid b N x).mpr ⟨hxN, hx⟩)
    (zero_notMem_truncatedMonoid hb N) hcount

end HadamardMultibase
