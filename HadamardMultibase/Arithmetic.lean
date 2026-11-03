module

public import HadamardMultibase.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.BitIndices

@[expose] public section

namespace HadamardMultibase

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Fact (Nat.Prime 13) := ⟨by decide⟩

@[simp] private theorem val₂₂ : padicValRat 2 2 = 1 :=
  (padicValRat.of_nat (p := 2) (n := 2)).trans (by norm_num [padicValNat, Nat.maxPowDvdDiv, Nat.maxPowDvdDiv.go])
@[simp] private theorem val₂₁₀ : padicValRat 2 10 = 1 :=
  (padicValRat.of_nat (p := 2) (n := 10)).trans (by norm_num [padicValNat, Nat.maxPowDvdDiv, Nat.maxPowDvdDiv.go])
@[simp] private theorem val₂₂₆ : padicValRat 2 26 = 1 :=
  (padicValRat.of_nat (p := 2) (n := 26)).trans (by norm_num [padicValNat, Nat.maxPowDvdDiv, Nat.maxPowDvdDiv.go])
@[simp] private theorem val₅₂ : padicValRat 5 2 = 0 :=
  (padicValRat.of_nat (p := 5) (n := 2)).trans (by norm_num [padicValNat, Nat.maxPowDvdDiv, Nat.maxPowDvdDiv.go])
@[simp] private theorem val₅₁₀ : padicValRat 5 10 = 1 :=
  (padicValRat.of_nat (p := 5) (n := 10)).trans (by norm_num [padicValNat, Nat.maxPowDvdDiv, Nat.maxPowDvdDiv.go])
@[simp] private theorem val₅₂₆ : padicValRat 5 26 = 0 :=
  (padicValRat.of_nat (p := 5) (n := 26)).trans (by norm_num [padicValNat, Nat.maxPowDvdDiv, Nat.maxPowDvdDiv.go])
@[simp] private theorem val₁₃₂ : padicValRat 13 2 = 0 :=
  (padicValRat.of_nat (p := 13) (n := 2)).trans (by norm_num [padicValNat, Nat.maxPowDvdDiv, Nat.maxPowDvdDiv.go])
@[simp] private theorem val₁₃₁₀ : padicValRat 13 10 = 0 :=
  (padicValRat.of_nat (p := 13) (n := 10)).trans (by norm_num [padicValNat, Nat.maxPowDvdDiv, Nat.maxPowDvdDiv.go])
@[simp] private theorem val₁₃₂₆ : padicValRat 13 26 = 1 :=
  (padicValRat.of_nat (p := 13) (n := 26)).trans (by norm_num [padicValNat, Nat.maxPowDvdDiv, Nat.maxPowDvdDiv.go])

private theorem val_smooth (p : ℕ) [Fact p.Prime] (a b c : ℤ) :
    padicValRat p ((2 : ℚ) ^ a * 10 ^ b * 26 ^ c) =
      a * padicValRat p 2 + b * padicValRat p 10 + c * padicValRat p 26 := by
  rw [padicValRat.mul (by positivity) (by positivity),
    padicValRat.mul (by positivity) (by positivity)]
  simp

/-- Full multiplicative independence, allowing arbitrary integer exponents. -/
theorem independent_two_ten_twentySix (a b c : ℤ)
    (h : (2 : ℚ) ^ a * 10 ^ b * 26 ^ c = 1) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have h₂ := congrArg (padicValRat 2) h
  have h₅ := congrArg (padicValRat 5) h
  have h₁₃ := congrArg (padicValRat 13) h
  simp only [val_smooth, val₂₂, val₂₁₀, val₂₂₆, val₅₂, val₅₁₀, val₅₂₆,
    val₁₃₂, val₁₃₁₀, val₁₃₂₆, padicValRat.one, mul_one, mul_zero, add_zero,
    zero_add] at h₂ h₅ h₁₃
  exact ⟨by omega, h₅, h₁₃⟩

theorem independent_two_ten (a b : ℤ) (h : (2 : ℚ) ^ a * 10 ^ b = 1) :
    a = 0 ∧ b = 0 := by
  have h' := independent_two_ten_twentySix a b 0 (by simpa using h)
  exact ⟨h'.1, h'.2.1⟩

/-- This finite encoding will also be used to count elements of the monoid. -/
theorem powerProducts₃_injective :
    Function.Injective (fun e : ℕ × ℕ × ℕ => 2 ^ e.1 * 10 ^ e.2.1 * 26 ^ e.2.2) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have hq : (2 : ℚ) ^ (a : ℤ) * 10 ^ (b : ℤ) * 26 ^ (c : ℤ) =
      2 ^ (a' : ℤ) * 10 ^ (b' : ℤ) * 26 ^ (c' : ℤ) := by
    exact_mod_cast h
  have h₂ := congrArg (padicValRat 2) hq
  have h₅ := congrArg (padicValRat 5) hq
  have h₁₃ := congrArg (padicValRat 13) hq
  simp only [val_smooth, val₂₂, val₂₁₀, val₂₂₆, val₅₂, val₅₁₀, val₅₂₆,
    val₁₃₂, val₁₃₁₀, val₁₃₂₆, mul_one, mul_zero, add_zero, zero_add] at h₂ h₅ h₁₃
  have ha : a = a' := by omega
  have hb : b = b' := by omega
  have hc : c = c' := by omega
  simp [ha, hb, hc]

theorem powerProducts₂_injective :
    Function.Injective (fun e : ℕ × ℕ => 2 ^ e.1 * 10 ^ e.2) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h' := powerProducts₃_injective (a₁ := (a, b, 0)) (a₂ := (a', b', 0))
    (by simpa using h)
  simpa using h'

/-- Every natural number has a distinct-summand multi-base representation,
using just the powers of two. This proves KSW's representability hypothesis. -/
theorem exists_sparseDecomposition (n : ℕ) : ∃ s : Finset ℕ, SparseDecomposition n s := by
  let s := n.bitIndices.toFinset.image (fun i => 2 ^ i)
  refine ⟨s, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨a, 0, by simp⟩
  · dsimp [s]
    rw [Finset.sum_image]
    · simpa using (List.sum_toFinset (fun i => 2 ^ i) Nat.bitIndices_nodup).trans
        (Nat.sum_map_two_pow_bitIndices n)
    · intro a _ b _ h
      exact Nat.pow_right_injective (by omega) h

end HadamardMultibase
