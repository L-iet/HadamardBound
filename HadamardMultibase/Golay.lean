module

public import HadamardMultibase.Basic

@[expose] public section

namespace HadamardMultibase

def IsBinary {n : ℕ} (A : Fin n → ℤ) : Prop := ∀ i, A i = 1 ∨ A i = -1

/-- Aperiodic autocorrelation, with no wraparound; shifts ≥ n have empty sums. -/
def autocorrelation {n : ℕ} (A : Fin n → ℤ) (s : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n - s),
    (if h : j + s < n then A ⟨j, by omega⟩ * A ⟨j + s, h⟩ else 0)

def IsGolayPair {n : ℕ} (A B : Fin n → ℤ) : Prop :=
  IsBinary A ∧ IsBinary B ∧
    ∀ s : ℕ, 0 < s → s < n → autocorrelation A s + autocorrelation B s = 0

def GolayLength (n : ℕ) : Prop :=
  0 < n ∧ ∃ A B : Fin n → ℤ, IsGolayPair A B

theorem golayLength_one : GolayLength 1 := by
  refine ⟨by omega, (fun _ => 1), (fun _ => 1), ?_⟩
  refine ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl, ?_⟩
  intro s hs hn
  omega

theorem autocorrelation_eq_zero_of_le {n : ℕ} (A : Fin n → ℤ) {s : ℕ}
    (h : n ≤ s) : autocorrelation A s = 0 := by
  simp [autocorrelation, Nat.sub_eq_zero_of_le h]

theorem IsGolayPair.correlation_sum {n : ℕ} {A B : Fin n → ℤ}
    (h : IsGolayPair A B) {s : ℕ} (hs : 0 < s) :
    autocorrelation A s + autocorrelation B s = 0 := by
  by_cases hn : s < n
  · exact h.2.2 s hs hn
  · simp [autocorrelation_eq_zero_of_le A (Nat.le_of_not_gt hn),
      autocorrelation_eq_zero_of_le B (Nat.le_of_not_gt hn)]

/-- The Golay--Turyn input, restricted to the family used in the main bound. -/
def GolayFamily : Prop := ∀ a b : ℕ, GolayLength (2 ^ a * 10 ^ b)

theorem golayLength_of_mem (h : GolayFamily) {n : ℕ} (hn : n ∈ golayMonoid₂) :
    GolayLength n := by
  obtain ⟨a, b, rfl⟩ := hn
  exact h a b

end HadamardMultibase
