module

public import HadamardMultibase.Golay

@[expose] public section

namespace HadamardMultibase

/-- Finite formulation suitable for kernel-checked evaluation of explicit pairs. -/
theorem isGolayPair_iff_fin {n : ℕ} (A B : Fin n → ℤ) :
    IsGolayPair A B ↔ IsBinary A ∧ IsBinary B ∧
      ∀ s : Fin n, 0 < s.val → autocorrelation A s.val + autocorrelation B s.val = 0 := by
  constructor
  · rintro ⟨hA, hB, h⟩
    exact ⟨hA, hB, fun s hs => h s.val hs s.isLt⟩
  · rintro ⟨hA, hB, h⟩
    exact ⟨hA, hB, fun s hs hn => h ⟨s, hn⟩ hs⟩

def seed₂A : Fin 2 → ℤ := ![1, 1]
def seed₂B : Fin 2 → ℤ := ![1, -1]

def seed₁₀A : Fin 10 → ℤ := ![1, 1, -1, 1, -1, 1, -1, -1, 1, 1]
def seed₁₀B : Fin 10 → ℤ := ![1, 1, -1, 1, 1, 1, 1, 1, -1, -1]

-- Livinskyi, thesis pp. 30–31. Entries are checked against the actual
-- aperiodic-autocorrelation definition, rather than trusting the transcription.
def seed₂₆A : Fin 26 → ℤ :=
  ![1, 1, 1, 1, -1, 1, 1, -1, -1, 1, -1, 1, -1,
    1, -1, -1, 1, -1, 1, 1, 1, -1, -1, 1, 1, 1]
def seed₂₆B : Fin 26 → ℤ :=
  ![1, 1, 1, 1, -1, 1, 1, -1, -1, 1, -1, 1, 1,
    1, 1, 1, -1, 1, -1, -1, -1, 1, 1, -1, -1, -1]

theorem seed₂_isGolayPair : IsGolayPair seed₂A seed₂B := by
  rw [isGolayPair_iff_fin]
  unfold IsBinary
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem seed₁₀_isGolayPair : IsGolayPair seed₁₀A seed₁₀B := by
  rw [isGolayPair_iff_fin]
  unfold IsBinary
  decide

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem seed₂₆_isGolayPair : IsGolayPair seed₂₆A seed₂₆B := by
  rw [isGolayPair_iff_fin]
  unfold IsBinary
  decide

theorem golayLength_two : GolayLength 2 :=
  ⟨by omega, seed₂A, seed₂B, seed₂_isGolayPair⟩

theorem golayLength_ten : GolayLength 10 :=
  ⟨by omega, seed₁₀A, seed₁₀B, seed₁₀_isGolayPair⟩

theorem golayLength_twentySix : GolayLength 26 :=
  ⟨by omega, seed₂₆A, seed₂₆B, seed₂₆_isGolayPair⟩

end HadamardMultibase
