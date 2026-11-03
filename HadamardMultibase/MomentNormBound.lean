module

public import HadamardMultibase.MomentConcentration
public import Mathlib.Data.Nat.Log

@[expose] public section

namespace HadamardMultibase

open Matrix
open scoped Matrix.Norms.L2Operator

theorem le_sqrt_bound_of_even_moment {x v : ℝ} {N k : ℕ}
    (hx : 0 ≤ x) (hv : 0 ≤ v) (hk : 0 < k) (hN : N ≤ 4 ^ k)
    (h : x ^ (2 * k) ≤ (2 : ℝ) ^ (2 * k) * (((2 * k + 1) ^ (2 * k) : ℕ) : ℝ) * N * v ^ k) :
    x ≤ 4 * (2 * (k : ℝ) + 1) * Real.sqrt v := by
  apply (pow_le_pow_iff_left₀ hx (by positivity) (show 2 * k ≠ 0 by omega)).mp
  have hNR : (N : ℝ) ≤ (4 : ℝ) ^ k := by exact_mod_cast hN
  have hsq : (Real.sqrt v) ^ (2 * k) = v ^ k := by rw [pow_mul, Real.sq_sqrt hv]
  have hcoef : (2 : ℝ) ^ (2 * k) * (4 : ℝ) ^ k = (4 : ℝ) ^ (2 * k) := by
    simp only [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    rw [← pow_add]
    congr 1
    omega
  push_cast at h
  calc
    _ ≤ (2 : ℝ) ^ (2 * k) * (2 * (k : ℝ) + 1) ^ (2 * k) * (N : ℝ) * v ^ k := h
    _ ≤ (2 : ℝ) ^ (2 * k) * (2 * (k : ℝ) + 1) ^ (2 * k) * (4 : ℝ) ^ k * v ^ k := by gcongr
    _ = ((2 : ℝ) ^ (2 * k) * (4 : ℝ) ^ k) * (2 * (k : ℝ) + 1) ^ (2 * k) * v ^ k := by ring
    _ = _ := by rw [hcoef, mul_pow, mul_pow, hsq]

/-- Integer logarithmic moment order, always positive. -/
def concentrationMomentOrder (N : ℕ) : ℕ := max 1 (Nat.clog 4 N)

theorem concentrationMomentOrder_pos (N : ℕ) : 0 < concentrationMomentOrder N := by
  unfold concentrationMomentOrder
  omega

theorem card_le_four_pow_momentOrder (N : ℕ) : N ≤ 4 ^ concentrationMomentOrder N :=
  (Nat.le_pow_clog (by norm_num) N).trans
    (pow_le_pow_right₀ (by norm_num) (le_max_right _ _))

/-- Independent centered symmetric rounding has a sample with an explicit
logarithmic operator-norm bound times the square root of its variance bound. -/
theorem exists_rounding_norm_bound
    {V τ : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype τ] [DecidableEq τ]
    (label : V → V → τ)
    (hlabel : ∀ a b c d, label a b = label c d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c))
    {μ : τ → ℝ} (hμ : ∀ a, |μ a| ≤ 1) {v : ℝ} (hv : 1 ≤ v)
    (hrow : ∀ x, ∑ y, (1 - (μ (label x y)) ^ 2) ≤ v)
    (mask : Matrix V V ℝ) (hmask : ∀ i j, |mask i j| ≤ 1)
    (hsym : ∀ ω : τ → Bool, (centeredLabelMatrix μ label mask ω)ᵀ =
      centeredLabelMatrix μ label mask ω) :
    ∃ ω : τ → Bool, ‖centeredLabelMatrix μ label mask ω‖ ≤
      4 * (2 * (concentrationMomentOrder (Fintype.card V) : ℝ) + 1) * Real.sqrt v := by
  obtain ⟨ω, hω⟩ := exists_rounding_norm_moment_bound label hlabel hμ hv hrow mask hmask hsym
    (concentrationMomentOrder_pos (Fintype.card V))
  exact ⟨ω, le_sqrt_bound_of_even_moment (norm_nonneg _) (by linarith)
    (concentrationMomentOrder_pos _) (card_le_four_pow_momentOrder _) hω⟩

end HadamardMultibase
