module

public import HadamardMultibase.HadamardFlatness
public import HadamardMultibase.RoundingAsymptotics

@[expose] public section

namespace HadamardMultibase

open Matrix Filter
open scoped Matrix.Norms.L2Operator ENNReal

theorem matrixConditionNumber_le_of_scaled_error {n : ℕ} (hn : 0 < n)
    (A Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ * Q = 1)
    {u e z : ℝ} (hu : 0 < u) (he : 0 ≤ e) (hz : z ≤ 1)
    (herror : ‖A - u⁻¹ • Q‖ ≤ e) (hscaled : 4 * u * e ≤ z) :
    matrixConditionNumber A ≤ ENNReal.ofReal (1 + z) := by
  have hue : 0 ≤ u * e := mul_nonneg hu.le he
  have hsmall : u * e ≤ 1 / 4 := by linarith
  have her : e < u⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hu]
    nlinarith
  have hratio : (u⁻¹ + e) / (u⁻¹ - e) = (1 + u * e) / (1 - u * e) := by
    have hden : u⁻¹ - e ≠ 0 := by linarith
    have hden' : 1 - u * e ≠ 0 := by linarith
    field_simp
  calc
    _ ≤ ENNReal.ofReal ((u⁻¹ + e) / (u⁻¹ - e)) :=
      matrixConditionNumber_perturbation hn A Q hQ he her herror
    _ = ENNReal.ofReal ((1 + u * e) / (1 - u * e)) := congrArg ENNReal.ofReal hratio
    _ ≤ ENNReal.ofReal (1 + 4 * (u * e)) :=
      ENNReal.ofReal_le_ofReal (perturbation_ratio_le hue (by linarith))
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith)

/-- For every strict exponent α<1/4, sufficiently large orders admit a sign
matrix with spectral condition number at most 1+n^(-α). All concentration,
spectral and asymptotic deductions are proved; only the sparse input remains. -/
theorem approximateHadamard_bound (hS : SparseRepresentationBound)
    {α : ℝ} (hα : 0 < α) (hαquarter : α < 1 / 4) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ A : Matrix (Fin n) (Fin n) ℝ, (∀ i j, A i j = 1 ∨ A i j = -1) ∧
        matrixConditionNumber A ≤ ENNReal.ofReal (1 + (n : ℝ) ^ (-α)) := by
  let ε : ℝ := 1 / 4 - α
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεhalf : ε < 1 / 2 := by dsimp [ε]; linarith
  have hmargin : α < 1 / 4 - ε / 2 := by dsimp [ε]; linarith
  obtain ⟨N₀, hN₀⟩ := flat_orthogonal_bound hS hε hεhalf
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (eventually_scaled_rounding_error hε.le hεhalf hmargin)
  refine ⟨max N₀ (max N₁ 2), ?_⟩
  intro n hn
  have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₂ : 2 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnpos : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  obtain ⟨Q, hQ, hentries⟩ := hN₀ n hn₀
  obtain ⟨hu, hscaled⟩ := hN₁ n hn₁
  obtain ⟨A, hsign, herror⟩ := exists_sign_rounding_error_bound hnpos Q hQ hu hentries
  have hpow : (n : ℝ) ^ (-α) ≤ 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hnR (show -α ≤ 0 by linarith)
  refine ⟨A, hsign, ?_⟩
  exact matrixConditionNumber_le_of_scaled_error hnpos A Q hQ hu (roundingErrorBound_nonneg _ _)
    hpow herror hscaled

/-- The manuscript's 1+n^(-1/4+δ) formulation, including large δ. -/
theorem approximateHadamard_condition_bound (hS : SparseRepresentationBound)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ A : Matrix (Fin n) (Fin n) ℝ, (∀ i j, A i j = 1 ∨ A i j = -1) ∧
        matrixConditionNumber A ≤ ENNReal.ofReal (1 + (n : ℝ) ^ (-1 / 4 + δ)) := by
  let α : ℝ := max (1 / 8) (1 / 4 - δ)
  have hα : 0 < α := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 8) (le_max_left _ _)
  have hαquarter : α < 1 / 4 := max_lt (by norm_num) (by linarith)
  obtain ⟨N, hN⟩ := approximateHadamard_bound hS hα hαquarter
  refine ⟨max N 1, ?_⟩
  intro n hn
  obtain ⟨A, hsign, hcond⟩ := hN n ((le_max_left _ _).trans hn)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast ((le_max_right N 1).trans hn)
  refine ⟨A, hsign, hcond.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hexp : -α ≤ -1 / 4 + δ := by have := le_max_right (1 / 8 : ℝ) (1 / 4 - δ); dsimp [α]; linarith
  simpa only [add_comm] using add_le_add_left (Real.rpow_le_rpow_of_exponent_le hnR hexp) 1

end HadamardMultibase
