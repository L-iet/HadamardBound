module

public import HadamardMultibase.Asymptotics
public import HadamardMultibase.CoveringUpper

@[expose] public section

namespace HadamardMultibase

open Filter
open scoped Topology

/-- A useful quantitative inverse to the logarithmic scale. The explicit
threshold avoids any monotonicity assertion near its singularity. -/
theorem logScaleReal_exp_mul_log_le {c x : ℝ} (hc : 0 < c) (hx : 0 < x)
    (hlog : 1 ≤ Real.log x) (hclog : -2 * Real.log c ≤ Real.log x) :
    logScaleReal (Real.exp (c * x * Real.log x)) ≤ 2 * c * x := by
  have hlogpos : 0 < Real.log x := by linarith
  have hloglog : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hlog
  have hden : Real.log x / 2 ≤ Real.log (c * x * Real.log x) := by
    rw [Real.log_mul (mul_pos hc hx).ne' hlogpos.ne', Real.log_mul hc.ne' hx.ne']
    linarith
  have hdenpos : 0 < Real.log (c * x * Real.log x) := by linarith
  unfold logScaleReal
  rw [Real.log_exp, div_le_iff₀ hdenpos]
  nlinarith [mul_le_mul_of_nonneg_left hden (show 0 ≤ 2 * c * x by positivity)]

theorem sumOfAtMost_of_one_mem {S : Set ℕ} (h1 : 1 ∈ S) {m n : ℕ} (hn : n ≤ m) :
    SumOfAtMost S m n := by
  refine ⟨List.replicate n 1, by simpa, ?_, by simp⟩
  intro x hx
  have hx1 : x = 1 := (List.mem_replicate.mp hx).2
  simpa [hx1] using h1

theorem SparseDecomposition.sumOfAtMost {n : ℕ} {s : Finset ℕ}
    (hs : SparseDecomposition n s) : SumOfAtMost golayMonoid₂ s.card n := by
  classical
  exact ⟨s.toList, by simp, by simpa using hs.1, by simpa using hs.2⟩

/-- Inversion of any eventual logarithmic representation estimate. The finite
initial interval is represented by ones, rather than using false global
monotonicity of log/loglog. -/
theorem coveringNumber_lower_of_representation {S : Set ℕ} (h1 : 1 ∈ S)
    (hmissing : ∀ m, HasMissing S m) {K : ℝ} (hK : 0 < K)
    (hrep : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ k : ℕ, SumOfAtMost S k n ∧ (k : ℝ) ≤ K * logScale n) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      Real.exp (c * m * Real.log m) ≤ (coveringNumber S m (hmissing m) : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := hrep
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp eventually_logScale_threshold
  let N := max N₀ N₁
  let c : ℝ := 1 / (4 * K)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (max 1 (-2 * Real.log c))
  filter_upwards [hlog, eventually_ge_atTop (max N 1)] with m hlm hm
  change max 1 (-2 * Real.log c) ≤ Real.log (m : ℝ) at hlm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlogm : 1 ≤ Real.log (m : ℝ) := (le_max_left _ _).trans hlm
  have hclog : -2 * Real.log c ≤ Real.log (m : ℝ) := (le_max_right _ _).trans hlm
  have hscale := logScaleReal_exp_mul_log_le hc hmpos hlogm hclog
  by_contra h
  have hnlt : (coveringNumber S m (hmissing m) : ℝ) < Real.exp (c * m * Real.log m) :=
    lt_of_not_ge h
  let n := coveringNumber S m (hmissing m)
  have hnnot : ¬ SumOfAtMost S m n := coveringNumber_not_representable _
  apply hnnot
  by_cases hnN : n < N
  · exact sumOfAtMost_of_one_mem h1 (by omega)
  · have hnN' : N ≤ n := by omega
    obtain ⟨k, hk, hkbound⟩ := hN₀ n ((le_max_left _ _).trans hnN')
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast coveringNumber_pos (hmissing m)
    have hnlog := hN₁ n ((le_max_right _ _).trans hnN')
    have hmono : logScale n ≤ logScaleReal (Real.exp (c * m * Real.log m)) :=
      logScaleReal_mono hnpos hnlog hnlt.le
    have hkm : (k : ℝ) ≤ m := by
      have hkb := hkbound.trans (mul_le_mul_of_nonneg_left (hmono.trans hscale) hK.le)
      have heq : K * (2 * c * m) = (m : ℝ) / 2 := by dsimp [c]; field_simp; ring
      rw [heq] at hkb
      linarith
    exact hk.mono_terms (by exact_mod_cast hkm)

theorem golayCoveringNumber₃_lower (hS : SparseRepresentationBound) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      Real.exp (c * m * Real.log m) ≤ (golayCoveringNumber₃ m : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := hS
  apply coveringNumber_lower_of_representation (S := golayMonoid₃)
    (by exact ⟨0, 0, 0, by simp⟩) hasMissing_golayMonoid₃ hK
  refine ⟨3, ?_⟩
  intro n hn
  obtain ⟨s, hs, hcard⟩ := hbound n (by omega)
  exact ⟨s.card, hs.sumOfAtMost.mono_set golayMonoid₂_subset, hcard⟩

end HadamardMultibase
