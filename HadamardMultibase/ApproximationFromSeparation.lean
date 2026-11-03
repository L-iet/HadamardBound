module

public import HadamardMultibase.LogMeshAsymptotics
public import HadamardMultibase.LogarithmicApproximation

@[expose] public section

namespace HadamardMultibase

open Filter

theorem logarithmicApproximation_of_separation {S : Set ℕ} {p q : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hmem : ∀ l m : ℕ, p ^ l * q ^ m ∈ S)
    (hsep : PolynomialRotationSeparation (Real.log (q : ℝ) / Real.log (p : ℝ))) :
    LogarithmicApproximation S := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hqR : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqR
  obtain ⟨κ, hκ, hmesh⟩ := eventual_nonnegative_log_mesh (div_pos hlogq hlogp) hsep
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ) / Real.log (p : ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const hlogp
  refine ⟨Real.log (p : ℝ) * (Real.log (p : ℝ)) ^ κ, κ, by positivity, hκ, ?_⟩
  filter_upwards [ht.eventually hmesh, eventually_ge_atTop (2 : ℕ)] with n hn hn₂
  obtain ⟨l, m, hl, hu⟩ := hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  let b : ℕ := p ^ l * q ^ m
  have hb : 0 < b := by dsimp [b]; positivity
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hlogb : Real.log (b : ℝ) =
      ((l : ℝ) + (m : ℝ) * (Real.log (q : ℝ) / Real.log (p : ℝ))) * Real.log (p : ℝ) := by
    dsimp [b]
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    field_simp
  have hupper : Real.log (b : ℝ) ≤ Real.log (n : ℝ) := by
    rw [hlogb]
    have h := mul_le_mul_of_nonneg_right hu hlogp.le
    simpa only [div_mul_cancel₀ _ hlogp.ne'] using h
  have hbn : b ≤ n := by
    have h := Real.exp_le_exp.mpr hupper
    rw [Real.exp_log hbR, Real.exp_log hn0] at h
    exact_mod_cast h
  refine ⟨b, hmem l m, hb, hbn, ?_⟩
  have hlower := mul_le_mul_of_nonneg_right hl hlogp.le
  have herror : 1 / (Real.log (n : ℝ) / Real.log (p : ℝ)) ^ κ * Real.log (p : ℝ) =
      Real.log (p : ℝ) * (Real.log (p : ℝ)) ^ κ / (Real.log (n : ℝ)) ^ κ := by
    rw [Real.div_rpow hlogn.le hlogp.le]
    field_simp
  rw [sub_mul, div_mul_cancel₀ _ hlogp.ne', herror, ← hlogb] at hlower
  exact hlower

theorem sparse_bound_of_separation {S : Set ℕ} {p q : ℕ}
    (hpos : ∀ a ∈ S, 0 < a)
    (hrep : ∀ n : ℕ, ∃ s : Finset ℕ, DistinctSum S n s)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hmem : ∀ l m : ℕ, p ^ l * q ^ m ∈ S)
    (hsep : PolynomialRotationSeparation (Real.log (q : ℝ) / Real.log (p : ℝ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 < n →
      ∃ s : Finset ℕ, DistinctSum S n s ∧ (s.card : ℝ) ≤ K * logScale n :=
  sparse_bound_of_approximation hpos hrep
    (logarithmicApproximation_of_separation hp hq hmem hsep).polynomialRemainder

theorem binary_sparse_bound_of_separation {S : Set ℕ} {q : ℕ}
    (hpos : ∀ a ∈ S, 0 < a) (hq : 2 ≤ q)
    (hmem : ∀ l m : ℕ, 2 ^ l * q ^ m ∈ S)
    (hsep : PolynomialRotationSeparation (Real.log (q : ℝ) / Real.log 2)) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 < n →
      ∃ s : Finset ℕ, DistinctSum S n s ∧ (s.card : ℝ) ≤ K * logScale n := by
  apply sparse_bound_of_separation hpos (p := 2) (q := q)
    (exists_distinctSum_of_powers_two (fun a => by simpa using hmem a 0))
    (by norm_num) hq hmem hsep

theorem sparseRepresentationBound_of_separation
    (hsep : PolynomialRotationSeparation (Real.log 10 / Real.log 2)) :
    SparseRepresentationBound := by
  apply sparseRepresentationBound_of_logarithmicApproximation
  exact logarithmicApproximation_of_separation (p := 2) (q := 10)
    (by norm_num) (by norm_num) (fun l m => ⟨l, m, rfl⟩) hsep

end HadamardMultibase
