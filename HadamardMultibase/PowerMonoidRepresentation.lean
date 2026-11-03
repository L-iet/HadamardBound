module

public import HadamardMultibase.CoveringFromSeparation
public import HadamardMultibase.NonLiouvilleSeparation
public import HadamardMultibase.LogIndependence

@[expose] public section

namespace HadamardMultibase

open Filter

theorem powerMonoid_one {r : ℕ} (b : Fin r → ℕ) : 1 ∈ powerMonoid b := by
  exact ⟨fun _ => 0, by simp [powerProduct]⟩

theorem powerMonoid_mul {r : ℕ} {b : Fin r → ℕ} {x y : ℕ}
    (hx : x ∈ powerMonoid b) (hy : y ∈ powerMonoid b) : x * y ∈ powerMonoid b := by
  obtain ⟨e, rfl⟩ := hx
  obtain ⟨f, rfl⟩ := hy
  refine ⟨fun i => e i + f i, ?_⟩
  simp only [powerProduct, pow_add, Finset.prod_mul_distrib]

theorem powerMonoid_base_pow {r : ℕ} (b : Fin r → ℕ) (i : Fin r) (a : ℕ) :
    b i ^ a ∈ powerMonoid b := by
  classical
  refine ⟨fun j => if j = i then a else 0, ?_⟩
  simp [powerProduct]

theorem powerMonoid_distinct_representability {r : ℕ} {b : Fin r → ℕ}
    {i : Fin r} (hi : b i = 2) (n : ℕ) :
    ∃ s : Finset ℕ, DistinctSum (powerMonoid b) n s := by
  apply exists_distinctSum_of_powers_two
  intro a
  simpa only [hi] using powerMonoid_base_pow b i a

/-- General multi-base sparse bound, with only the logarithmic separation
ingredient left as a hypothesis. Binary representability is discharged. -/
theorem powerMonoid_sparse_bound_of_separation {r : ℕ} {b : Fin r → ℕ}
    (hb : ∀ i, 2 ≤ b i) {i₀ i₁ : Fin r} (hi₀ : b i₀ = 2)
    (hsep : PolynomialRotationSeparation (Real.log (b i₁ : ℝ) / Real.log 2)) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 < n →
      ∃ s : Finset ℕ, DistinctSum (powerMonoid b) n s ∧ (s.card : ℝ) ≤ K * logScale n := by
  apply binary_sparse_bound_of_separation (q := b i₁) ?_ (hb i₁) ?_ hsep
  · rintro a ⟨e, rfl⟩
    exact powerProduct_pos hb e
  · intro l m
    apply powerMonoid_mul
    · simpa only [hi₀] using powerMonoid_base_pow b i₀ l
    · exact powerMonoid_base_pow b i₁ m

theorem powerMonoid_covering_lower_of_separation {r : ℕ} {b : Fin r → ℕ}
    (hb : ∀ i, 2 ≤ b i) {i₀ i₁ : Fin r} (hi₀ : b i₀ = 2)
    (hsep : PolynomialRotationSeparation (Real.log (b i₁ : ℝ) / Real.log 2)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      Real.exp (c * m * Real.log m) ≤
        (coveringNumber (powerMonoid b) m (hasMissing_powerMonoid hb m) : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := powerMonoid_sparse_bound_of_separation hb hi₀ hsep
  apply coveringNumber_lower_of_representation (powerMonoid_one b) _ hK
  refine ⟨3, ?_⟩
  intro n hn
  obtain ⟨s, hs, hcard⟩ := hbound n (by omega)
  exact ⟨s.card, hs.sumOfAtMost, hcard⟩

theorem sparseRepresentationBound_of_not_liouville
    (hL : ¬Liouville (Real.log 10 / Real.log 2)) : SparseRepresentationBound :=
  sparseRepresentationBound_of_separation
    (polynomialRotationSeparation_of_not_liouville irrational_log_ten_div_log_two hL)

end HadamardMultibase
