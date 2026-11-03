module

public import HadamardMultibase.PowerMonoidRepresentation

@[expose] public section

namespace HadamardMultibase

/-- Multiplicative independence in the manuscript's integer-exponent sense. -/
def IndependentBases {r : ℕ} (b : Fin r → ℕ) : Prop :=
  ∀ e : Fin r → ℤ, (∏ i, (b i : ℚ) ^ e i) = 1 → ∀ i, e i = 0

theorem IndependentBases.pair {r : ℕ} {b : Fin r → ℕ}
    (hind : IndependentBases b) (hb : ∀ i, 2 ≤ b i)
    {i₀ i₁ : Fin r} (hne : i₀ ≠ i₁) (a c : ℤ)
    (h : (b i₀ : ℚ) ^ a * (b i₁ : ℚ) ^ c = 1) : a = 0 ∧ c = 0 := by
  classical
  let e : Fin r → ℤ := fun i => (if i = i₀ then a else 0) + (if i = i₁ then c else 0)
  have hfactor : (fun i => (b i : ℚ) ^ e i) =
      fun i => (if i = i₀ then (b i₀ : ℚ) ^ a else 1) *
        (if i = i₁ then (b i₁ : ℚ) ^ c else 1) := by
    funext i
    have hb0 : (b i : ℚ) ≠ 0 := by have := hb i; positivity
    dsimp [e]
    rw [zpow_add₀ hb0]
    split_ifs <;> simp_all
  have hprod : (∏ i, (b i : ℚ) ^ e i) = 1 := by
    change (∏ i, (fun j => (b j : ℚ) ^ e j) i) = 1
    rw [hfactor, Finset.prod_mul_distrib]
    simpa using h
  have hz := hind e hprod
  exact ⟨by simpa [e, hne] using hz i₀, by simpa [e, hne, Ne.symm hne] using hz i₁⟩

theorem irrational_log_ratio_of_independent_pair {p q : ℕ}
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hind : ∀ a c : ℤ, (p : ℚ) ^ a * (q : ℚ) ^ c = 1 → a = 0 ∧ c = 0) :
    Irrational (Real.log (q : ℝ) / Real.log (p : ℝ)) := by
  rw [irrational_iff_ne_rational]
  intro a c hc heq
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hcross := (div_eq_div_iff hlogp.ne' hcR).mp heq
  have hlogs : Real.log ((q : ℝ) ^ c) = Real.log ((p : ℝ) ^ a) := by
    rw [Real.log_zpow, Real.log_zpow]
    nlinarith
  have hpowers : (q : ℝ) ^ c = (p : ℝ) ^ a :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (zpow_pos hq0 _))
      (Set.mem_Ioi.mpr (zpow_pos hp0 _)) hlogs
  have hpowersQ : (q : ℚ) ^ c = (p : ℚ) ^ a := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact hpowers
  have hpQ : (p : ℚ) ≠ 0 := by positivity
  have hrel : (p : ℚ) ^ (-a) * (q : ℚ) ^ c = 1 := by
    rw [zpow_neg, hpowersQ, inv_mul_cancel₀ (zpow_ne_zero _ hpQ)]
  exact hc (hind (-a) c hrel).2

theorem IndependentBases.irrational_log_ratio {r : ℕ} {b : Fin r → ℕ}
    (hind : IndependentBases b) (hb : ∀ i, 2 ≤ b i)
    {i₀ i₁ : Fin r} (hne : i₀ ≠ i₁) :
    Irrational (Real.log (b i₁ : ℝ) / Real.log (b i₀ : ℝ)) :=
  irrational_log_ratio_of_independent_pair (hb i₀) (hb i₁) (hind.pair hb hne)

theorem independentBases_two_ten : IndependentBases ![2, 10] := by
  intro e h
  have hrel : (2 : ℚ) ^ e 0 * (10 : ℚ) ^ e 1 = 1 := by
    simpa [Fin.prod_univ_succ] using h
  obtain ⟨h0, h1⟩ := independent_two_ten (e 0) (e 1) hrel
  intro i
  fin_cases i <;> assumption

theorem independentBases_two_ten_twentySix : IndependentBases ![2, 10, 26] := by
  intro e h
  have hrel : (2 : ℚ) ^ e 0 * (10 : ℚ) ^ e 1 * (26 : ℚ) ^ e 2 = 1 := by
    simpa [Fin.prod_univ_succ, mul_assoc] using h
  obtain ⟨h0, h1, h2⟩ := independent_two_ten_twentySix (e 0) (e 1) (e 2) hrel
  intro i
  fin_cases i <;> assumption

end HadamardMultibase
