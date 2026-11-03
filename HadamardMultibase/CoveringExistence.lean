module

public import HadamardMultibase.MultiBase
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

namespace HadamardMultibase

open Filter
open scoped Topology

/-- Every fixed polynomial is eventually smaller than a geometric sequence,
including the shift needed for the exponent-box count. -/
theorem eventually_polynomial_lt_two_pow (C d : ℕ) :
    ∀ᶠ k : ℕ in atTop, C * (k + 1) ^ d < 2 ^ k := by
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt d
    (r := (2 : ℝ)) (by norm_num)).comp (tendsto_add_atTop_nat 1)
  have ht' : Tendsto (fun k : ℕ => (C : ℝ) * 2 *
      (((k + 1 : ℕ) : ℝ) ^ d / (2 : ℝ) ^ (k + 1))) atTop (𝓝 0) := by
    simpa using ht.const_mul ((C : ℝ) * 2)
  filter_upwards [(tendsto_order.mp ht').2 1 (by norm_num)] with k hk
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  rw [pow_succ] at hk
  have h : (C : ℝ) * ((k + 1 : ℕ) : ℝ) ^ d < (2 : ℝ) ^ k := by
    have := (div_lt_iff₀ (show (0 : ℝ) < 2 ^ k * 2 by positivity)).mp
      (show (C : ℝ) * 2 * ((k + 1 : ℕ) : ℝ) ^ d / (2 ^ k * 2) < 1 by
        simpa only [div_eq_mul_inv, mul_assoc] using hk)
    nlinarith
  exact_mod_cast h

/-- Every finitely generated power monoid with bases at least two has a
positive integer requiring more than any prescribed number of summands. -/
theorem hasMissing_powerMonoid {r : ℕ} {b : Fin r → ℕ}
    (hb : ∀ i, 2 ≤ b i) (m : ℕ) : HasMissing (powerMonoid b) m := by
  classical
  obtain ⟨k, hk⟩ := (eventually_polynomial_lt_two_pow ((m + 1) ^ m) (r * m)).exists
  have hlog : Nat.log 2 (2 ^ k) = k := Nat.log_pow (by norm_num) _
  have hcard := truncatedMonoid_card_le hb (2 ^ k)
  rw [hlog] at hcard
  have hone : 1 ≤ (k + 1) ^ r := Nat.one_le_pow _ _ (by omega)
  have hbase : (truncatedMonoid b (2 ^ k)).card + m ≤ (m + 1) * (k + 1) ^ r := by
    nlinarith
  have hcount : ((truncatedMonoid b (2 ^ k)).card + m).choose m < 2 ^ k := by
    calc
      _ ≤ ((truncatedMonoid b (2 ^ k)).card + m) ^ m := Nat.choose_le_pow _ _
      _ ≤ ((m + 1) * (k + 1) ^ r) ^ m := Nat.pow_le_pow_left hbase _
      _ = (m + 1) ^ m * (k + 1) ^ (r * m) := by rw [mul_pow, ← pow_mul]
      _ < _ := hk
  obtain ⟨n, hn, _, hnot⟩ := exists_missing_powerMonoid_of_count hb hcount
  exact ⟨n, by omega, hnot⟩

theorem powerMonoid_two_ten : powerMonoid ![2, 10] = golayMonoid₂ := by
  ext n
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e 0, e 1, by simp [powerProduct, Fin.prod_univ_succ]⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨![a, b], by simp [powerProduct, Fin.prod_univ_succ]⟩

theorem powerMonoid_two_ten_twentySix : powerMonoid ![2, 10, 26] = golayMonoid₃ := by
  ext n
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e 0, e 1, e 2, by simp [powerProduct, Fin.prod_univ_succ, mul_assoc]⟩
  · rintro ⟨a, b, c, rfl⟩
    exact ⟨![a, b, c], by simp [powerProduct, Fin.prod_univ_succ, mul_assoc]⟩

theorem hasMissing_golayMonoid₂ (m : ℕ) : HasMissing golayMonoid₂ m := by
  rw [← powerMonoid_two_ten]
  exact hasMissing_powerMonoid (by decide) m

theorem hasMissing_golayMonoid₃ (m : ℕ) : HasMissing golayMonoid₃ m := by
  rw [← powerMonoid_two_ten_twentySix]
  exact hasMissing_powerMonoid (by decide) m

/-- Livinskyi's covering function for the Golay monoid is well defined at every m. -/
noncomputable def golayCoveringNumber₃ (m : ℕ) : ℕ :=
  coveringNumber golayMonoid₃ m (hasMissing_golayMonoid₃ m)

theorem golayCoveringNumber₃_pos (m : ℕ) : 0 < golayCoveringNumber₃ m :=
  coveringNumber_pos _

theorem golayCoveringNumber₃_not_representable (m : ℕ) :
    ¬ SumOfAtMost golayMonoid₃ m (golayCoveringNumber₃ m) :=
  coveringNumber_not_representable _

end HadamardMultibase
