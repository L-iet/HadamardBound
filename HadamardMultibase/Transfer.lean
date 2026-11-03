module

public import HadamardMultibase.Golay

@[expose] public section

namespace HadamardMultibase

/-- The Golay-pair consequence of Craigen's construction. A list permits repetitions.
Proved as `craigenTransfer` in CraigenTransfer.lean. -/
def CraigenTransfer : Prop :=
  ∀ l : List ℕ, (∀ n ∈ l, GolayLength n) →
    HadamardOrder (4 ^ (l.length + 1) * (2 * l.sum + 1))

theorem four_pow_eq_two_pow (r : ℕ) : 4 ^ (r + 1) = 2 ^ (2 * r + 2) := by
  calc
    4 ^ (r + 1) = (2 ^ 2) ^ (r + 1) := by norm_num
    _ = 2 ^ (2 * (r + 1)) := by rw [pow_mul]
    _ = 2 ^ (2 * r + 2) := by simp [Nat.mul_add]

/-- Existence needs no sparse representation theorem: q trivial pairs suffice.
This also covers the small multipliers omitted by the asymptotic input. -/
theorem hasExponent_two_mul_add_one (hC : CraigenTransfer) (q : ℕ) :
    HasExponent (2 * q + 1) := by
  refine ⟨2 * q + 2, ?_⟩
  have h := hC (List.replicate q 1) (by
    intro n hn
    have hn' : n = 1 := (List.mem_replicate.mp hn).2
    simpa [hn'] using golayLength_one)
  simpa [four_pow_eq_two_pow] using h

theorem hasExponent_odd (hC : CraigenTransfer) {p : ℕ} (hp : Odd p) :
    HasExponent p := by
  obtain ⟨q, rfl⟩ := hp.exists_bit1
  exact hasExponent_two_mul_add_one hC q

/-- Once one exponent works, every larger exponent works by Sylvester doubling. -/
theorem hadamardOrder_atExponent_ge {p t : ℕ} (h : HasExponent p)
    (ht : tau p h ≤ t) : HadamardOrder (2 ^ t * p) := by
  have horder := (tau_spec h).two_pow_mul (t - tau p h)
  simpa [← mul_assoc, ← pow_add, Nat.sub_add_cancel ht] using horder

/-- The finite core of the main argument, conditional on its two construction inputs. -/
theorem hadamardOrder_of_sparse (hG : GolayFamily) (hC : CraigenTransfer)
    {q : ℕ} {s : Finset ℕ} (hs : SparseDecomposition q s) :
    HadamardOrder (2 ^ (2 * s.card + 2) * (2 * q + 1)) := by
  have h := hC s.toList (by
    intro n hn
    exact golayLength_of_mem hG (hs.1 n (by simpa using hn)))
  simpa [four_pow_eq_two_pow, hs.2] using h

theorem hasExponent_of_sparse (hG : GolayFamily) (hC : CraigenTransfer)
    {q : ℕ} {s : Finset ℕ} (hs : SparseDecomposition q s) :
    HasExponent (2 * q + 1) :=
  ⟨2 * s.card + 2, hadamardOrder_of_sparse hG hC hs⟩

theorem tau_le_of_sparse (hG : GolayFamily) (hC : CraigenTransfer)
    {q : ℕ} {s : Finset ℕ} (hs : SparseDecomposition q s)
    (h : HasExponent (2 * q + 1)) : tau (2 * q + 1) h ≤ 2 * s.card + 2 :=
  tau_le h (hadamardOrder_of_sparse hG hC hs)

/-- Quantitative transfer at p = 2q + 1. The remaining analytic step is comparison
of logScale q with logScale p and absorption of the additive constant. -/
theorem exponent_bound_of_inputs (hG : GolayFamily) (hC : CraigenTransfer)
    (hS : SparseRepresentationBound) :
    ∃ K : ℝ, 0 < K ∧ ∀ q : ℕ, 2 < q →
      ∃ t : ℕ, HadamardOrder (2 ^ t * (2 * q + 1)) ∧
        (t : ℝ) ≤ 2 * K * logScale q + 2 := by
  obtain ⟨K, hK, hS⟩ := hS
  refine ⟨K, hK, ?_⟩
  intro q hq
  obtain ⟨s, hs, hcard⟩ := hS q hq
  refine ⟨2 * s.card + 2, hadamardOrder_of_sparse hG hC hs, ?_⟩
  push_cast
  linarith

end HadamardMultibase

