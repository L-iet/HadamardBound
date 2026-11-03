/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerInterpolationStability
public import HadamardMultibase.BakerNewtonInterpolation

@[expose] public section

/-! # Quantitative extrapolation from an integer grid

Small divided derivatives at 1,...,N imply a disk bound consisting of a
controlled data term and a geometrically decaying contour remainder. The
estimate retains k, N, both radii and the boundary bound explicitly.
-/

namespace HadamardMultibase

theorem baker_grid_extrapolation {R ρ ε M : ℝ} {k N : ℕ}
    (hk : 0 < k) (hNρ : (N : ℝ) ≤ ρ) (hρR : ρ < R)
    (hε : 0 ≤ ε) (hM : 0 ≤ M) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (Metric.ball 0 R))
    (hboundary : ∀ w ∈ Metric.sphere 0 R, ‖f w‖ ≤ M)
    (hjet : ∀ l : ℕ, 1 ≤ l → l ≤ N → ∀ u : ℕ, u < k →
      ‖iteratedDeriv u f (l : ℂ)‖ / (u.factorial : ℝ) ≤ ε)
    (z : ℂ) (hz : ‖z‖ ≤ ρ) :
    ‖f z‖ ≤ (k * N : ℕ) * ε *
        (1 + 2 * (k : ℝ) * (ρ + N)) ^ (k - 1) * Real.exp (2 * (k : ℝ) * (ρ + N)) +
      (ρ + N) ^ (k * N) * (R * M / (R - ρ) ^ (k * N + 1)) := by
  classical
  have hρ : 0 ≤ ρ := (Nat.cast_nonneg N).trans hNρ
  have hR : 0 < R := hρ.trans_lt hρR
  have hNR : (N : ℝ) < R := hNρ.trans_lt hρR
  let nodes := interpolationGridList k 0 (k * N)
  have hnodes : ∀ a ∈ nodes, ‖a‖ ≤ (N : ℝ) :=
    interpolationGridList_norm_le hk (by omega)
  have hcoeff (j : ℕ) (hj : j < nodes.length) :
      ‖cauchyDividedDifference R f (nodes.take (j + 1))‖ ≤ confluentMajorant k j ε := by
    have hjm : j + 1 ≤ k * N := by
      have hjlt : j < k * N := by simpa only [nodes, interpolationGridList_length] using hj
      omega
    rw [show nodes.take (j + 1) = interpolationGridList k 0 (j + 1) from
      interpolationGridList_take k 0 (k * N) (j + 1) hjm]
    exact cauchyGrid_coefficient_bound hR hf hk hNR hε hjet j 0 (by omega)
  have hsum := cauchyNewtonExpansion_norm_bound (show 0 ≤ ρ + (N : ℝ) by positivity)
    f nodes hnodes (fun j => confluentMajorant k j ε)
    (fun j => confluentMajorant_nonneg k j hε) hcoeff z hz
  have hdata : ‖cauchyNewtonExpansion R f [] nodes z‖ ≤
      (k * N : ℕ) * ε * (1 + 2 * (k : ℝ) * (ρ + N)) ^ (k - 1) *
        Real.exp (2 * (k : ℝ) * (ρ + N)) := by
    apply hsum.trans
    calc (∑ j ∈ Finset.range nodes.length, (ρ + N) ^ j * confluentMajorant k j ε)
        ≤ ∑ _j ∈ Finset.range nodes.length,
          ε * (1 + 2 * (k : ℝ) * (ρ + N)) ^ (k - 1) * Real.exp (2 * (k : ℝ) * (ρ + N)) := by
            apply Finset.sum_le_sum
            intro j _
            simpa only [mul_comm] using
              (confluentMajorant_mul_pow_bound hk j hε (show 0 ≤ ρ + (N : ℝ) by positivity))
      _ = _ := by simp [nodes]; ring
  have hrem := cauchyNewtonRemainder_norm_bound hR.le (Nat.cast_nonneg N) hNρ hρR
    f nodes.reverse (by intro a ha; exact hnodes a (List.mem_reverse.mp ha)) hM hboundary z hz
  have he := cauchyNewton_formula hR.le hf nodes
    (fun a ha => (hnodes a ha).trans_lt hNR) z (hz.trans_lt hρR)
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hdata (by
    simpa only [List.length_reverse, nodes, interpolationGridList_length] using hrem))

end HadamardMultibase
