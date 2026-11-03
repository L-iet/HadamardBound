/-
Copyright (c) 2026 Joshua Mark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HadamardMultibase.BakerInterpolation

@[expose] public section

/-! # Newton expansion with a Cauchy remainder

Nodes may repeat. The contour definition of the coefficients makes the
expansion valid without separate cases for confluent nodes. Its remainder
has an explicit geometric bound in the number of interpolation nodes.
-/

namespace HadamardMultibase

noncomputable def newtonNodeProduct (nodes : List ℂ) (z : ℂ) : ℂ :=
  (nodes.map (fun a => z - a)).prod

@[simp] theorem newtonNodeProduct_nil (z : ℂ) : newtonNodeProduct [] z = 1 := by
  simp [newtonNodeProduct]

@[simp] theorem newtonNodeProduct_cons (a : ℂ) (nodes : List ℂ) (z : ℂ) :
    newtonNodeProduct (a :: nodes) z = (z - a) * newtonNodeProduct nodes z := by
  simp [newtonNodeProduct]

@[simp] theorem newtonNodeProduct_reverse (nodes : List ℂ) (z : ℂ) :
    newtonNodeProduct nodes.reverse z = newtonNodeProduct nodes z := by
  simp [newtonNodeProduct, List.map_reverse, List.prod_reverse]

@[simp] theorem cauchyDividedDifference_reverse (R : ℝ) (f : ℂ → ℂ) (nodes : List ℂ) :
    cauchyDividedDifference R f nodes.reverse = cauchyDividedDifference R f nodes :=
  cauchyDividedDifference_perm R f nodes.reverse_perm

noncomputable def cauchyNewtonRemainder (R : ℝ) (f : ℂ → ℂ)
    (nodes : List ℂ) (z : ℂ) : ℂ :=
  newtonNodeProduct nodes z * cauchyDividedDifference R f (z :: nodes)

noncomputable def cauchyNewtonExpansion (R : ℝ) (f : ℂ → ℂ) : List ℂ → List ℂ → ℂ → ℂ
  | _, [], _ => 0
  | headNodes, a :: nodes, z =>
      newtonNodeProduct headNodes z * cauchyDividedDifference R f (a :: headNodes) +
        cauchyNewtonExpansion R f (a :: headNodes) nodes z

theorem cauchyNewtonExpansion_eq_sum (R : ℝ) (f : ℂ → ℂ) (headNodes nodes : List ℂ) (z : ℂ) :
    cauchyNewtonExpansion R f headNodes nodes z =
      ∑ j ∈ Finset.range nodes.length,
        newtonNodeProduct ((nodes.take j).reverse ++ headNodes) z *
          cauchyDividedDifference R f ((nodes.take (j + 1)).reverse ++ headNodes) := by
  induction nodes generalizing headNodes with
  | nil => simp [cauchyNewtonExpansion]
  | cons a nodes ih =>
    rw [cauchyNewtonExpansion, ih]
    simp only [List.length_cons, Finset.sum_range_succ', List.take_zero,
      List.reverse_nil, List.nil_append, List.take_succ_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append]
    exact add_comm _ _

theorem cauchyNewtonRemainder_step {R : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.sphere 0 R)) (headNodes : List ℂ)
    (hp : ∀ a ∈ headNodes, ‖a‖ < R) (a z : ℂ) (ha : ‖a‖ < R) (hz : ‖z‖ < R) :
    cauchyNewtonRemainder R f headNodes z =
      newtonNodeProduct headNodes z * cauchyDividedDifference R f (a :: headNodes) +
        cauchyNewtonRemainder R f (a :: headNodes) z := by
  have hs := cauchyDividedDifference_recurrence hR hf z a headNodes hz ha hp
  unfold cauchyNewtonRemainder
  rw [newtonNodeProduct_cons]
  linear_combination -newtonNodeProduct headNodes z * hs

theorem cauchyNewtonExpansion_identity {R : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ}
    (hf : ContinuousOn f (Metric.sphere 0 R)) (headNodes nodes : List ℂ)
    (hp : ∀ a ∈ headNodes, ‖a‖ < R) (hn : ∀ a ∈ nodes, ‖a‖ < R)
    (z : ℂ) (hz : ‖z‖ < R) :
    cauchyNewtonRemainder R f headNodes z = cauchyNewtonExpansion R f headNodes nodes z +
      cauchyNewtonRemainder R f (nodes.reverse ++ headNodes) z := by
  induction nodes generalizing headNodes with
  | nil => simp [cauchyNewtonExpansion]
  | cons a nodes ih =>
    have ha := hn a (by simp)
    have ht := ih (a :: headNodes) (by simpa using And.intro ha hp)
      (fun b hb => hn b (List.mem_cons_of_mem _ hb))
    rw [cauchyNewtonRemainder_step hR hf headNodes hp a z ha hz, ht]
    simp only [cauchyNewtonExpansion, List.reverse_cons, List.append_assoc, List.singleton_append]
    ring

theorem cauchyNewton_formula {R : ℝ} (hR : 0 ≤ R) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f (Metric.ball 0 R)) (nodes : List ℂ)
    (hn : ∀ a ∈ nodes, ‖a‖ < R) (z : ℂ) (hz : ‖z‖ < R) :
    f z = cauchyNewtonExpansion R f [] nodes z +
      cauchyNewtonRemainder R f nodes.reverse z := by
  have hcont : ContinuousOn f (Metric.sphere 0 R) :=
    hf.continuousOn_ball.mono Metric.sphere_subset_closedBall
  have he := cauchyNewtonExpansion_identity hR hcont [] nodes (by simp) hn z hz
  simpa only [cauchyNewtonRemainder, newtonNodeProduct_nil, one_mul,
    cauchyDividedDifference_singleton hf hz, List.append_nil] using he

theorem newtonNodeProduct_norm_bound {r ρ : ℝ} (hρ : 0 ≤ ρ + r)
    (nodes : List ℂ) (hnodes : ∀ a ∈ nodes, ‖a‖ ≤ r) (z : ℂ) (hz : ‖z‖ ≤ ρ) :
    ‖newtonNodeProduct nodes z‖ ≤ (ρ + r) ^ nodes.length := by
  induction nodes with
  | nil => simp
  | cons a nodes ih =>
    have ha := hnodes a (by simp)
    have ht := ih (fun b hb => hnodes b (List.mem_cons_of_mem _ hb))
    have hza : ‖z - a‖ ≤ ρ + r := (norm_sub_le z a).trans (add_le_add hz ha)
    rw [newtonNodeProduct_cons, norm_mul, List.length_cons, pow_succ']
    exact mul_le_mul hza ht (norm_nonneg _) hρ

theorem cauchyNewtonRemainder_norm_bound {R r ρ M : ℝ}
    (hR : 0 ≤ R) (hr : 0 ≤ r) (hrρ : r ≤ ρ) (hρR : ρ < R)
    (f : ℂ → ℂ) (nodes : List ℂ) (hnodes : ∀ a ∈ nodes, ‖a‖ ≤ r)
    (hM : 0 ≤ M) (hf : ∀ w ∈ Metric.sphere 0 R, ‖f w‖ ≤ M)
    (z : ℂ) (hz : ‖z‖ ≤ ρ) :
    ‖cauchyNewtonRemainder R f nodes z‖ ≤
      (ρ + r) ^ nodes.length * (R * M / (R - ρ) ^ (nodes.length + 1)) := by
  have hp := newtonNodeProduct_norm_bound (show 0 ≤ ρ + r by linarith) nodes hnodes z hz
  have hd := cauchyDividedDifference_norm_bound hR hρR f (z :: nodes)
    (by simpa using And.intro hz (fun a ha => (hnodes a ha).trans hrρ)) hM hf
  unfold cauchyNewtonRemainder
  rw [norm_mul]
  apply mul_le_mul hp _ (norm_nonneg _) (pow_nonneg (by linarith) _)
  simpa using hd

theorem cauchyNewtonExpansion_norm_bound {R r ρ : ℝ} (hρr : 0 ≤ ρ + r)
    (f : ℂ → ℂ) (nodes : List ℂ) (hnodes : ∀ a ∈ nodes, ‖a‖ ≤ r)
    (B : ℕ → ℝ) (_hB : ∀ j, 0 ≤ B j)
    (hcoeff : ∀ j < nodes.length,
      ‖cauchyDividedDifference R f (nodes.take (j + 1))‖ ≤ B j)
    (z : ℂ) (hz : ‖z‖ ≤ ρ) :
    ‖cauchyNewtonExpansion R f [] nodes z‖ ≤
      ∑ j ∈ Finset.range nodes.length, (ρ + r) ^ j * B j := by
  rw [cauchyNewtonExpansion_eq_sum]
  simp only [List.append_nil, newtonNodeProduct_reverse, cauchyDividedDifference_reverse]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  have hjlen : j < nodes.length := Finset.mem_range.mp hj
  have hlen : (nodes.take j).length = j := by simp [List.length_take, Nat.min_eq_left hjlen.le]
  have hp := newtonNodeProduct_norm_bound hρr (nodes.take j)
    (fun a ha => hnodes a (List.mem_of_mem_take ha)) z hz
  rw [hlen] at hp
  rw [norm_mul]
  exact mul_le_mul hp (hcoeff j hjlen) (norm_nonneg _) (pow_nonneg hρr _)

end HadamardMultibase
