/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RegularVariationGeneralizedInverse

@[expose] public section

open Filter
open scoped Topology
open MathlibExt.Probability.RegularVariationGenInv

namespace MathlibExtTest.Probability.RegularVariationGeneralizedInverse

/-- The constant function `1` is slowly varying. -/
example : IsSlowlyVarying (fun _ => (1 : ℝ)) := by
  refine ⟨fun _ _ => one_pos, fun _ _ => ?_⟩
  simp

/-- The power function `x ↦ x ^ (-1 : ℝ)` is regularly varying of index `-1`. -/
example : IsRegularlyVarying (fun x : ℝ => x ^ (-1 : ℝ)) (-1) := by
  refine ⟨fun _ => (1 : ℝ), ⟨fun _ _ => one_pos, fun _ _ => ?_⟩, ?_⟩
  · simp
  · exact Filter.Eventually.of_forall fun _ => by simp

/-- The power function `x ↦ x ^ (-2 : ℝ)` is regularly varying of index `-2`. -/
example : IsRegularlyVarying (fun x : ℝ => x ^ (-2 : ℝ)) (-2) := by
  refine ⟨fun _ => (1 : ℝ), ⟨fun _ _ => one_pos, fun _ _ => ?_⟩, ?_⟩
  · simp
  · exact Filter.Eventually.of_forall fun _ => by simp

/-- The generalized-inverse theorem, restated with its exact public signature,
for the power function `x ↦ x ^ (-1 : ℝ)`. -/
example : ∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧
    Tendsto (fun n => ↑n * (a n) ^ (-1 : ℝ)) atTop (𝓝 1) := by
  apply regularlyVarying_generalized_inverse (fun x : ℝ => x ^ (-1 : ℝ)) 1 (by norm_num)
  · refine ⟨fun _ => (1 : ℝ), ⟨fun _ _ => one_pos, fun _ _ => ?_⟩, ?_⟩
    · simp
    · exact Filter.Eventually.of_forall fun _ => by simp
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx y hy
    exact Real.rpow_le_rpow_of_nonpos hx hy (by norm_num)

/-- The generalized-inverse theorem, restated with its exact public signature,
for the power function `x ↦ x ^ (-2 : ℝ)`. -/
example : ∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧
    Tendsto (fun n => ↑n * (a n) ^ (-2 : ℝ)) atTop (𝓝 1) := by
  apply regularlyVarying_generalized_inverse (fun x : ℝ => x ^ (-2 : ℝ)) 2 (by norm_num)
  · refine ⟨fun _ => (1 : ℝ), ⟨fun _ _ => one_pos, fun _ _ => ?_⟩, ?_⟩
    · simp
    · exact Filter.Eventually.of_forall fun _ => by simp
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx y hy
    exact Real.rpow_le_rpow_of_nonpos hx hy (by norm_num)

#print axioms regularlyVarying_generalized_inverse

end MathlibExtTest.Probability.RegularVariationGeneralizedInverse
