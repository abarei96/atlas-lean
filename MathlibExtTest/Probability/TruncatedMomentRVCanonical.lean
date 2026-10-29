/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.RegularVariation
import MathlibExt.Probability.TruncatedMomentRV

open MeasureTheory Filter Set
open scoped Topology ENNReal
open MathlibExt.Probability.RegularVariation
open MathlibExt.Probability.TruncatedMoment

namespace MathlibExtTest.Probability.TruncatedMomentRVCanonical

-- An atom at either excluded boundary contributes to tailGe, not the strict tail.
example : combinedTail (Measure.dirac (-1 : ℝ)) 1 = 0 ∧
    tailGe (Measure.dirac (-1 : ℝ)) 1 = 1 ∧ tailGt (Measure.dirac (-1 : ℝ)) 1 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [combinedTail, rightTail, leftTail, tailGe, tailGt, Measure.dirac_apply]

example : combinedTail (Measure.dirac (1 : ℝ)) 1 = 0 ∧
    tailGe (Measure.dirac (1 : ℝ)) 1 = 1 ∧ tailGt (Measure.dirac (1 : ℝ)) 1 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [combinedTail, rightTail, leftTail, tailGe, tailGt, Measure.dirac_apply]

-- At zero the two endpoints coincide: that atom is counted only once.
example : combinedTail (Measure.dirac (0 : ℝ)) 0 = 0 ∧
    tailGe (Measure.dirac (0 : ℝ)) 0 = 1 ∧ tailGt (Measure.dirac (0 : ℝ)) 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [combinedTail, rightTail, leftTail, tailGe, tailGt, Measure.dirac_apply]

-- Negative thresholds have overlapping one-sided tails, so no global alias is valid.
example : combinedTail (Measure.dirac (0 : ℝ)) (-1) = 2 ∧
    tailGe (Measure.dirac (0 : ℝ)) (-1) = 1 ∧ tailGt (Measure.dirac (0 : ℝ)) (-1) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [combinedTail, rightTail, leftTail, tailGe, tailGt, Measure.dirac_apply]

private noncomputable def earlyFactor : ℝ → ℝ := fun x => if x ≤ 1 then -1 else 1

private theorem earlyFactor_slow : IsSlowlyVarying earlyFactor := by
  apply isSlowlyVarying_one.of_eventuallyEq
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp [earlyFactor, not_le.mpr hx]

example : IsSlowlyVarying earlyFactor ∧ earlyFactor (1 / 2) < 0 := by
  refine ⟨earlyFactor_slow, ?_⟩
  norm_num [earlyFactor]

-- Early factor values change the chosen factor, while regular variation is asymptotic.
example : IsRegularlyVarying (fun x => x ^ (-1 : ℝ) * earlyFactor x) (-1) := by
  apply (isRegularlyVarying_rpow (-1)).of_eventuallyEq
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp [earlyFactor, not_le.mpr hx]

end MathlibExtTest.Probability.TruncatedMomentRVCanonical
