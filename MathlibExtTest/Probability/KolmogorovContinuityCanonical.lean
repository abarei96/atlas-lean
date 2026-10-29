/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Probability.Process.Kolmogorov
import MathlibExt.Probability.KolmogorovContinuity

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExtTest.Probability.KolmogorovContinuityCanonical

private def constantProcess : ℝ → Unit → ℝ := fun _ _ => 3

private theorem constant_canonical :
    IsKolmogorovProcess constantProcess (Measure.dirac ()) 2 (1 + 1) 0 := by
  apply IsKolmogorovProcess.mk_of_secondCountableTopology
  · intro s
    exact measurable_const
  · intro s t
    norm_num [constantProcess]
  · norm_num
  · norm_num

private def identityProcess : ℝ → Unit → ℝ := fun t _ => t

private theorem identity_canonical :
    IsKolmogorovProcess identityProcess (Measure.dirac ()) 2 (1 + 1) 1 := by
  apply IsKolmogorovProcess.mk_of_secondCountableTopology
  · intro s
    exact measurable_const
  · intro s t
    norm_num [identityProcess]
  · norm_num
  · norm_num

end MathlibExtTest.Probability.KolmogorovContinuityCanonical
