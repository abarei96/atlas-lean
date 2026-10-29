/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.BackwardsMartingales
import MathlibExt.Probability.BackwardsMartingale

/-! Signed, nonzero, shrinking-filtration characterization and importing clients. -/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace MathlibExtTest.Probability.BackwardsMartingaleCanonical

local instance : MeasurableSpace Bool := ⊤

private noncomputable def twoAtomMeasure : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • (Measure.dirac false + Measure.dirac true)

local instance : IsProbabilityMeasure twoAtomMeasure :=
  ⟨by norm_num [twoAtomMeasure, ENNReal.inv_two_add_inv_two]⟩

private def signedInitial (b : Bool) : ℝ := if b then 3 else -1

private theorem signedInitial_stronglyMeasurable : StronglyMeasurable signedInitial := by
  apply Measurable.stronglyMeasurable
  intro s hs
  trivial

private theorem signedInitial_integrable (μ : Measure Bool) [IsFiniteMeasure μ] :
    Integrable signedInitial μ := by
  refine (integrable_const (3 : ℝ)).mono'
    signedInitial_stronglyMeasurable.aestronglyMeasurable ?_
  exact ae_of_all μ fun b => by cases b <;> norm_num [signedInitial]

private theorem signedInitial_integral : ∫ b, signedInitial b ∂twoAtomMeasure = 1 := by
  rw [twoAtomMeasure, integral_smul_measure,
    integral_add_measure (signedInitial_integrable _) (signedInitial_integrable _),
    integral_dirac, integral_dirac]
  norm_num [signedInitial]

private def shrinkingFiltration : Filtration ℕᵒᵈ (⊤ : MeasurableSpace Bool) where
  seq n := if n = 0 then ⊤ else ⊥
  mono' := by
    intro i j hij
    change Nat.le j i at hij
    change (if i = 0 then ⊤ else ⊥) ≤ (if j = 0 then ⊤ else ⊥)
    by_cases hi : i = 0
    · subst i
      have hj : j = 0 := Nat.le_zero.mp hij
      simp [hj]
    · simp [hi]
  le' _ := le_top

private theorem conditional_zero :
    twoAtomMeasure[signedInitial | shrinkingFiltration 0] = signedInitial := by
  change twoAtomMeasure[signedInitial | ⊤] = signedInitial
  exact condExp_of_stronglyMeasurable le_rfl signedInitial_stronglyMeasurable
    (signedInitial_integrable _)

private theorem conditional_one :
    twoAtomMeasure[signedInitial | shrinkingFiltration 1] = fun _ => 1 := by
  change twoAtomMeasure[signedInitial | ⊥] = fun _ => 1
  rw [condExp_bot, signedInitial_integral]

private theorem process_changes :
    (twoAtomMeasure[signedInitial | shrinkingFiltration 0]) false ≠
      (twoAtomMeasure[signedInitial | shrinkingFiltration 1]) false := by
  rw [conditional_zero, conditional_one]
  norm_num [signedInitial]

private theorem filtration_changes : shrinkingFiltration 0 ≠ shrinkingFiltration 1 := by
  intro h
  exact process_changes (congrArg
    (fun m : MeasurableSpace Bool => (twoAtomMeasure[signedInitial | m]) false) h)

end MathlibExtTest.Probability.BackwardsMartingaleCanonical
