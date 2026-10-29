/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BlumenthalZeroOne

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MathlibExt.Probability.BlumenthalZeroOneTest

open MathlibExt.Probability.BlumenthalZeroOne

/-- The natural filtration of `B` augmented by a coin variable `Z`: at time
`t` it is the join of the natural filtration of `B` and `σ(Z)`. This is the
filtration of the Wiener-measure-times-fair-coin model used to show that
v1's `blumenthal_zero_one` is false as stated: v1's `IsBrownianMotion` does
not require the filtration to be the natural one, so the coin can be smuggled
into the germ σ-algebra. -/
def augFiltration {Ω : Type*} {m : MeasurableSpace Ω} {E : Type*} [MeasurableSpace E]
    (B : NNReal → Ω → E) (hB : ∀ t, Measurable (B t)) (Z : Ω → ℝ)
    (hZ : Measurable Z) : Filtration NNReal m where
  seq t := naturalFiltration B hB t ⊔ MeasurableSpace.comap Z inferInstance
  mono' := by
    intro a b hab
    exact sup_le_sup ((naturalFiltration B hB).mono hab) le_rfl
  le' t := sup_le ((naturalFiltration B hB).le t) (measurable_iff_comap_le.mp hZ)

/-- The coin event `{Z = 1}` lies in the germ σ-algebra of the augmented
filtration, since `σ(Z)` is contained in every positive-time component. -/
theorem coin_event_mem_germ {Ω : Type*} {m : MeasurableSpace Ω} {E : Type*}
    [MeasurableSpace E] {B : NNReal → Ω → E} (hB : ∀ t, Measurable (B t))
    {Z : Ω → ℝ} (hZ : Measurable Z) :
    MeasurableSet[germSigmaAlgebraZero (augFiltration B hB Z hZ)] {ω | Z ω = 1} := by
  have hle : MeasurableSpace.comap Z inferInstance ≤
      germSigmaAlgebraZero (augFiltration B hB Z hZ) := by
    show MeasurableSpace.comap Z inferInstance ≤
      ⨅ t > (0 : NNReal), (augFiltration B hB Z hZ) t
    apply le_iInf₂
    intro t _
    exact le_sup_right
  have hmeas : MeasurableSet[MeasurableSpace.comap Z inferInstance] {ω | Z ω = 1} :=
    MeasurableSpace.measurableSet_comap.mpr ⟨{1}, measurableSet_singleton 1, rfl⟩
  exact hle _ hmeas

/-- **Counterexample to v1's `blumenthal_zero_one`.** For the augmented
filtration, v1's `IsBrownianMotion` can hold (it is satisfied in the
Wiener-measure-times-fair-coin model, where the Brownian coordinate and the
coin are independent) while the germ σ-algebra contains the coin event
`{Z = 1}`, which has probability `1 / 2`, hence is neither null nor conull.
So v1's statement, which quantifies over an arbitrary filtration satisfying
`IsBrownianMotion`, is false as stated; the corrected theorem
`blumenthal_zero_one_natural` is about the germ of the *natural* filtration.
The hypotheses `hBM` and `hHalf` are jointly satisfiable (Wiener × coin);
the coin model itself is not constructed in Lean. -/
theorem v1_blumenthal_counterexample {Ω : Type*} {m : MeasurableSpace Ω} {E : Type*}
    [MeasurableSpace E] [AddCommGroup E] [TopologicalSpace E]
    {B : NNReal → Ω → E} (hB : ∀ t, Measurable (B t)) {Z : Ω → ℝ} (hZ : Measurable Z)
    {μ : Measure Ω} {x : E}
    (hBM : IsBrownianMotion B (augFiltration B hB Z hZ) μ x)
    (hHalf : μ {ω | Z ω = 1} = 1 / 2) :
    IsBrownianMotion B (augFiltration B hB Z hZ) μ x ∧
      MeasurableSet[germSigmaAlgebraZero (augFiltration B hB Z hZ)] {ω | Z ω = 1} ∧
      μ {ω | Z ω = 1} ≠ 0 ∧ μ {ω | Z ω = 1} ≠ 1 := by
  refine ⟨hBM, coin_event_mem_germ hB hZ, ?_, ?_⟩
  · rw [hHalf]
    intro h0
    have h := congrArg ENNReal.toReal h0
    rw [ENNReal.toReal_div] at h
    norm_num at h
  · rw [hHalf]
    intro h1
    have h := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_div] at h
    norm_num at h

/-- The corrected theorem applies to germ events of the natural filtration. -/
example {Ω : Type*} {m : MeasurableSpace Ω} {E : Type*} [MeasurableSpace E] [AddCommGroup E]
    [PseudoMetricSpace E] [BorelSpace E] [SecondCountableTopology E] [ContinuousAdd E]
    [ContinuousSub E] {B : NNReal → Ω → E} {𝓕 : Filtration NNReal m} {μ : Measure Ω} {x : E}
    (hBM : IsBrownianMotion B 𝓕 μ x) (hB : ∀ t, Measurable (B t))
    {A : Set Ω} (hA : MeasurableSet[naturalGerm B hB] A) :
    μ A = 0 ∨ μ A = 1 :=
  blumenthal_zero_one_natural hBM hB hA

end MathlibExt.Probability.BlumenthalZeroOneTest
