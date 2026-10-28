/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.StoppedSumMaximal

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open MathlibExt.Probability.StoppedSumMaximal

namespace MathlibExtTest.Probability.StoppedSumMaximal

/-- Signature restatement: square-integrability of a stopped partial sum,
general-filtration form. -/
theorem integrable_stopped_partialSum_sq_test {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_int : Integrable (X 0) μ)
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {ℱ : Filtration ℕ m0}
    (hIndep : ∀ k, Indep (ℱ k) (MeasurableSpace.comap (X k) inferInstance) μ)
    (hadapt : ∀ k, Measurable[ℱ (k + 1)] (X k))
    {τ : Ω → ℕ} (hT : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℕ)))
    (hτ_int : Integrable (fun ω => (τ ω : ℝ)) μ) :
    Integrable (fun ω => (∑ i ∈ Finset.range (τ ω), X i ω) ^ 2) μ :=
  integrable_stopped_partialSum_sq hX_iid hX_meas hX_int hX_sq_int hmean hIndep hadapt hT
    hτ_int

/-- Signature restatement: square-integrability of the maximal stopped partial
sum, in v1's form. -/
theorem integrable_maximal_stopped_partial_sum_sq_test {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_ind : iIndepFun (β := fun _ => ℝ) X μ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_int : Integrable (X 0) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    {T : Ω → ℕ}
    (hT : IsStoppingTime (predictableFiltration m0 X hX_meas) (fun ω => (T ω : WithTop ℕ)))
    (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
    Integrable (fun ω => (Finset.range (T ω + 1)).sup'
      ⟨0, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _))⟩
      (fun k => (∑ i ∈ Finset.range k, X i ω) ^ 2)) μ :=
  integrable_maximal_stopped_partial_sum_sq hX_iid hX_ind hX_meas hX_int hmean hX_sq_int hT
    hT_int

/-- Degenerate example: the zero sequence, stopped at the constant time `5`,
has a square-integrable stopped partial sum (it is `0`). This exercises the
general-filtration theorem with the trivial filtration `⊥`. -/
theorem integrable_stopped_partialSum_sq_zero {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] :
    Integrable (fun ω => (∑ i ∈ Finset.range (5 : ℕ),
      (fun _ : ℕ => fun _ : Ω => (0 : ℝ)) i ω) ^ 2) μ := by
  apply integrable_stopped_partialSum_sq (X := fun _ _ => (0 : ℝ))
    (ℱ := ⊥) (τ := fun _ => 5)
  · intro i j
    exact IdentDistrib.refl measurable_const.aemeasurable
  · intro i
    exact measurable_const
  · exact integrable_const _
  · simp
  · simp
  · intro k
    exact indep_bot_left _
  · intro k
    exact measurable_const
  · exact isStoppingTime_const ⊥ _
  · exact integrable_const _

#print axioms integrable_stopped_partialSum_sq_zero

end MathlibExtTest.Probability.StoppedSumMaximal
