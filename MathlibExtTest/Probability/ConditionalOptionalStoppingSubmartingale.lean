/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ConditionalOptionalStoppingSubmartingale

@[expose] public section

open MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}

omit [MeasurableSpace Ω] in
/-- The stopped value of a constant process is the constant, at any
stopping time. -/
private lemma stoppedValueAtInf_const (c : ℝ) (τ : Ω → WithTop ℕ) :
    stoppedValueAtInf (fun _ => fun _ => c) τ = fun _ => c := by
  funext ω
  show (if τ ω = ⊤ then limUnder atTop (fun n => (fun _ => fun _ => c) n ω)
    else stoppedValue (fun _ => fun _ => c) τ ω) = c
  by_cases h : τ ω = ⊤
  · rw [ite_eq_left h]
    simpa using (tendsto_const_nhds (x := c)).limUnder_eq
  · rw [ite_eq_right h]
    rfl

/-- The constant process is a uniformly integrable submartingale, so the
main theorem applies to it. -/
private theorem submartingale_const (c : ℝ) :
    Submartingale (fun _ => fun _ => c) ℱ μ :=
  (martingale_const ℱ μ c).submartingale

/-- The constant process is uniformly integrable. -/
private theorem uniformIntegrable_const' (c : ℝ) :
    UniformIntegrable (fun _ : ℕ => fun _ : Ω => c) 1 μ :=
  uniformIntegrable_const le_rfl ENNReal.one_ne_top (memLp_const c)

/-- For the constant process, the conditional optional stopping
inequality says `c ≤ᵐ μ[c | ℱ_L]`, and both sides are `c`. -/
example (c : ℝ) (L M : Ω → WithTop ℕ) (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    (fun _ : Ω => c) ≤ᵐ[μ] μ[fun _ : Ω => c | hL.measurableSpace] := by
  have h := Submartingale.stoppedValueAtInf_le_condExp_stoppedValueAtInf
    (submartingale_const (μ := μ) (ℱ := ℱ) c)
    (uniformIntegrable_const' (μ := μ) c) hL hM hLM
  rw [stoppedValueAtInf_const, stoppedValueAtInf_const] at h
  rw [condExp_const hL.measurableSpace_le] at h ⊢

/-- For the constant process, the expectation form says `∫ c ≤ ∫ c`. -/
example (c : ℝ) (L M : Ω → WithTop ℕ) (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    ∫ ω, stoppedValueAtInf (fun _ => fun _ => c) L ω ∂μ ≤
      ∫ ω, stoppedValueAtInf (fun _ => fun _ => c) M ω ∂μ :=
  Submartingale.integral_stoppedValueAtInf_mono_of_uniformIntegrable
    (submartingale_const (μ := μ) (ℱ := ℱ) c)
    (uniformIntegrable_const' (μ := μ) c) hL hM hLM

/-- Applying the main theorem under abstract hypotheses: this checks the
statement is usable in the form in which it is stated, without
re-proving it. -/
example {f : ℕ → Ω → ℝ}
    (hsub : Submartingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    {L M : Ω → WithTop ℕ} (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    stoppedValueAtInf f L ≤ᵐ[μ] μ[stoppedValueAtInf f M | hL.measurableSpace] :=
  Submartingale.stoppedValueAtInf_le_condExp_stoppedValueAtInf hsub hui hL hM hLM

/-- Applying the expectation corollary under abstract hypotheses. -/
example {f : ℕ → Ω → ℝ}
    (hsub : Submartingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    {L M : Ω → WithTop ℕ} (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    ∫ ω, stoppedValueAtInf f L ω ∂μ ≤ ∫ ω, stoppedValueAtInf f M ω ∂μ :=
  Submartingale.integral_stoppedValueAtInf_mono_of_uniformIntegrable hsub hui hL hM hLM

#print axioms Submartingale.stoppedValueAtInf_le_condExp_stoppedValueAtInf
#print axioms Submartingale.integral_stoppedValueAtInf_mono_of_uniformIntegrable
