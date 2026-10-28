/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Probability.Process.Adapted
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Probability.Kernel.MeasurableLIntegral

@[expose] public section

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace MathlibExt.Probability.MarkovChainFunctionCK

/-!
# Chapman–Kolmogorov equations for bounded measurable functions

For a discrete-time Markov chain `X` with transition kernel `κ`, the
`n`-step transition probabilities are the kernel powers `κ ^ n`. The
indicator form of this statement (conditional probability that
`X (m + n)` lies in `B`) is the Chapman–Kolmogorov theorem. This file
proves the function form: for every bounded measurable `f`, the
conditional expectation of `f (X (m + n))` given the past up to time `m`
is the `κ ^ n`-integral of `f` evaluated at `X m`.

## Source

This formalizes the targets "Definition (Markov chain, general)" and
"Theorem (Markov property)" (Lecture 30/31) of
`v1/Atlas/TheoryOfProbability/targets.yaml`. The v1 formalization is
`v1/Atlas/TheoryOfProbability/code/MarkovChain.lean` (the `IsMarkovChain`
definition, ported here verbatim) and
`v1/Atlas/TheoryOfProbability/code/MarkovPropertyChain.lean` (whose
`IsMarkovChain.markov_property` is the one-step indicator case of the
conditional form below).

## Relation to Mathlib and to earlier batches

Mathlib has the Chapman–Kolmogorov equations for kernel composition
itself (`ProbabilityTheory.Kernel.pow_add`): the `n`-step kernel is a
composite of one-step kernels. It has no statement linking those kernel
powers to the conditional law of a Markov chain `X` satisfying
`IsMarkovChain`. Batch 46 (PR #467) proved the indicator (set) form and
the forward law form, and explicitly left the general
bounded-measurable-function form open ("from which the function form
follows by the usual measure-identification argument, but it is not
restated here"). This file proves that function form. Its one-step
set-integral engine is the one-step indicator form rewritten (the same
argument as batch 46's private `measure_inter_preimage_eq_lintegral`),
and the `IsMarkovChain` definition is a copy of the v1 / batch-46
definition, kept in this file's own namespace so the file is
self-contained on the base; on rebase, delete the copy and re-point at
the canonical definition.

## Main results

* `IsMarkovChain`: `X` is a Markov chain with transition kernel `κ`
  with respect to the filtration `ℱ` under `μ` (adapted, plus the
  one-step conditional-probability identity).
* `IsMarkovChain.condExp_one_step_eq_integral`: the one-step function
  form: `μ[ f ∘ X (k+1) | ℱ k ] =ᵐ fun ω => ∫ y, f y ∂ κ (X k ω)`.
* `IsMarkovChain.condExp_comp_eq_integral_pow`: the `n`-step function
  form: `μ[ f ∘ X (m+n) | ℱ m ] =ᵐ fun ω => ∫ y, f y ∂ (κ ^ n) (X m ω)`.
* `IsMarkovChain.integral_comp_eq`: the integrated form:
  `∫ ω, f (X (m+n) ω) ∂μ = ∫ ω, (∫ y, f y ∂ (κ ^ n) (X m ω)) ∂μ`.
-/

/-- `IsMarkovChain X ℱ κ μ` asserts that the sequence of random variables
`X : ℕ → Ω → S` is a Markov chain with respect to the filtration `ℱ` with
transition probability kernel `κ` under the measure `μ`. Concretely it
requires that `X` is `ℱ`-adapted and that for each `n` and measurable
`B ⊆ S`,

  `μ[1_{B} ∘ X (n+1) | ℱ n] = κ (X n ·) B  μ`-a.e.,

which is the standard form `P(X_{n+1} ∈ B | ℱ_n) = κ(X_n, B)` of the
Markov property. -/
structure IsMarkovChain {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    (X : ℕ → Ω → S) (ℱ : Filtration ℕ m) (κ : Kernel S S)
    [IsMarkovKernel κ] (μ : Measure Ω) : Prop where
  adapted : Adapted ℱ X
  markov_prop : ∀ n : ℕ, ∀ B : Set S, MeasurableSet B →
    μ[(B.indicator (fun _ => (1 : ℝ))) ∘ (X (n + 1)) | ℱ n] =ᵐ[μ]
      fun ω => (κ (X n ω) B).toReal

namespace IsMarkovChain

variable {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]

omit [IsProbabilityMeasure μ] in
/-- Each coordinate of a Markov chain is measurable. -/
private lemma measurable (hMC : IsMarkovChain X ℱ κ μ) (n : ℕ) : Measurable (X n) :=
  hMC.adapted.measurable

/-- Powers of a Markov kernel are Markov kernels. -/
private instance isMarkovKernel_pow (n : ℕ) : IsMarkovKernel (κ ^ n) := by
  induction n with
  | zero =>
    show IsMarkovKernel (Kernel.id : Kernel S S)
    infer_instance
  | succ n ih =>
    show IsMarkovKernel (Kernel.comp (κ ^ n) κ)
    infer_instance

omit [MeasurableSpace S] in
/-- Composing an indicator with a map is the indicator of the preimage. -/
private lemma indicator_comp_preimage {Y : Ω → S} {B : Set S} :
    (B.indicator (fun _ => (1 : ℝ))) ∘ Y =
      Set.indicator (Y ⁻¹' B) (fun _ => (1 : ℝ)) := by
  ext ω
  rw [Function.comp_apply]
  by_cases hω : Y ω ∈ B
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
  · rw [Set.indicator_of_notMem hω,
      Set.indicator_of_notMem (fun h => hω (Set.mem_preimage.mp h))]

/-- One-step form of the transition law, as a measure identity: for `C ∈ ℱ k`,
the mass of `C ∩ {X (k+1) ∈ B}` equals the `κ`-average of `B` over `C`.
This is the set-integral form of the defining `markov_prop`. -/
private lemma measure_inter_preimage_eq_lintegral
    (hMC : IsMarkovChain X ℱ κ μ) (k : ℕ) {B : Set S} (hB : MeasurableSet B)
    {C : Set Ω} (hC : MeasurableSet[ℱ k] C) :
    μ (C ∩ X (k + 1) ⁻¹' B) = ∫⁻ ω in C, κ (X k ω) B ∂μ := by
  have hX_meas : Measurable (X (k + 1)) := hMC.measurable (k + 1)
  have hXk_meas : Measurable (X k) := hMC.measurable k
  have hf_int : Integrable ((B.indicator (fun _ => (1 : ℝ))) ∘ (X (k + 1))) μ := by
    rw [indicator_comp_preimage]
    exact (integrable_const (1 : ℝ)).indicator (hX_meas hB)
  have h_set : ∫ ω in C,
      μ[((B.indicator (fun _ => (1 : ℝ))) ∘ (X (k + 1))) | ℱ k] ω ∂μ =
      ∫ ω in C, ((B.indicator (fun _ => (1 : ℝ))) ∘ (X (k + 1))) ω ∂μ :=
    setIntegral_condExp (ℱ.le k) hf_int hC
  have h_ae' : ∀ᵐ ω ∂μ, ω ∈ C →
      μ[((B.indicator (fun _ => (1 : ℝ))) ∘ (X (k + 1))) | ℱ k] ω =
        (κ (X k ω) B).toReal :=
    (ae_restrict_iff' ((ℱ.le k) C hC)).mp (ae_restrict_of_ae (hMC.markov_prop k B hB))
  rw [setIntegral_congr_ae ((ℱ.le k) C hC) h_ae'] at h_set
  have h_lhs : ∫ ω in C, ((B.indicator (fun _ => (1 : ℝ))) ∘ (X (k + 1))) ω ∂μ =
      (μ (C ∩ X (k + 1) ⁻¹' B)).toReal := by
    rw [indicator_comp_preimage, setIntegral_indicator (hX_meas hB),
      setIntegral_const, smul_eq_mul, mul_one]
    rfl
  have h_rhs : ∫ ω in C, (κ (X k ω) B).toReal ∂μ =
      (∫⁻ ω in C, κ (X k ω) B ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    · congr 1
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [ENNReal.ofReal_toReal]
      exact (measure_lt_top _ _).ne
    · exact Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg
    · exact ((Kernel.measurable_coe κ hB).comp hXk_meas).ennreal_toReal.aestronglyMeasurable
  rw [h_lhs, h_rhs] at h_set
  have h_fin_lhs : μ (C ∩ X (k + 1) ⁻¹' B) ≠ ⊤ := (measure_lt_top _ _).ne
  have h_fin_rhs : ∫⁻ ω in C, κ (X k ω) B ∂μ ≠ ⊤ := by
    have h_le : ∫⁻ ω in C, κ (X k ω) B ∂μ ≤ 1 := by
      calc ∫⁻ ω in C, κ (X k ω) B ∂μ ≤ ∫⁻ ω, κ (X k ω) B ∂μ :=
            setLIntegral_le_lintegral _ _
        _ ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ := lintegral_mono fun ω => by
              calc κ (X k ω) B ≤ κ (X k ω) Set.univ := measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ
        _ = 1 := by simp [lintegral_const, measure_univ]
    exact (lt_of_le_of_lt h_le ENNReal.one_lt_top).ne
  exact (ENNReal.toReal_eq_toReal_iff' h_fin_lhs h_fin_rhs).mp h_set.symm

/-- One-step form of the transition law, as a pushforward identity:
restricting `μ` to `C ∈ ℱ k` and pushing forward through `X (k+1)` is
the same as pushing forward through `X k` and then binding with `κ`. -/
private lemma map_restrict_eq_bind_one_step
    (hMC : IsMarkovChain X ℱ κ μ) (k : ℕ)
    {C : Set Ω} (hC : MeasurableSet[ℱ k] C) :
    (μ.restrict C).map (X (k + 1)) =
      ((μ.restrict C).map (X k)).bind κ := by
  ext A hA
  have h_lhs : ((μ.restrict C).map (X (k + 1))) A = μ (C ∩ X (k + 1) ⁻¹' A) := by
    rw [Measure.map_apply (hMC.measurable _) hA,
      Measure.restrict_apply ((hMC.measurable _) hA), Set.inter_comm]
  have h_rhs : (((μ.restrict C).map (X k)).bind κ) A =
      ∫⁻ ω in C, κ (X k ω) A ∂μ := by
    rw [Measure.bind_apply hA (Kernel.aemeasurable κ),
      lintegral_map (Kernel.measurable_coe κ hA) (hMC.measurable k)]
  rw [h_lhs, h_rhs]
  exact hMC.measure_inter_preimage_eq_lintegral k hA hC

/-- Bochner integral against a bind: for a bounded strongly measurable
`f`, integrating against `ν.bind κ` is the `ν`-integral of the
`κ`-integrals. This is the Bochner form of `Measure.lintegral_bind`. -/
private theorem integral_bind_of_bounded {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {ν : Measure α} [IsFiniteMeasure ν]
    {η : Kernel α β} [IsMarkovKernel η] {f : β → ℝ}
    (hf : StronglyMeasurable f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    ∫ y, f y ∂ (ν.bind η) = ∫ x, ∫ y, f y ∂ (η x) ∂ν := by
  have h_int_η : ∀ x, Integrable f (η x) := fun x =>
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have h_int_bind : Integrable f (ν.bind η) := by
    apply Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  -- Key step: the bind identity for nonnegative bounded `g`, proved by
  -- passing to `ENNReal` and using `Measure.lintegral_bind`.
  have h_key : ∀ {g : β → ℝ}, StronglyMeasurable g → (∀ y, 0 ≤ g y) →
      (∀ y, ‖g y‖ ≤ C) →
      ∫ y, g y ∂ (ν.bind η) = ∫ x, ∫ y, g y ∂ (η x) ∂ν := by
    intro g hg hg_nonneg hg_bdd
    have h_int_η_g : ∀ x, Integrable g (η x) := fun x =>
      Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ hg_bdd)
    have h_int_bind_g : Integrable g (ν.bind η) :=
      Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ hg_bdd)
    have h_int_inner : Integrable (fun x => ∫ y, g y ∂ (η x)) ν := by
      apply Integrable.of_bound hg.integral_kernel.aestronglyMeasurable C
      filter_upwards with x
      calc ‖∫ y, g y ∂ (η x)‖ ≤ ∫ y, ‖g y‖ ∂ (η x) := norm_integral_le_integral_norm _
        _ ≤ ∫ _, C ∂ (η x) := by
            apply integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _)
            · exact integrable_const C
            · exact ae_of_all _ hg_bdd
        _ = C := by simp [integral_const]
    have h_ofReal : ∀ x, ENNReal.ofReal (∫ y, g y ∂ (η x)) =
        ∫⁻ y, ENNReal.ofReal (g y) ∂ (η x) := fun x =>
      ofReal_integral_eq_lintegral_ofReal (h_int_η_g x) (ae_of_all _ hg_nonneg)
    have h_eq_ofReal : ENNReal.ofReal (∫ y, g y ∂ (ν.bind η)) =
        ENNReal.ofReal (∫ x, ∫ y, g y ∂ (η x) ∂ν) := by
      rw [ofReal_integral_eq_lintegral_ofReal h_int_bind_g (ae_of_all _ hg_nonneg),
        ofReal_integral_eq_lintegral_ofReal h_int_inner
          (ae_of_all _ fun x => integral_nonneg_of_ae (ae_of_all _ hg_nonneg)),
        Measure.lintegral_bind (Kernel.aemeasurable η)
          ((hg.measurable.ennreal_ofReal).aemeasurable)]
      exact lintegral_congr_ae (ae_of_all _ fun x => (h_ofReal x).symm)
    exact (ENNReal.ofReal_eq_ofReal_iff
      (integral_nonneg_of_ae (ae_of_all _ hg_nonneg))
      (integral_nonneg_of_ae (ae_of_all _ fun x =>
        integral_nonneg_of_ae (ae_of_all _ hg_nonneg)))).mp h_eq_ofReal
  -- General case: split `f` into its positive and negative parts.
  set gpos : β → ℝ := fun y => max (f y) 0 with hgpos_def
  set gneg : β → ℝ := fun y => max (-(f y)) 0 with hgneg_def
  have hgpos_sm : StronglyMeasurable gpos := hf.sup stronglyMeasurable_const
  have hgneg_sm : StronglyMeasurable gneg := hf.neg.sup stronglyMeasurable_const
  have hgpos_nonneg : ∀ y, 0 ≤ gpos y := fun y => le_max_right _ _
  have hgneg_nonneg : ∀ y, 0 ≤ gneg y := fun y => le_max_right _ _
  have hgpos_bdd : ∀ y, ‖gpos y‖ ≤ C := by
    intro y
    simp only [hgpos_def]
    rw [Real.norm_eq_abs, abs_of_nonneg le_sup_right]
    exact sup_le ((le_abs_self (f y)).trans (by simpa [Real.norm_eq_abs] using hC y))
      ((norm_nonneg (f y)).trans (hC y))
  have hgneg_bdd : ∀ y, ‖gneg y‖ ≤ C := by
    intro y
    simp only [hgneg_def]
    rw [Real.norm_eq_abs, abs_of_nonneg le_sup_right]
    exact sup_le ((neg_le_abs (f y)).trans (by simpa [Real.norm_eq_abs] using hC y))
      ((norm_nonneg (f y)).trans (hC y))
  have h_int_pos : ∀ x, Integrable gpos (η x) := fun x =>
    Integrable.of_bound hgpos_sm.aestronglyMeasurable C (ae_of_all _ hgpos_bdd)
  have h_int_neg : ∀ x, Integrable gneg (η x) := fun x =>
    Integrable.of_bound hgneg_sm.aestronglyMeasurable C (ae_of_all _ hgneg_bdd)
  have h_int_inner_pos : Integrable (fun x => ∫ y, gpos y ∂ (η x)) ν := by
    apply Integrable.of_bound hgpos_sm.integral_kernel.aestronglyMeasurable C
    filter_upwards with x
    calc ‖∫ y, gpos y ∂ (η x)‖ ≤ ∫ y, ‖gpos y‖ ∂ (η x) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ _, C ∂ (η x) := by
          apply integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _)
          · exact integrable_const C
          · exact ae_of_all _ hgpos_bdd
      _ = C := by simp [integral_const]
  have h_int_inner_neg : Integrable (fun x => ∫ y, gneg y ∂ (η x)) ν := by
    apply Integrable.of_bound hgneg_sm.integral_kernel.aestronglyMeasurable C
    filter_upwards with x
    calc ‖∫ y, gneg y ∂ (η x)‖ ≤ ∫ y, ‖gneg y‖ ∂ (η x) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ _, C ∂ (η x) := by
          apply integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _)
          · exact integrable_const C
          · exact ae_of_all _ hgneg_bdd
      _ = C := by simp [integral_const]
  have h_toNNReal : ∀ y, (Real.toNNReal (f y) : ℝ) = gpos y := fun y => by
    simp [hgpos_def, Real.toNNReal]
  have h_toNNReal_neg : ∀ y, (Real.toNNReal (-(f y)) : ℝ) = gneg y := fun y => by
    simp [hgneg_def, Real.toNNReal]
  calc ∫ y, f y ∂ (ν.bind η)
      = ∫ y, (Real.toNNReal (f y) : ℝ) ∂ (ν.bind η) -
          ∫ y, (Real.toNNReal (-(f y)) : ℝ) ∂ (ν.bind η) :=
        integral_eq_integral_pos_part_sub_integral_neg_part h_int_bind
    _ = ∫ y, gpos y ∂ (ν.bind η) - ∫ y, gneg y ∂ (ν.bind η) := by
        simp only [h_toNNReal, h_toNNReal_neg]
    _ = (∫ x, ∫ y, gpos y ∂ (η x) ∂ν) - (∫ x, ∫ y, gneg y ∂ (η x) ∂ν) := by
        rw [h_key hgpos_sm hgpos_nonneg hgpos_bdd, h_key hgneg_sm hgneg_nonneg hgneg_bdd]
    _ = ∫ x, (∫ y, gpos y ∂ (η x) - ∫ y, gneg y ∂ (η x)) ∂ν :=
        (integral_sub h_int_inner_pos h_int_inner_neg).symm
    _ = ∫ x, ∫ y, f y ∂ (η x) ∂ν := by
        apply integral_congr_ae
        filter_upwards with x
        have h := integral_eq_integral_pos_part_sub_integral_neg_part (h_int_η x)
        simp only [h_toNNReal, h_toNNReal_neg] at h
        exact h.symm

/-- **One-step Chapman–Kolmogorov equation for functions.** For a
bounded measurable `f`, the conditional expectation of `f (X (k+1))`
given `ℱ k` is the `κ`-integral of `f` evaluated at `X k`. -/
theorem condExp_one_step_eq_integral (hMC : IsMarkovChain X ℱ κ μ) (k : ℕ)
    {f : S → ℝ} (hf : StronglyMeasurable f) (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    μ[ f ∘ X (k + 1) | ℱ k ] =ᵐ[μ] fun ω => ∫ y, f y ∂ (κ (X k ω)) := by
  obtain ⟨C, hC⟩ := hfb
  have hXk : Measurable (X k) := hMC.measurable k
  have hXk1 : Measurable (X (k + 1)) := hMC.measurable (k + 1)
  have hf_int : Integrable (f ∘ X (k + 1)) μ :=
    Integrable.of_bound (hf.measurable.comp hXk1).aestronglyMeasurable C
      (ae_of_all _ fun ω => hC (X (k + 1) ω))
  have hg_sm : StronglyMeasurable (fun x => ∫ y, f y ∂ (κ x)) := hf.integral_kernel
  have hg_bdd : ∀ x, ‖∫ y, f y ∂ (κ x)‖ ≤ C := by
    intro x
    calc ‖∫ y, f y ∂ (κ x)‖ ≤ ∫ y, ‖f y‖ ∂ (κ x) := norm_integral_le_integral_norm _
      _ ≤ ∫ _, C ∂ (κ x) := by
          apply integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _)
          · exact integrable_const C
          · exact ae_of_all _ hC
      _ = C := by simp [integral_const]
  have hg_int : Integrable (fun ω => ∫ y, f y ∂ (κ (X k ω))) μ :=
    Integrable.of_bound (hg_sm.measurable.comp hXk).aestronglyMeasurable C
      (ae_of_all _ fun ω => hg_bdd (X k ω))
  have hg_meas : AEStronglyMeasurable[ℱ k]
      (fun ω => ∫ y, f y ∂ (κ (X k ω))) μ :=
    (hg_sm.measurable.comp (hMC.adapted k)).aestronglyMeasurable
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le k) hf_int ?_ ?_ hg_meas).symm
  · intro s _ _
    exact hg_int.integrableOn
  · intro s hCs _
    calc ∫ x in s, (∫ y, f y ∂ (κ (X k x))) ∂μ
        = ∫ y, (∫ z, f z ∂ (κ y)) ∂ ((μ.restrict s).map (X k)) := by
          symm
          exact integral_map (hXk.aemeasurable) hg_sm.aestronglyMeasurable
      _ = ∫ z, f z ∂ (((μ.restrict s).map (X k)).bind κ) :=
          (integral_bind_of_bounded hf hC).symm
      _ = ∫ z, f z ∂ ((μ.restrict s).map (X (k + 1))) := by
          rw [map_restrict_eq_bind_one_step hMC k hCs]
      _ = ∫ x in s, (f ∘ X (k + 1)) x ∂μ :=
          integral_map (hXk1.aemeasurable) hf.aestronglyMeasurable

/-- **Chapman–Kolmogorov equations for bounded measurable functions.**
For a Markov chain `X` with transition kernel `κ`, the conditional
expectation of `f (X (m + n))` given the past up to time `m` is the
`κ ^ n`-integral of `f` evaluated at `X m`. For `n = 1` this is the
defining one-step Markov property; the general case follows by the
tower property and the integral form of kernel composition. -/
theorem condExp_comp_eq_integral_pow (hMC : IsMarkovChain X ℱ κ μ)
    (m n : ℕ) {f : S → ℝ} (hf : StronglyMeasurable f)
    (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    μ[ f ∘ X (m + n) | ℱ m ] =ᵐ[μ]
      fun ω => ∫ y, f y ∂ (κ ^ n) (X m ω) := by
  revert f hf hfb
  induction n generalizing m with
  | zero =>
    intro f hf hfb
    rw [Nat.add_zero]
    have h_eq : (fun ω => ∫ y, f y ∂ (κ ^ 0) (X m ω)) = f ∘ X m := by
      funext ω
      rw [pow_zero]
      show ∫ y, f y ∂ (Kernel.id (X m ω)) = f (X m ω)
      rw [Kernel.id_apply]
      exact integral_dirac' _ _ hf
    rw [h_eq]
    have hf_int_m : Integrable (f ∘ X m) μ :=
      Integrable.of_bound (hf.measurable.comp (hMC.measurable m)).aestronglyMeasurable
        (Classical.choose hfb) (ae_of_all _ fun ω =>
          Classical.choose_spec hfb (X m ω))
    refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le m) hf_int_m ?_ ?_ ?_).symm
    · intro s _ _
      exact hf_int_m.integrableOn
    · intro s _ _
      rfl
    · exact (hf.measurable.comp (hMC.adapted m)).aestronglyMeasurable
  | succ n ih =>
    intro f hf hfb
    obtain ⟨C, hC⟩ := hfb
    set g : S → ℝ := fun y => ∫ z, f z ∂ (κ y) with hg_def
    have hg_sm : StronglyMeasurable g := hf.integral_kernel
    have hg_bdd : ∃ C', ∀ y, ‖g y‖ ≤ C' := by
      refine ⟨C, fun y => ?_⟩
      calc ‖g y‖ = ‖∫ z, f z ∂ (κ y)‖ := by rw [hg_def]
        _ ≤ ∫ z, ‖f z‖ ∂ (κ y) := norm_integral_le_integral_norm _
        _ ≤ ∫ _, C ∂ (κ y) := by
            apply integral_mono_of_nonneg (ae_of_all _ fun z => norm_nonneg _)
            · exact integrable_const C
            · exact ae_of_all _ hC
        _ = C := by simp [integral_const]
    have h_tower : μ[ f ∘ X (m + (n + 1)) | ℱ m ] =ᵐ[μ]
        μ[ μ[ f ∘ X (m + (n + 1)) | ℱ (m + n) ] | ℱ m ] :=
      (condExp_condExp_of_le (ℱ.mono (Nat.le_add_right m n)) (ℱ.le (m + n))).symm
    have h_inner : μ[ f ∘ X ((m + n) + 1) | ℱ (m + n) ] =ᵐ[μ]
        fun ω => ∫ z, f z ∂ (κ (X (m + n) ω)) :=
      condExp_one_step_eq_integral hMC (m + n) hf ⟨C, hC⟩
    have h_outer : μ[ g ∘ X (m + n) | ℱ m ] =ᵐ[μ]
        fun ω => ∫ y, g y ∂ (κ ^ n) (X m ω) := ih m hg_sm hg_bdd
    have h_pow : ∀ ω, ∫ y, g y ∂ (κ ^ n) (X m ω) =
        ∫ z, f z ∂ (κ ^ (n + 1)) (X m ω) := by
      intro ω
      have h_int : Integrable f ((κ ∘ₖ (κ ^ n)) (X m ω)) :=
        Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
      have h_eq : (κ ^ (n + 1)) = κ ∘ₖ (κ ^ n) := by
        rw [Nat.add_comm n 1, Kernel.pow_add, pow_one]
      rw [h_eq]
      simp only [hg_def]
      exact (Kernel.integral_comp h_int).symm
    calc μ[ f ∘ X (m + (n + 1)) | ℱ m ]
        =ᵐ[μ] μ[ μ[ f ∘ X (m + (n + 1)) | ℱ (m + n) ] | ℱ m ] := h_tower
      _ =ᵐ[μ] μ[ g ∘ X (m + n) | ℱ m ] := by
          apply condExp_congr_ae
          exact h_inner.trans (Filter.EventuallyEq.of_eq
            (funext fun ω => by simp [hg_def, Function.comp_apply]))
      _ =ᵐ[μ] fun ω => ∫ y, g y ∂ (κ ^ n) (X m ω) := h_outer
      _ =ᵐ[μ] fun ω => ∫ z, f z ∂ (κ ^ (n + 1)) (X m ω) :=
          Filter.EventuallyEq.of_eq (funext fun ω => h_pow ω)

/-- **Integrated Chapman–Kolmogorov equation for functions.** The
unconditional expectation of `f (X (m + n))` is the expectation of the
`κ ^ n`-integral of `f` evaluated at `X m`. -/
theorem integral_comp_eq (hMC : IsMarkovChain X ℱ κ μ)
    (m n : ℕ) {f : S → ℝ} (hf : StronglyMeasurable f)
    (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    ∫ ω, f (X (m + n) ω) ∂μ =
      ∫ ω, (∫ y, f y ∂ (κ ^ n) (X m ω)) ∂μ := by
  have h := hMC.condExp_comp_eq_integral_pow m n hf hfb
  calc ∫ ω, f (X (m + n) ω) ∂μ
      = ∫ ω, (μ[ f ∘ X (m + n) | ℱ m ]) ω ∂μ := (integral_condExp (ℱ.le m)).symm
    _ = ∫ ω, (∫ y, f y ∂ (κ ^ n) (X m ω)) ∂μ := integral_congr_ae h

end IsMarkovChain

end MathlibExt.Probability.MarkovChainFunctionCK

end
