/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Process.Filtration
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal

namespace MathlibExt.Probability.FiniteMarkovChain

/-!
# Finite-state Markov chains

A finite-state Markov chain is a sequence `X : ℕ → Ω → Fin (M + 1)` whose
one-step conditional probabilities are given by a row-stochastic matrix `P`:
`μ[Xₙ₊₁ = j | ℱₙ] = P.prob (Xₙ) j` almost surely.

Source: `v1/Atlas/TheoryOfProbability/code/FiniteMarkovChain.lean`
(Definition: Markov chain, finite state, Lecture 30/31) and
`v1/Atlas/TheoryOfProbability/code/MarkovChain.lean` (Definition: Markov
chain, general). The two `v1` definitions are ported below in the form they
are used: the matrix and the finite-chain predicate are verbatim from `v1`;
the bridge theorems `condExp_indicator` and `map_succ_eq_bind` are new, and
give the general one-step Markov property and the one-step forward equation
for the kernel built from the matrix.

The general `IsMarkovChain` predicate is not restated here: batches 46 and
65 define their own namespace-scoped copies of it. The bridge theorem states
the same one-step conditional-expectation equation directly for
`finiteChainKernel P`, so it can be used without choosing between those
copies.
-/

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- A `StochasticMatrix M` is an `(M+1) × (M+1)` row-stochastic matrix: entries
`prob i j` are non-negative real numbers, and the rows sum to `1`. This is the
transition matrix of a Markov chain on the finite state space `Fin (M + 1)`.
Ported verbatim from `v1/Atlas/TheoryOfProbability/code/FiniteMarkovChain.lean`.
Namespace-scoped copy: batches 37 and 60 define their own namespace-scoped
copies for the cycle theorem and ergodic chains; unify on rebase. -/
structure StochasticMatrix (M : ℕ) where
  prob : Fin (M + 1) → Fin (M + 1) → ℝ
  nonneg : ∀ i j, 0 ≤ prob i j
  row_sum : ∀ i, ∑ j, prob i j = 1

/-- `IsFiniteMarkovChain X P ℱ μ` asserts that the sequence `X : ℕ → Ω → Fin (M+1)`
is a Markov chain with transition matrix `P`, adapted to the filtration `ℱ`,
under the measure `μ`. Concretely: each `X n` is `ℱ n`-measurable, and the conditional
probability that `X (n+1) = j` given `ℱ n` equals `P.prob (X n) j`, matching the
Markov property `P(X_{n+1} = j | X_n = i, ...) = P_{ij}`.
Ported verbatim from `v1/Atlas/TheoryOfProbability/code/FiniteMarkovChain.lean`;
`v1` writes the filtration as `DiscreteFiltration Ω m`, which is `Filtration ℕ m`. -/
structure IsFiniteMarkovChain {M : ℕ} (X : ℕ → Ω → Fin (M + 1))
    (P : StochasticMatrix M) (ℱ : Filtration ℕ m) (μ : Measure Ω) : Prop where
  adapted : ∀ n, @Measurable _ _ (ℱ n) _ (X n)
  markov_prop : ∀ n : ℕ, ∀ j : Fin (M + 1),
    μ[(fun ω => if X (n + 1) ω = j then (1 : ℝ) else 0) | ℱ n] =ᵐ[μ]
      fun ω => P.prob (X n ω) j

/-- The transition kernel of a stochastic matrix: `finiteChainKernel P x` is the
probability measure on `Fin (M + 1)` putting mass `P.prob x j` on each state `j`.
This is the kernel form of the transition matrix. -/
noncomputable def finiteChainKernel {M : ℕ} (P : StochasticMatrix M) :
    Kernel (Fin (M + 1)) (Fin (M + 1)) where
  toFun x := ∑ j, ENNReal.ofReal (P.prob x j) • Measure.dirac j
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have hsum : ∀ x : Fin (M + 1),
        (∑ j, ENNReal.ofReal (P.prob x j) • Measure.dirac j) s
          = ∑ j, ENNReal.ofReal (P.prob x j) * (Measure.dirac j s) := by
      intro x
      have h := congrFun
        (Measure.coe_finsetSum Finset.univ
          (fun j => ENNReal.ofReal (P.prob x j) • Measure.dirac j)) s
      simp only [Finset.sum_apply, Measure.smul_apply, smul_eq_mul] at h
      exact h
    simp_rw [hsum]
    apply Finset.measurable_sum
    intro j _
    have h1 : Measurable (fun x : Fin (M + 1) => P.prob x j) := measurable_from_top
    exact (ENNReal.measurable_ofReal.comp h1).const_mul (Measure.dirac j s)

/-- The kernel of a stochastic matrix is a Markov kernel: each row is a
probability measure, by non-negativity and the row-sum condition. -/
instance finiteChainKernel.isMarkovKernel {M : ℕ} (P : StochasticMatrix M) :
    IsMarkovKernel (finiteChainKernel P) where
  isProbabilityMeasure x := by
    refine ⟨?_⟩
    show (∑ j, ENNReal.ofReal (P.prob x j) • Measure.dirac j) Set.univ = 1
    have hsum : (∑ j, ENNReal.ofReal (P.prob x j) • Measure.dirac j) Set.univ
        = ∑ j, ENNReal.ofReal (P.prob x j) := by
      have h := congrFun
        (Measure.coe_finsetSum Finset.univ
          (fun j => ENNReal.ofReal (P.prob x j) • Measure.dirac j)) Set.univ
      simp only [Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one] at h
      exact h
    rw [hsum, ← ENNReal.ofReal_sum_of_nonneg (fun j _ => P.nonneg x j), P.row_sum x,
      ENNReal.ofReal_one]

/-- The kernel of a stochastic matrix evaluated at a finite set is the sum of the
transition probabilities into that set. -/
theorem finiteChainKernel_apply {M : ℕ} (P : StochasticMatrix M) (x : Fin (M + 1))
    (B : Finset (Fin (M + 1))) :
    finiteChainKernel P x ↑B = ∑ j ∈ B, ENNReal.ofReal (P.prob x j) := by
  show (∑ j, ENNReal.ofReal (P.prob x j) • Measure.dirac j) ↑B = _
  have h1 : (∑ j, ENNReal.ofReal (P.prob x j) • Measure.dirac j) ↑B
      = ∑ j, ENNReal.ofReal (P.prob x j) * (Measure.dirac j ↑B) := by
    have h := congrFun (Measure.coe_finsetSum Finset.univ
      (fun j => ENNReal.ofReal (P.prob x j) • Measure.dirac j)) ↑B
    simp only [Finset.sum_apply, Measure.smul_apply, smul_eq_mul] at h
    exact h
  rw [h1]
  have h2 : ∀ j, Measure.dirac j ↑B = if j ∈ B then (1 : ℝ≥0∞) else 0 := by
    intro j
    rw [Measure.dirac_apply' _ (Finset.measurableSet B)]
    simp [Set.indicator_apply]
  simp_rw [h2]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- Finite sums of almost-everywhere equal functions are almost-everywhere equal. -/
private theorem eventuallyEq_finset_sum {ι : Type*} {s : Finset ι}
    {f g : ι → Ω → ℝ} (h : ∀ i ∈ s, f i =ᵐ[μ] g i) :
    (∑ i ∈ s, f i) =ᵐ[μ] ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    rw [Finset.sum_insert his, Finset.sum_insert his]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- **Bridge: finite-state Markov chains satisfy the general one-step Markov
property.** For a finite Markov chain, the conditional expectation of the
indicator of `X (n+1) ∈ B` given `ℱ n` is the kernel of `P` evaluated at
`X n`, almost surely. This is the one-step form of `v1`'s general
`IsMarkovChain.markov_prop` specialized to the matrix kernel. No measurability
hypothesis on `B` is needed: the indicator is defined for every set, and the
proof only sums over the finite state space. -/
theorem IsFiniteMarkovChain.condExp_indicator {M : ℕ} {X : ℕ → Ω → Fin (M + 1)}
    {P : StochasticMatrix M} {ℱ : Filtration ℕ m} [IsProbabilityMeasure μ]
    (hX : IsFiniteMarkovChain X P ℱ μ) {n : ℕ} {B : Set (Fin (M + 1))} :
    μ[(B.indicator (fun _ => (1 : ℝ))) ∘ (X (n + 1)) | ℱ n] =ᵐ[μ]
      fun ω => (finiteChainKernel P (X n ω) B).toReal := by
  classical
  have hLHS : (B.indicator (fun _ => (1 : ℝ))) ∘ (X (n + 1))
      = ∑ j ∈ B, (fun ω => if X (n + 1) ω = j then (1 : ℝ) else 0) := by
    funext ω
    simp only [Function.comp_apply, Finset.sum_apply, Set.indicator_apply]
    rw [Finset.sum_ite_eq]
    by_cases h : X (n + 1) ω ∈ B <;> simp [h, Set.mem_toFinset]
  have hInt : ∀ j ∈ B.toFinset,
      Integrable (fun ω => if X (n + 1) ω = j then (1 : ℝ) else 0) μ := by
    intro j _
    have hXmeas : Measurable (X (n + 1)) := (hX.adapted (n + 1)).mono (ℱ.le _) le_rfl
    have hEq : (fun ω => if X (n + 1) ω = j then (1 : ℝ) else 0)
        = (X (n + 1) ⁻¹' {j}).indicator (fun _ => (1 : ℝ)) := by
      funext ω
      simp [Set.indicator_apply]
    rw [hEq]
    exact (integrable_const (1 : ℝ)).indicator (hXmeas (measurableSet_singleton j))
  have hRHS : ∀ ω, (finiteChainKernel P (X n ω) B).toReal
      = ∑ j ∈ B, P.prob (X n ω) j := by
    intro ω
    have hApply := finiteChainKernel_apply P (X n ω) B.toFinset
    rw [Set.coe_toFinset] at hApply
    rw [hApply, ENNReal.toReal_sum (fun j _ => ENNReal.ofReal_ne_top)]
    exact Finset.sum_congr rfl fun j _ => ENNReal.toReal_ofReal (P.nonneg _ _)
  calc μ[(B.indicator (fun _ => (1 : ℝ))) ∘ (X (n + 1)) | ℱ n]
      =ᵐ[μ] μ[∑ j ∈ B, (fun ω => if X (n + 1) ω = j then (1 : ℝ) else 0) | ℱ n] :=
        Filter.EventuallyEq.of_eq (by rw [hLHS])
    _ =ᵐ[μ] ∑ j ∈ B, μ[(fun ω => if X (n + 1) ω = j then (1 : ℝ) else 0) | ℱ n] :=
        condExp_finsetSum hInt (ℱ n)
    _ =ᵐ[μ] ∑ j ∈ B, (fun ω => P.prob (X n ω) j) :=
        eventuallyEq_finset_sum (fun j _ => hX.markov_prop n j)
    _ =ᵐ[μ] fun ω => (finiteChainKernel P (X n ω) B).toReal :=
        Filter.EventuallyEq.of_eq (by
          funext ω
          rw [Finset.sum_apply]
          exact (hRHS ω).symm)

/-- **One-step forward equation.** The law of `X (n+1)` is the law of `X n`
transported by the transition kernel of `P`. -/
theorem IsFiniteMarkovChain.map_succ_eq_bind {M : ℕ} {X : ℕ → Ω → Fin (M + 1)}
    {P : StochasticMatrix M} {ℱ : Filtration ℕ m} [IsProbabilityMeasure μ]
    (hX : IsFiniteMarkovChain X P ℱ μ) (n : ℕ) :
    μ.map (X (n + 1)) = (μ.map (X n)).bind (finiteChainKernel P) := by
  have hXmeas_succ : Measurable (X (n + 1)) := (hX.adapted (n + 1)).mono (ℱ.le _) le_rfl
  have hXmeas_n : Measurable (X n) := (hX.adapted n).mono (ℱ.le _) le_rfl
  ext B hB
  have hBind : ((μ.map (X n)).bind (finiteChainKernel P)) B
      = ∫⁻ x, finiteChainKernel P x B ∂(μ.map (X n)) :=
    Measure.bind_apply hB (Kernel.aemeasurable _)
  have hMeas : Measurable (fun x => (finiteChainKernel P x B).toReal) :=
    (Kernel.measurable_coe _ hB).ennreal_toReal
  have hIntble : Integrable (fun x => (finiteChainKernel P x B).toReal) (μ.map (X n)) := by
    refine Integrable.of_bound hMeas.aestronglyMeasurable 1 ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    calc (finiteChainKernel P x B).toReal ≤ (1 : ℝ≥0∞).toReal :=
          ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
      _ = 1 := ENNReal.toReal_one
  have hInt : ∫⁻ x, finiteChainKernel P x B ∂(μ.map (X n))
      = ENNReal.ofReal (∫ x, (finiteChainKernel P x B).toReal ∂(μ.map (X n))) := by
    have hEq : ∀ x, finiteChainKernel P x B
        = ENNReal.ofReal ((finiteChainKernel P x B).toReal) :=
      fun x => (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    rw [lintegral_congr_ae (Filter.Eventually.of_forall fun x => hEq x)]
    exact (ofReal_integral_eq_lintegral_ofReal hIntble
      (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)).symm
  have hMap : ∫ ω, (finiteChainKernel P (X n ω) B).toReal ∂μ
      = ∫ x, (finiteChainKernel P x B).toReal ∂(μ.map (X n)) :=
    (MeasureTheory.integral_map hXmeas_n.aemeasurable
      hMeas.aestronglyMeasurable).symm
  have hCond : ∫ ω, μ[((B.indicator (fun _ => (1 : ℝ))) ∘ X (n + 1)) | ℱ n] ω ∂μ
      = ∫ ω, (finiteChainKernel P (X n ω) B).toReal ∂μ :=
    integral_congr_ae (hX.condExp_indicator)
  have hTot : ∫ ω, μ[((B.indicator (fun _ => (1 : ℝ))) ∘ X (n + 1)) | ℱ n] ω ∂μ
      = ∫ ω, ((B.indicator (fun _ => (1 : ℝ))) ∘ X (n + 1)) ω ∂μ :=
    integral_condExp (ℱ.le n)
  have hInd : ∫ ω, ((B.indicator (fun _ => (1 : ℝ))) ∘ X (n + 1)) ω ∂μ
      = (μ (X (n + 1) ⁻¹' B)).toReal := by
    have hEq : (B.indicator (fun _ => (1 : ℝ))) ∘ X (n + 1)
        = (X (n + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ)) := by
      classical
      funext ω
      simp only [Function.comp_apply, Set.indicator_apply, Set.mem_preimage]
    rw [hEq, integral_indicator_const (1 : ℝ) (hXmeas_succ hB)]
    simp [Measure.real]
  calc μ.map (X (n + 1)) B = μ (X (n + 1) ⁻¹' B) :=
        Measure.map_apply hXmeas_succ hB
    _ = ENNReal.ofReal (μ (X (n + 1) ⁻¹' B)).toReal :=
        (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    _ = ENNReal.ofReal (∫ ω, ((B.indicator (fun _ => (1 : ℝ))) ∘ X (n + 1)) ω ∂μ) := by
        rw [hInd]
    _ = ENNReal.ofReal (∫ ω, μ[((B.indicator (fun _ => (1 : ℝ))) ∘ X (n + 1)) | ℱ n] ω ∂μ) := by
        rw [← hTot]
    _ = ENNReal.ofReal (∫ ω, (finiteChainKernel P (X n ω) B).toReal ∂μ) := by
        rw [hCond]
    _ = ENNReal.ofReal (∫ x, (finiteChainKernel P x B).toReal ∂(μ.map (X n))) := by
        rw [hMap]
    _ = ∫⁻ x, finiteChainKernel P x B ∂(μ.map (X n)) := hInt.symm
    _ = ((μ.map (X n)).bind (finiteChainKernel P)) B := hBind.symm

end MathlibExt.Probability.FiniteMarkovChain
