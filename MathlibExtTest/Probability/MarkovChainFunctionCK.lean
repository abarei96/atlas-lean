/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChainFunctionCK

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open MathlibExt.Probability.MarkovChainFunctionCK

namespace MathlibExtTest.Probability.MarkovChainFunctionCK

/-- The one-step function form, restated with its exact public signature. -/
example {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]
    (hMC : IsMarkovChain X ℱ κ μ) (k : ℕ) {f : S → ℝ}
    (hf : StronglyMeasurable f) (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    μ[ f ∘ X (k + 1) | ℱ k ] =ᵐ[μ] fun ω => ∫ y, f y ∂ (κ (X k ω)) :=
  hMC.condExp_one_step_eq_integral k hf hfb

/-- The `n`-step function form, restated with its exact public signature. -/
example {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]
    (hMC : IsMarkovChain X ℱ κ μ) (m n : ℕ) {f : S → ℝ}
    (hf : StronglyMeasurable f) (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    μ[ f ∘ X (m + n) | ℱ m ] =ᵐ[μ]
      fun ω => ∫ y, f y ∂ (κ ^ n) (X m ω) :=
  hMC.condExp_comp_eq_integral_pow m n hf hfb

/-- The integrated form, restated with its exact public signature. -/
example {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {ℱ : Filtration ℕ m} {κ : Kernel S S} [IsMarkovKernel κ]
    (hMC : IsMarkovChain X ℱ κ μ) (m n : ℕ) {f : S → ℝ}
    (hf : StronglyMeasurable f) (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    ∫ ω, f (X (m + n) ω) ∂μ =
      ∫ ω, (∫ y, f y ∂ (κ ^ n) (X m ω)) ∂μ :=
  hMC.integral_comp_eq m n hf hfb

/-- A constant chain is a Markov chain with the constant Dirac kernel:
at each time the next state is `c`, so the one-step conditional
probability of `B` is `1` if `c ∈ B` and `0` otherwise, on both sides. -/
theorem constant_chain_isMarkovChain {Ω S : Type*} {m : MeasurableSpace Ω}
    [MeasurableSpace S] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (c : S) :
    IsMarkovChain (fun _ (_ : Ω) => c) ℱ (Kernel.const S (Measure.dirac c)) μ := by
  refine ⟨?_, ?_⟩
  · exact fun _ => measurable_const
  · intro n B hB
    classical
    have h_lhs : (B.indicator (fun _ => (1 : ℝ))) ∘ ((fun _ (_ : Ω) => c) (n + 1)) =
        fun _ => if c ∈ B then (1 : ℝ) else 0 := by
      ext ω
      simp [Set.indicator]
    rw [h_lhs, condExp_const (ℱ.le n)]
    refine Filter.EventuallyEq.of_eq ?_
    funext ω
    by_cases h : c ∈ B
    · simp [Kernel.const_apply, Measure.dirac_apply' _ hB, h]
    · simp [Kernel.const_apply, Measure.dirac_apply' _ hB, h]

/-- The `n`-step function form applied to the constant chain: the
conditional expectation of `f` at time `m + n` given `ℱ m` is the
`n`-step constant-kernel integral of `f` at `c`. -/
example {Ω S : Type*} {m : MeasurableSpace Ω} [MeasurableSpace S]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (c : S) (m n : ℕ) {f : S → ℝ}
    (hf : StronglyMeasurable f) (hfb : ∃ C, ∀ y, ‖f y‖ ≤ C) :
    μ[ f ∘ ((fun _ (_ : Ω) => c) (m + n)) | ℱ m ] =ᵐ[μ]
      fun ω => ∫ y, f y ∂ (((Kernel.const S (Measure.dirac c)) ^ n)
        ((fun _ (_ : Ω) => c) m ω)) :=
  (constant_chain_isMarkovChain ℱ c).condExp_comp_eq_integral_pow m n hf hfb

/-- The one-step kernel integral of the identity on `ℝ` against the
constant Dirac kernel at `c` is `c`: the constant chain really does stay
at `c`. -/
example {Ω : Type*} (c : ℝ) :
    (fun ω : Ω => ∫ y, y ∂ (((Kernel.const ℝ (Measure.dirac c)) ^ 1)
      ((fun _ (_ : Ω) => c) 0 ω))) = fun _ => c := by
  funext ω
  rw [pow_one, Kernel.const_apply]
  exact integral_dirac' _ _ stronglyMeasurable_id

#print axioms MathlibExt.Probability.MarkovChainFunctionCK.IsMarkovChain.condExp_one_step_eq_integral
#print axioms MathlibExt.Probability.MarkovChainFunctionCK.IsMarkovChain.condExp_comp_eq_integral_pow
#print axioms MathlibExt.Probability.MarkovChainFunctionCK.IsMarkovChain.integral_comp_eq

end MathlibExtTest.Probability.MarkovChainFunctionCK
