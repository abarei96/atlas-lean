/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Backwards martingales

A *backwards martingale* is a process indexed by `ℕ` that is a martingale with
respect to a *decreasing* filtration: the conditioning σ-algebras shrink as
`n → ∞`, so the process is `M n = μ[M 0 | ℱ n]` almost everywhere. This is the
setting of Durrett's backwards-martingale convergence theorem (Lecture 29),
where `X_{-∞} = lim_{n → -∞} Xₙ` exists a.s. and in `L¹`.

This file ports the definitions and the fully proved API lemmas from
`v1/Atlas/TheoryOfProbability/code/BackwardsMartingales.lean`. The convergence
theorems themselves (`levy_downward_ae`, `backwards_martingale_ae_tendsto`) are
*not* claimed here: in v1 they rest on `condExp_antitone_ae_tendsto`, which is
left unproved there, and they were ported by other batches through a different
route. What is ported here is the infrastructure those theorems are stated in,
plus one new consequence: the one-step conditional-expectation recurrence
`μ[M n | ℱ (n+1)] =ᵐ[μ] M (n+1)`.

## Main definitions

- `MathlibExt.Probability.BackwardsMartingale.DecreasingFiltration`: a sequence
  of sub-σ-algebras `ℱ n ⊆ m0` that is antitone in `n`.
- `MathlibExt.Probability.BackwardsMartingale.DecreasingFiltration.tailAlgebra`:
  the tail σ-algebra `⨅ n, ℱ n`.
- `MathlibExt.Probability.BackwardsMartingale.IsBackwardsMartingale`: `M 0`
  integrable, each `M n` is `ℱ n`-strongly measurable, and
  `M n =ᵐ[μ] μ[M 0 | ℱ n]`.

## Main results

- `IsBackwardsMartingale.integrable`: every term of a backwards martingale is
  integrable.
- `IsBackwardsMartingale.uniformIntegrable`: a backwards martingale is uniformly
  integrable in `L¹`.
- `IsBackwardsMartingale.condExp_succ_ae_eq`: the one-step recurrence
  `μ[M n | ℱ (n+1)] =ᵐ[μ] M (n+1)`.
- `isBackwardsMartingale_condExp`: the conditional expectations
  `n ↦ μ[g | ℱ n]` of a single function `g` form a backwards martingale.
-/

@[expose] public section

namespace MathlibExt.Probability.BackwardsMartingale

open MeasureTheory Filter

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- A *decreasing filtration* on `(Ω, m0)` is a sequence of sub-σ-algebras
`ℱ n ⊆ m0` that is antitone in `n` (i.e. `ℱ 0 ⊇ ℱ 1 ⊇ ℱ 2 ⊇ ⋯`). This is the
natural index structure for backwards martingales, where the conditioning
σ-algebras shrink as `n → ∞`. -/
structure DecreasingFiltration (Ω : Type*) (m0 : MeasurableSpace Ω) where
  seq : ℕ → MeasurableSpace Ω
  antitone' : Antitone seq
  le' : ∀ n, seq n ≤ m0

namespace DecreasingFiltration

/-- The *constant* decreasing filtration: every component is the same
sub-σ-algebra `m ≤ m0`. -/
def const (m : MeasurableSpace Ω) (hm : m ≤ m0) : DecreasingFiltration Ω m0 :=
  ⟨fun _ => m, antitone_const, fun _ => hm⟩

/-- The *tail σ-algebra* of a decreasing filtration `ℱ`, defined as the
intersection `⨅ n, ℱ n`. This is the σ-algebra of events that lie in every
`ℱ n`, i.e. the limit as the filtration shrinks. -/
@[reducible]
def tailAlgebra (ℱ : DecreasingFiltration Ω m0) : MeasurableSpace Ω :=
  ⨅ n, ℱ.seq n

/-- The tail σ-algebra of a decreasing filtration is contained in the ambient
σ-algebra `m0`. -/
theorem tailAlgebra_le (ℱ : DecreasingFiltration Ω m0) : ℱ.tailAlgebra ≤ m0 :=
  le_trans (iInf_le _ 0) (ℱ.le' 0)

/-- The tail σ-algebra is contained in every component `ℱ n` of the filtration. -/
theorem tailAlgebra_le_seq (ℱ : DecreasingFiltration Ω m0) (n : ℕ) :
    ℱ.tailAlgebra ≤ ℱ.seq n :=
  iInf_le _ n

/-- The tail σ-algebra of the constant filtration with value `m` is `m` itself. -/
theorem tailAlgebra_const (m : MeasurableSpace Ω) (hm : m ≤ m0) :
    (DecreasingFiltration.const m hm).tailAlgebra = m := by
  show (⨅ _n : ℕ, m) = m
  exact iInf_const

end DecreasingFiltration

/-- A *backwards martingale* with respect to a decreasing filtration `ℱ` and
measure `μ` is a process `M : ℕ → Ω → ℝ` such that `M 0` is integrable, each
`M n` is `ℱ n`-strongly measurable, and `M n = μ[M 0 | ℱ n]` `μ`-a.e.
In particular, `μ[M n | ℱ (n+1)] =ᵐ[μ] M (n+1)` for all `n` (see
`IsBackwardsMartingale.condExp_succ_ae_eq` below). This corresponds to the
setting of Durrett's backwards-martingale convergence theorem. -/
structure IsBackwardsMartingale (M : ℕ → Ω → ℝ) (ℱ : DecreasingFiltration Ω m0)
    (μ : Measure Ω) : Prop where
  integrable_zero : Integrable (M 0) μ
  adapted : ∀ n, StronglyMeasurable[ℱ.seq n] (M n)
  condExp_ae_eq : ∀ n, M n =ᵐ[μ] μ[M 0 | ℱ.seq n]

namespace IsBackwardsMartingale

/-- Every term `M n` of a backwards martingale is integrable, since it is
`μ`-a.e. equal to the integrable conditional expectation `μ[M 0 | ℱ n]`. -/
theorem integrable
    {M : ℕ → Ω → ℝ} {ℱ : DecreasingFiltration Ω m0}
    (hM : IsBackwardsMartingale M ℱ μ) (n : ℕ) : Integrable (M n) μ :=
  integrable_condExp.congr (hM.condExp_ae_eq n).symm

/-- A backwards martingale is uniformly integrable in `L¹`: this follows from the
standard fact that the family of conditional expectations `{μ[M 0 | ℱ n]}` of a
single integrable function `M 0` is uniformly integrable. -/
theorem uniformIntegrable [IsFiniteMeasure μ]
    {M : ℕ → Ω → ℝ} {ℱ : DecreasingFiltration Ω m0}
    (hM : IsBackwardsMartingale M ℱ μ) : UniformIntegrable M 1 μ :=
  (hM.integrable_zero.uniformIntegrable_condExp ℱ.le').ae_eq
    (fun n => (hM.condExp_ae_eq n).symm)

/-- The one-step recurrence for a backwards martingale: conditioning `M n` on the
smaller σ-algebra `ℱ (n+1)` gives `M (n+1)` almost everywhere. This is the
tower property of conditional expectation applied to `M n =ᵐ[μ] μ[M 0 | ℱ n]`. -/
theorem condExp_succ_ae_eq [IsFiniteMeasure μ]
    {M : ℕ → Ω → ℝ} {ℱ : DecreasingFiltration Ω m0}
    (hM : IsBackwardsMartingale M ℱ μ) (n : ℕ) :
    μ[M n | ℱ.seq (n + 1)] =ᵐ[μ] M (n + 1) := by
  calc μ[M n | ℱ.seq (n + 1)]
      =ᵐ[μ] μ[μ[M 0 | ℱ.seq n] | ℱ.seq (n + 1)] :=
        condExp_congr_ae (hM.condExp_ae_eq n)
    _ =ᵐ[μ] μ[M 0 | ℱ.seq (n + 1)] :=
        condExp_condExp_of_le (ℱ.antitone' (Nat.le_succ n)) (ℱ.le' n)
    _ =ᵐ[μ] M (n + 1) := (hM.condExp_ae_eq (n + 1)).symm

end IsBackwardsMartingale

/-- The conditional expectations `n ↦ μ[g | ℱ n]` of a single function `g`
along a decreasing filtration form a backwards martingale. This is the
canonical example of a backwards martingale. No integrability of `g` is needed:
conditional expectation is integrable by convention, and the `condExp_ae_eq`
field is the tower property: `ℱ n ≤ ℱ 0`, so conditioning `μ[g | ℱ 0]` on
`ℱ n` recovers `μ[g | ℱ n]`. -/
theorem isBackwardsMartingale_condExp (g : Ω → ℝ)
    (ℱ : DecreasingFiltration Ω m0) (μ : Measure Ω) [IsFiniteMeasure μ] :
    IsBackwardsMartingale (fun n => μ[g | ℱ.seq n]) ℱ μ := by
  refine ⟨integrable_condExp, fun _ => stronglyMeasurable_condExp, fun n => ?_⟩
  have h := condExp_condExp_of_le (μ := μ) (f := g) (m₁ := ℱ.seq n)
    (m₂ := ℱ.seq 0) (m₀ := m0) (ℱ.antitone' (Nat.zero_le n)) (ℱ.le' 0)
  exact h.symm

end MathlibExt.Probability.BackwardsMartingale
