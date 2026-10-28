/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Stable distributions

A probability measure `μ` on `ℝ` is *stable* with index `α ∈ (0, 2]` if
every `n`-fold convolution power of `μ` is an affine rescaling of `μ`
itself: `μ^{*n} = (x ↦ aₙ x + bₙ)₊ μ` for some `aₙ > 0` and `bₙ`.
Stable laws are exactly the possible nondegenerate weak limits of
normalized sums of i.i.d. random variables.

## Source

This formalizes the definitions from
`v1/Atlas/TheoryOfProbability/code/DomainAttraction.lean`
(`IsStable`, `IsNondegenerate`, `InDomainOfAttraction`,
`InDomainOfAttractionIndex`), which are the limit objects of the
"Domain of attraction to stable random variable" target (Lecture 18) of
`v1/Atlas/TheoryOfProbability/targets.yaml`.

## Scope

In:

* `convPowStable`: the `n`-fold convolution power of a measure on `ℝ`.
* `IsStable`: the definition, ported verbatim from v1 (with
  `convPowStable` in place of v1's `convPow`).
* The Dirac measure is stable of every index `α ∈ (0, 2]`
  (`isStable_dirac`), and every real Gaussian measure is stable of index
  `2` (`isStable_gaussianReal`).
* `IsNondegenerate`: the definition, ported verbatim from v1. A Gaussian
  with nonzero variance is nondegenerate
  (`isNondegenerate_gaussianReal`), while a Dirac measure is not
  (`not_isNondegenerate_dirac`).
* `InDomainOfAttraction` / `InDomainOfAttractionIndex`: the definitions,
  ported verbatim from v1. The Dirac measure is in its own domain of
  attraction, hence in the domain of attraction of index `α` for every
  `α ∈ (0, 2]` (`inDomainOfAttraction_dirac`,
  `inDomainOfAttractionIndex_dirac`).

Out: the domain-of-attraction characterization theorems in v1
(`domain_of_attraction_limit_is_stable`,
`domain_of_attraction_of_tail_conditions`,
`tail_conditions_of_domain_of_attraction`,
`domain_of_attraction_iff_tail_alpha_lt_two`,
`domain_of_attraction_iff_tail_alpha_eq_two`): all left unproved in v1,
not claimed here. Lévy–Khinchin representations and characteristic-function
characterizations of stable laws are also left for a follow-up.

## Naming

`convPowStable` is deliberately *not* named `MeasureTheory.Measure.convPow`:
that name is already used for the convolution-power algebra in the
unmerged batch-41 PR (#459, `InfinitelyDivisible.lean`). On rebase,
`convPowStable` should be replaced by that `convPow` and this definition
dropped.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Filter ProbabilityTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MathlibExt.Probability.StableDistribution

/-!
### Convolution powers
-/

/-- The `n`-fold convolution power of a measure `μ` on `ℝ`: `μ^{*0} = δ₀`
and `μ^{*(n+1)} = μ^{*n} ∗ μ`. If `μ` is the law of `Y`, then
`μ^{*n}` is the law of the sum of `n` i.i.d. copies of `Y`. -/
noncomputable def convPowStable (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => dirac 0
  | n + 1 => (convPowStable μ n) ∗ μ

/-- The `0`-th convolution power is the Dirac measure at `0`. -/
theorem convPowStable_zero (μ : Measure ℝ) : convPowStable μ 0 = dirac 0 :=
  rfl

/-- The `(n+1)`-st convolution power is the `n`-th power convolved with `μ`. -/
theorem convPowStable_succ (μ : Measure ℝ) (n : ℕ) :
    convPowStable μ (n + 1) = convPowStable μ n ∗ μ :=
  rfl

/-- The convolution power of a Dirac measure is Dirac at the scaled point:
`(δ_a)^{*n} = δ_{n·a}`. -/
theorem convPowStable_dirac (a : ℝ) (n : ℕ) :
    convPowStable (dirac a) n = dirac ((n : ℝ) * a) := by
  induction n with
  | zero => simp [convPowStable_zero]
  | succ n ih =>
    rw [convPowStable_succ, ih, conv_dirac, map_dirac]
    congr 1
    push_cast
    ring

/-- The convolution power of a Gaussian is Gaussian with the mean and the
variance multiplied by `n`: the law of the sum of `n` i.i.d.
`N(μ, v)` variables is `N(nμ, nv)`. -/
theorem convPowStable_gaussianReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    convPowStable (gaussianReal μ v) n =
      gaussianReal ((n : ℝ) * μ) ((n : ℝ≥0) * v) := by
  induction n with
  | zero =>
    simp [convPowStable_zero, gaussianReal_zero_var]
  | succ n ih =>
    rw [convPowStable_succ, ih, gaussianReal_conv_gaussianReal]
    congr 1
    · push_cast
      ring
    · push_cast
      ring

/-!
### Stable laws
-/

/-- A probability measure `μ` on `ℝ` is *stable* with index `α ∈ (0, 2]`
if for every `n > 0` there exist constants `aₙ > 0` and `bₙ` such that
the `n`-fold convolution `μ^{*n}` equals the pushforward of `μ` under
the affine map `x ↦ aₙ x + bₙ`. -/
def IsStable (μ : Measure ℝ) (α : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧
  0 < α ∧ α ≤ 2 ∧
  ∀ (n : ℕ), 0 < n →
    ∃ (aₙ : ℝ) (bₙ : ℝ), 0 < aₙ ∧
      convPowStable μ n = Measure.map (fun x => aₙ * x + bₙ) μ

/-- The Dirac measure at any point is stable of every index `α ∈ (0, 2]`:
with `aₙ = 1` and `bₙ = (n - 1) a`, the affine rescaling sends `δ_a` to
`δ_{a + (n-1)a} = δ_{na} = (δ_a)^{*n}`. -/
theorem isStable_dirac (a : ℝ) {α : ℝ} (hα0 : 0 < α) (hα2 : α ≤ 2) :
    IsStable (dirac a) α := by
  refine ⟨inferInstance, hα0, hα2, fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
  refine ⟨1, (m : ℝ) * a, one_pos, ?_⟩
  rw [convPowStable_dirac, map_dirac]
  congr 1
  push_cast
  ring

/-- Every real Gaussian measure is stable of index `2`: the sum of `n`
i.i.d. `N(μ, v)` variables is `N(nμ, nv)`, which is the pushforward of
`N(μ, v)` under `x ↦ √n · x + (n - √n) μ`. -/
theorem isStable_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    IsStable (gaussianReal μ v) 2 := by
  refine ⟨inferInstance, by norm_num, by norm_num, fun n hn => ?_⟩
  refine ⟨Real.sqrt n, ((n : ℝ) - Real.sqrt n) * μ,
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn), ?_⟩
  rw [convPowStable_gaussianReal]
  have hmap : Measure.map (fun x => Real.sqrt (n : ℝ) * x +
        ((n : ℝ) - Real.sqrt n) * μ) (gaussianReal μ v) =
      Measure.map (fun y => y + ((n : ℝ) - Real.sqrt n) * μ)
        (Measure.map (fun x => Real.sqrt (n : ℝ) * x) (gaussianReal μ v)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hmap, gaussianReal_map_const_mul, gaussianReal_map_add_const]
  have hmk : (NNReal.mk ((Real.sqrt (n : ℝ)) ^ 2) (sq_nonneg _)) = (n : ℝ≥0) := by
    apply NNReal.coe_injective
    simp [Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [hmk]
  congr 1
  ring

/-- A measure `μ` on `ℝ` is *nondegenerate* if it is not a point mass
`δ_a` for any `a`. -/
def IsNondegenerate (μ : Measure ℝ) : Prop :=
  ¬ ∃ a : ℝ, μ = Measure.dirac a

/-- A Gaussian with nonzero variance is nondegenerate: it gives mass `0`
to every singleton, while `δ_a` gives mass `1` to `{a}`. -/
theorem isNondegenerate_gaussianReal {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    IsNondegenerate (gaussianReal μ v) := by
  rintro ⟨a, ha⟩
  have : NullSingletonClass (gaussianReal μ v) := nullSingletonClass_gaussianReal hv
  have h0 : gaussianReal μ v {a} = 0 :=
    NullSingletonClass.measure_singleton (μ := gaussianReal μ v) a
  rw [ha] at h0
  simp at h0

/-- A Dirac measure is degenerate, by definition. -/
theorem not_isNondegenerate_dirac (a : ℝ) :
    ¬ IsNondegenerate (Measure.dirac a) :=
  fun h => h ⟨a, rfl⟩

/-!
### Domains of attraction
-/

/-- The probability measure `μ` is *in the domain of attraction* of `G`
if there exist sequences of normalizing constants `a n > 0` and
centering constants `b n` such that the law of `(S_n - b n) / a n`
(where `S_n` has law `μ^{*n}`) converges weakly to `G`, expressed here
as integration against arbitrary bounded continuous functions. -/
def InDomainOfAttraction (μ G : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ IsProbabilityMeasure G ∧
  ∃ (a : ℕ → ℝ) (b : ℕ → ℝ),
    (∀ n, 0 < a n) ∧
    ∀ (f : ℝ →ᵇ ℝ),
      Tendsto
        (fun n => ∫ x, f x ∂(Measure.map (fun y => (y - b n) / a n)
          (convPowStable μ n)))
        atTop (𝓝 (∫ x, f x ∂G))

/-- `μ` is in the domain of attraction of index `α` if there exists a
stable law `G` of index `α` such that `μ` is in the domain of attraction
of `G`. -/
def InDomainOfAttractionIndex (μ : Measure ℝ) (α : ℝ) : Prop :=
  ∃ G : Measure ℝ, IsStable G α ∧ InDomainOfAttraction μ G

/-- The Dirac measure is in its own domain of attraction: with
`a n = 1` and `b n = (n - 1) a`, the normalized law of `S_n` is
`δ_a` for every `n`. -/
theorem inDomainOfAttraction_dirac (a : ℝ) :
    InDomainOfAttraction (Measure.dirac a) (Measure.dirac a) := by
  refine ⟨inferInstance, inferInstance, fun _ => 1, fun n => ((n : ℝ) - 1) * a,
    fun _ => one_pos, fun f => ?_⟩
  have hterm : ∀ n : ℕ,
      ∫ x, f x ∂(Measure.map (fun y => (y - ((n : ℝ) - 1) * a) / 1)
        (convPowStable (Measure.dirac a) n)) = f a := by
    intro n
    rw [convPowStable_dirac, Measure.map_dirac]
    rw [integral_dirac]
    congr 1
    field_simp
    ring
  simp_rw [hterm, integral_dirac]
  exact tendsto_const_nhds

/-- The Dirac measure is in the domain of attraction of index `α` for
every `α ∈ (0, 2]`, witnessed by the Dirac measure itself. -/
theorem inDomainOfAttractionIndex_dirac (a : ℝ) {α : ℝ}
    (hα0 : 0 < α) (hα2 : α ≤ 2) :
    InDomainOfAttractionIndex (Measure.dirac a) α :=
  ⟨Measure.dirac a, isStable_dirac a hα0 hα2, inDomainOfAttraction_dirac a⟩

end MathlibExt.Probability.StableDistribution
