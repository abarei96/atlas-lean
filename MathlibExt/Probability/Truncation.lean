/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Truncation of random variables

The truncation `Yₙ = Xₙ · 1_{|Xₙ| ≤ A}` is the key construction in
Kolmogorov's three-series theorem: the three series in that theorem are
the tail probabilities `∑ₙ P(|Xₙ| > A)`, the means `∑ₙ E[Yₙ]`, and the
variances `∑ₙ Var(Yₙ)` of the truncations.

## Source

This formalizes the truncation helpers of
`v1/Atlas/TheoryOfProbability/code/KolmogorovThreeSeries.lean`:
`truncatedRV_eq_comp`, `measurable_truncation_fun`,
`iIndepFun_truncatedRV`, `abs_truncatedRV_le`,
`truncated_indicator_eq_of_bdd`, `truncatedRV_eq_of_bdd`, and
`ae_tendsto_truncatedRV_of_bdd`. It does not re-declare v1's
`truncatedRV`: that definition already lives in
`ProbabilityTheory.KolmogorovThreeSeries` in the batch-10 file
(`MathlibExt/Probability/KolmogorovThreeSeries.lean`), which also
ports the sufficiency direction of the three-series theorem. The
truncation here is named `truncRV` and is definitionally the same
function, so the two files agree on rebase.

## Scope

Only the truncation API is ported. The necessity direction of the
three-series theorem is **not** claimed: in v1 it rests on
`summable_mean_and_variance_of_ae_tendsto_ax`, which is left unproved
there. The new lemmas below (pointwise truncation identities,
measurability, `MemLp` / integrability / variance bounds for the
truncations) are proved from scratch; they are the form in which the
truncation API is used downstream.

## Main results

* `MathlibExt.Probability.Truncation.truncationFun`: the deterministic
  truncation function `x ↦ x · 1_{|x| ≤ A}`.
* `MathlibExt.Probability.Truncation.truncRV`: the truncation
  `Xₙ · 1_{|Xₙ| ≤ A}` of a random variable.
* `MathlibExt.Probability.Truncation.iIndepFun_truncRV`: truncation
  preserves independence of a family.
* `MathlibExt.Probability.Truncation.abs_truncRV_le`,
  `MathlibExt.Probability.Truncation.memLp_truncRV`,
  `MathlibExt.Probability.Truncation.variance_truncRV_le`: the
  truncations are uniformly bounded, in every `Lᵖ`, and have variance
  at most `A²`.
* `MathlibExt.Probability.Truncation.ae_tendsto_truncRV_of_bdd`:
  for a uniformly bounded family, a.s. convergence of the partial sums
  is unchanged by truncation.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal Topology

noncomputable section

namespace MathlibExt.Probability.Truncation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The deterministic truncation function at level `A`: it is the identity
on `[-A, A]` and `0` outside. Truncating a random variable `X` at level `A`
is composition with this function. -/
def truncationFun (A : ℝ) : ℝ → ℝ :=
  fun x => x * Set.indicator {x : ℝ | |x| ≤ A} 1 x

/-- The truncation of the random variable `X n` at level `A`:
`truncRV X A n ω = X n ω` when `|X n ω| ≤ A`, and `0` otherwise. -/
def truncRV (X : ℕ → Ω → ℝ) (A : ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => X n ω * Set.indicator {ω : Ω | |X n ω| ≤ A} 1 ω

/-- Truncation at level `A` is the identity on points with `|x| ≤ A`. -/
theorem truncationFun_eq_self_of_abs_le {A x : ℝ} (hx : |x| ≤ A) :
    truncationFun A x = x := by
  unfold truncationFun
  rw [Set.indicator_of_mem (by simpa using hx), Pi.one_apply, mul_one]

/-- Truncation at level `A` kills points with `|x| > A`. -/
theorem truncationFun_eq_zero_of_abs_gt {A x : ℝ} (hx : A < |x|) :
    truncationFun A x = 0 := by
  unfold truncationFun
  rw [Set.indicator_of_notMem (by simpa using not_le.mpr hx)]
  exact mul_zero _


/-- Truncation preserves nonnegativity: truncating a nonnegative value
gives a nonnegative value. -/
theorem truncationFun_nonneg_of_nonneg {A x : ℝ} (hx : 0 ≤ x) :
    0 ≤ truncationFun A x := by
  by_cases h : |x| ≤ A
  · rw [truncationFun_eq_self_of_abs_le h]; exact hx
  · rw [truncationFun_eq_zero_of_abs_gt (not_le.mp h)]

set_option linter.unusedSectionVars false in
/-- `truncRV` factors as the composition of `Xₙ` with the deterministic
truncation function `x ↦ x · 1_{|x| ≤ A}`. -/
theorem truncRV_eq_comp (X : ℕ → Ω → ℝ) (A : ℝ) (n : ℕ) :
    truncRV X A n = truncationFun A ∘ X n := by
  ext ω
  simp only [truncRV, Function.comp, truncationFun, Set.indicator, Set.mem_ofPred_eq,
    Pi.one_apply]

/-- The deterministic truncation function `x ↦ x · 1_{|x| ≤ A}` is measurable. -/
theorem measurable_truncationFun (A : ℝ) : Measurable (truncationFun A) := by
  unfold truncationFun
  exact measurable_id.mul (Measurable.indicator measurable_one
    (measurableSet_le measurable_norm measurable_const))

/-- The truncation of a measurable random variable is measurable. -/
theorem measurable_truncRV {X : ℕ → Ω → ℝ} (n : ℕ) (hX : Measurable (X n)) (A : ℝ) :
    Measurable (truncRV X A n) := by
  rw [truncRV_eq_comp]
  exact (measurable_truncationFun A).comp hX

/-- If `(Xₙ)` is an independent family then so is its truncation
`(truncRV X A n)`, since truncation is a measurable function applied
componentwise. -/
theorem iIndepFun_truncRV {X : ℕ → Ω → ℝ} (hX : iIndepFun X μ) (A : ℝ) :
    iIndepFun (fun n => truncRV X A n) μ := by
  have heq : (fun n => truncRV X A n) = fun n => truncationFun A ∘ X n :=
    funext fun n => truncRV_eq_comp X A n
  rw [heq]
  exact hX.comp _ (fun _ => measurable_truncationFun A)


set_option linter.unusedSectionVars false in
/-- Truncation of a value already inside the band is the value itself. -/
theorem truncRV_eq_self_of_abs_le {X : ℕ → Ω → ℝ} {A : ℝ} {n : ℕ} {ω : Ω}
    (h : |X n ω| ≤ A) : truncRV X A n ω = X n ω := by
  unfold truncRV
  rw [Set.indicator_of_mem (by simpa using h), Pi.one_apply, mul_one]

set_option linter.unusedSectionVars false in
/-- Truncation of a value outside the band is `0`. -/
theorem truncRV_eq_zero_of_abs_gt {X : ℕ → Ω → ℝ} {A : ℝ} {n : ℕ} {ω : Ω}
    (h : A < |X n ω|) : truncRV X A n ω = 0 := by
  unfold truncRV
  rw [Set.indicator_of_notMem (by simpa using not_le.mpr h)]
  exact mul_zero _

set_option linter.unusedSectionVars false in
/-- The truncated random variable is bounded by `|A|` in absolute value,
with no sign hypothesis on `A`. -/
theorem abs_truncRV_le_abs {X : ℕ → Ω → ℝ} {A : ℝ} (n : ℕ) (ω : Ω) :
    |truncRV X A n ω| ≤ |A| := by
  by_cases h : |X n ω| ≤ A
  · rw [truncRV_eq_self_of_abs_le h]
    exact h.trans (le_abs_self A)
  · rw [truncRV_eq_zero_of_abs_gt (not_le.mp h), abs_zero]
    exact abs_nonneg A

set_option linter.unusedSectionVars false in
/-- The truncated random variable is bounded by `A` in absolute value. -/
theorem abs_truncRV_le {X : ℕ → Ω → ℝ} {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (ω : Ω) :
    |truncRV X A n ω| ≤ A := by
  have h := abs_truncRV_le_abs (X := X) (A := A) n ω
  rwa [abs_of_nonneg hA] at h

set_option linter.unusedSectionVars false in
/-- Truncation preserves nonnegativity pointwise. -/
theorem truncRV_nonneg_of_nonneg {X : ℕ → Ω → ℝ} {A : ℝ} {n : ℕ} {ω : Ω}
    (h : 0 ≤ X n ω) : 0 ≤ truncRV X A n ω := by
  rw [truncRV_eq_comp]
  exact truncationFun_nonneg_of_nonneg h

set_option linter.unusedSectionVars false in
/-- If `|Yₙ| ≤ A` everywhere, then truncation at level `A` is the identity,
i.e. `Yₙ · 1_{|Yₙ| ≤ A} = Yₙ`. -/
theorem truncRV_eq_of_bdd
    {Y : ℕ → Ω → ℝ} {A : ℝ} (hY : ∀ n ω, |Y n ω| ≤ A) (n : ℕ) :
    truncRV Y A n = Y n := by
  funext ω
  exact truncRV_eq_self_of_abs_le (hY n ω)

/-- If `(Yₙ)` is uniformly bounded by `A` and its partial sums converge a.s.,
then so do the partial sums of the truncations `truncRV Y A n`
(in fact to the same limit). -/
theorem ae_tendsto_truncRV_of_bdd
    {Y : ℕ → Ω → ℝ} {A : ℝ} (hY : ∀ n ω, |Y n ω| ≤ A)
    (hY_tend : ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => Y i ω)) atTop (nhds (S ω))) :
    ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => truncRV Y A i ω)) atTop (nhds (S ω)) := by
  obtain ⟨S, hS⟩ := hY_tend
  refine ⟨S, hS.mono fun ω hω => ?_⟩
  have heq : (fun n => (Finset.range n).sum (fun i => truncRV Y A i ω)) =
      (fun n => (Finset.range n).sum (fun i => Y i ω)) := by
    ext n
    exact Finset.sum_congr rfl (fun i _ => congr_fun (truncRV_eq_of_bdd hY i) ω)
  rw [heq]
  exact hω

/-- A truncation is in `Lᵖ` for every `p`, since it is measurable and
bounded by `|A|`. -/
theorem memLp_truncRV [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (A : ℝ) (n : ℕ) (p : ℝ≥0∞) :
    MemLp (truncRV X A n) p μ :=
  MemLp.of_bound ((measurable_truncRV n (hX n) A).aestronglyMeasurable) |A|
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_truncRV_le_abs n ω)

/-- A truncation is integrable. -/
theorem integrable_truncRV [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (A : ℝ) (n : ℕ) :
    Integrable (truncRV X A n) μ :=
  (memLp_truncRV hX A n 1).integrable le_rfl

/-- The variance of a truncation is at most `A²`. This is Popoviciu's
inequality for the range `[-|A|, |A|]` containing the truncation. -/
theorem variance_truncRV_le [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (A : ℝ) (n : ℕ) :
    variance (truncRV X A n) μ ≤ A ^ 2 := by
  have hmem : ∀ᵐ ω ∂μ, truncRV X A n ω ∈ Set.Icc (-|A|) |A| := by
    filter_upwards with ω
    exact abs_le.mp (abs_truncRV_le_abs n ω)
  have hbound := variance_le_sq_of_bounded (a := -|A|) (b := |A|) hmem
    ((measurable_truncRV n (hX n) A).aemeasurable)
  calc variance (truncRV X A n) μ ≤ ((|A| - -|A|) / 2) ^ 2 := hbound
    _ = A ^ 2 := by
        rw [sub_neg_eq_add, ← two_mul, mul_div_cancel_left₀ _ (two_ne_zero), sq_abs]

/-- The absolute value of the mean of a truncation is at most `|A|`. -/
theorem abs_integral_truncRV_le [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (A : ℝ) (n : ℕ) :
    |∫ ω, truncRV X A n ω ∂μ| ≤ |A| := by
  calc |∫ ω, truncRV X A n ω ∂μ| ≤ ∫ ω, |truncRV X A n ω| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _, |A| ∂μ :=
        integral_mono_ae (integrable_truncRV hX A n).abs (integrable_const _)
          (Filter.Eventually.of_forall fun ω => abs_truncRV_le_abs n ω)
    _ = |A| := by simp

end MathlibExt.Probability.Truncation

end
