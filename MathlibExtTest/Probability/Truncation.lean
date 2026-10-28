/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Truncation

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
open MathlibExt.Probability.Truncation

namespace MathlibExtTest.Probability.Truncation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Truncation at level `2` fixes `1`. -/
theorem truncationFun_two_one : truncationFun 2 1 = 1 :=
  truncationFun_eq_self_of_abs_le (by norm_num)

/-- Truncation at level `2` fixes `-1`. -/
theorem truncationFun_two_neg_one : truncationFun 2 (-1) = -1 :=
  truncationFun_eq_self_of_abs_le (by norm_num)

/-- Truncation at level `2` kills `3`. -/
theorem truncationFun_two_three : truncationFun 2 3 = 0 :=
  truncationFun_eq_zero_of_abs_gt (by norm_num)

/-- Truncation at level `2` kills `-3`. -/
theorem truncationFun_two_neg_three : truncationFun 2 (-3) = 0 :=
  truncationFun_eq_zero_of_abs_gt (by norm_num)

/-- Signature restatement: the deterministic truncation function is measurable. -/
theorem measurable_truncationFun_test (A : ℝ) : Measurable (truncationFun A) :=
  measurable_truncationFun A

/-- Signature restatement: the truncation of a measurable random variable
is measurable. -/
theorem measurable_truncRV_test {X : ℕ → Ω → ℝ} (n : ℕ) (hX : Measurable (X n)) (A : ℝ) :
    Measurable (truncRV X A n) :=
  measurable_truncRV n hX A

/-- Signature restatement: truncation preserves independence. -/
theorem iIndepFun_truncRV_test {X : ℕ → Ω → ℝ} (hX : iIndepFun X μ) (A : ℝ) :
    iIndepFun (fun n => truncRV X A n) μ :=
  iIndepFun_truncRV hX A

/-- Signature restatement: a truncation is bounded by `A` in absolute value. -/
theorem abs_truncRV_le_test {X : ℕ → Ω → ℝ} {A : ℝ} (hA : 0 ≤ A) (n : ℕ) (ω : Ω) :
    |truncRV X A n ω| ≤ A :=
  abs_truncRV_le hA n ω

/-- Signature restatement: truncation is the identity on a uniformly
bounded family. -/
theorem truncRV_eq_of_bdd_test
    {Y : ℕ → Ω → ℝ} {A : ℝ} (hY : ∀ n ω, |Y n ω| ≤ A) (n : ℕ) :
    truncRV Y A n = Y n :=
  truncRV_eq_of_bdd hY n

/-- A uniformly bounded family whose partial sums converge a.s. keeps that
property after truncation. -/
theorem ae_tendsto_truncRV_of_bdd_test
    {Y : ℕ → Ω → ℝ} {A : ℝ} (hY : ∀ n ω, |Y n ω| ≤ A)
    (hY_tend : ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => Y i ω)) atTop (nhds (S ω))) :
    ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => truncRV Y A i ω)) atTop (nhds (S ω)) :=
  ae_tendsto_truncRV_of_bdd hY hY_tend

/-- The zero family satisfies the bounded-convergence hypothesis, and its
truncation is itself. -/
theorem ae_tendsto_truncRV_zero :
    ∃ S : Ω → ℝ, ∀ᵐ ω ∂μ, Tendsto (fun n =>
      (Finset.range n).sum (fun i => truncRV (fun _ _ => (0 : ℝ)) 1 i ω)) atTop
        (nhds (S ω)) := by
  refine ⟨0, Filter.Eventually.of_forall fun ω => ?_⟩
  have h : (fun n => (Finset.range n).sum (fun i => truncRV (fun _ _ => (0 : ℝ)) 1 i ω))
      = fun _ => (0 : ℝ) := by
    funext n
    simp [truncRV]
  rw [h]
  exact tendsto_const_nhds

/-- Signature restatement: a truncation is in `Lᵖ` for every `p`. -/
theorem memLp_truncRV_test [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (A : ℝ) (n : ℕ) (p : ℝ≥0∞) :
    MemLp (truncRV X A n) p μ :=
  memLp_truncRV hX A n p

/-- Signature restatement: a truncation is integrable. -/
theorem integrable_truncRV_test [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (A : ℝ) (n : ℕ) :
    Integrable (truncRV X A n) μ :=
  integrable_truncRV hX A n

/-- Signature restatement: the variance of a truncation is at most `A²`. -/
theorem variance_truncRV_le_test [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (A : ℝ) (n : ℕ) :
    variance (truncRV X A n) μ ≤ A ^ 2 :=
  variance_truncRV_le hX A n

/-- Signature restatement: the mean of a truncation is at most `|A|` in
absolute value. -/
theorem abs_integral_truncRV_le_test [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n)) (A : ℝ) (n : ℕ) :
    |∫ ω, truncRV X A n ω ∂μ| ≤ |A| :=
  abs_integral_truncRV_le hX A n

#print axioms variance_truncRV_le_test

end MathlibExtTest.Probability.Truncation
