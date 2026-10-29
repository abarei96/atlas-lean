/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Diagonal terms in Wald's second equation

When expanding the square of a stopped partial sum `S_T = ∑_{i<T} X_i`,
Wald's second equation splits into a diagonal part and a cross part:

`(∑_{i<T} X_i)² = ∑_{i<T} X_i² + 2 ∑_{i<T} ∑_{j<i} X_j · X_i`.

This file ports the diagonal part from v1:
`E[∑_{i<T} X_i²] = E[X_0²] · E[T]`, together with the integrability of the
stopped sum of squares.

## Source

This formalizes `wald_diagonal_terms` and `integrable_stopped_sum_sq_diag`
from `v1/Atlas/TheoryOfProbability/code/WaldSecondEquation.lean`.
The cross part is batch 67 (`WaldCrossTerms.lean`); batch 14 proved
`wald_second_equation` itself by a different route and ported neither
statement here, and neither statement appears in any earlier batch's
committed file, in base `MathlibExt`, or in Mathlib.

## Proof strategy and hypothesis changes

In v1 both statements are proved by applying Wald's equation to the
squared sequence `Y_i = X_i²`, i.e. they rest on batch 5's `wald_equation`,
which is not in the base. The proofs here are direct and do not use
Wald's equation at all: the stopped sum is a sum of nonnegative terms,
so Tonelli's theorem gives
`E[∑_{i<T} Y_i] = ∑_i E[Y_i · 1_{T>i}]`, each factor splits as
`E[Y_i · 1_{T>i}] = E[Y_i] · P(T > i)` because `Y_i` is independent of
the filtration at time `i` while `{T > i}` lies in it, identical
distribution gives `E[Y_i] = E[Y_0]`, and `∑_i P(T > i) = E[T]`.

As a consequence the two hypotheses v1 needed only for its detour
through Wald's equation are dropped: the proof uses neither
independence of the `X_i` across different indices (`iIndepFun`,
used in v1 only for the Wald application) nor integrability of
`X_0` itself (v1's diagonal-terms theorem marks it `_hX_int`, unused).
The hypotheses kept are the ones the direct proof uses:
identical distribution, square-integrability, the stopping time,
`X_k` independent of the filtration at time `k`, and integrability
of `T`.

Two elementary helpers duplicate, under distinct names, private
lemmas of batch 5's unmerged `WaldEquation.lean` (to be unified on
rebase): `integral_natCast_eq_tsum_measure_gt` (batch 5's private
`integral_nat_eq_tsum_prob`) and the factorisation in
`integral_mul_indicator_sq_eq` (batch 5's private `indep_factor`,
in the squared case needed here).

## Main results

* `MathlibExt.Probability.WaldDiagonalTerms.integrable_stopped_sum_sq_diag`:
  the stopped sum of squares `∑_{i<T} X_i²` is integrable.
* `MathlibExt.Probability.WaldDiagonalTerms.wald_diagonal_terms`:
  `E[∑_{i<T} X_i²] = E[X_0²] · E[T]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset ENNReal

namespace MathlibExt.Probability.WaldDiagonalTerms

/-- The event `{T > i}` is measurable, for a stopping time `T`. -/
private theorem measurableSet_lt_stopping_time
    {Ω : Type*} {m : MeasurableSpace Ω}
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ))) (i : ℕ) :
    MeasurableSet {ω | i < T ω} := by
  have hset : {ω | i < T ω} = {ω | (i : WithTop ℕ) < (T ω : WithTop ℕ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Nat.cast_lt]
  rw [hset]
  exact f.le i _ (hT.measurableSet_gt i)

/-- The event `{T ≤ k}` is measurable, for a stopping time `T`. -/
private theorem measurableSet_le_stopping_time
    {Ω : Type*} {m : MeasurableSpace Ω}
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ))) (k : ℕ) :
    MeasurableSet {ω | T ω ≤ k} := by
  have hset : {ω | T ω ≤ k} = {ω | (T ω : WithTop ℕ) ≤ (k : WithTop ℕ)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Nat.cast_le]
  rw [hset]
  exact f.le k _ (hT.measurableSet_le k)

/-- A stopping time `T : Ω → ℕ` is measurable: `{T = i}` is
`{T ≤ i} ∖ {T ≤ i - 1}`. -/
private theorem measurable_of_isStoppingTime_nat
    {Ω : Type*} {m : MeasurableSpace Ω}
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ))) : Measurable T := by
  intro s _
  have hEq : T ⁻¹' s = ⋃ i ∈ s, {ω | T ω = i} := by
    ext ω
    simp [Set.mem_preimage, Set.mem_iUnion]
  rw [hEq]
  apply MeasurableSet.biUnion (Set.to_countable s)
  intro i _
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have h0 : {ω | T ω = 0} = {ω | T ω ≤ 0} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      omega
    rw [h0]
    exact measurableSet_le_stopping_time hT 0
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi)
    have hEq' : {ω | T ω = k + 1} = {ω | T ω ≤ k + 1} \ {ω | T ω ≤ k} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
      omega
    rw [hEq']
    exact (measurableSet_le_stopping_time hT (k + 1)).diff
      (measurableSet_le_stopping_time hT k)

/-- The `ℝ≥0∞` layer-cake identity `∫⁻ (T : ℝ≥0∞) = ∑_i μ{T > i}`. -/
private theorem tsum_measure_gt_eq_lintegral_coe_nat
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {T : Ω → ℕ}
    (hT_meas : ∀ i, MeasurableSet {ω | i < T ω}) :
    ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ = ∑' i, μ {ω | i < T ω} := by
  have hpt : ∀ ω, (T ω : ℝ≥0∞) =
      ∑' i, (Set.indicator {ω | i < T ω} (1 : Ω → ℝ≥0∞)) ω := by
    intro ω
    have hsum : ∀ n : ℕ, (∑' i, (if i < n then (1 : ℝ≥0∞) else 0)) = n := by
      intro n
      rw [tsum_eq_sum (s := Finset.range n)
        (f := fun i => if i < n then (1 : ℝ≥0∞) else 0)
        (by
          intro i hi
          simp only [Finset.mem_range, not_lt] at hi
          simp [hi])]
      trans (∑ i ∈ Finset.range n, (1 : ℝ≥0∞))
      · apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mem_range.mp hi, ite_true]
      · simp
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    exact (hsum (T ω)).symm
  calc ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ
      = ∫⁻ ω, ∑' i, (Set.indicator {ω | i < T ω} (1 : Ω → ℝ≥0∞)) ω ∂μ := by
        simp_rw [hpt]
    _ = ∑' i, ∫⁻ ω, (Set.indicator {ω | i < T ω} (1 : Ω → ℝ≥0∞)) ω ∂μ :=
        lintegral_tsum (fun i =>
          (measurable_const.indicator (hT_meas i)).aemeasurable)
    _ = ∑' i, μ {ω | i < T ω} := by
        simp_rw [lintegral_indicator_one (hT_meas _)]

/-- The layer-cake identity `E[T] = ∑_i P(T > i)` for a nonnegative
integer-valued random variable. No finite-expectation hypothesis is
needed: both sides are `0` when `T` is not integrable. -/
private theorem integral_natCast_eq_tsum_measure_gt
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ))) :
    ∫ ω, (T ω : ℝ) ∂μ = ∑' i, (μ {ω | i < T ω}).toReal := by
  have hT_meas : ∀ i, MeasurableSet {ω | i < T ω} :=
    fun i => measurableSet_lt_stopping_time hT i
  have hENN : ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ = ∑' i, μ {ω | i < T ω} :=
    tsum_measure_gt_eq_lintegral_coe_nat hT_meas
  have hInt : ∫ ω, (T ω : ℝ) ∂μ =
      (∫⁻ ω, (T ω : ℝ≥0∞) ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => Nat.cast_nonneg _)
      (Measurable.comp (continuous_of_discreteTopology.measurable)
        (measurable_of_isStoppingTime_nat hT)).aestronglyMeasurable]
    simp only [ENNReal.ofReal_natCast]
  rw [hInt, hENN, ENNReal.tsum_toReal_eq (fun i => measure_ne_top μ _)]

/-- The squared sequence is integrable at every index, by identical
distribution with the square-integrable zeroth term. -/
private theorem integrable_sq_of_identDistrib
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ) (i : ℕ) :
    Integrable (fun ω => (X i ω) ^ 2) μ := by
  have hY : IdentDistrib (fun ω => (X 0 ω) ^ 2) (fun ω => (X i ω) ^ 2) μ μ :=
    (hX_iid 0 i).comp (measurable_id.pow_const 2)
  refine ⟨hY.aestronglyMeasurable_snd hX_sq_int.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hEq : (∫⁻ ω, ‖(X i ω) ^ 2‖ₑ ∂μ) = ∫⁻ ω, ‖(X 0 ω) ^ 2‖ₑ ∂μ := by
    have hcomp : IdentDistrib (fun ω => ‖(X 0 ω) ^ 2‖ₑ) (fun ω => ‖(X i ω) ^ 2‖ₑ) μ μ :=
      hY.comp measurable_enorm
    exact hcomp.lintegral_eq.symm
  rw [hEq]
  exact hX_sq_int.hasFiniteIntegral

/-- One diagonal summand is integrable. -/
private theorem integrable_ite_sq
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (i : ℕ) :
    Integrable (fun ω => if i < T ω then (X i ω) ^ 2 else 0) μ := by
  have hY_int : Integrable (fun ω => (X i ω) ^ 2) μ :=
    integrable_sq_of_identDistrib hX_iid hX_sq_int i
  have hmeas : MeasurableSet {ω | i < T ω} := measurableSet_lt_stopping_time hT i
  have hEq : (fun ω => if i < T ω then (X i ω) ^ 2 else 0) =
      Set.indicator {ω | i < T ω} (fun ω => (X i ω) ^ 2) := by
    funext ω
    by_cases h : i < T ω <;> simp [h]
  rw [hEq]
  exact hY_int.indicator hmeas

/-- One diagonal summand is a.e. strongly measurable. -/
private theorem aesm_ite_sq
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (i : ℕ) :
    AEStronglyMeasurable (fun ω => if i < T ω then (X i ω) ^ 2 else 0) μ :=
  (integrable_ite_sq hX_iid hX_sq_int hT i).aestronglyMeasurable

/-- Factorisation of one diagonal summand: the square `X_i²` is
independent of the event `{T > i}` (it is independent of the
filtration at time `i`, which contains the event), so its expectation
splits. -/
private theorem integral_mul_indicator_sq_eq
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (i : ℕ) :
    ∫ ω, (if i < T ω then (X i ω) ^ 2 else 0) ∂μ =
      (∫ ω, (X 0 ω) ^ 2 ∂μ) * (μ {ω | i < T ω}).toReal := by
  have hmeas : MeasurableSet {ω | i < T ω} := measurableSet_lt_stopping_time hT i
  have hY_int : Integrable (fun ω => (X i ω) ^ 2) μ :=
    integrable_sq_of_identDistrib hX_iid hX_sq_int i
  have hEq : (fun ω => if i < T ω then (X i ω) ^ 2 else 0) =
      (fun ω => (X i ω) ^ 2 * Set.indicator {ω | i < T ω} (1 : Ω → ℝ) ω) := by
    funext ω
    by_cases h : i < T ω <;> simp [h]
  rw [hEq]
  have hcomapY : MeasurableSpace.comap (fun ω => (X i ω) ^ 2) inferInstance ≤
      MeasurableSpace.comap (X i) inferInstance :=
    MeasurableSpace.comap_le_comap_of_eq_comp (fun x : ℝ => x ^ 2)
      (measurable_id.pow_const 2) rfl
  have hmeas_f : MeasurableSet[f i] {ω | i < T ω} := by
    have hset : {ω | i < T ω} = {ω | (i : WithTop ℕ) < (T ω : WithTop ℕ)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Nat.cast_lt]
    rw [hset]
    exact hT.measurableSet_gt i
  have hcomapInd : MeasurableSpace.comap
        (Set.indicator {ω | i < T ω} (1 : Ω → ℝ)) inferInstance ≤ f i :=
    measurable_iff_comap_le.mp (measurable_const.indicator hmeas_f)
  have hIndep : IndepFun (fun ω => (X i ω) ^ 2)
      (Set.indicator {ω | i < T ω} (1 : Ω → ℝ)) μ :=
    indep_of_indep_of_le (hXf i) hcomapY hcomapInd
  have hfactor := hIndep.integral_mul_eq_mul_integral
    hY_int.aestronglyMeasurable
    (measurable_const.indicator hmeas).aestronglyMeasurable
  calc ∫ ω, (X i ω) ^ 2 * Set.indicator {ω | i < T ω} (1 : Ω → ℝ) ω ∂μ
      = (∫ ω, (X i ω) ^ 2 ∂μ) * (∫ ω, Set.indicator {ω | i < T ω} (1 : Ω → ℝ) ω ∂μ) :=
        hfactor
    _ = (∫ ω, (X i ω) ^ 2 ∂μ) * (μ {ω | i < T ω}).toReal := by
        simp only [integral_indicator_one hmeas, Measure.real]
    _ = (∫ ω, (X 0 ω) ^ 2 ∂μ) * (μ {ω | i < T ω}).toReal := by
        congr 1
        exact ((hX_iid i 0).comp (measurable_id.pow_const 2)).integral_eq

/-- The `ℝ≥0∞` integrals of the norms of the diagonal summands are
summable (in the `∑' ≠ ⊤` sense): each is
`ENNReal.ofReal ((∫ X_0²) · P(T > i))`, and `∑_i P(T > i) = E[T] < ∞`. -/
private theorem tsum_lintegral_enorm_ite_sq_ne_top
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
    (∑' i, ∫⁻ ω, ‖(if i < T ω then (X i ω) ^ 2 else 0)‖ₑ ∂μ) ≠ ⊤ := by
  have hcoe : ∀ i, (∫⁻ ω, ‖(if i < T ω then (X i ω) ^ 2 else 0)‖ₑ ∂μ) =
      ENNReal.ofReal (∫ ω, ‖(if i < T ω then (X i ω) ^ 2 else 0)‖ ∂μ) := by
    intro i
    exact (ofReal_integral_norm_eq_lintegral_enorm
      (integrable_ite_sq hX_iid hX_sq_int hT i)).symm
  simp_rw [hcoe]
  have hnorm : ∀ i, (∫ ω, ‖(if i < T ω then (X i ω) ^ 2 else 0)‖ ∂μ) =
      (∫ ω, (X 0 ω) ^ 2 ∂μ) * (μ {ω | i < T ω}).toReal := by
    intro i
    have hnn : ∀ ω, ‖(if i < T ω then (X i ω) ^ 2 else 0)‖ =
        (if i < T ω then (X i ω) ^ 2 else 0) := by
      intro ω
      split_ifs with h
      · rw [Real.norm_of_nonneg (sq_nonneg _)]
      · simp
    simp_rw [hnn]
    exact integral_mul_indicator_sq_eq hX_iid hX_sq_int hT hXf i
  simp_rw [hnorm]
  have hsum : Summable (fun i => (μ {ω | i < T ω}).toReal) := by
    have hENN : (∑' i, μ {ω | i < T ω}) ≠ ⊤ := by
      have hEq : ∫⁻ ω, (T ω : ℝ≥0∞) ∂μ = ∑' i, μ {ω | i < T ω} :=
        tsum_measure_gt_eq_lintegral_coe_nat (fun i => measurableSet_lt_stopping_time hT i)
      rw [← hEq]
      have hfi : HasFiniteIntegral (fun ω => (T ω : ℝ)) μ := hT_int.hasFiniteIntegral
      rw [hasFiniteIntegral_iff_enorm] at hfi
      have hEq2 : (fun ω => ‖(T ω : ℝ)‖ₑ) = (fun ω => (T ω : ℝ≥0∞)) := by
        funext ω
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
      rw [hEq2] at hfi
      exact hfi.ne
    exact ENNReal.summable_toReal hENN
  have hSumm : Summable (fun i => (∫ ω, (X 0 ω) ^ 2 ∂μ) * (μ {ω | i < T ω}).toReal) :=
    hsum.mul_left _
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg
    (integral_nonneg fun ω => sq_nonneg _) ENNReal.toReal_nonneg) hSumm]
  exact ENNReal.ofReal_ne_top

/-- Pointwise, the infinite sum of the diagonal summands is the finite
stopped sum: all terms past `T ω` vanish. -/
private theorem tsum_ite_sq_eq_sum_range
    {Ω : Type*} {X : ℕ → Ω → ℝ} {T : Ω → ℕ} (ω : Ω) :
    (∑' i, (if i < T ω then (X i ω) ^ 2 else 0)) =
      ∑ i ∈ Finset.range (T ω), (X i ω) ^ 2 := by
  rw [tsum_eq_sum (s := Finset.range (T ω))
    (f := fun i => if i < T ω then (X i ω) ^ 2 else 0)
    (by
      intro i hi
      simp only [Finset.mem_range, not_lt] at hi
      simp [hi])]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  simp [hi]

/-- **Diagonal part of Wald's second equation: integrability.**
For identically distributed `X_i` with `E[X_0²] < ∞` and a stopping
time `T` with `E[T] < ∞`, the stopped sum of squares
`∑_{i<T} X_i²` is integrable. -/
theorem integrable_stopped_sum_sq_diag
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
    Integrable (fun ω => ∑ i ∈ Finset.range (T ω), (X i ω) ^ 2) μ := by
  have hae := fun i => aesm_ite_sq hX_iid hX_sq_int hT i
  have hne := tsum_lintegral_enorm_ite_sq_ne_top hX_iid hX_sq_int hT hXf hT_int
  have hAESM : AEStronglyMeasurable
      (fun ω => ∑' i, (if i < T ω then (X i ω) ^ 2 else 0)) μ := by
    apply aestronglyMeasurable_of_tendsto_ae (u := atTop)
      (f := fun N ω => ∑ i ∈ Finset.range N, (if i < T ω then (X i ω) ^ 2 else 0))
    · intro N
      induction N with
      | zero => simpa using aestronglyMeasurable_const
      | succ N ih =>
        have hsum : (fun ω => ∑ i ∈ Finset.range (N + 1),
              (if i < T ω then (X i ω) ^ 2 else 0)) =
            (fun ω => ∑ i ∈ Finset.range N,
              (if i < T ω then (X i ω) ^ 2 else 0)) +
            (fun ω => if N < T ω then (X N ω) ^ 2 else 0) := by
          funext ω
          simp only [Finset.sum_range_succ, Pi.add_apply]
        rw [hsum]
        exact ih.add (hae N)
    · filter_upwards with ω
      apply tendsto_atTop_of_eventually_const (i₀ := T ω)
      intro N hN
      have hEq : (∑ i ∈ Finset.range N, (if i < T ω then (X i ω) ^ 2 else 0)) =
          ∑ i ∈ Finset.range (T ω), (X i ω) ^ 2 := by
        have h1 : (∑ i ∈ Finset.range (T ω), (X i ω) ^ 2) =
            ∑ i ∈ Finset.range (T ω), (if i < T ω then (X i ω) ^ 2 else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [Finset.mem_range.mp hi, ite_true]
        rw [h1]
        symm
        apply Finset.sum_subset (Finset.range_mono hN)
        intro i _ hi
        simp only [Finset.mem_range, not_lt] at hi
        simp [hi]
      rw [hEq]
      exact (tsum_ite_sq_eq_sum_range ω).symm
  have hHFI : HasFiniteIntegral
      (fun ω => ∑' i, (if i < T ω then (X i ω) ^ 2 else 0)) μ := by
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ ω, ‖(∑' i, (if i < T ω then (X i ω) ^ 2 else 0))‖ₑ ∂μ
        ≤ ∫⁻ ω, ∑' i, ‖(if i < T ω then (X i ω) ^ 2 else 0)‖ₑ ∂μ := by
          apply lintegral_mono_ae
          exact ae_of_all _ fun ω => enorm_tsum_le_tsum_enorm
      _ = ∑' i, ∫⁻ ω, ‖(if i < T ω then (X i ω) ^ 2 else 0)‖ₑ ∂μ :=
          lintegral_tsum (fun i => (hae i).enorm)
      _ < ⊤ := lt_top_iff_ne_top.mpr hne
  have hInt : Integrable (fun ω => ∑' i, (if i < T ω then (X i ω) ^ 2 else 0)) μ :=
    ⟨hAESM, hHFI⟩
  have hEq : (fun ω => ∑' i, (if i < T ω then (X i ω) ^ 2 else 0)) =ᵐ[μ]
      (fun ω => ∑ i ∈ Finset.range (T ω), (X i ω) ^ 2) :=
    ae_of_all _ fun ω => tsum_ite_sq_eq_sum_range ω
  exact hInt.congr hEq

/-- **Diagonal part of Wald's second equation.**
For identically distributed `X_i` with `E[X_0²] < ∞` and a stopping
time `T` with `E[T] < ∞`, the expected stopped sum of squares is
`E[∑_{i<T} X_i²] = E[X_0²] · E[T]`. -/
theorem wald_diagonal_terms
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    {f : Filtration ℕ m} {T : Ω → ℕ}
    (hT : IsStoppingTime f (fun ω => (T ω : WithTop ℕ)))
    (hXf : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (f k) μ)
    (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
    ∫ ω, (∑ i ∈ Finset.range (T ω), (X i ω) ^ 2) ∂μ =
      (∫ ω, (X 0 ω) ^ 2 ∂μ) * (∫ ω, (T ω : ℝ) ∂μ) := by
  have hae := fun i => aesm_ite_sq hX_iid hX_sq_int hT i
  have hne := tsum_lintegral_enorm_ite_sq_ne_top hX_iid hX_sq_int hT hXf hT_int
  calc ∫ ω, (∑ i ∈ Finset.range (T ω), (X i ω) ^ 2) ∂μ
      = ∫ ω, (∑' i, (if i < T ω then (X i ω) ^ 2 else 0)) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ fun ω => (tsum_ite_sq_eq_sum_range ω).symm
    _ = ∑' i, ∫ ω, (if i < T ω then (X i ω) ^ 2 else 0) ∂μ :=
        integral_tsum hae hne
    _ = ∑' i, (∫ ω, (X 0 ω) ^ 2 ∂μ) * (μ {ω | i < T ω}).toReal := by
        apply tsum_congr
        intro i
        exact integral_mul_indicator_sq_eq hX_iid hX_sq_int hT hXf i
    _ = (∫ ω, (X 0 ω) ^ 2 ∂μ) * ∑' i, (μ {ω | i < T ω}).toReal := tsum_mul_left
    _ = (∫ ω, (X 0 ω) ^ 2 ∂μ) * (∫ ω, (T ω : ℝ) ∂μ) := by
        congr 1
        exact (integral_natCast_eq_tsum_measure_gt hT).symm

end MathlibExt.Probability.WaldDiagonalTerms
