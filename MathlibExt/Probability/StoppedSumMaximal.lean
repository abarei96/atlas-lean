/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Integrability of stopped partial sums and of their running maximum

Let `X₁, X₂, …` be i.i.d. real random variables with `E[X₁] = 0` and
`E[X₁²] < ∞`, and let `τ` be a stopping time with `E[τ] < ∞`. Writing
`Sₖ = X₁ + ⋯ + Xₖ`, the stopped partial sum `S_τ` is square-integrable, and
the running maximum `max_{0 ≤ k ≤ τ} Sₖ²` is integrable.

## Source

This formalizes `v1/Atlas/TheoryOfProbability/code/StoppedSumSqUI.lean`:
`integrable_maximal_stopped_partial_sum_sq`, whose proof in v1 was
left unproved. The predictable filtration `predictableFiltration` is ported
verbatim from `v1/Atlas/TheoryOfProbability/code/WaldSecondEquation.lean`.

The proof of the maximal statement goes through the general-filtration
theorem `integrable_stopped_partialSum_sq` below. Its proof applies the
truncated Doob `L²` maximal inequality to the stopped martingale (an
argument that also underlies batch 1's Doob `L²` maximal inequality, but
no statement is re-ported here), lets the truncation tend to infinity, and
then applies Fatou's lemma. The finite-horizon Wald identity
`E[S_{τ∧n}²] = E[X₀²] · E[τ∧n]` is proved from scratch by expanding the
square into diagonal and cross terms, as in batch 14's proof of Wald's
second equation, but neither Wald's second equation itself nor any other
earlier batch's statement is re-ported.

The general-filtration theorem drops v1's `iIndepFun` hypothesis as unused,
following batch 5's treatment of Wald's equation: only independence of
each `Xₖ` from the filtration at time `k` is used. The `iIndepFun`
hypothesis is retained in the v1-form corollary, where it is what yields
the needed independence and adaptedness for the predictable filtration.

## Main results

* `MathlibExt.Probability.StoppedSumMaximal.integrable_stopped_partialSum_sq`:
  for an i.i.d. mean-zero sequence with `E[X₀²] < ∞` and a stopping time
  `τ` with `E[τ] < ∞` (both with respect to a general filtration), the
  stopped partial sum `S_τ` is square-integrable.
* `MathlibExt.Probability.StoppedSumMaximal.integrable_maximal_stopped_partial_sum_sq`:
  v1's statement: `max_{0 ≤ k ≤ τ} Sₖ²` is integrable for a stopping time
  `τ` of the predictable filtration.
* `MathlibExt.Probability.StoppedSumMaximal.predictableFiltration`:
  the predictable filtration `ℱₖ = σ(X₀, …, X_{k-1})`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset ENNReal NNReal Topology Set

namespace MathlibExt.Probability.StoppedSumMaximal

noncomputable section

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Running maximum of `|f k ω|` over `0 ≤ k ≤ n`. -/
private noncomputable def maxAbs (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k => |f k ω|)

private theorem measurable_maxAbs {f : ℕ → Ω → ℝ} (hf : ∀ k, Measurable (f k)) (n : ℕ) :
    Measurable (maxAbs f n) := by
  unfold maxAbs
  apply Finset.measurable_range_sup''
  intro k _
  simpa only [Real.norm_eq_abs] using (hf k).norm

private theorem maxAbs_nonneg {f : ℕ → Ω → ℝ} (n : ℕ) (ω : Ω) : 0 ≤ maxAbs f n ω := by
  unfold maxAbs
  exact le_trans (abs_nonneg _)
    (Finset.le_sup' (fun k => |f k ω|) (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

/-- `|f|` is a submartingale when `f` is a martingale. -/
private theorem submartingale_abs_of_martingale {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
    (hmart : Martingale f ℱ μ) :
    Submartingale (fun k ω => |f k ω|) ℱ μ := by
  have hadp : StronglyAdapted ℱ (fun k ω => ‖f k ω‖) :=
    fun i => (hmart.stronglyAdapted i).norm
  have hadp' : StronglyAdapted ℱ (fun k ω => |f k ω|) := hadp
  apply submartingale_of_setIntegral_le_succ hadp' (fun i => (hmart.integrable i).abs)
  intro i s hs
  have h1I : Integrable (f (i + 1)) μ := hmart.integrable (i + 1)
  have h2I : Integrable (fun ω => ‖f (i + 1) ω‖) μ := (hmart.integrable (i + 1)).norm
  have hce : μ[f (i + 1) | ℱ i] =ᵐ[μ] f i := hmart.condExp_ae_eq (Nat.le_succ i)
  have hnorm : (fun ω => ‖f i ω‖) =ᵐ[μ] (fun ω => ‖μ[f (i + 1) | ℱ i] ω‖) := by
    filter_upwards [hce] with ω hω
    rw [hω]
  have h1 : ∫ ω in s, |f i ω| ∂μ = ∫ ω in s, ‖μ[f (i + 1) | ℱ i] ω‖ ∂μ := by
    apply setIntegral_congr_ae ((ℱ.le i) s hs)
    filter_upwards [hnorm] with ω hω _
    rw [Real.norm_eq_abs] at hω
    exact hω
  have h2 : ∫ ω in s, ‖μ[f (i + 1) | ℱ i] ω‖ ∂μ ≤
      ∫ ω in s, μ[fun ω => ‖f (i + 1) ω‖ | ℱ i] ω ∂μ := by
    apply setIntegral_mono_ae_restrict
    · exact (integrable_condExp (f := f (i + 1))).norm.integrableOn
    · exact (integrable_condExp (f := fun ω => ‖f (i + 1) ω‖)).integrableOn
    · filter_upwards [(norm_condExp_le (fun ω => f (i + 1) ω)).filter_mono
        MeasureTheory.ae_restrict_le] with ω hω
      exact hω
  have h3 : ∫ ω in s, μ[fun ω => ‖f (i + 1) ω‖ | ℱ i] ω ∂μ =
      ∫ ω in s, ‖f (i + 1) ω‖ ∂μ :=
    setIntegral_condExp (ℱ.le i) (hmart.integrable (i + 1)).norm hs
  calc ∫ ω in s, |f i ω| ∂μ = ∫ ω in s, ‖μ[f (i + 1) | ℱ i] ω‖ ∂μ := h1
    _ ≤ ∫ ω in s, μ[fun ω => ‖f (i + 1) ω‖ | ℱ i] ω ∂μ := h2
    _ = ∫ ω in s, ‖f (i + 1) ω‖ ∂μ := h3
    _ = ∫ ω in s, |f (i + 1) ω| ∂μ := by simp only [Real.norm_eq_abs]

private theorem lintegral_setIntegral_eq (M g : Ω → ℝ) (hM : Measurable M)
    (hg : Measurable g) (hg_int : Integrable g μ) (hg_nn : 0 ≤ g) {A : ℝ} :
    ∫⁻ t in Set.Ioc 0 A, ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, g ω ∂μ) ∂MeasureTheory.volume =
      ∫⁻ ω, ENNReal.ofReal (g ω * min (M ω) A) ∂μ := by
  have hS : MeasurableSet {p : ℝ × Ω | p.1 ≤ M p.2} :=
    measurableSet_le measurable_fst (hM.comp measurable_snd)
  have hF : AEMeasurable (fun p : ℝ × Ω => if p.1 ≤ M p.2 then ENNReal.ofReal (g p.2) else 0)
      ((MeasureTheory.volume.restrict (Set.Ioc 0 A)).prod μ) := by
    have hmeas : Measurable (Set.indicator {p : ℝ × Ω | p.1 ≤ M p.2}
        (fun p => ENNReal.ofReal (g p.2))) :=
      ((ENNReal.measurable_ofReal.comp hg).comp measurable_snd).indicator hS
    apply AEMeasurable.congr hmeas.aemeasurable
    exact Filter.Eventually.of_forall fun p => by
      by_cases h : p.1 ≤ M p.2 <;> simp [Set.indicator, h]
  have hstep : ∀ t : ℝ, ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, g ω ∂μ) =
      ∫⁻ ω, (if t ≤ M ω then ENNReal.ofReal (g ω) else 0) ∂μ := by
    intro t
    rw [ofReal_integral_eq_lintegral_ofReal]
    · rw [← lintegral_indicator (measurableSet_le measurable_const hM)]
      apply lintegral_congr
      intro ω
      by_cases h : t ≤ M ω <;> simp [Set.indicator, h]
    · exact hg_int.integrableOn
    · exact Eventually.of_forall fun ω => hg_nn ω
  rw [setLIntegral_congr_fun measurableSet_Ioc (fun t _ => hstep t)]
  rw [lintegral_lintegral_swap hF]
  apply lintegral_congr
  intro ω
  -- inner integral over t
  have hinner : ∫⁻ t in Set.Ioc 0 A, (if t ≤ M ω then ENNReal.ofReal (g ω) else 0)
      ∂MeasureTheory.volume = ENNReal.ofReal (g ω * min (M ω) A) := by
    have h1 : (fun t : ℝ => if t ≤ M ω then ENNReal.ofReal (g ω) else 0) =
        (Set.Iic (M ω)).indicator (fun _ => ENNReal.ofReal (g ω)) := by
      funext t
      by_cases h : t ≤ M ω <;> simp [Set.indicator, h]
    have hset : Set.Iic (M ω) ∩ Set.Ioc 0 A = Set.Ioc 0 (min (M ω) A) := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc, le_min_iff]
      tauto
    rw [h1, setLIntegral_indicator measurableSet_Iic, setLIntegral_const, hset,
      Real.volume_Ioc, sub_zero, min_comm, ENNReal.ofReal_mul (hg_nn ω)]
  rw [hinner]


/-- **Truncated Doob `L²` maximal inequality** (private engine). For a martingale `f`,
the truncated running maximum `min (max_{k≤n} |f_k|²) K` has expectation at most
`4 · E[(f_n)²]`. The proof uses Doob's maximal inequality
(`MeasureTheory.maximal_ineq`) for the submartingale `|f|`, the layer-cake formula,
Tonelli's theorem, and Cauchy–Schwarz. -/
private theorem lintegral_min_maxAbs_sq_le {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
    (hmart : Martingale f ℱ μ) (n : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    ∫⁻ ω, ENNReal.ofReal (min ((maxAbs f n ω) ^ 2) K) ∂μ ≤
      4 * ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ 2) ∂μ := by
  set M := maxAbs f n with hMdef
  set A := Real.sqrt K with hAdef
  set Y : Ω → ℝ := fun ω => min (M ω) A with hYdef
  have hMmeas : Measurable M := measurable_maxAbs (fun k => ((hmart.stronglyMeasurable k).measurable).mono (ℱ.le k) le_rfl) n
  have hYmeas : Measurable Y := hMmeas.min measurable_const
  have hYnn : 0 ≤ Y := fun ω => le_min (maxAbs_nonneg n ω) (Real.sqrt_nonneg K)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg K
  have hYsq : ∀ ω, (Y ω) ^ 2 = min ((M ω) ^ 2) K := by
    intro ω
    by_cases h : M ω ≤ A
    · show (min (M ω) A) ^ 2 = min ((M ω) ^ 2) K
      rw [min_eq_left h, min_eq_left]
      · exact (pow_le_pow_left₀ (maxAbs_nonneg n ω) h 2).trans_eq (Real.sq_sqrt hK)
    · show (min (M ω) A) ^ 2 = min ((M ω) ^ 2) K
      rw [min_eq_right (not_le.mp h).le, min_eq_right]
      · exact Real.sq_sqrt hK
      · calc K = A ^ 2 := (Real.sq_sqrt hK).symm
          _ ≤ (M ω) ^ 2 := pow_le_pow_left₀ hA0 (not_le.mp h).le 2
  -- layer cake for Y
  have hlayer : ∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂μ =
      ∫⁻ t in Set.Ioi 0, μ {a | t ≤ Y a} * ENNReal.ofReal (2 * t) := by
    have key := lintegral_comp_eq_lintegral_meas_le_mul μ (f_nn := Eventually.of_forall hYnn)
      (f_mble := hYmeas.aemeasurable) (g := fun t => 2 * t)
      (g_intble := fun t _ => (continuous_const.mul continuous_id).intervalIntegrable 0 t)
      (g_nn := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (by norm_num) ht.le)
    rw [← key]
    apply lintegral_congr
    intro ω
    congr 1
    rw [intervalIntegral.integral_const_mul, integral_id]
    simp
    ring
  -- restrict the layer-cake integral to `(0, A]`
  have hrestrict : ∫⁻ t in Set.Ioi 0, μ {a | t ≤ Y a} * ENNReal.ofReal (2 * t) =
      ∫⁻ t in Set.Ioc 0 A, μ {a | t ≤ Y a} * ENNReal.ofReal (2 * t) := by
    have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 A ∪ Set.Ioi A := (Set.Ioc_union_Ioi_eq_Ioi hA0).symm
    rw [hsplit, lintegral_union measurableSet_Ioi (Set.Ioc_disjoint_Ioi le_rfl)]
    have hzero : ∫⁻ t in Set.Ioi A, μ {a | t ≤ Y a} * ENNReal.ofReal (2 * t) = 0 := by
      have hz : ∀ t ∈ Set.Ioi A, μ {a | t ≤ Y a} * ENNReal.ofReal (2 * t) = 0 := by
        intro t ht
        have hset : {a : Ω | t ≤ Y a} = ∅ := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          intro hle
          have hleA : Y ω ≤ A := min_le_right _ _
          exact absurd (hle.trans hleA) (not_le.mpr ht)
        rw [hset, measure_empty, zero_mul]
      rw [setLIntegral_congr_fun measurableSet_Ioi hz]
      simp
    rw [hzero, add_zero]
  -- maximal inequality on `(0, A]`
  have hmax : ∫⁻ t in Set.Ioc 0 A, μ {a | t ≤ Y a} * ENNReal.ofReal (2 * t) ≤
      2 * ∫⁻ t in Set.Ioc 0 A, ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, |f n ω| ∂μ) := by
    rw [← lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    apply setLIntegral_mono' measurableSet_Ioc (fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    have htA : t ≤ A := ht.2
    have hset : {a : Ω | t ≤ Y a} = {a : Ω | t ≤ M a} := by
      ext ω
      simp only [Set.mem_ofPred_eq, hYdef]
      constructor
      · intro hle
        exact le_trans hle (min_le_left _ _)
      · intro hle
        exact le_min hle htA
    set ε : ℝ≥0 := ⟨t, ht0.le⟩ with hεdef
    have hεcoe : (ε : ℝ) = t := by rw [hεdef]; exact NNReal.coe_mk _ _
    have hmaxineq := maximal_ineq (μ := μ) (𝒢 := ℱ) (f := fun k ω => |f k ω|)
      (submartingale_abs_of_martingale hmart) (fun _ _ => abs_nonneg _)
      (ε := ε) n
    rw [hset]
    have hcoef : (ε : ℝ≥0∞) = ENNReal.ofReal t := by
      rw [← hεcoe, ENNReal.ofReal_coe_nnreal]
    have h2t : ENNReal.ofReal (2 * t) = 2 * ENNReal.ofReal t := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [h2t]
    have hMset : {ω : Ω | (ε : ℝ) ≤
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one (fun k => |f k ω|)} =
        {ω : Ω | t ≤ M ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq, hεcoe, hMdef, maxAbs]
    have hmaxineq' : ENNReal.ofReal t * μ {ω | t ≤ M ω} ≤
        ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, |f n ω| ∂μ) := by
      simpa only [hMset, hcoef] using hmaxineq
    calc μ {a : Ω | t ≤ M a} * (2 * ENNReal.ofReal t)
        = 2 * (ENNReal.ofReal t * μ {a : Ω | t ≤ M a}) := by ring
      _ ≤ 2 * ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, |f n ω| ∂μ) :=
          mul_le_mul_of_nonneg_left hmaxineq' (by norm_num : (0 : ℝ≥0∞) ≤ 2)
  -- swap the double integral
  have hfnmeas : Measurable (fun ω => |f n ω|) := by
    simpa only [Real.norm_eq_abs] using
      (((hmart.stronglyMeasurable n).measurable).mono (ℱ.le n) le_rfl).norm
  have hswap := lintegral_setIntegral_eq (M := M) (g := fun ω => |f n ω|) (A := A) hMmeas hfnmeas
    (hmart.integrable n).abs (fun ω => abs_nonneg _)
  have hmain : ∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂μ ≤
      2 * ∫⁻ ω, ENNReal.ofReal (|f n ω| * Y ω) ∂μ := by
    rw [hlayer, hrestrict]
    calc ∫⁻ t in Set.Ioc 0 A, μ {a | t ≤ Y a} * ENNReal.ofReal (2 * t)
        ≤ 2 * ∫⁻ t in Set.Ioc 0 A,
            ENNReal.ofReal (∫ ω in {ω | t ≤ M ω}, |f n ω| ∂μ) := hmax
      _ = 2 * ∫⁻ ω, ENNReal.ofReal (|f n ω| * Y ω) ∂μ := by rw [hswap]
  -- Cauchy–Schwarz (Hölder with `p = q = 2`)
  have hholder : ∫⁻ ω, ENNReal.ofReal (|f n ω| * Y ω) ∂μ ≤
      (∫⁻ ω, ENNReal.ofReal ((f n ω) ^ 2) ∂μ) ^ (1 / 2 : ℝ) *
        (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂μ) ^ (1 / 2 : ℝ) := by
    have hconj : (2 : ℝ).HolderConjugate 2 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj
      (f := fun ω => ENNReal.ofReal |f n ω|) (g := fun ω => ENNReal.ofReal (Y ω))
      (ENNReal.measurable_ofReal.comp hfnmeas).aemeasurable
      (ENNReal.measurable_ofReal.comp hYmeas).aemeasurable
    have hpow1 : ∀ ω, (ENNReal.ofReal |f n ω|) ^ (2 : ℝ) =
        ENNReal.ofReal ((f n ω) ^ 2) := by
      intro ω
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      rw [Real.rpow_two, sq_abs]
    have hpow2 : ∀ ω, (ENNReal.ofReal (Y ω)) ^ (2 : ℝ) =
        ENNReal.ofReal ((Y ω) ^ 2) := by
      intro ω
      rw [ENNReal.ofReal_rpow_of_nonneg (hYnn ω) (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      rw [Real.rpow_two]
    have hconv : ∫⁻ ω, (ENNReal.ofReal |f n ω| * ENNReal.ofReal (Y ω)) ∂μ =
        ∫⁻ ω, ENNReal.ofReal (|f n ω| * Y ω) ∂μ := by
      apply lintegral_congr
      intro ω
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
    simp only [Pi.mul_apply] at h1
    rw [hconv] at h1
    rw [show (∫⁻ ω, (ENNReal.ofReal |f n ω|) ^ (2 : ℝ) ∂μ) =
        ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ 2) ∂μ from lintegral_congr fun ω => hpow1 ω,
      show (∫⁻ ω, (ENNReal.ofReal (Y ω)) ^ (2 : ℝ) ∂μ) =
        ∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂μ from lintegral_congr fun ω => hpow2 ω] at h1
    -- the Hölder conclusion uses `(1 / 2 : ℝ)` exponents, matching the goal
    convert h1 using 2
  -- absorb the constants
  set AA : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂μ with hAAdef
  set BB : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ 2) ∂μ with hBBdef
  have hAA_top : AA ≠ ⊤ := by
    have hle : AA ≤ ENNReal.ofReal K := by
      have h := lintegral_mono (μ := μ) (f := fun ω => ENNReal.ofReal ((Y ω) ^ 2))
        (g := fun _ => ENNReal.ofReal K) (fun ω => by
          show ENNReal.ofReal ((Y ω) ^ 2) ≤ ENNReal.ofReal K
          rw [hYsq ω]
          exact ENNReal.ofReal_le_ofReal (min_le_right _ _))
      rwa [lintegral_const, measure_univ, mul_one] at h
    exact ne_of_lt (hle.trans_lt ENNReal.ofReal_lt_top)
  have hchain : AA ≤ 2 * (BB ^ (1 / 2 : ℝ) * AA ^ (1 / 2 : ℝ)) := by
    calc AA ≤ 2 * ∫⁻ ω, ENNReal.ofReal (|f n ω| * Y ω) ∂μ := hmain
      _ ≤ 2 * (BB ^ (1 / 2 : ℝ) * AA ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hholder (by norm_num : (0 : ℝ≥0∞) ≤ 2)
  have hgoal : ∫⁻ ω, ENNReal.ofReal (min ((maxAbs f n ω) ^ 2) K) ∂μ = AA := by
    apply lintegral_congr
    intro ω
    rw [← hYsq ω]
  rw [hgoal]
  by_cases hBB : BB = ⊤
  · rw [hBB, ENNReal.mul_top (by norm_num : (4 : ℝ≥0∞) ≠ 0)]
    exact le_top
  · by_cases hAA0 : AA = 0
    · rw [hAA0]
      exact bot_le
    · have hAAfin : AA < ⊤ := lt_top_iff_ne_top.mpr hAA_top
      have hBBfin : BB < ⊤ := lt_top_iff_ne_top.mpr hBB
      have hne : 2 * (BB ^ (1 / 2 : ℝ) * AA ^ (1 / 2 : ℝ)) ≠ ⊤ := by
        apply ENNReal.mul_ne_top (by norm_num)
        apply ENNReal.mul_ne_top
        · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBB
        · exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hAA_top
      have hreal : AA.toReal ≤ 2 * (BB.toReal ^ (1 / 2 : ℝ) * AA.toReal ^ (1 / 2 : ℝ)) := by
        have h := ENNReal.toReal_mono hne hchain
        simpa only [ENNReal.toReal_mul, ENNReal.toReal_rpow, ENNReal.toReal_ofNat]
          using h
      rw [← Real.sqrt_eq_rpow BB.toReal, ← Real.sqrt_eq_rpow AA.toReal] at hreal
      have ha_pos : 0 < AA.toReal := by
        refine lt_of_le_of_ne ENNReal.toReal_nonneg ?_
        intro h
        exact hAA0 (((ENNReal.toReal_eq_zero_iff AA).mp h.symm).resolve_right hAA_top)
      set s := Real.sqrt AA.toReal with hsdef
      set u := Real.sqrt BB.toReal with hudef
      have hs : s ^ 2 = AA.toReal := Real.sq_sqrt (ENNReal.toReal_nonneg)
      have hu : u ^ 2 = BB.toReal := Real.sq_sqrt (ENNReal.toReal_nonneg)
      have hspos : 0 < s := Real.sqrt_pos.mpr ha_pos
      have hle : s ≤ 2 * u := by
        have h1 : s * s ≤ s * (2 * u) := by
          calc s * s = AA.toReal := (pow_two s).symm.trans hs
            _ ≤ 2 * (u * s) := hreal
            _ = s * (2 * u) := by ring
        exact le_of_mul_le_mul_left h1 hspos
      have hfin : AA.toReal ≤ 4 * BB.toReal := by
        calc AA.toReal = s * s := hs.symm.trans (pow_two s)
          _ ≤ (2 * u) * (2 * u) :=
              mul_le_mul hle hle (Real.sqrt_nonneg _) (by positivity)
          _ = 4 * BB.toReal := by rw [← hu]; ring
      have hgoal : AA.toReal ≤ (4 * BB).toReal := by
        rw [ENNReal.toReal_mul]
        simpa only [ENNReal.toReal_ofNat] using hfin
      exact (ENNReal.toReal_le_toReal hAA_top
        (ENNReal.mul_ne_top (by norm_num) hBB)).mp hgoal


/-- A `ℕ`-valued stopping time is measurable. -/
private theorem measurable_of_isStoppingTime {ℱ : Filtration ℕ m0} {T : Ω → ℕ}
    (hT : IsStoppingTime ℱ (fun ω => (T ω : WithTop ℕ))) : Measurable T := by
  apply measurable_to_nat
  intro ω
  have hset : T ⁻¹' {T ω} = {ω' | (T ω' : WithTop ℕ) = (T ω : WithTop ℕ)} := by
    ext ω'
    simp [Nat.cast_inj]
  rw [hset]
  exact (ℱ.le (T ω)) _ (hT.measurableSet_eq (T ω))

/-- Algebraic expansion of a square of a finite sum. -/
private theorem sum_sq_eq (n : ℕ) (D : ℕ → ℝ) :
    (∑ k ∈ Finset.range n, D k) ^ 2 =
      ∑ k ∈ Finset.range n, (D k) ^ 2 + 2 * ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range k,
        D j * D k := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    have h1 : (∑ k ∈ Finset.range n, D k + D n) ^ 2 =
        (∑ k ∈ Finset.range n, D k) ^ 2 + 2 * (∑ k ∈ Finset.range n, D k) * D n + (D n) ^ 2 := by
      ring
    rw [h1, ih]
    have h2 : (2 * ∑ k ∈ Finset.range n, D k) * D n = 2 * ∑ j ∈ Finset.range n, D j * D n := by
      rw [mul_assoc, Finset.sum_mul]
    rw [h2]
    ring

/-- A natural number is the sum of its tail indicators. -/
private theorem natCast_eq_sum_indicator {τ : Ω → ℕ} :
    ∀ (n : ℕ) (ω : Ω), τ ω ≤ n →
      (τ ω : ℝ) = ∑ k ∈ Finset.range n, (if k < τ ω then (1 : ℝ) else 0) := by
  intro n
  induction n with
  | zero =>
    intro ω hle
    rw [Nat.eq_zero_of_le_zero hle]
    simp
  | succ n ih =>
    intro ω hle
    by_cases h : τ ω = n + 1
    · rw [h]
      rw [Finset.sum_congr rfl (fun k hk => ite_eq_left (Finset.mem_range.mp hk : k < n + 1))]
      simp [Finset.sum_const, Finset.card_range, Nat.cast_add]
    · have hle' : τ ω ≤ n := by omega
      have hih := ih ω hle'
      rw [Finset.sum_range_succ, hih, ite_eq_right (not_lt.mpr hle'), add_zero]


/-- The partial sums of a mean-zero sequence with `Xₖ` independent of `ℱₖ` form a
martingale. -/
private theorem martingale_partialSum {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_int : Integrable (X 0) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {ℱ : Filtration ℕ m0}
    (hIndep : ∀ k, Indep (ℱ k) (MeasurableSpace.comap (X k) inferInstance) μ)
    (hadapt : ∀ k, Measurable[ℱ (k + 1)] (X k)) :
    Martingale (fun n ω => ∑ i ∈ Finset.range n, X i ω) ℱ μ := by
  have hXi_int : ∀ i, Integrable (X i) μ := fun i => (hX_iid i 0).integrable_iff.mpr hX_int
  have hmean_i : ∀ i, ∫ ω, X i ω ∂μ = 0 := fun i => by
    rw [(hX_iid i 0).integral_eq]; exact hmean
  have hadp : StronglyAdapted ℱ (fun n ω => ∑ i ∈ Finset.range n, X i ω) := by
    intro n
    exact ((Finset.measurable_sum (s := Finset.range n) (f := fun i ω => X i ω)
      (fun i hi => (hadapt i).mono (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hi)))
        le_rfl)).stronglyMeasurable)
  apply martingale_of_setIntegral_eq_succ hadp
    (fun n => integrable_finsetSum _ (fun i _ => hXi_int i))
  intro n s hs
  have hXs : ∫ ω in s, X n ω ∂μ = 0 := by
    have hmeas_s : Measurable[ℱ n] (Set.indicator s (fun _ => (1 : ℝ))) :=
      measurable_const.indicator hs
    have hindep : IndepFun (X n) (Set.indicator s (fun _ => (1 : ℝ))) μ := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_right (hIndep n).symm hmeas_s.comap_le
    have h1 : ∫ ω, X n ω * Set.indicator s (fun _ => (1 : ℝ)) ω ∂μ =
        (∫ ω, X n ω ∂μ) * (∫ ω, Set.indicator s (fun _ => (1 : ℝ)) ω ∂μ) :=
      hindep.integral_mul_eq_mul_integral (hX_meas n).aestronglyMeasurable
        ((hmeas_s.mono (ℱ.le n) le_rfl)).aestronglyMeasurable
    have h2 : ∫ ω in s, X n ω ∂μ = ∫ ω, X n ω * Set.indicator s (fun _ => (1 : ℝ)) ω ∂μ := by
      rw [← integral_indicator ((ℱ.le n) s hs)]
      apply integral_congr_ae
      filter_upwards with ω
      by_cases hω : ω ∈ s <;> simp [Set.indicator, hω]
    rw [h2, h1, hmean_i n, zero_mul]
  have hsum : (fun ω => ∑ i ∈ Finset.range (n + 1), X i ω) =
      fun ω => (∑ i ∈ Finset.range n, X i ω) + X n ω :=
    funext fun ω => Finset.sum_range_succ _ _
  have hsplit : ∫ ω in s, ((∑ i ∈ Finset.range n, X i ω) + X n ω) ∂μ =
      ∫ ω in s, ∑ i ∈ Finset.range n, X i ω ∂μ + ∫ ω in s, X n ω ∂μ := by
    apply integral_add
    · exact (integrable_finsetSum _ (fun i _ => hXi_int i)).integrableOn
    · exact (hXi_int n).integrableOn
  rw [hsum, hsplit, hXs, add_zero]


/-- The stopped increment `Xₖ · 1_{τ > k}`. -/
private noncomputable def stoppedIncr (X : ℕ → Ω → ℝ) (τ : Ω → ℕ) (k : ℕ) (ω : Ω) : ℝ :=
  X k ω * Set.indicator {ω | k < τ ω} (fun _ => (1 : ℝ)) ω

/-- **Wald's second equation at a bounded stopping time** (private engine): for
`τ ≤ n`,
`E[(S_τ)²] = E[X₀²] · E[τ]`, where `S_τ = ∑_{i < τ} Xᵢ`. The proof expands the
square into diagonal and cross terms; the cross terms vanish by independence
and the mean-zero hypothesis, and the diagonal terms factor by independence. -/
private theorem integral_stopped_partialSum_sq {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {ℱ : Filtration ℕ m0}
    (hIndep : ∀ k, Indep (ℱ k) (MeasurableSpace.comap (X k) inferInstance) μ)
    (hadapt : ∀ k, Measurable[ℱ (k + 1)] (X k))
    {τ : Ω → ℕ} (hT : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℕ)))
    {n : ℕ} (hτn : ∀ ω, τ ω ≤ n) :
    ∫ ω, (∑ i ∈ Finset.range (τ ω), X i ω) ^ 2 ∂μ =
      (∫ ω, (X 0 ω) ^ 2 ∂μ) * (∫ ω, (τ ω : ℝ) ∂μ) := by
  have hTmeas : Measurable τ := measurable_of_isStoppingTime hT
  have hset_meas : ∀ k, MeasurableSet {ω | k < τ ω} :=
    fun k => measurableSet_lt measurable_const hTmeas
  have hset_measF : ∀ k, MeasurableSet[ℱ k] {ω | k < τ ω} := by
    intro k
    have h1 : {ω | k < τ ω} = {ω | (k : WithTop ℕ) < (τ ω : WithTop ℕ)} := by
      ext ω
      simp [Nat.cast_lt]
    rw [h1]
    exact hT.measurableSet_gt k
  have hmean_i : ∀ i, ∫ ω, X i ω ∂μ = 0 := fun i => by
    rw [(hX_iid i 0).integral_eq]; exact hmean
  have hXk2_int : ∀ k, Integrable (fun ω => (X k ω) ^ 2) μ := fun k =>
    ((hX_iid k 0).comp (measurable_id.pow_const 2)).integrable_iff.mpr hX_sq_int
  have hXk2_eq : ∀ k, ∫ ω, (X k ω) ^ 2 ∂μ = ∫ ω, (X 0 ω) ^ 2 ∂μ := fun k =>
    ((hX_iid k 0).comp (measurable_id.pow_const 2)).integral_eq
  have hDmeas : ∀ k, Measurable (stoppedIncr X τ k) := fun k =>
    (hX_meas k).mul (measurable_const.indicator (hset_meas k))
  have hDsq_int : ∀ k, Integrable (fun ω => (stoppedIncr X τ k ω) ^ 2) μ := by
    intro k
    have hfun : (fun ω => (stoppedIncr X τ k ω) ^ 2) =
        fun ω => (X k ω) ^ 2 * Set.indicator {ω | k < τ ω} (fun _ => (1 : ℝ)) ω := by
      funext ω
      by_cases h : k < τ ω <;> simp [stoppedIncr, Set.indicator, h]
    rw [hfun]
    exact (hXk2_int k).mul_bdd (c := 1)
      ((measurable_const.indicator (hset_meas k)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => by
        by_cases h : ω ∈ {ω | k < τ ω} <;> simp [Set.indicator, h])
  have hDmemLp : ∀ k, MemLp (stoppedIncr X τ k) 2 μ := fun k =>
    (memLp_two_iff_integrable_sq (hDmeas k).aestronglyMeasurable).mpr (hDsq_int k)
  have hDcross_int : ∀ j k, Integrable (fun ω => stoppedIncr X τ j ω * stoppedIncr X τ k ω) μ :=
    fun j k => (hDmemLp j).integrable_mul (hDmemLp k)
  -- the increments are independent of the filtration at their own time
  have hindep_ind : ∀ k, IndepFun (X k) (Set.indicator {ω | k < τ ω} (fun _ => (1 : ℝ))) μ := by
    intro k
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (hIndep k).symm
      (measurable_const.indicator (hset_measF k)).comap_le
  -- diagonal terms
  have hDsq : ∀ k, ∫ ω, (stoppedIncr X τ k ω) ^ 2 ∂μ =
      (∫ ω, (X 0 ω) ^ 2 ∂μ) * (μ {ω | k < τ ω}).toReal := by
    intro k
    have hfun : (fun ω => (stoppedIncr X τ k ω) ^ 2) =
        fun ω => (X k ω) ^ 2 * Set.indicator {ω | k < τ ω} (fun _ => (1 : ℝ)) ω := by
      funext ω
      by_cases h : k < τ ω <;> simp [stoppedIncr, Set.indicator, h]
    have hindep2 : IndepFun (fun ω => (X k ω) ^ 2)
        (Set.indicator {ω | k < τ ω} (fun _ => (1 : ℝ))) μ :=
      (hindep_ind k).comp (measurable_id.pow_const 2) measurable_id
    have hfactor : ∫ ω, (X k ω) ^ 2 * Set.indicator {ω | k < τ ω} (fun _ => (1 : ℝ)) ω ∂μ =
        (∫ ω, (X k ω) ^ 2 ∂μ) *
          (∫ ω, Set.indicator {ω | k < τ ω} (fun _ => (1 : ℝ)) ω ∂μ) :=
      hindep2.integral_mul_eq_mul_integral (hXk2_int k).aestronglyMeasurable
        (measurable_const.indicator (hset_meas k)).aestronglyMeasurable
    rw [hfun, hfactor, hXk2_eq k, integral_indicator_const (1 : ℝ) (hset_meas k), smul_eq_mul, mul_one]
    rfl
  -- cross terms vanish
  have hDcross : ∀ j k, j < k → ∫ ω, stoppedIncr X τ j ω * stoppedIncr X τ k ω ∂μ = 0 := by
    intro j k hjk
    have hGmeas : Measurable[ℱ k] (fun ω => X j ω *
        Set.indicator {ω | j < τ ω} (fun _ => (1 : ℝ)) ω *
        Set.indicator {ω | k < τ ω} (fun _ => (1 : ℝ)) ω) := by
      apply Measurable.mul
      · apply Measurable.mul
        · exact (hadapt j).mono (ℱ.mono (Nat.succ_le_of_lt hjk)) le_rfl
        · exact (measurable_const.indicator (hset_measF j)).mono (ℱ.mono (le_of_lt hjk)) le_rfl
      · exact measurable_const.indicator (hset_measF k)
    have hindepG : IndepFun (X k) (fun ω => X j ω *
        Set.indicator {ω | j < τ ω} (fun _ => (1 : ℝ)) ω *
        Set.indicator {ω | k < τ ω} (fun _ => (1 : ℝ)) ω) μ := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_right (hIndep k).symm hGmeas.comap_le
    have hfun : (fun ω => stoppedIncr X τ j ω * stoppedIncr X τ k ω) =
        (fun ω => (X j ω * Set.indicator {ω | j < τ ω} (fun _ => (1 : ℝ)) ω *
          Set.indicator {ω | k < τ ω} (fun _ => (1 : ℝ)) ω) * X k ω) := by
      funext ω
      simp only [stoppedIncr]
      ring
    have hfactor : ∫ ω, (X j ω * Set.indicator {ω | j < τ ω} (fun _ => (1 : ℝ)) ω *
          Set.indicator {ω | k < τ ω} (fun _ => (1 : ℝ)) ω) * X k ω ∂μ =
        (∫ ω, (X j ω * Set.indicator {ω | j < τ ω} (fun _ => (1 : ℝ)) ω *
          Set.indicator {ω | k < τ ω} (fun _ => (1 : ℝ)) ω) ∂μ) *
          (∫ ω, X k ω ∂μ) :=
      hindepG.symm.integral_mul_eq_mul_integral
        ((hGmeas.mono (ℱ.le k) le_rfl)).aestronglyMeasurable
        (hX_meas k).aestronglyMeasurable
    rw [hfun, hfactor, hmean_i k, mul_zero]
  -- partial sums are stopped sums
  have hDsum : ∀ ω, (∑ i ∈ Finset.range (τ ω), X i ω) = ∑ k ∈ Finset.range n,
      stoppedIncr X τ k ω := by
    intro ω
    have h1 : ∑ i ∈ Finset.range (τ ω), X i ω =
        ∑ k ∈ Finset.range (τ ω), stoppedIncr X τ k ω := by
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < τ ω := Finset.mem_range.mp hk
      simp [stoppedIncr, hklt]
    rw [h1]
    exact Finset.sum_subset (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (hτn ω))) (fun k _ hk => by
      have hklt : ¬ k < τ ω := by
        simp only [Finset.mem_range, not_lt] at hk
        exact not_lt.mpr hk
      simp [stoppedIncr, hklt])
  -- tail-sum formula for `E[τ]`
  have hτint : ∫ ω, (τ ω : ℝ) ∂μ = ∑ k ∈ Finset.range n, (μ {ω | k < τ ω}).toReal := by
    have hite : ∀ k, (fun ω => if k < τ ω then (1 : ℝ) else 0) =
        Set.indicator {ω | k < τ ω} (fun _ => (1 : ℝ)) := by
      intro k
      funext ω
      by_cases h : k < τ ω <;> simp [Set.indicator, h]
    calc ∫ ω, (τ ω : ℝ) ∂μ
        = ∫ ω, ∑ k ∈ Finset.range n, (if k < τ ω then (1 : ℝ) else 0) ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          exact natCast_eq_sum_indicator n ω (hτn ω)
      _ = ∑ k ∈ Finset.range n,
            ∫ ω, (if k < τ ω then (1 : ℝ) else 0) ∂μ :=
          integral_finsetSum _ (fun k _ => by
            rw [hite k]
            exact (integrable_const (1 : ℝ)).indicator (hset_meas k))
      _ = ∑ k ∈ Finset.range n, (μ {ω | k < τ ω}).toReal := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hite k, integral_indicator_const (1 : ℝ) (hset_meas k), smul_eq_mul, mul_one]
          rfl
  -- assemble
  have hS_eq : (fun ω => (∑ i ∈ Finset.range (τ ω), X i ω) ^ 2) =
      fun ω => (∑ k ∈ Finset.range n, stoppedIncr X τ k ω) ^ 2 :=
    funext fun ω => by rw [hDsum ω]
  rw [hS_eq]
  calc ∫ ω, (∑ k ∈ Finset.range n, stoppedIncr X τ k ω) ^ 2 ∂μ
      = ∫ ω, (∑ k ∈ Finset.range n, (stoppedIncr X τ k ω) ^ 2 +
          2 * ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range k,
            stoppedIncr X τ j ω * stoppedIncr X τ k ω) ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        exact sum_sq_eq n (fun k => stoppedIncr X τ k ω)
    _ = ∫ ω, ∑ k ∈ Finset.range n, (stoppedIncr X τ k ω) ^ 2 ∂μ +
          ∫ ω, 2 * ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range k,
            stoppedIncr X τ j ω * stoppedIncr X τ k ω ∂μ := by
        apply integral_add
        · exact integrable_finsetSum _ (fun k _ => hDsq_int k)
        · exact (integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun j _ =>
            hDcross_int j k))).const_mul 2
    _ = ∑ k ∈ Finset.range n, ∫ ω, (stoppedIncr X τ k ω) ^ 2 ∂μ +
          2 * ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range k,
            ∫ ω, stoppedIncr X τ j ω * stoppedIncr X τ k ω ∂μ := by
        rw [integral_finsetSum _ (fun k _ => hDsq_int k), integral_const_mul,
          integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun j _ =>
            hDcross_int j k))]
        congr 1
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        exact integral_finsetSum _ (fun j _ => hDcross_int j k)
    _ = ∑ k ∈ Finset.range n,
          ((∫ ω, (X 0 ω) ^ 2 ∂μ) * (μ {ω | k < τ ω}).toReal) + 0 := by
        rw [Finset.sum_congr rfl (fun k _ => hDsq k)]
        congr 1
        have hz : ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range k,
            ∫ ω, stoppedIncr X τ j ω * stoppedIncr X τ k ω ∂μ = 0 := by
          apply Finset.sum_eq_zero
          intro k _
          apply Finset.sum_eq_zero
          intro j hj
          exact hDcross j k (Finset.mem_range.mp hj)
        rw [hz, mul_zero]
    _ = (∫ ω, (X 0 ω) ^ 2 ∂μ) * (∫ ω, (τ ω : ℝ) ∂μ) := by
        rw [add_zero, ← Finset.mul_sum, ← hτint]


/-- The partial sum process `Sₙ = ∑_{i < n} Xᵢ`. -/
private def partialSum (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, X i ω

/-- **Square-integrability of a stopped partial sum at a bounded stopping time**:
if `τ ≤ n` then `(S_τ)²` is integrable. The proof expands the square into
diagonal and cross terms of stopped increments, each integrable. -/
private theorem integrable_stopped_partialSum_sq_of_le {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    {ℱ : Filtration ℕ m0}
    {τ : Ω → ℕ} (hT : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℕ)))
    {n : ℕ} (hτn : ∀ ω, τ ω ≤ n) :
    Integrable (fun ω => (∑ i ∈ Finset.range (τ ω), X i ω) ^ 2) μ := by
  have hTmeas : Measurable τ := measurable_of_isStoppingTime hT
  have hset_meas : ∀ k, MeasurableSet {ω | k < τ ω} :=
    fun k => measurableSet_lt measurable_const hTmeas
  have hXk2_int : ∀ k, Integrable (fun ω => (X k ω) ^ 2) μ := fun k =>
    ((hX_iid k 0).comp (measurable_id.pow_const 2)).integrable_iff.mpr hX_sq_int
  have hDmeas : ∀ k, Measurable (stoppedIncr X τ k) := fun k =>
    (hX_meas k).mul (measurable_const.indicator (hset_meas k))
  have hDsq_int : ∀ k, Integrable (fun ω => (stoppedIncr X τ k ω) ^ 2) μ := by
    intro k
    have hfun : (fun ω => (stoppedIncr X τ k ω) ^ 2) =
        fun ω => (X k ω) ^ 2 * Set.indicator {ω | k < τ ω} (fun _ => (1 : ℝ)) ω := by
      funext ω
      by_cases h : k < τ ω <;> simp [stoppedIncr, Set.indicator, h]
    rw [hfun]
    exact (hXk2_int k).mul_bdd (c := 1)
      ((measurable_const.indicator (hset_meas k)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => by
        by_cases h : ω ∈ {ω | k < τ ω} <;> simp [Set.indicator, h])
  have hDmemLp : ∀ k, MemLp (stoppedIncr X τ k) 2 μ := fun k =>
    (memLp_two_iff_integrable_sq (hDmeas k).aestronglyMeasurable).mpr (hDsq_int k)
  have hDcross_int : ∀ j k, Integrable (fun ω => stoppedIncr X τ j ω * stoppedIncr X τ k ω) μ :=
    fun j k => (hDmemLp j).integrable_mul (hDmemLp k)
  have hDsum : ∀ ω, (∑ i ∈ Finset.range (τ ω), X i ω) = ∑ k ∈ Finset.range n,
      stoppedIncr X τ k ω := by
    intro ω
    have h1 : ∑ i ∈ Finset.range (τ ω), X i ω =
        ∑ k ∈ Finset.range (τ ω), stoppedIncr X τ k ω := by
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < τ ω := Finset.mem_range.mp hk
      simp [stoppedIncr, hklt]
    rw [h1]
    exact Finset.sum_subset
      (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (hτn ω)))
      (fun k _ hk => by
        have hklt : ¬ k < τ ω := by
          simp only [Finset.mem_range, not_lt] at hk
          exact not_lt.mpr hk
        simp [stoppedIncr, hklt])
  have hfun : (fun ω => (∑ i ∈ Finset.range (τ ω), X i ω) ^ 2) =
      fun ω => (∑ k ∈ Finset.range n, (stoppedIncr X τ k ω) ^ 2 +
        2 * ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range k,
          stoppedIncr X τ j ω * stoppedIncr X τ k ω) :=
    funext fun ω => by rw [hDsum ω]; exact sum_sq_eq n (fun k => stoppedIncr X τ k ω)
  rw [hfun]
  apply Integrable.add
  · exact integrable_finsetSum _ (fun k _ => hDsq_int k)
  · exact (integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun j _ =>
      hDcross_int j k))).const_mul 2

/-- **Main theorem**: for an i.i.d. mean-zero sequence with `E[X₀²] < ∞` and a stopping
time `τ` with `E[τ] < ∞`, the stopped partial sum `S_τ` is square-integrable.
The proof applies the truncated Doob `L²` bound to the stopped martingale,
lets the truncation `K → ∞`, then applies Fatou as `n → ∞`. -/
private theorem integrable_stopped_partialSum_sq_of_integrable_tau {X : ℕ → Ω → ℝ}
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
    Integrable (fun ω => (∑ i ∈ Finset.range (τ ω), X i ω) ^ 2) μ := by
  have hTmeas : Measurable τ := measurable_of_isStoppingTime hT
  have hS : Martingale (fun n ω => partialSum X n ω) ℱ μ :=
    martingale_partialSum hX_iid hX_meas hX_int hmean hIndep hadapt
  have hσ2 : 0 ≤ ∫ ω, (X 0 ω) ^ 2 ∂μ :=
    integral_nonneg_of_ae (Eventually.of_forall fun ω => sq_nonneg _)
  -- the truncated partial sums are measurable
  have hSmin_meas_all : ∀ n : ℕ, Measurable (fun ω => partialSum X (min (τ ω) n) ω) := by
    intro n
    set σ : Ω → WithTop ℕ := fun ω => ((min (τ ω) n : ℕ) : WithTop ℕ) with hσdef
    have hσ_stop : IsStoppingTime ℱ σ := by
      exact hT.min_const n
    have hsm : StronglyMeasurable (stoppedValue (fun n ω => partialSum X n ω) σ) :=
      (stronglyMeasurable_stoppedValue_of_le hS.stronglyAdapted.isStronglyProgressive_of_discrete
        hσ_stop (fun ω => by
          rw [hσdef]
          exact WithTop.coe_le_coe.mpr (min_le_right _ _))).mono (ℱ.le n)
    have h2 : stoppedValue (fun n ω => partialSum X n ω) σ =
        fun ω => partialSum X (min (τ ω) n) ω := by
      funext ω
      rfl
    rw [h2] at hsm
    exact hsm.measurable
  -- measurability of the stopped sum itself
  have hSτ_meas : Measurable (fun ω => partialSum X (τ ω) ω) := by
    have h1 : Measurable (stoppedValue (fun n ω => partialSum X n ω)
        (fun ω => (τ ω : WithTop ℕ))) :=
      (measurable_stoppedValue hS.stronglyAdapted.isStronglyProgressive_of_discrete hT).mono
        hT.measurableSpace_le le_rfl
    have h2 : stoppedValue (fun n ω => partialSum X n ω) (fun ω => (τ ω : WithTop ℕ)) =
        fun ω => partialSum X (τ ω) ω := by
      funext ω
      rfl
    rw [h2] at h1
    exact h1
  -- per-`n` bound from the truncated Doob inequality applied to the stopped martingale
  have hbound : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal ((partialSum X (min (τ ω) n) ω) ^ 2) ∂μ ≤
      4 * ENNReal.ofReal ((∫ ω, (X 0 ω) ^ 2 ∂μ) * (∫ ω, ((min (τ ω) n : ℕ) : ℝ) ∂μ)) := by
    intro n
    set σ : Ω → WithTop ℕ := fun ω => ((min (τ ω) n : ℕ) : WithTop ℕ) with hσdef
    have hσ_stop : IsStoppingTime ℱ σ := by
      exact hT.min_const n
    have hstop : Martingale (stoppedProcess (fun n ω => partialSum X n ω) σ) ℱ μ := by
      rw [martingale_iff]
      refine ⟨?_, hS.submartingale.stoppedProcess hσ_stop⟩
      have h1 := hS.supermartingale.neg.stoppedProcess hσ_stop
      have hneg : stoppedProcess (-(fun n ω => partialSum X n ω)) σ =
          -stoppedProcess (fun n ω => partialSum X n ω) σ := by
        funext i ω
        simp [stoppedProcess, Pi.neg_apply]
      rw [hneg] at h1
      simpa only [neg_neg] using h1.neg
    have hg_n : ∀ ω, stoppedProcess (fun n ω => partialSum X n ω) σ n ω =
        partialSum X (min (τ ω) n) ω := by
      intro ω
      show partialSum X (min (n : WithTop ℕ) (σ ω)).untopA ω =
        partialSum X (min (τ ω) n) ω
      have hle : σ ω ≤ (n : WithTop ℕ) := by
        rw [hσdef]
        exact WithTop.coe_le_coe.mpr (min_le_right _ _)
      rw [min_eq_right hle, hσdef]
      rfl
    have hK : ∀ K : ℝ, 0 ≤ K →
        ∫⁻ ω, ENNReal.ofReal (min ((partialSum X (min (τ ω) n) ω) ^ 2) K) ∂μ ≤
          4 * ENNReal.ofReal ((∫ ω, (X 0 ω) ^ 2 ∂μ) * (∫ ω, ((min (τ ω) n : ℕ) : ℝ) ∂μ)) := by
      intro K hK
      have h1 : ∫⁻ ω, ENNReal.ofReal (min ((partialSum X (min (τ ω) n) ω) ^ 2) K) ∂μ ≤
          ∫⁻ ω, ENNReal.ofReal (min ((maxAbs (stoppedProcess (fun n ω => partialSum X n ω) σ) n ω) ^ 2) K) ∂μ := by
        apply lintegral_mono_ae (Eventually.of_forall fun ω => ?_)
        apply ENNReal.ofReal_le_ofReal
        apply min_le_min_right K
        rw [← sq_abs (partialSum X (min (τ ω) n) ω)]
        apply pow_le_pow_left₀ (abs_nonneg _) _ 2
        rw [← hg_n ω]
        exact Finset.le_sup' (fun k => |stoppedProcess (fun n ω => partialSum X n ω) σ k ω|)
          (Finset.mem_range.mpr (Nat.lt_succ_self n))
      have h2 := lintegral_min_maxAbs_sq_le hstop n hK
      have h3 : ∫⁻ ω, ENNReal.ofReal ((stoppedProcess (fun n ω => partialSum X n ω) σ n ω) ^ 2) ∂μ =
          ENNReal.ofReal ((∫ ω, (X 0 ω) ^ 2 ∂μ) * (∫ ω, ((min (τ ω) n : ℕ) : ℝ) ∂μ)) := by
        have hcongr : (fun ω => ENNReal.ofReal ((stoppedProcess (fun n ω => partialSum X n ω) σ n ω) ^ 2)) =
            fun ω => ENNReal.ofReal ((partialSum X (min (τ ω) n) ω) ^ 2) :=
          funext fun ω => by rw [hg_n ω]
        have hInt : Integrable (fun ω => (partialSum X (min (τ ω) n) ω) ^ 2) μ := by
          have hmem := integrable_stopped_partialSum_sq_of_le hX_iid hX_meas hX_sq_int
            (τ := fun ω => min (τ ω) n) (hT.min_const n) (fun ω => min_le_right _ _)
          have hfun : (fun ω => (partialSum X (min (τ ω) n) ω) ^ 2) =
              (fun ω => (∑ i ∈ Finset.range (min (τ ω) n), X i ω) ^ 2) := rfl
          rw [hfun]
          exact hmem
        rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal hInt
          (Eventually.of_forall fun ω => sq_nonneg _)]
        have hwal : ∫ ω, (partialSum X (min (τ ω) n) ω) ^ 2 ∂μ =
            (∫ ω, (X 0 ω) ^ 2 ∂μ) * (∫ ω, ((min (τ ω) n : ℕ) : ℝ) ∂μ) :=
          integral_stopped_partialSum_sq hX_iid hX_meas hX_sq_int hmean hIndep hadapt
            (τ := fun ω => min (τ ω) n) (hT.min_const n) (fun ω => min_le_right _ _)
        rw [hwal]
      exact h1.trans (h2.trans (by rw [h3]))
    -- let `K → ∞`
    have hF_meas : ∀ K : ℕ, Measurable (fun ω =>
        ENNReal.ofReal (min ((partialSum X (min (τ ω) n) ω) ^ 2) (K : ℝ))) :=
      fun K => ENNReal.measurable_ofReal.comp
        (((hSmin_meas_all n).pow_const 2).min measurable_const)
    have hF_mono : Monotone (fun (K : ℕ) ω =>
        ENNReal.ofReal (min ((partialSum X (min (τ ω) n) ω) ^ 2) (K : ℝ))) := by
      intro K₁ K₂ hK ω
      exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hK))
    have hiSup : ∀ ω, ⨆ K : ℕ, ENNReal.ofReal (min ((partialSum X (min (τ ω) n) ω) ^ 2) (K : ℝ)) =
        ENNReal.ofReal ((partialSum X (min (τ ω) n) ω) ^ 2) := by
      intro ω
      apply le_antisymm
      · apply iSup_le
        intro K
        exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
      · have h1 := le_iSup (fun K : ℕ =>
            ENNReal.ofReal (min ((partialSum X (min (τ ω) n) ω) ^ 2) (K : ℝ)))
          ⌈(partialSum X (min (τ ω) n) ω) ^ 2⌉₊
        have h2 : ENNReal.ofReal (min ((partialSum X (min (τ ω) n) ω) ^ 2)
              ((⌈(partialSum X (min (τ ω) n) ω) ^ 2⌉₊ : ℕ) : ℝ)) =
            ENNReal.ofReal ((partialSum X (min (τ ω) n) ω) ^ 2) := by
          congr 1
          exact min_eq_left (Nat.le_ceil _)
        rw [h2] at h1
        exact h1
    have hcalc : ∫⁻ ω, ENNReal.ofReal ((partialSum X (min (τ ω) n) ω) ^ 2) ∂μ =
        ⨆ K : ℕ, ∫⁻ ω, ENNReal.ofReal (min ((partialSum X (min (τ ω) n) ω) ^ 2) (K : ℝ)) ∂μ := by
      rw [← lintegral_iSup hF_meas hF_mono]
      apply lintegral_congr
      intro ω
      exact (hiSup ω).symm
    rw [hcalc]
    exact iSup_le fun K => hK (K : ℝ) (Nat.cast_nonneg K)
  -- Fatou as `n → ∞`
  have hfatou : ∫⁻ ω, ENNReal.ofReal ((partialSum X (τ ω) ω) ^ 2) ∂μ ≤
      liminf (fun n => ∫⁻ ω, ENNReal.ofReal ((partialSum X (min (τ ω) n) ω) ^ 2) ∂μ) atTop := by
    have h := lintegral_liminf_le (μ := μ) (u := atTop) (fun n =>
      ENNReal.measurable_ofReal.comp ((hSmin_meas_all n).pow_const 2))
    have hlim : ∀ ω, liminf (fun n =>
        ENNReal.ofReal ((partialSum X (min (τ ω) n) ω) ^ 2)) atTop =
        ENNReal.ofReal ((partialSum X (τ ω) ω) ^ 2) := by
      intro ω
      apply Tendsto.liminf_eq
      apply Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [eventually_ge_atTop (τ ω)] with n hn
      rw [min_eq_left hn]
    have h2 : ∫⁻ a, ENNReal.ofReal ((partialSum X (τ a) a) ^ 2) ∂μ =
        ∫⁻ a, liminf (fun i => ENNReal.ofReal ((partialSum X (min (τ a) i) a) ^ 2)) atTop ∂μ := by
      apply lintegral_congr
      intro a
      exact (hlim a).symm
    rw [h2]
    exact h
  have hliminf_le : liminf (fun n =>
      ∫⁻ ω, ENNReal.ofReal ((partialSum X (min (τ ω) n) ω) ^ 2) ∂μ) atTop ≤
      4 * ENNReal.ofReal ((∫ ω, (X 0 ω) ^ 2 ∂μ) * (∫ ω, (τ ω : ℝ) ∂μ)) := by
    have hE : ∀ n, ∫ ω, ((min (τ ω) n : ℕ) : ℝ) ∂μ ≤ ∫ ω, (τ ω : ℝ) ∂μ := by
      intro n
      apply integral_mono_ae _ hτ_int
        (Eventually.of_forall fun ω => Nat.cast_le.mpr (min_le_left _ _))
      exact hτ_int.mono'
        ((measurable_from_top.comp (Measurable.min hTmeas measurable_const)).aestronglyMeasurable)
        (Eventually.of_forall fun ω => by
          rw [Real.norm_of_nonneg (Nat.cast_nonneg (min (τ ω) n))]
          exact Nat.cast_le.mpr (min_le_left _ _))
    have hbound' : ∀ n, ∫⁻ ω, ENNReal.ofReal ((partialSum X (min (τ ω) n) ω) ^ 2) ∂μ ≤
        4 * ENNReal.ofReal ((∫ ω, (X 0 ω) ^ 2 ∂μ) * (∫ ω, (τ ω : ℝ) ∂μ)) := by
      intro n
      exact (hbound n).trans (by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ≥0∞) ≤ 4)
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hE n) hσ2))
    refine liminf_le_of_le (by isBoundedDefault) ?_
    intro b hb
    obtain ⟨n, hn⟩ := hb.exists
    exact le_trans hn (hbound' n)
  have hfin : (∫⁻ ω, ENNReal.ofReal ((partialSum X (τ ω) ω) ^ 2) ∂μ) < ⊤ := by
    apply lt_of_le_of_lt (hfatou.trans hliminf_le)
    exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
  have hfi : HasFiniteIntegral (fun ω => (partialSum X (τ ω) ω) ^ 2) μ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _)).mpr hfin
  exact ⟨(hSτ_meas.pow_const 2).aestronglyMeasurable, hfi⟩


/-- **Maximal form**: `max_{0 ≤ k ≤ τ} Sₖ²` is integrable. This is v1's
`integrable_maximal_stopped_partial_sum_sq`, proved via the stopped-process Doob
bound plus Fatou. -/
private theorem integrable_sup_stopped_partialSum_sq_of_integrable_tau {X : ℕ → Ω → ℝ}
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
    Integrable (fun ω => (Finset.range (τ ω + 1)).sup'
      ⟨0, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _))⟩
      (fun k => (partialSum X k ω) ^ 2)) μ := by
  have hTmeas : Measurable τ := measurable_of_isStoppingTime hT
  have hS : Martingale (fun n ω => partialSum X n ω) ℱ μ :=
    martingale_partialSum hX_iid hX_meas hX_int hmean hIndep hadapt
  have hσ2 : 0 ≤ ∫ ω, (X 0 ω) ^ 2 ∂μ :=
    integral_nonneg_of_ae (Eventually.of_forall fun ω => sq_nonneg _)
  -- the stopped process
  set g : ℕ → Ω → ℝ := stoppedProcess (fun n ω => partialSum X n ω)
    (fun ω => (τ ω : WithTop ℕ)) with hgdef
  have hstop : Martingale g ℱ μ := by
    rw [hgdef, martingale_iff]
    refine ⟨?_, hS.submartingale.stoppedProcess hT⟩
    have h1 := hS.supermartingale.neg.stoppedProcess hT
    have hneg : stoppedProcess (-(fun n ω => partialSum X n ω)) (fun ω => (τ ω : WithTop ℕ)) =
        -stoppedProcess (fun n ω => partialSum X n ω) (fun ω => (τ ω : WithTop ℕ)) := by
      funext i ω
      simp [stoppedProcess, Pi.neg_apply]
    rw [hneg] at h1
    simpa only [neg_neg] using h1.neg
  have hg : ∀ k ω, k ≤ τ ω → g k ω = partialSum X k ω := by
    intro k ω hk
    show partialSum X (min (k : WithTop ℕ) ((τ ω : WithTop ℕ))).untopA ω =
      partialSum X k ω
    have hmin : min (k : WithTop ℕ) ((τ ω : WithTop ℕ)) = (k : WithTop ℕ) :=
      min_eq_left (WithTop.coe_le_coe.mpr hk)
    rw [hmin]
    rfl
  -- the running maximum `U ω = sup_{k ≤ τ ω} |Sₖ ω|`, as an `⨆` over `ℕ`
  set U : Ω → ℝ := fun ω => ⨆ k : ℕ, maxAbs g k ω with hUdef
  have hU_meas : Measurable U := by
    rw [hUdef]
    apply Measurable.iSup
    intro k
    exact measurable_maxAbs (fun j => ((hstop.stronglyAdapted j).measurable).mono (ℱ.le j) le_rfl) k
  -- `g` stopped at `b` is the partial sum up to `min b τ`
  have hgb : ∀ b ω, g b ω = partialSum X (min b (τ ω)) ω := by
    intro b ω
    show partialSum X (min (b : WithTop ℕ) ((τ ω : WithTop ℕ))).untopA ω =
      partialSum X (min b (τ ω)) ω
    by_cases h : b ≤ τ ω
    · have hmin : min (b : WithTop ℕ) ((τ ω : WithTop ℕ)) = (b : WithTop ℕ) :=
        min_eq_left (WithTop.coe_le_coe.mpr h)
      have hmin' : min b (τ ω) = b := min_eq_left h
      rw [hmin, hmin']
      rfl
    · have hmin : min (b : WithTop ℕ) ((τ ω : WithTop ℕ)) = ((τ ω : WithTop ℕ)) :=
        min_eq_right (WithTop.coe_le_coe.mpr (not_le.mp h).le)
      have hmin' : min b (τ ω) = τ ω := min_eq_right (not_le.mp h).le
      rw [hmin, hmin']
      rfl
  have hU_abs : ∀ ω, U ω = (Finset.range (τ ω + 1)).sup'
      ⟨0, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _))⟩
      (fun k => |partialSum X k ω|) := by
    intro ω
    have hper : ∀ k : ℕ, maxAbs g k ω ≤ (Finset.range (τ ω + 1)).sup'
        ⟨0, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _))⟩
        (fun k => |partialSum X k ω|) := by
      intro k
      refine (Finset.sup'_le_iff _ _).mpr ?_
      intro b hb
      show |g b ω| ≤ (Finset.range (τ ω + 1)).sup' _ (fun k => |partialSum X k ω|)
      rw [hgb b ω]
      exact Finset.le_sup' (fun k => |partialSum X k ω|)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_right _ _)))
    have hU_le : (⨆ k : ℕ, maxAbs g k ω) ≤ (Finset.range (τ ω + 1)).sup'
        ⟨0, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _))⟩
        (fun k => |partialSum X k ω|) := ciSup_le hper
    have hU_ge : (Finset.range (τ ω + 1)).sup'
        ⟨0, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _))⟩
        (fun k => |partialSum X k ω|) ≤ ⨆ k : ℕ, maxAbs g k ω := by
      calc (Finset.range (τ ω + 1)).sup' _ (fun k => |partialSum X k ω|)
            ≤ maxAbs g (τ ω) ω := by
              refine (Finset.sup'_le_iff _ _).mpr ?_
              intro b hb
              rw [← hg b ω (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))]
              exact Finset.le_sup' (fun k => |g k ω|) hb
        _ ≤ ⨆ k : ℕ, maxAbs g k ω :=
            le_ciSup (f := fun k => maxAbs g k ω) ⟨(Finset.range (τ ω + 1)).sup' _ (fun k => |partialSum X k ω|),
              fun _ ⟨k, hk⟩ => by rw [← hk]; exact hper k⟩ (τ ω)
    rw [hUdef]
    exact le_antisymm hU_le hU_ge
  have hU_eq : ∀ ω, (U ω) ^ 2 = (Finset.range (τ ω + 1)).sup'
      ⟨0, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _))⟩
      (fun k => (partialSum X k ω) ^ 2) := by
    intro ω
    have h2 : ((Finset.range (τ ω + 1)).sup'
        ⟨0, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _))⟩
        (fun k => |partialSum X k ω|)) ^ 2 =
        (Finset.range (τ ω + 1)).sup'
        ⟨0, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _))⟩
        (fun k => (partialSum X k ω) ^ 2) := by
      apply le_antisymm
      · obtain ⟨j, hj, hjsup⟩ := Finset.exists_mem_eq_sup' ⟨0, Finset.mem_range.mpr
          (Nat.lt_succ_of_le (Nat.zero_le _))⟩ (fun k => |partialSum X k ω|)
        rw [hjsup, sq_abs]
        exact Finset.le_sup' (fun k => (partialSum X k ω) ^ 2) hj
      · refine (Finset.sup'_le_iff _ _).mpr ?_
        intro k hk
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (Finset.le_sup' (fun k => |partialSum X k ω|) hk) 2
    rw [hU_abs ω, h2]
  -- integrability of `U²`
  have hU_int : Integrable (fun ω => (U ω) ^ 2) μ := by
    have hmaxAbs_bound : ∀ n : ℕ, ∫⁻ ω, ENNReal.ofReal ((maxAbs g n ω) ^ 2) ∂μ ≤
        4 * ENNReal.ofReal ((∫ ω, (X 0 ω) ^ 2 ∂μ) *
          (∫ ω, ((min n (τ ω) : ℕ) : ℝ) ∂μ)) := by
      intro n
      have hK : ∀ K : ℝ, 0 ≤ K →
          ∫⁻ ω, ENNReal.ofReal (min ((maxAbs g n ω) ^ 2) K) ∂μ ≤
            4 * ENNReal.ofReal ((∫ ω, (X 0 ω) ^ 2 ∂μ) *
              (∫ ω, ((min n (τ ω) : ℕ) : ℝ) ∂μ)) := by
        intro K hK
        have h2 := lintegral_min_maxAbs_sq_le hstop n hK
        have h3 : ∫⁻ ω, ENNReal.ofReal ((g n ω) ^ 2) ∂μ =
            ENNReal.ofReal ((∫ ω, (X 0 ω) ^ 2 ∂μ) *
              (∫ ω, ((min n (τ ω) : ℕ) : ℝ) ∂μ)) := by
          have hInt : Integrable (fun ω => (g n ω) ^ 2) μ := by
            have hmem := integrable_stopped_partialSum_sq_of_le hX_iid hX_meas hX_sq_int
              (τ := fun ω => min n (τ ω)) ((isStoppingTime_const ℱ n).min hT)
              (fun ω => min_le_left _ _)
            have hfun : (fun ω => (g n ω) ^ 2) =
                (fun ω => (∑ i ∈ Finset.range (min n (τ ω)), X i ω) ^ 2) := by
              funext ω
              congr 1
            rw [hfun]
            exact hmem
          rw [← ofReal_integral_eq_lintegral_ofReal hInt
            (Eventually.of_forall fun ω => sq_nonneg _)]
          have hwal : ∫ ω, (g n ω) ^ 2 ∂μ =
              (∫ ω, (X 0 ω) ^ 2 ∂μ) * (∫ ω, ((min n (τ ω) : ℕ) : ℝ) ∂μ) := by
            have hwal0 := integral_stopped_partialSum_sq hX_iid hX_meas hX_sq_int hmean hIndep
              hadapt (τ := fun ω => min n (τ ω)) ((isStoppingTime_const ℱ n).min hT)
              (fun ω => min_le_left _ _)
            have hfun : (fun ω => (∑ i ∈ Finset.range (min n (τ ω)), X i ω) ^ 2) =
                (fun ω => (g n ω) ^ 2) := by
              funext ω
              congr 1
            rw [← hfun]
            exact hwal0
          rw [hwal]
        exact h2.trans (by rw [h3])
      -- let `K → ∞`
      have hF_meas : ∀ K : ℕ, Measurable (fun ω =>
          ENNReal.ofReal (min ((maxAbs g n ω) ^ 2) (K : ℝ))) :=
        fun K => ENNReal.measurable_ofReal.comp
          (((measurable_maxAbs (fun j => ((hstop.stronglyAdapted j).measurable).mono
              (ℱ.le j) le_rfl) n).pow_const 2).min measurable_const)
      have hF_mono : Monotone (fun (K : ℕ) ω =>
          ENNReal.ofReal (min ((maxAbs g n ω) ^ 2) (K : ℝ))) := by
        intro K₁ K₂ hK ω
        exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.mpr hK))
      have hiSup : ∀ ω, ⨆ K : ℕ, ENNReal.ofReal (min ((maxAbs g n ω) ^ 2) (K : ℝ)) =
          ENNReal.ofReal ((maxAbs g n ω) ^ 2) := by
        intro ω
        apply le_antisymm
        · apply iSup_le
          intro K
          exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
        · have h1 := le_iSup (fun K : ℕ =>
              ENNReal.ofReal (min ((maxAbs g n ω) ^ 2) (K : ℝ)))
            ⌈(maxAbs g n ω) ^ 2⌉₊
          have h2 : ENNReal.ofReal (min ((maxAbs g n ω) ^ 2)
                ((⌈(maxAbs g n ω) ^ 2⌉₊ : ℕ) : ℝ)) =
              ENNReal.ofReal ((maxAbs g n ω) ^ 2) := by
            congr 1
            exact min_eq_left (Nat.le_ceil _)
          rw [h2] at h1
          exact h1
      have hcalc : ∫⁻ ω, ENNReal.ofReal ((maxAbs g n ω) ^ 2) ∂μ =
          ⨆ K : ℕ, ∫⁻ ω, ENNReal.ofReal (min ((maxAbs g n ω) ^ 2) (K : ℝ)) ∂μ := by
        rw [← lintegral_iSup hF_meas hF_mono]
        apply lintegral_congr
        intro ω
        exact (hiSup ω).symm
      rw [hcalc]
      exact iSup_le fun K => hK (K : ℝ) (Nat.cast_nonneg K)
    -- Fatou as `n → ∞`: `maxAbs g n` is eventually constant `= U`
    have hfatou : ∫⁻ ω, ENNReal.ofReal ((U ω) ^ 2) ∂μ ≤
        liminf (fun n => ∫⁻ ω, ENNReal.ofReal ((maxAbs g n ω) ^ 2) ∂μ) atTop := by
      have h := lintegral_liminf_le (μ := μ) (u := atTop) (fun n =>
        ENNReal.measurable_ofReal.comp ((measurable_maxAbs
          (fun j => ((hstop.stronglyAdapted j).measurable).mono (ℱ.le j) le_rfl) n).pow_const 2))
      have hlim : ∀ ω, liminf (fun n => ENNReal.ofReal ((maxAbs g n ω) ^ 2)) atTop =
          ENNReal.ofReal ((U ω) ^ 2) := by
        intro ω
        apply Tendsto.liminf_eq
        apply Tendsto.congr' _ tendsto_const_nhds
        filter_upwards [eventually_ge_atTop (τ ω)] with n hn
        -- for `n ≥ τ ω`, `maxAbs g n ω = U ω`
        have hmax : maxAbs g n ω = U ω := by
          rw [hU_abs ω]
          apply le_antisymm
          · refine (Finset.sup'_le_iff _ _).mpr ?_
            intro b hb
            rw [hgb b ω]
            exact Finset.le_sup' (fun k => |partialSum X k ω|)
              (Finset.mem_range.mpr (Nat.lt_succ_of_le (min_le_right _ _)))
          · refine (Finset.sup'_le_iff _ _).mpr ?_
            intro b hb
            rw [← hg b ω (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))]
            exact Finset.le_sup' (fun k => |g k ω|)
              (Finset.mem_range.mpr
                (Nat.lt_of_lt_of_le (Finset.mem_range.mp hb) (Nat.succ_le_succ hn)))
        rw [hmax]
      have h2 : ∫⁻ a, ENNReal.ofReal ((U a) ^ 2) ∂μ =
          ∫⁻ a, liminf (fun i => ENNReal.ofReal ((maxAbs g i a) ^ 2)) atTop ∂μ := by
        apply lintegral_congr
        intro a
        exact (hlim a).symm
      rw [h2]
      exact h
    have hliminf_le : liminf (fun n => ∫⁻ ω, ENNReal.ofReal ((maxAbs g n ω) ^ 2) ∂μ) atTop ≤
        4 * ENNReal.ofReal ((∫ ω, (X 0 ω) ^ 2 ∂μ) * (∫ ω, (τ ω : ℝ) ∂μ)) := by
      have hE : ∀ n, ∫ ω, ((min n (τ ω) : ℕ) : ℝ) ∂μ ≤ ∫ ω, (τ ω : ℝ) ∂μ := by
        intro n
        apply integral_mono_ae _ hτ_int
          (Eventually.of_forall fun ω => Nat.cast_le.mpr (min_le_right _ _))
        exact hτ_int.mono'
          ((measurable_from_top.comp (Measurable.min measurable_const hTmeas)).aestronglyMeasurable)
          (Eventually.of_forall fun ω => by
            rw [Real.norm_of_nonneg (Nat.cast_nonneg (min n (τ ω)))]
            exact Nat.cast_le.mpr (min_le_right _ _))
      have hbound' : ∀ n, ∫⁻ ω, ENNReal.ofReal ((maxAbs g n ω) ^ 2) ∂μ ≤
          4 * ENNReal.ofReal ((∫ ω, (X 0 ω) ^ 2 ∂μ) * (∫ ω, (τ ω : ℝ) ∂μ)) := by
        intro n
        exact (hmaxAbs_bound n).trans (by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ≥0∞) ≤ 4)
          exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hE n) hσ2))
      refine liminf_le_of_le (by isBoundedDefault) ?_
      intro b hb
      obtain ⟨n, hn⟩ := hb.exists
      exact le_trans hn (hbound' n)
    have hfin : (∫⁻ ω, ENNReal.ofReal ((U ω) ^ 2) ∂μ) < ⊤ := by
      apply lt_of_le_of_lt (hfatou.trans hliminf_le)
      exact ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
    have hfi : HasFiniteIntegral (fun ω => (U ω) ^ 2) μ :=
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _)).mpr hfin
    exact ⟨(hU_meas.pow_const 2).aestronglyMeasurable, hfi⟩
  exact hU_int.congr (Eventually.of_forall fun ω => hU_eq ω)

/-- The "predictable" filtration associated to a sequence `X : ℕ → Ω → ℝ`:
`ℱ_k = σ(X_0, …, X_{k-1})`. Ported verbatim from v1 `WaldSecondEquation.lean`. -/
noncomputable def predictableFiltration
    {Ω : Type*} (m : MeasurableSpace Ω) (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i)) : Filtration ℕ m where
  seq k := ⨆ (j : ℕ) (_ : j < k), MeasurableSpace.comap (X j) inferInstance
  mono' _i _j hij := iSup₂_le fun l hl => le_iSup₂ (f := fun (l' : ℕ) (_ : l' < _j) =>
    MeasurableSpace.comap (X l') inferInstance) l (Nat.lt_of_lt_of_le hl hij)
  le' _k := iSup₂_le fun j _ => (hX_meas j).comap_le

/-- The predictable filtration contains no observations at time zero. -/
@[simp] theorem predictableFiltration_zero {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i)) :
    predictableFiltration m0 X hX_meas 0 = ⊥ := by
  simp [predictableFiltration]

/-- A successor step adds exactly the next observation to the predictable filtration. -/
theorem predictableFiltration_succ {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i)) (k : ℕ) :
    predictableFiltration m0 X hX_meas (k + 1) =
      predictableFiltration m0 X hX_meas k ⊔ MeasurableSpace.comap (X k) inferInstance :=
  Nat.iSup_lt_succ (fun j => MeasurableSpace.comap (X j) inferInstance) k

private theorem measurable_predictableFiltration_succ {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i)) (k : ℕ) :
    Measurable[predictableFiltration m0 X hX_meas (k + 1)] (X k) := by
  rw [measurable_iff_comap_le]
  exact le_iSup₂ (f := fun (j : ℕ) (_ : j < k + 1) =>
    MeasurableSpace.comap (X j) inferInstance) k (Nat.lt_succ_self k)

private theorem indep_predictableFiltration {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_ind : iIndepFun (β := fun _ => ℝ) X μ) (k : ℕ) :
    Indep (predictableFiltration m0 X hX_meas k)
      (MeasurableSpace.comap (X k) inferInstance) μ := by
  have h1 := indep_iSup_of_disjoint (m := fun j => MeasurableSpace.comap (X j) inferInstance)
    (fun j => (hX_meas j).comap_le) (hX_ind.iIndep) (S := {j | j < k}) (T := {k})
    (by simp)
  have h2 : (⨆ i ∈ ({k} : Set ℕ), MeasurableSpace.comap (X i) inferInstance) =
      MeasurableSpace.comap (X k) inferInstance := by simp
  have h3 : (⨆ i ∈ ({j | j < k} : Set ℕ), MeasurableSpace.comap (X i) inferInstance) =
      predictableFiltration m0 X hX_meas k := rfl
  rw [h2, h3] at h1
  exact h1

/-- **Square-integrability of a stopped partial sum**, general-filtration form. -/
theorem integrable_stopped_partialSum_sq {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_int : Integrable (X 0) μ)
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {ℱ : Filtration ℕ m0}
    (hIndep : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (ℱ k) μ)
    (hadapt : ∀ k, Measurable[ℱ (k + 1)] (X k))
    {τ : Ω → ℕ} (hT : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℕ)))
    (hτ_int : Integrable (fun ω => (τ ω : ℝ)) μ) :
    Integrable (fun ω => (∑ i ∈ Finset.range (τ ω), X i ω) ^ 2) μ := by
  have hX_meas : ∀ k, Measurable (X k) :=
    fun k => (hadapt k).mono (ℱ.le (k + 1)) le_rfl
  exact integrable_stopped_partialSum_sq_of_integrable_tau hX_iid hX_meas hX_int hX_sq_int
    hmean (fun k => (hIndep k).symm) hadapt hT hτ_int

/-- **Square-integrability of the maximal stopped partial sum**, in v1's form:
`max_{0 ≤ k ≤ T} Sₖ²` is integrable. This is v1's
`integrable_maximal_stopped_partial_sum_sq`, whose proof in v1 was left unproved. -/
theorem integrable_maximal_stopped_partial_sum_sq {X : ℕ → Ω → ℝ}
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
  integrable_sup_stopped_partialSum_sq_of_integrable_tau hX_iid hX_meas hX_int hX_sq_int hmean
    (fun k => indep_predictableFiltration hX_meas hX_ind k)
    (fun k => measurable_predictableFiltration_succ hX_meas k) hT hT_int

end

end MathlibExt.Probability.StoppedSumMaximal
