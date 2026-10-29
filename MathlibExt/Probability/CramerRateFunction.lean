/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Cramér rate function

The rate function in Cramér's theorem (Lecture 13): for a random vector
`X` in `ℝᵈ` with law `μ`, the Cramér rate function is the Legendre transform
of the cumulant generating function `Λ(t) = log E[exp ⟪t, X⟫]`,
`Λ*(x) = sup_t {⟪t, x⟫ - Λ(t)}`.

## Source

This formalizes the rate-function part of `cramer_theorem` in
`v1/Atlas/TheoryOfProbability/code/CramerTheorem.lean` (Lecture 13).
The full Cramér theorem (the large deviation principle for the empirical
means, with the lower bound) is not claimed here: in v1 its proof is left
unproved, and the upper bound was ported separately in batch 73 (#546).

## Statement correction

In v1 the rate function is defined as
`ENNReal.ofReal (legendreTransform (logMGFVec X μ) x)`, where
`legendreTransform Λ x = ⨆ t, (⟪t, x⟫ - Λ t)` is a supremum taken in `ℝ`.
That is the wrong place for the supremum: in `ℝ`, the supremum of a set
that is not bounded above is `0` by convention (`Real.iSup_of_not_bddAbove`),
so v1's definition collapses to `0` exactly when the true Legendre
transform is `+∞`. For example, if `X` is identically equal to a constant `c`,
then `⟪t, x⟫ - Λ(t) = ⟪t, x - c⟫` is unbounded above for every `x ≠ c`,
so v1's definition gives `0` at every `x ≠ c`, while the true rate
function is `+∞` there (see `cramerRateFunction_const` and the test file).

The definition here therefore takes the supremum in `ℝ≥0∞`:
`cramerRateFunction X μ x = ⨆ t, ENNReal.ofReal (⟪t, x⟫ - logMGFVec X μ t)`.
This agrees with v1's definition whenever the set of values
`{⟪t, x⟫ - Λ(t) | t}` is bounded above in `ℝ`, proved in
`cramerRateFunction_eq_ofReal_iSup` (in particular at the mean, where
it is bounded above by `0`; see `cramerRateFunction_eq_zero_at_mean`).

## Main results

* `logMGFVec`: the cumulant generating function, ported verbatim from v1.
* `cramerRateFunction`: the corrected Cramér rate function.
* `le_cramerRateFunction`: the Fenchel-Young inequality, one dual variable
  at a time.
* `cramerRateFunction_eq_ofReal_iSup`: agreement with v1's definition
  when the values are bounded above in `ℝ`.
* `cramerRateFunction_eq_zero_at_mean`: the rate function vanishes at the
  mean of `X` (Jensen's inequality).
* `lowerSemicontinuous_cramerRateFunction`: the rate function is lower
  semicontinuous, so it is a rate function in the large-deviation sense.
* `cramerRateFunction_convex`: the convexity inequality for the rate
  function.
* `cramerRateFunction_const`: for an identically constant `X = c`, the
  rate is `0` at `c` and `⊤` elsewhere; this is the case where v1's
  definition gives the wrong value `0` away from `c`.

## Relation to earlier batches

Batch 73 (#546) defines `logMGFVec` (and `empiricalMeanMeasureVec`,
not copied here) in namespace `MathlibExt.Probability.CramerUpperBound`;
the copy of `logMGFVec` here lives in the distinct namespace
`MathlibExt.Probability.CramerRateFunction` and is to be unified on
rebase. Batch 51 (#478) defines the general
`legendreTransform` as a supremum in `ℝ` with the `0`-on-unbounded
convention; the rate function here deliberately does not reuse it, for
the reason above. Batch 48 (#473) defines the large-deviation structures
`IsRateFunction` / `IsConvexRateFunction`; the results here are stated
directly (lower semicontinuity, convexity) rather than through those
structures, which live in an unmerged batch.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace MathlibExt.Probability.CramerRateFunction

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Vector-valued cumulant generating function** `Λ(t) = log E[exp ⟪t, X⟫]`.

For a random vector `X : Ω → ℝᵈ`, this returns the logarithm of the moment
generating function evaluated at the dual variable `t ∈ ℝᵈ`, using the
Euclidean inner product. Ported verbatim from v1. -/
noncomputable def logMGFVec {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    (μ : Measure Ω) (t : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.log (∫ ω, Real.exp ⟪t, X ω⟫_ℝ ∂μ)

/-- **Cramér rate function** `Λ*(x) = sup_λ {⟨λ, x⟩ − Λ(λ)}` (Lecture 13).

The Legendre transform of the cumulant generating function
`Λ = logMGFVec X μ`, viewed as an `ℝ≥0∞`-valued rate function for the
large deviation principle of the empirical means of i.i.d. copies of `X`.

CORRECTED with respect to v1: v1 writes
`ENNReal.ofReal (legendreTransform (logMGFVec X μ) x)`, taking the
supremum in `ℝ` before applying `ENNReal.ofReal`. Since a supremum in `ℝ`
of an unbounded-above set is `0`, v1's version collapses to `0` whenever
the true Legendre transform is `+∞`. Here the supremum is taken in
`ℝ≥0∞`, after applying `ENNReal.ofReal` to each value. -/
noncomputable def cramerRateFunction {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    (μ : Measure Ω) (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ⨆ t, ENNReal.ofReal (⟪t, x⟫_ℝ - logMGFVec X μ t)

/-- The cumulant generating function at `0` is `log E[1] = 0`. -/
theorem logMGFVec_zero {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    [IsProbabilityMeasure μ] :
    logMGFVec X μ 0 = 0 := by
  have h0 : ∀ ω, ⟪(0 : EuclideanSpace ℝ (Fin d)), X ω⟫_ℝ = 0 := fun ω => inner_zero_left _
  simp only [logMGFVec, h0, Real.exp_zero, integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, one_smul, Real.log_one]

/-- **Fenchel-Young inequality** for the Cramér rate function: every dual
variable `t` gives a lower bound `⟪t, x⟫ - Λ(t) ≤ Λ*(x)`. -/
theorem le_cramerRateFunction {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    (μ : Measure Ω) (x t : EuclideanSpace ℝ (Fin d)) :
    ENNReal.ofReal (⟪t, x⟫_ℝ - logMGFVec X μ t) ≤ cramerRateFunction X μ x :=
  le_iSup_of_le t le_rfl

/-- **Agreement with v1's definition when bounded above.** When the set of
values `{⟪t, x⟫ - Λ(t)}` is bounded above in `ℝ`, the corrected rate
function equals v1's `ENNReal.ofReal (⨆ t, ⟪t, x⟫ - Λ(t))`. In
particular the correction only changes the value when the Legendre
transform is infinite. -/
theorem cramerRateFunction_eq_ofReal_iSup {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    (μ : Measure Ω) {x : EuclideanSpace ℝ (Fin d)}
    (hbdd : BddAbove (Set.range fun t => ⟪t, x⟫_ℝ - logMGFVec X μ t)) :
    cramerRateFunction X μ x =
      ENNReal.ofReal (⨆ t, ⟪t, x⟫_ℝ - logMGFVec X μ t) := by
  obtain ⟨B, hB⟩ := hbdd
  have hle : ∀ t : EuclideanSpace ℝ (Fin d),
      ⟪t, x⟫_ℝ - logMGFVec X μ t ≤ B := fun t => hB (Set.mem_range_self t)
  have hS_ne : (⨆ t, ENNReal.ofReal (⟪t, x⟫_ℝ - logMGFVec X μ t)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (iSup_le fun t => ENNReal.ofReal_le_ofReal (hle t))
  have hmaxBdd : BddAbove (Set.range fun t : EuclideanSpace ℝ (Fin d) =>
      max (⟪t, x⟫_ℝ - logMGFVec X μ t) 0) :=
    ⟨max B 0, fun _ ⟨t, ht⟩ => by
      rw [← ht]
      exact max_le_max (hle t) le_rfl⟩
  have hreal : (⨆ t, ⟪t, x⟫_ℝ - logMGFVec X μ t) ≤
      ⨆ t, max (⟪t, x⟫_ℝ - logMGFVec X μ t) 0 := by
    apply ciSup_le
    intro t
    exact (le_max_left _ _).trans (le_ciSup hmaxBdd t)
  apply le_antisymm
  · show (⨆ t, ENNReal.ofReal (⟪t, x⟫_ℝ - logMGFVec X μ t)) ≤ _
    exact iSup_le fun t => ENNReal.ofReal_le_ofReal (le_ciSup ⟨B, hB⟩ t)
  · show ENNReal.ofReal (⨆ t, ⟪t, x⟫_ℝ - logMGFVec X μ t) ≤
        ⨆ t, ENNReal.ofReal (⟪t, x⟫_ℝ - logMGFVec X μ t)
    rw [ENNReal.ofReal_le_iff_le_toReal hS_ne,
      ENNReal.toReal_iSup (fun _ => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal']
    exact hreal

/-- **The Cramér rate function vanishes at the mean.** If `X` is integrable
and every exponential moment is integrable, then `Λ*(E X) = 0`: by Jensen,
`⟪t, E X⟫ ≤ Λ(t)` for every `t`, and `t = 0` attains equality. -/
theorem cramerRateFunction_eq_zero_at_mean {d : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin d)) [IsProbabilityMeasure μ]
    (hX : Integrable X μ)
    (hInt : ∀ t : EuclideanSpace ℝ (Fin d),
      Integrable (fun ω => Real.exp ⟪t, X ω⟫_ℝ) μ) :
    cramerRateFunction X μ (∫ ω, X ω ∂μ) = 0 := by
  have hterm : ∀ t : EuclideanSpace ℝ (Fin d),
      ENNReal.ofReal (⟪t, ∫ ω, X ω ∂μ⟫_ℝ - logMGFVec X μ t) = 0 := by
    intro t
    rw [ENNReal.ofReal_eq_zero]
    have hinner : ⟪t, ∫ ω, X ω ∂μ⟫_ℝ = ∫ ω, ⟪t, X ω⟫_ℝ ∂μ := by
      have h := ContinuousLinearMap.integral_comp_comm (innerSL ℝ t) hX
      simp only [innerSL_apply_apply] at h
      exact h.symm
    have hfi : Integrable (fun ω => ⟪t, X ω⟫_ℝ) μ :=
      (innerSL ℝ t).integrable_comp hX
    have hJensen : Real.exp (∫ ω, ⟪t, X ω⟫_ℝ ∂μ) ≤
        ∫ ω, Real.exp ⟪t, X ω⟫_ℝ ∂μ :=
      ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn
        isClosed_univ (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
        hfi (hInt t)
    have hlog : ⟪t, ∫ ω, X ω ∂μ⟫_ℝ ≤ logMGFVec X μ t := by
      show ⟪t, ∫ ω, X ω ∂μ⟫_ℝ ≤ Real.log (∫ ω, Real.exp ⟪t, X ω⟫_ℝ ∂μ)
      rw [← Real.log_exp (⟪t, ∫ ω, X ω ∂μ⟫_ℝ)]
      exact Real.log_le_log (Real.exp_pos _) (by rw [hinner]; exact hJensen)
    exact sub_nonpos.mpr hlog
  show (⨆ t, ENNReal.ofReal (⟪t, ∫ ω, X ω ∂μ⟫_ℝ - logMGFVec X μ t)) = 0
  rw [show (fun t : EuclideanSpace ℝ (Fin d) =>
      ENNReal.ofReal (⟪t, ∫ ω, X ω ∂μ⟫_ℝ - logMGFVec X μ t)) = fun _ => (0 : ℝ≥0∞)
      from funext hterm]
  exact iSup_const

/-- **The Cramér rate function is lower semicontinuous**, as a supremum of
continuous functions. In particular it is a rate function in the
large-deviation sense. -/
theorem lowerSemicontinuous_cramerRateFunction {d : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin d)) (μ : Measure Ω) :
    LowerSemicontinuous (cramerRateFunction X μ) := by
  apply lowerSemicontinuous_iSup
  intro t
  exact (ENNReal.continuous_ofReal.comp
    ((continuous_const.inner continuous_id).sub continuous_const)).lowerSemicontinuous

/-- **Convexity of the Cramér rate function**:
`Λ*(a • x + b • y) ≤ a • Λ*(x) + b • Λ*(y)` for `a, b ≥ 0` with `a + b = 1`.
This is the convexity field of the `IsConvexRateFunction` conjunct of
Cramér's theorem in v1; the large-deviation bounds themselves are not
claimed here. -/
theorem cramerRateFunction_convex {d : ℕ} (X : Ω → EuclideanSpace ℝ (Fin d))
    (μ : Measure Ω) {x y : EuclideanSpace ℝ (Fin d)} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    cramerRateFunction X μ (a • x + b • y) ≤
      ENNReal.ofReal a * cramerRateFunction X μ x +
        ENNReal.ofReal b * cramerRateFunction X μ y := by
  show (⨆ t, ENNReal.ofReal (⟪t, a • x + b • y⟫_ℝ - logMGFVec X μ t)) ≤ _
  apply iSup_le
  intro t
  have hinner : ⟪t, a • x + b • y⟫_ℝ = a * ⟪t, x⟫_ℝ + b * ⟪t, y⟫_ℝ := by
    simp [inner_add_right, inner_smul_right]
  have hrewrite : ⟪t, a • x + b • y⟫_ℝ - logMGFVec X μ t
      = a * (⟪t, x⟫_ℝ - logMGFVec X μ t) + b * (⟪t, y⟫_ℝ - logMGFVec X μ t) := by
    rw [hinner]
    have hΛ : a * logMGFVec X μ t + b * logMGFVec X μ t = logMGFVec X μ t := by
      rw [← add_mul, hab, one_mul]
    linarith [hΛ]
  calc ENNReal.ofReal (⟪t, a • x + b • y⟫_ℝ - logMGFVec X μ t)
      = ENNReal.ofReal (a * (⟪t, x⟫_ℝ - logMGFVec X μ t) +
          b * (⟪t, y⟫_ℝ - logMGFVec X μ t)) := by rw [hrewrite]
    _ ≤ ENNReal.ofReal (a * (⟪t, x⟫_ℝ - logMGFVec X μ t)) +
          ENNReal.ofReal (b * (⟪t, y⟫_ℝ - logMGFVec X μ t)) :=
        ENNReal.ofReal_add_le
    _ = ENNReal.ofReal a * ENNReal.ofReal (⟪t, x⟫_ℝ - logMGFVec X μ t) +
          ENNReal.ofReal b * ENNReal.ofReal (⟪t, y⟫_ℝ - logMGFVec X μ t) := by
        rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
    _ ≤ ENNReal.ofReal a * cramerRateFunction X μ x +
          ENNReal.ofReal b * cramerRateFunction X μ y := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (le_cramerRateFunction X μ x t) zero_le
        · exact mul_le_mul_of_nonneg_left (le_cramerRateFunction X μ y t) zero_le

/-- The cumulant generating function of a constant random vector is the
inner product itself: `Λ(t) = ⟪t, c⟫`. -/
theorem logMGFVec_const {d : ℕ} (c : EuclideanSpace ℝ (Fin d))
    [IsProbabilityMeasure μ] (t : EuclideanSpace ℝ (Fin d)) :
    logMGFVec (fun _ => c) μ t = ⟪t, c⟫_ℝ := by
  simp only [logMGFVec, integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    one_smul, Real.log_exp]

/-- **The rate function of an identically constant random vector.** If `X = c`
identically, then `Λ*(c) = 0` and `Λ*(x) = ⊤` for `x ≠ c`.
This is the case where v1's definition is wrong: v1's
`ENNReal.ofReal (⨆ t, ⟪t, x⟫ - Λ(t))` equals `0` for every `x ≠ c`,
because the set `{⟪t, x - c⟫}` is unbounded above in `ℝ` and a supremum
in `ℝ` of an unbounded-above set is `0`. -/
theorem cramerRateFunction_const {d : ℕ} (c : EuclideanSpace ℝ (Fin d))
    [IsProbabilityMeasure μ] :
    cramerRateFunction (fun _ => c) μ c = 0 ∧
    ∀ x : EuclideanSpace ℝ (Fin d), x ≠ c → cramerRateFunction (fun _ => c) μ x = ⊤ := by
  have hΛ : ∀ t : EuclideanSpace ℝ (Fin d), logMGFVec (fun _ => c) μ t = ⟪t, c⟫_ℝ :=
    fun t => logMGFVec_const c t
  refine ⟨?_, ?_⟩
  · show (⨆ t, ENNReal.ofReal (⟪t, c⟫_ℝ - logMGFVec (fun _ => c) μ t)) = 0
    simp only [hΛ, sub_self, ENNReal.ofReal_zero, iSup_const]
  · intro x hx
    show (⨆ t, ENNReal.ofReal (⟪t, x⟫_ℝ - logMGFVec (fun _ => c) μ t)) = ⊤
    rw [iSup_eq_top]
    intro b hb
    have hq : (0 : ℝ) < ‖x - c‖ ^ 2 := by
      apply sq_pos_of_pos
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr hx
    obtain ⟨N, hN⟩ := exists_nat_gt (b.toReal / ‖x - c‖ ^ 2)
    refine ⟨(N : ℝ) • (x - c), ?_⟩
    have hterm : ENNReal.ofReal (⟪(N : ℝ) • (x - c), x⟫_ℝ -
        logMGFVec (fun _ => c) μ ((N : ℝ) • (x - c))) =
        ENNReal.ofReal ((N : ℝ) * ‖x - c‖ ^ 2) := by
      rw [hΛ]
      congr 1
      rw [← inner_sub_right]
      simp [inner_smul_left]
    rw [hterm, ENNReal.lt_ofReal_iff_toReal_lt (ne_of_lt hb)]
    exact (div_lt_iff₀ hq).mp hN

end MathlibExt.Probability.CramerRateFunction
