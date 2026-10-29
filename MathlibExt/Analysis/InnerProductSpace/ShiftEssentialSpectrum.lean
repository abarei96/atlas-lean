/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Analysis.Normed.Operator.Fredholm.Open
public import Mathlib.Algebra.Module.LinearMap.Index

import Mathlib.Algebra.Module.LinearMap.FiniteRange
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Essential spectrum of the unilateral shift on `ℓ²(ℕ, 𝕜)`

Let `S` be the unilateral (forward) shift on `ℓ²(ℕ, 𝕜)`. Its
spectrum is the closed unit disc (see e.g. Reed–Simon, *Methods of
Modern Mathematical Physics I: Functional Analysis*, Section VII.2).
This file computes the smaller **essential spectrum**: the set of
`μ` for which `S - μ • 1` is not a Fredholm operator.

* `essentialSpectrum_shiftCLM`: the essential spectrum of `S` is the
  unit circle `Metric.sphere 0 1`.
* `isFredholm_shift_sub_smul_one_of_norm_lt_one`: for `‖μ‖ < 1`,
  `S - μ • 1` is Fredholm of index `-1`.
* `isFredholm_shift_sub_smul_one_of_one_lt_norm`: for `‖μ‖ > 1`,
  `S - μ • 1` is Fredholm of index `0` (it is a unit).
* `not_isFredholm_shift_sub_smul_one_of_norm_eq_one`: for `‖μ‖ = 1`,
  `S - μ • 1` is not Fredholm, because the truncated geometric
  vectors `(1, μ̄, μ̄², …, μ̄ᴺ, 0, …)` are approximate eigenvectors
  with `‖(S - μ) v_N‖² = 2` while `‖v_N‖² = N + 1`, so `S - μ • 1`
  is not bounded below, whereas a Fredholm operator with trivial
  kernel is.

This is a companion to the Hilbert-space / spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(the spectral theorem, the Fredholm alternative). It is not one of
the 72 v1 targets, and the essential spectrum is not in the pinned
Mathlib (which has the general Fredholm-operator API
`ContinuousLinearMap.IsFredholm` but no essential spectrum) or in
base MathlibExt. The shift operators are developed here from scratch
so that this file is self-contained.

## Main declarations

* `essentialSpectrum`: `μ` is in the essential spectrum of `T` iff
  `T - μ • 1` is not a Fredholm operator.
* `shiftCLM`, `backwardCLM`: the unilateral and backward shifts as
  bounded operators on `ℓ²(ℕ, 𝕜)`.
* `essentialSpectrum_shiftCLM`: the essential spectrum of the shift
  is the unit circle.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.ShiftEssentialSpectrum

open Filter Topology Set
open scoped _root_.lp ENNReal
open scoped LinearMap.FiniteRangeSetoid

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The **essential spectrum** of a bounded operator `T`: the set of
scalars `μ` for which `T - μ • 1` is not a Fredholm operator. -/
def essentialSpectrum {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T : E →L[𝕜] E) : Set 𝕜 :=
  {μ | ¬ (T - μ • 1).IsFredholm}

/-- The forward-shift function on sequences: insert `0` at `0` and shift up by one. -/
def shiftFun (x : ℕ → 𝕜) : ℕ → 𝕜
  | 0 => 0
  | n + 1 => x n

/-- The backward-shift function on sequences: drop coordinate `0` and shift down by one. -/
def backwardFun (x : ℕ → 𝕜) (i : ℕ) : 𝕜 := x (i + 1)

@[simp] theorem shiftFun_zero (x : ℕ → 𝕜) : shiftFun x 0 = 0 := rfl

@[simp] theorem shiftFun_succ (x : ℕ → 𝕜) (n : ℕ) : shiftFun x (n + 1) = x n := rfl

omit [RCLike 𝕜] in
@[simp] theorem backwardFun_apply (x : ℕ → 𝕜) (i : ℕ) : backwardFun x i = x (i + 1) :=
  rfl

/-- The shifted sequence of an `ℓ²` sequence is in `ℓ²`: its squared
norms are the squared norms of the original sequence, shifted by one. -/
theorem memℓp_shiftFun {x : ℓ²(ℕ, 𝕜)} : Memℓp (shiftFun (x : ℕ → 𝕜)) 2 := by
  apply memℓp_gen
  have h := (lp.memℓp x).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have h' : Summable (fun n => ‖shiftFun (x : ℕ → 𝕜) (n + 1)‖ ^ (2 : ℝ≥0∞).toReal) := by
    simpa only [shiftFun_succ] using h
  exact (summable_nat_add_iff 1).mp h'

/-- The backward-shifted sequence of an `ℓ²` sequence is in `ℓ²`: its squared
norms are a tail of the squared norms of the original sequence. -/
theorem memℓp_backwardFun {x : ℓ²(ℕ, 𝕜)} : Memℓp (backwardFun (x : ℕ → 𝕜)) 2 := by
  apply memℓp_gen
  have h := (lp.memℓp x).summable (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  have h' : Summable (fun n => ‖backwardFun (x : ℕ → 𝕜) n‖ ^ (2 : ℝ≥0∞).toReal) := by
    simpa only [backwardFun_apply] using (summable_nat_add_iff 1).mpr h
  exact h'

/-- The forward shift as a linear map. -/
noncomputable def shiftLinMap : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) where
  toFun x := ⟨shiftFun (x : ℕ → 𝕜), memℓp_shiftFun⟩
  map_add' x y := by
    apply lp.ext
    funext i
    cases i with
    | zero =>
        simp only [lp.coeFn_add, shiftFun_zero, Pi.add_apply, add_zero]
    | succ n => simp only [lp.coeFn_add, shiftFun_succ, Pi.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext i
    cases i with
    | zero =>
        simp only [lp.coeFn_smul, shiftFun_zero, Pi.smul_apply, smul_zero]
    | succ n =>
        simp only [lp.coeFn_smul, shiftFun_succ, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]

/-- The backward shift as a linear map. -/
noncomputable def backwardLinMap : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜) where
  toFun x := ⟨backwardFun (x : ℕ → 𝕜), memℓp_backwardFun⟩
  map_add' x y := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_add, backwardFun_apply, Pi.add_apply]
  map_smul' c x := by
    apply lp.ext
    funext i
    simp only [lp.coeFn_smul, backwardFun_apply, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]

/-- The squared norms of a shifted sequence sum to the squared norms of
the original sequence. -/
theorem tsum_shiftFun_norm (x : ℓ²(ℕ, 𝕜)) :
    ∑' i, ‖shiftFun (x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal =
      ∑' i, ‖(x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal := by
  have hs : Summable (fun i => ‖shiftFun (x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal) :=
    memℓp_shiftFun.summable (by simp)
  rw [hs.tsum_eq_zero_add]
  simp only [shiftFun_zero, shiftFun_succ, norm_zero,
    Real.zero_rpow (by simp : (2 : ℝ≥0∞).toReal ≠ 0), zero_add]

/-- The squared norms of a backward-shifted sequence sum to at most the
squared norms of the original sequence: they are a tail sum. -/
theorem tsum_backwardFun_norm_le (x : ℓ²(ℕ, 𝕜)) :
    ∑' i, ‖backwardFun (x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal ≤
      ∑' i, ‖(x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal := by
  have hs : Summable (fun i => ‖(x : ℕ → 𝕜) i‖ ^ (2 : ℝ≥0∞).toReal) :=
    (lp.memℓp x).summable (by simp)
  rw [hs.tsum_eq_zero_add]
  simp only [backwardFun_apply]
  exact le_add_of_nonneg_left (Real.rpow_nonneg (norm_nonneg _) _)

/-- The forward shift preserves norms. -/
theorem norm_shiftLinMap_apply (x : ℓ²(ℕ, 𝕜)) : ‖shiftLinMap x‖ = ‖x‖ := by
  have hpow : ‖shiftLinMap x‖ ^ (2 : ℝ≥0∞).toReal = ‖x‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (shiftLinMap x),
      lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x]
    exact tsum_shiftFun_norm x
  have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [hexp, Real.rpow_two, Real.rpow_two] at hpow
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hpow

/-- The backward shift does not increase norms. -/
theorem norm_backwardLinMap_apply_le (x : ℓ²(ℕ, 𝕜)) : ‖backwardLinMap x‖ ≤ ‖x‖ := by
  have hpow : ‖backwardLinMap x‖ ^ (2 : ℝ≥0∞).toReal ≤ ‖x‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (backwardLinMap x),
      lp.norm_rpow_eq_tsum (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) x]
    exact tsum_backwardFun_norm_le x
  have hexp : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  rw [hexp, Real.rpow_two, Real.rpow_two] at hpow
  exact le_of_sq_le_sq hpow (norm_nonneg _)

/-- The unilateral shift as a bounded operator on `ℓ²(ℕ, 𝕜)`. -/
noncomputable def shiftCLM : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  shiftLinMap.mkContinuous 1 (fun x => by
    rw [one_mul]
    exact le_of_eq (norm_shiftLinMap_apply x))

/-- The backward shift as a bounded operator on `ℓ²(ℕ, 𝕜)`. -/
noncomputable def backwardCLM : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) :=
  backwardLinMap.mkContinuous 1 (fun x => by
    rw [one_mul]
    exact norm_backwardLinMap_apply_le x)

/-- Pointwise action of the unilateral shift. -/
theorem shiftCLM_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    shiftCLM x i = shiftFun (x : ℕ → 𝕜) i :=
  rfl

/-- Pointwise action of the backward shift. -/
theorem backwardCLM_apply (x : ℓ²(ℕ, 𝕜)) (i : ℕ) :
    backwardCLM x i = (x : ℕ → 𝕜) (i + 1) :=
  rfl

/-- The operator norm of the backward shift is at most `1`. -/
theorem norm_backwardCLM_le_one : ‖backwardCLM (𝕜 := 𝕜)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1) ?_
  intro x
  rw [one_mul]
  exact norm_backwardLinMap_apply_le x

/-- Shifting down after shifting up recovers the original sequence. -/
theorem backwardCLM_comp_shiftCLM :
    (backwardCLM (𝕜 := 𝕜)) ∘L (shiftCLM (𝕜 := 𝕜)) = (1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  simp only [ContinuousLinearMap.comp_apply, backwardCLM_apply, shiftCLM_apply,
    one_apply_eq_self]
  cases i with
  | zero => rfl
  | succ n => rfl

/-- The unilateral shift is injective: the backward shift is a left inverse. -/
theorem injective_shiftCLM :
    Function.Injective ⇑(shiftCLM (𝕜 := 𝕜) : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) := by
  apply Function.LeftInverse.injective (g := ⇑(backwardCLM (𝕜 := 𝕜)))
  intro x
  simpa using DFunLike.congr_fun (backwardCLM_comp_shiftCLM (𝕜 := 𝕜)) x

/-- Pointwise action of scalar multiplication on `PreLp`: it is
pointwise, but there is no such named lemma in Mathlib, so we prove
it here by `rfl`. -/
theorem preLp_smul_apply (c : 𝕜) (f : PreLp (fun _ : ℕ => 𝕜)) (i : ℕ) :
    (c • f) i = c • f i :=
  rfl

section Defect

/-- The zeroth standard basis vector of `ℓ²(ℕ, 𝕜)`. -/
noncomputable def e0 : ℓ²(ℕ, 𝕜) := lp.single 2 0 1

@[simp] theorem e0_apply_zero : (e0 (𝕜 := 𝕜) : ℕ → 𝕜) 0 = 1 := lp.single_apply_self _ _ _

theorem e0_apply_succ (n : ℕ) : (e0 (𝕜 := 𝕜) : ℕ → 𝕜) (n + 1) = 0 :=
  lp.single_apply_ne _ _ _ (by omega)

/-- Shifting up after shifting down differs from the identity only in
coordinate `0`: `(S B - 1) x = -(x 0) • e₀`. -/
theorem shift_comp_backward_sub_one_apply (x : ℓ²(ℕ, 𝕜)) :
    ((shiftCLM (𝕜 := 𝕜)) ∘L (backwardCLM (𝕜 := 𝕜)) - 1) x = -(x : ℕ → 𝕜) 0 • e0 := by
  apply lp.ext
  funext i
  cases i with
  | zero =>
      simp only [sub_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self,
        shiftCLM_apply, shiftFun_zero,
        lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, e0_apply_zero, mul_one, zero_sub]
  | succ n =>
      simp only [sub_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self,
        shiftCLM_apply, backwardCLM_apply, shiftFun_succ,
        lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul, e0_apply_succ, mul_zero, sub_self]

/-- The defect `S B - 1` has finite rank: its range lies in the span of `e₀`. -/
theorem defect_hasFiniteRange :
    ((shiftCLM (𝕜 := 𝕜)) ∘L (backwardCLM (𝕜 := 𝕜)) - 1).toLinearMap.HasFiniteRange := by
  rw [LinearMap.hasFiniteRange_iff_range, Submodule.fg_iff_finiteDimensional]
  have hfin : FiniteDimensional 𝕜 (Submodule.span 𝕜 {e0 (𝕜 := 𝕜)}) :=
    (Submodule.fg_iff_finiteDimensional _).mp (Submodule.fg_span_singleton _)
  have hle : LinearMap.range
        ((shiftCLM (𝕜 := 𝕜)) ∘L (backwardCLM (𝕜 := 𝕜)) - 1).toLinearMap ≤
      Submodule.span 𝕜 {e0 (𝕜 := 𝕜)} := by
    intro y hy
    rw [LinearMap.mem_range] at hy
    obtain ⟨x, hx⟩ := hy
    rw [← hx, ContinuousLinearMap.coe_coe, shift_comp_backward_sub_one_apply]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  exact @Submodule.finiteDimensional_of_le 𝕜 _ _ _ _ _ _ hfin hle

end Defect

/-- The unilateral shift is a Fredholm operator: the backward shift is
a quasi-inverse, with defects `0` and the finite-rank `S B - 1`. -/
theorem isFredholm_shiftCLM : (shiftCLM (𝕜 := 𝕜)).IsFredholm := by
  apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := backwardCLM (𝕜 := 𝕜))
  constructor
  · show (↑(backwardCLM (𝕜 := 𝕜)) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)) ∘ₗ
        ↑(shiftCLM (𝕜 := 𝕜)) ≈ LinearMap.id
    rw [LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange]
    have hcomp : (↑(backwardCLM (𝕜 := 𝕜)) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)) ∘ₗ
        ↑(shiftCLM (𝕜 := 𝕜)) = LinearMap.id := by
      refine LinearMap.ext fun x => ?_
      show (backwardCLM (𝕜 := 𝕜)) ((shiftCLM (𝕜 := 𝕜)) x) = x
      have h := DFunLike.congr_fun (backwardCLM_comp_shiftCLM (𝕜 := 𝕜)) x
      simpa using h
    rw [hcomp, sub_self]
    exact LinearMap.HasFiniteRange.zero
  · show (↑(shiftCLM (𝕜 := 𝕜)) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)) ∘ₗ
        ↑(backwardCLM (𝕜 := 𝕜)) ≈ LinearMap.id
    rw [LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange]
    have hsub : (↑(shiftCLM (𝕜 := 𝕜)) : ℓ²(ℕ, 𝕜) →ₗ[𝕜] ℓ²(ℕ, 𝕜)) ∘ₗ
        ↑(backwardCLM (𝕜 := 𝕜)) - LinearMap.id =
        ((shiftCLM (𝕜 := 𝕜)) ∘L (backwardCLM (𝕜 := 𝕜)) - 1).toLinearMap := by
      ext x
      simp [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_sub,
        ContinuousLinearMap.toLinearMap_one]
    rw [hsub]
    exact defect_hasFiniteRange

section EvalZero

/-- Evaluation at coordinate `0`, as a linear functional on `ℓ²`. -/
noncomputable def evalZero : ℓ²(ℕ, 𝕜) →ₗ[𝕜] 𝕜 where
  toFun x := (x : ℕ → 𝕜) 0
  map_add' x y := by simp
  map_smul' c x := by simp [lp.coeFn_smul, smul_eq_mul, RingHom.id_apply]

/-- Pointwise action of evaluation at `0`. -/
theorem evalZero_apply (x : ℓ²(ℕ, 𝕜)) : evalZero x = (x : ℕ → 𝕜) 0 := rfl

/-- Evaluation at `0` is surjective: `y • e₀` maps to `y`. -/
theorem evalZero_surjective : Function.Surjective (evalZero (𝕜 := 𝕜)) := by
  intro y
  refine ⟨y • e0, ?_⟩
  rw [evalZero_apply]
  simp [smul_eq_mul]

/-- The kernel of evaluation at `0` is the range of the shift: both are
the sequences whose `0`-th coordinate vanishes. -/
theorem ker_evalZero_eq_range_shiftCLM :
    LinearMap.ker (evalZero (𝕜 := 𝕜)) =
      LinearMap.range (shiftCLM (𝕜 := 𝕜)).toLinearMap := by
  ext y
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hy
    rw [evalZero_apply] at hy
    refine ⟨backwardCLM y, ?_⟩
    apply lp.ext
    funext i
    cases i with
    | zero =>
        simp only [ContinuousLinearMap.coe_coe, shiftCLM_apply, shiftFun_zero, hy]
    | succ n =>
        simp only [ContinuousLinearMap.coe_coe, shiftCLM_apply, backwardCLM_apply,
          shiftFun_succ]
  · rintro ⟨x, rfl⟩
    rw [evalZero_apply, ContinuousLinearMap.coe_coe, shiftCLM_apply, shiftFun_zero]

/-- The cokernel of the shift is one-dimensional. -/
theorem finrank_quotient_range_shiftCLM :
    Module.finrank 𝕜 (ℓ²(ℕ, 𝕜) ⧸ LinearMap.range (shiftCLM (𝕜 := 𝕜)).toLinearMap) = 1 := by
  have hsurj : Function.Surjective (evalZero (𝕜 := 𝕜)) := evalZero_surjective
  have heq := LinearEquiv.finrank_eq
    (LinearMap.quotKerEquivOfSurjective (evalZero (𝕜 := 𝕜)) hsurj)
  rw [ker_evalZero_eq_range_shiftCLM] at heq
  rw [heq, Module.finrank_self]

/-- The Fredholm index of the unilateral shift is `-1`: it is
injective, and its cokernel has dimension `1`. -/
theorem index_shiftCLM : (shiftCLM (𝕜 := 𝕜)).index = -1 := by
  have hinj : Function.Injective (shiftCLM (𝕜 := 𝕜)).toLinearMap :=
    injective_shiftCLM
  rw [LinearMap.index_of_injective hinj, finrank_quotient_range_shiftCLM]
  norm_num

end EvalZero

section ShiftSub

/-- Pointwise action of `1 - μ • B`. -/
theorem one_sub_smul_backward_apply (μ : 𝕜) (x : ℓ²(ℕ, 𝕜)) (j : ℕ) :
    ((1 - μ • backwardCLM (𝕜 := 𝕜)) x : ℕ → 𝕜) j =
      (x : ℕ → 𝕜) j - μ * (x : ℕ → 𝕜) (j + 1) := by
  simp only [sub_apply, smul_apply, one_apply_eq_self, lp.coeFn_sub, lp.coeFn_smul,
    Pi.sub_apply, Pi.smul_apply, backwardCLM_apply, smul_eq_mul]

/-- The key factorization: `S - μ = S (1 - μ B) + μ (S B - 1)`. -/
theorem shift_sub_smul_one_eq (μ : 𝕜) :
    shiftCLM (𝕜 := 𝕜) - μ • 1 =
      shiftCLM (𝕜 := 𝕜) ∘L (1 - μ • backwardCLM (𝕜 := 𝕜)) +
        μ • (shiftCLM (𝕜 := 𝕜) ∘L backwardCLM (𝕜 := 𝕜) - 1) := by
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  cases i with
  | zero =>
      simp only [sub_apply, smul_apply, one_apply_eq_self,
        ContinuousLinearMap.comp_apply, add_apply, lp.coeFn_sub, lp.coeFn_add,
        lp.coeFn_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, shiftCLM_apply, shiftFun_zero,
        zero_sub, zero_add, mul_neg]
  | succ n =>
      simp only [sub_apply, smul_apply, one_apply_eq_self,
        ContinuousLinearMap.comp_apply, add_apply, lp.coeFn_sub, lp.coeFn_add,
        lp.coeFn_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, shiftCLM_apply, backwardCLM_apply, shiftFun_succ,
        sub_self, mul_zero, add_zero]

/-- `S - μ • 1` has trivial kernel for every `μ`: the coordinate
equations force every coordinate to vanish. -/
theorem injective_shift_sub (μ : 𝕜) :
    Function.Injective ⇑(shiftCLM (𝕜 := 𝕜) - μ • 1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) := by
  rw [← ContinuousLinearMap.coe_coe, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have heq : ∀ m, shiftFun (x : ℕ → 𝕜) m = μ * (x : ℕ → 𝕜) m := by
    intro m
    have hm := congr_fun (congr_arg (fun z : ℓ²(ℕ, 𝕜) => (z : ℕ → 𝕜)) hx) m
    simp only [ContinuousLinearMap.coe_coe, sub_apply, smul_apply,
      one_apply_eq_self, shiftCLM_apply, lp.coeFn_sub, lp.coeFn_smul, lp.coeFn_zero,
      Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, sub_eq_zero] at hm
    exact hm
  apply lp.ext
  funext n
  simp only [lp.coeFn_zero, Pi.zero_apply]
  induction n with
  | zero =>
      by_cases hμ0 : μ = 0
      · have h1 := heq 1
        rw [hμ0, shiftFun_succ, zero_mul] at h1
        exact h1
      · have h0 := heq 0
        rw [shiftFun_zero] at h0
        have hmul : μ * (x : ℕ → 𝕜) 0 = 0 := h0.symm
        rcases mul_eq_zero.mp hmul with h | h
        · exact absurd h hμ0
        · exact h
  | succ n ih =>
      by_cases hμ0 : μ = 0
      · have h := heq (n + 2)
        rw [hμ0, shiftFun_succ, zero_mul] at h
        exact h
      · have h := heq (n + 1)
        rw [shiftFun_succ, ih] at h
        have hmul : μ * (x : ℕ → 𝕜) (n + 1) = 0 := h.symm
        rcases mul_eq_zero.mp hmul with h' | h'
        · exact absurd h' hμ0
        · exact h'

/-- `1 - μ • B` is a unit when `‖μ‖ < 1`, by the Neumann-series
criterion `isUnit_one_sub_of_norm_lt_one`. -/
theorem isUnit_one_sub_smul_backward {μ : 𝕜} (hμ : ‖μ‖ < 1) :
    IsUnit (1 - μ • backwardCLM (𝕜 := 𝕜)) := by
  apply isUnit_one_sub_of_norm_lt_one
  calc ‖μ • backwardCLM (𝕜 := 𝕜)‖ = ‖μ‖ * ‖backwardCLM (𝕜 := 𝕜)‖ := norm_smul _ _
    _ ≤ ‖μ‖ * 1 := mul_le_mul_of_nonneg_left norm_backwardCLM_le_one (norm_nonneg _)
    _ = ‖μ‖ := mul_one _
    _ < 1 := hμ

/-- A unit operator is Fredholm, via `IsHomeomorph` and
`IsInvertible.isFredholm`. -/
theorem isFredholm_of_isUnit {T : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)} (hT : IsUnit T) :
    T.IsFredholm := by
  have hhome : IsHomeomorph T := ContinuousLinearMap.isHomeomorph_of_isUnit hT
  exact (ContinuousLinearMap.IsInvertible.of_isHomeomorph hhome).isFredholm

/-- `1 - μ • B` is Fredholm when `‖μ‖ < 1`. -/
theorem isFredholm_one_sub_smul_backward {μ : 𝕜} (hμ : ‖μ‖ < 1) :
    (1 - μ • backwardCLM (𝕜 := 𝕜)).IsFredholm :=
  isFredholm_of_isUnit (isUnit_one_sub_smul_backward hμ)

/-- For `‖μ‖ < 1`, `S - μ • 1` is Fredholm: it is the Fredholm
operator `S (1 - μ B)` plus the finite-rank operator `μ (S B - 1)`. -/
theorem isFredholm_shift_sub_smul_one_of_norm_lt_one {μ : 𝕜} (hμ : ‖μ‖ < 1) :
    (shiftCLM (𝕜 := 𝕜) - μ • 1).IsFredholm := by
  rw [shift_sub_smul_one_eq μ]
  apply ContinuousLinearMap.IsFredholm.add_hasFiniteRange _ _
  · exact isFredholm_shiftCLM.comp (isFredholm_one_sub_smul_backward hμ)
  · exact (defect_hasFiniteRange (𝕜 := 𝕜)).smul μ

/-- The index of `S - μ • 1` is `-1` for `‖μ‖ < 1`: it is constant
along the segment `S - (t μ) • 1`, `t ∈ [0, 1]`, by local constancy
of the index (`IsFredholm.eventually_nhds_index_eq`), and it equals
`-1` at `t = 0`. -/
theorem index_shift_sub_smul_one_of_norm_lt_one {μ : 𝕜} (hμ : ‖μ‖ < 1) :
    (shiftCLM (𝕜 := 𝕜) - μ • 1).index = -1 := by
  have hfred : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (shiftCLM (𝕜 := 𝕜) - ((t : 𝕜) * μ) • 1).IsFredholm := by
    intro t ht
    apply isFredholm_shift_sub_smul_one_of_norm_lt_one
    rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg ht.1]
    calc t * ‖μ‖ ≤ 1 * ‖μ‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
      _ = ‖μ‖ := one_mul _
      _ < 1 := hμ
  have hcont : ContinuousOn
      (fun t : ℝ => (shiftCLM (𝕜 := 𝕜) - ((t : 𝕜) * μ) • 1).index) (Set.Icc 0 1) := by
    intro t ht
    have h1 : Continuous (fun s : ℝ => (s : 𝕜) * μ) :=
      Continuous.mul RCLike.continuous_ofReal continuous_const
    have h2 : Continuous (fun s : ℝ =>
        algebraMap 𝕜 (ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) ((s : 𝕜) * μ)) :=
      (continuous_algebraMap 𝕜 _).comp h1
    have hγ : Continuous (fun s : ℝ => shiftCLM (𝕜 := 𝕜) -
        algebraMap 𝕜 (ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) ((s : 𝕜) * μ)) :=
      Continuous.sub continuous_const h2
    have hγcont : ContinuousAt (fun s : ℝ => shiftCLM (𝕜 := 𝕜) - ((s : 𝕜) * μ) • 1) t := by
      rw [show (fun s : ℝ => shiftCLM (𝕜 := 𝕜) - ((s : 𝕜) * μ) • 1) =
          (fun s : ℝ => shiftCLM (𝕜 := 𝕜) -
            algebraMap 𝕜 (ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) ((s : 𝕜) * μ)) from
        funext fun s => by rw [Algebra.algebraMap_eq_smul_one]]
      exact hγ.continuousAt
    have hev : ∀ᶠ s in 𝓝[Set.Icc (0 : ℝ) 1] t,
        (shiftCLM (𝕜 := 𝕜) - (RCLike.ofReal s * μ) • 1).index =
          (shiftCLM (𝕜 := 𝕜) - ((t : 𝕜) * μ) • 1).index := by
      have hcont2 : ContinuousWithinAt
          (fun s : ℝ => shiftCLM (𝕜 := 𝕜) - ((s : 𝕜) * μ) • 1) (Set.Icc (0 : ℝ) 1) t :=
        hγcont.continuousWithinAt
      have hev2 : ∀ᶠ y in 𝓝 (shiftCLM (𝕜 := 𝕜) - ((t : 𝕜) * μ) • 1),
          y.index = (shiftCLM (𝕜 := 𝕜) - ((t : 𝕜) * μ) • 1).index :=
        (hfred t ht).eventually_nhds_index_eq
      exact hcont2.eventually hev2
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev) tendsto_const_nhds
  have hconst := isPreconnected_Icc.constant hcont
    (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  simp only [RCLike.ofReal_zero, RCLike.ofReal_one, zero_mul, one_mul] at hconst
  rw [← hconst]
  have hz : (0 : 𝕜) • (1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) = 0 :=
    Module.zero_smul (R := 𝕜) (M := ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) _
  rw [hz]
  have hsub : shiftCLM (𝕜 := 𝕜) - (0 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) = shiftCLM (𝕜 := 𝕜) :=
    sub_zero _
  rw [hsub]
  exact index_shiftCLM

/-- For `‖μ‖ > 1`, `S - μ • 1` is a unit: it equals
`(algebraMap (-μ)) * (1 - μ⁻¹ • S)`, a product of units. -/
theorem isUnit_shift_sub_smul_one_of_one_lt_norm {μ : 𝕜} (hμ : 1 < ‖μ‖) :
    IsUnit (shiftCLM (𝕜 := 𝕜) - μ • 1) := by
  have hμ0 : μ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hμ
    exact absurd hμ (by norm_num)
  have hnormS : ‖shiftCLM (𝕜 := 𝕜)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
      (fun x => by rw [one_mul]; exact le_of_eq (norm_shiftLinMap_apply x))
  have hsmall : IsUnit (1 - μ⁻¹ • shiftCLM (𝕜 := 𝕜)) := by
    apply isUnit_one_sub_of_norm_lt_one
    calc ‖μ⁻¹ • shiftCLM (𝕜 := 𝕜)‖ = ‖μ⁻¹‖ * ‖shiftCLM (𝕜 := 𝕜)‖ := norm_smul _ _
      _ ≤ ‖μ⁻¹‖ * 1 := mul_le_mul_of_nonneg_left hnormS (norm_nonneg _)
      _ = ‖μ‖⁻¹ := by rw [mul_one, norm_inv]
      _ < 1 := inv_lt_one_of_one_lt₀ hμ
  have hscalar : IsUnit (algebraMap 𝕜 (ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) (-μ)) :=
    IsUnit.map (algebraMap 𝕜 (ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)))
      (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hμ0))
  have hprod : algebraMap 𝕜 (ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) (-μ) * (1 - μ⁻¹ • shiftCLM (𝕜 := 𝕜)) =
      shiftCLM (𝕜 := 𝕜) - μ • 1 := by
    ext x
    simp only [mul_apply_eq_comp, sub_apply,
      smul_apply, one_apply_eq_self,
      Algebra.algebraMap_eq_smul_one]
    rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ hμ0, neg_one_smul, sub_neg_eq_add,
      neg_smul, add_comm, sub_eq_add_neg]
  rw [← hprod]
  exact hscalar.mul hsmall

/-- For `‖μ‖ > 1`, `S - μ • 1` is Fredholm, as it is a unit. -/
theorem isFredholm_shift_sub_smul_one_of_one_lt_norm {μ : 𝕜} (hμ : 1 < ‖μ‖) :
    (shiftCLM (𝕜 := 𝕜) - μ • 1).IsFredholm :=
  isFredholm_of_isUnit (isUnit_shift_sub_smul_one_of_one_lt_norm hμ)

/-- For `‖μ‖ > 1`, `S - μ • 1` has index `0`: a unit is bijective. -/
theorem index_shift_sub_smul_one_of_one_lt_norm {μ : 𝕜} (hμ : 1 < ‖μ‖) :
    (shiftCLM (𝕜 := 𝕜) - μ • 1).index = 0 := by
  have hhome : IsHomeomorph ⇑(shiftCLM (𝕜 := 𝕜) - μ • 1) :=
    ContinuousLinearMap.isHomeomorph_of_isUnit
      (isUnit_shift_sub_smul_one_of_one_lt_norm hμ)
  have hbij : Function.Bijective ⇑(shiftCLM (𝕜 := 𝕜) - μ • 1) :=
    (ContinuousLinearMap.IsInvertible.of_isHomeomorph hhome).bijective
  exact LinearMap.index_of_bijective hbij

end ShiftSub

section ApproximateEigenvectors

/-- The truncated geometric sequence `(1, μ̄, μ̄², …, μ̄ᴺ, 0, …)`. -/
def approxFun (μ : 𝕜) (N : ℕ) : ℕ → 𝕜 := fun n => if n ≤ N then (star μ) ^ n else 0

/-- The truncated geometric sequence is in `ℓ²`: it has finite support. -/
theorem memℓp_approxFun (μ : 𝕜) (N : ℕ) : Memℓp (approxFun μ N) 2 := by
  apply memℓp_gen
  apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
  intro n hn
  rw [Finset.mem_range] at hn
  have hle : ¬ n ≤ N := by omega
  simp [approxFun, hle]

/-- The truncated geometric sequence as an `ℓ²` vector. -/
noncomputable def approxVec (μ : 𝕜) (N : ℕ) : ℓ²(ℕ, 𝕜) := ⟨approxFun μ N, memℓp_approxFun μ N⟩

theorem approxVec_apply (μ : 𝕜) (N n : ℕ) :
    (approxVec μ N) n = approxFun μ N n := rfl

/-- The squared norm of the truncated geometric vector is `N + 1`,
when `‖μ‖ = 1`. -/
theorem norm_sq_approxVec {μ : 𝕜} (hμ : ‖μ‖ = 1) (N : ℕ) :
    ‖approxVec μ N‖ ^ 2 = (N + 1 : ℝ) := by
  have hpow := lp.norm_rpow_eq_tsum (p := 2) (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    (approxVec μ N)
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  simp only [h2, Real.rpow_two] at hpow
  rw [hpow]
  rw [tsum_eq_sum (s := Finset.range (N + 1))]
  · have hterm : ∀ i ∈ Finset.range (N + 1), ‖(approxVec μ N) i‖ ^ 2 = 1 := by
      intro i hi
      rw [Finset.mem_range] at hi
      simp only [approxVec_apply, approxFun, ite_eq_left (show i ≤ N from by omega), norm_pow,
        norm_star, hμ, one_pow]
    refine (Finset.sum_congr rfl hterm).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  · intro i hi
    rw [Finset.mem_range] at hi
    simp [approxVec_apply, approxFun, show ¬ i ≤ N from by omega]

/-- The coordinates of `(S - μ • 1)` applied to the truncated
geometric vector: `-μ` at `0`, `(star μ)^N` at `N + 1`, and `0`
elsewhere, when `‖μ‖ = 1`. -/
theorem sub_smul_one_approxVec_apply_zero {μ : 𝕜} (N : ℕ) :
    ((shiftCLM (𝕜 := 𝕜) - μ • 1) (approxVec μ N)) 0 = -μ := by
  simp only [sub_apply, smul_apply, one_apply_eq_self, lp.coeFn_sub, lp.coeFn_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, shiftCLM_apply, shiftFun_zero,
    approxVec_apply, approxFun, ite_eq_left (Nat.zero_le N), pow_zero, mul_one, zero_sub]

theorem sub_smul_one_approxVec_apply_succ {μ : 𝕜} (_hμ : ‖μ‖ = 1) (N : ℕ) :
    ((shiftCLM (𝕜 := 𝕜) - μ • 1) (approxVec μ N)) (N + 1) = (star μ) ^ N := by
  simp only [sub_apply, smul_apply, one_apply_eq_self, lp.coeFn_sub, lp.coeFn_smul,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, shiftCLM_apply, shiftFun_succ,
    approxVec_apply, approxFun, ite_eq_right (by omega : ¬ N + 1 ≤ N), mul_zero, sub_zero,
    ite_eq_left (le_refl N)]

theorem sub_smul_one_approxVec_apply_of_ne {μ : 𝕜} (hμ : ‖μ‖ = 1) (N : ℕ) {m : ℕ}
    (hm0 : m ≠ 0) (hmN : m ≠ N + 1) :
    ((shiftCLM (𝕜 := 𝕜) - μ • 1) (approxVec μ N)) m = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 : ((shiftCLM (𝕜 := 𝕜) - μ • 1) (approxVec μ N)) (k + 1) =
      (approxVec μ N) k - μ * (approxVec μ N) (k + 1) := by
    simp only [sub_apply, smul_apply, one_apply_eq_self, lp.coeFn_sub, lp.coeFn_smul,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, shiftCLM_apply, shiftFun_succ]
  rw [h1]
  by_cases hk : k + 1 ≤ N
  · have hkN : k ≤ N := by omega
    have hstar : μ * star μ = 1 := by
      rw [RCLike.star_def, RCLike.mul_conj, hμ]
      simp
    rw [approxVec_apply, approxVec_apply, approxFun, approxFun, ite_eq_left hk, ite_eq_left hkN,
      pow_succ]
    have key : μ * ((star μ) ^ k * star μ) = (star μ) ^ k := by
      calc μ * ((star μ) ^ k * star μ) = (star μ) ^ k * (μ * star μ) := by ring
        _ = (star μ) ^ k * 1 := by rw [hstar]
        _ = (star μ) ^ k := mul_one _
    rw [key, sub_self]
  · have hkN : ¬ k ≤ N := by omega
    rw [approxVec_apply, approxVec_apply, approxFun, approxFun, ite_eq_right hk, ite_eq_right hkN]
    simp

/-- The squared norm of `(S - μ • 1)` applied to the truncated
geometric vector is `2`, when `‖μ‖ = 1`. -/
theorem norm_sq_sub_smul_one_approxVec {μ : 𝕜} (hμ : ‖μ‖ = 1) (N : ℕ) :
    ‖(shiftCLM (𝕜 := 𝕜) - μ • 1) (approxVec μ N)‖ ^ 2 = 2 := by
  have hpow := lp.norm_rpow_eq_tsum (p := 2) (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
    ((shiftCLM (𝕜 := 𝕜) - μ • 1) (approxVec μ N))
  have h2 : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by simp
  simp only [h2, Real.rpow_two] at hpow
  rw [hpow]
  rw [tsum_eq_sum (s := {0, N + 1})]
  · rw [Finset.sum_pair (by omega : (0 : ℕ) ≠ N + 1),
      sub_smul_one_approxVec_apply_zero, sub_smul_one_approxVec_apply_succ hμ]
    have h1 : ‖-(μ : 𝕜)‖ ^ 2 = 1 := by simp [norm_neg, hμ]
    have h2 : ‖(star μ) ^ N‖ ^ 2 = 1 := by simp [norm_pow, hμ]
    rw [h1, h2]
    norm_num
  · intro i hi
    rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    have hz : ((shiftCLM (𝕜 := 𝕜) - μ • 1) (approxVec μ N)) i = 0 :=
      sub_smul_one_approxVec_apply_of_ne hμ N hi.1 hi.2
    rw [hz]
    simp

/-- For `‖μ‖ = 1`, `S - μ • 1` is not Fredholm: it has trivial kernel
and closed range would make it bounded below, contradicting the
approximate eigenvectors. -/
theorem not_isFredholm_shift_sub_smul_one_of_norm_eq_one {μ : 𝕜} (hμ : ‖μ‖ = 1) :
    ¬ (shiftCLM (𝕜 := 𝕜) - μ • 1).IsFredholm := by
  intro hfred
  have hinj : Function.Injective ⇑(shiftCLM (𝕜 := 𝕜) - μ • 1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜)) :=
    injective_shift_sub μ
  have hclosed : IsClosed (Set.range ⇑(shiftCLM (𝕜 := 𝕜) - μ • 1 : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜))) := by
    have h := hfred.isClosed_range
    rwa [LinearMap.coe_range] at h
  obtain ⟨K, hK⟩ :=
    ContinuousLinearMap.antilipschitz_of_injective_of_isClosed_range
      (shiftCLM (𝕜 := 𝕜) - μ • 1) hinj hclosed
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 2 * (K : ℝ) ^ 2 < (N : ℝ) := exists_nat_gt _
  have hnorm : ‖approxVec μ N‖ = Real.sqrt ((N : ℝ) + 1) := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_approxVec hμ N]
  have hTnorm : ‖(shiftCLM (𝕜 := 𝕜) - μ • 1) (approxVec μ N)‖ = Real.sqrt 2 := by
    rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_sub_smul_one_approxVec hμ N]
  have hanti := hK.le_mul_dist (approxVec μ N) 0
  simp only [map_zero, dist_zero_right] at hanti
  rw [hnorm, hTnorm] at hanti
  have hlt : (K : ℝ) * Real.sqrt 2 < Real.sqrt ((N : ℝ) + 1) := by
    have h1 : (K : ℝ) * Real.sqrt 2 = Real.sqrt ((K : ℝ) ^ 2 * 2) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by exact_mod_cast K.2)]
    rw [h1]
    apply Real.sqrt_lt_sqrt (by positivity)
    have hN' : 2 * (K : ℝ) ^ 2 < (N : ℝ) + 1 := by linarith [hN]
    linarith [hN']
  exact absurd hanti (not_le_of_gt hlt)

end ApproximateEigenvectors

section Main

/-- The essential spectrum of the unilateral shift is the unit circle:
`S - μ • 1` is Fredholm exactly off the circle. -/
theorem essentialSpectrum_shiftCLM :
    essentialSpectrum (shiftCLM (𝕜 := 𝕜)) = Metric.sphere (0 : 𝕜) 1 := by
  ext μ
  simp only [essentialSpectrum, Set.mem_ofPred_eq, Metric.mem_sphere, dist_eq_norm, sub_zero]
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact h (isFredholm_shift_sub_smul_one_of_norm_lt_one hlt)
    · exact h (isFredholm_shift_sub_smul_one_of_one_lt_norm hgt)
  · intro hnorm hfred
    exact not_isFredholm_shift_sub_smul_one_of_norm_eq_one hnorm hfred

/-- Membership form: `μ` is in the essential spectrum of the shift
iff `‖μ‖ = 1`. -/
theorem mem_essentialSpectrum_shiftCLM {μ : 𝕜} :
    μ ∈ essentialSpectrum (shiftCLM (𝕜 := 𝕜)) ↔ ‖μ‖ = 1 := by
  rw [essentialSpectrum_shiftCLM, Metric.mem_sphere, dist_zero_right]

end Main

end MathlibExt.Analysis.InnerProductSpace.ShiftEssentialSpectrum
