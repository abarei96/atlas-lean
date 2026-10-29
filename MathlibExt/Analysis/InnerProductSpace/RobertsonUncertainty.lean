/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Robertson–Schrödinger uncertainty principle for bounded self-adjoint operators

For self-adjoint operators `A B` on a complex Hilbert space and a unit vector `x`,
let `a = ⟪A x, x⟫` and `b = ⟪B x, x⟫` be the expectation values, and let
`u = A x - a • x`, `v = B x - b • x` be the centered vectors. The
**Robertson–Schrödinger uncertainty principle** says

  `‖u‖² * ‖v‖² ≥ (re ⟪u, v⟫)² + (1/4) * ‖⟪[A, B] x, x⟫‖²`,

where `[A, B] = A ∘L B - B ∘L A` is the commutator. Dropping the
covariance term `(re ⟪u, v⟫)²` gives Robertson's original form
(`robertson`):

  `‖u‖² * ‖v‖² ≥ (1/4) * ‖⟪[A, B] x, x⟫‖²`.

The key identity is `commutator_inner`: the commutator expectation is the
skew part of `⟪u, v⟫`, hence purely imaginary (`commutator_inner_re`), with
norm `2 * |im ⟪u, v⟫|` (`norm_commutator_inner_eq`). The variance of `A` in
the state `x` is `variance A x = ‖u‖²`, and it also equals
`re ⟪(A * A) x, x⟫ - a²` (`variance_eq`).

This is a companion to the Hilbert-space / spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(self-adjoint operators, expectation values `⟪A x, x⟫`). It is not one of
the 72 v1 targets, and it is in neither the pinned Mathlib (which has no
uncertainty principle for operators) nor base MathlibExt (which has no
uncertainty content at all; the Donoho–Stark principle for finite abelian
groups is batch 73's PR, a different setting). The position–momentum form,
with unbounded operators, is not claimed here.

Sources: H. P. Robertson, "The uncertainty principle", Physical Review 34
(1929), 163–164; E. Schrödinger, "Zum Heisenbergschen Unschärfeprinzip",
Sitzungsberichte der Preußischen Akademie der Wissenschaften (1930),
296–303; J. J. Sakurai, *Modern Quantum Mechanics*, §1.4.

## Main declarations

* `meanValue` : the expectation value `(⟪A x, x⟫).re`.
* `centered` : the centered vector `A x - meanValue A x • x`.
* `variance` : the variance `‖centered A x‖²`.
* `commutator_inner` : commutator expectation as a skew inner product.
* `norm_commutator_inner_eq` : its norm is `2 * |im ⟪u, v⟫|`.
* `schrodinger` : the Robertson–Schrödinger inequality.
* `robertson` : Robertson's inequality.
* `variance_eq` : variance via `re ⟪(A * A) x, x⟫ - mean²`.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.RobertsonUncertainty

open scoped _root_.InnerProductSpace InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The **expectation value** of a bounded operator `A` in the state `x`:
the real part of `⟪A x, x⟫`. For self-adjoint `A` this is the whole
inner product (`inner_self_of_isSelfAdjoint`). -/
noncomputable def meanValue (A : E →L[ℂ] E) (x : E) : ℝ :=
  (⟪A x, x⟫_ℂ).re

/-- The **centered vector** of `A` at `x`: `A x` with its expectation
value removed. Its squared norm is the variance (`variance`). -/
noncomputable def centered (A : E →L[ℂ] E) (x : E) : E :=
  A x - (meanValue A x : ℂ) • x

/-- The **variance** of a bounded operator `A` in the state `x`:
the squared norm of the centered vector. -/
noncomputable def variance (A : E →L[ℂ] E) (x : E) : ℝ :=
  ‖centered A x‖ ^ 2

omit [CompleteSpace E] in
theorem variance_nonneg (A : E →L[ℂ] E) (x : E) : 0 ≤ variance A x :=
  sq_nonneg _

/-- For a self-adjoint operator, the expectation inner product is real:
it equals its real part, the mean value. -/
theorem inner_self_of_isSelfAdjoint {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (x : E) :
    ⟪A x, x⟫_ℂ = (meanValue A x : ℂ) := by
  have hAdj : A† = A := ContinuousLinearMap.isSelfAdjoint_iff'.mp hA
  have hsym : ⟪A x, x⟫_ℂ = ⟪x, A x⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right A x x, hAdj]
  have him : (⟪A x, x⟫_ℂ).im = 0 := by
    have hconj := inner_conj_symm (𝕜 := ℂ) (A x) x
    rw [← hsym] at hconj
    have h := congrArg Complex.im hconj
    rw [Complex.conj_im] at h
    linarith
  apply Complex.ext
  · simp [meanValue]
  · simp [meanValue, him]

/-- For a self-adjoint operator, the flipped expectation inner product
is also the (real) mean value. -/
theorem inner_right_of_isSelfAdjoint {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (x : E) :
    ⟪x, A x⟫_ℂ = (meanValue A x : ℂ) := by
  rw [← inner_conj_symm (𝕜 := ℂ) x (A x), inner_self_of_isSelfAdjoint hA x]
  simp

/-- Moving a self-adjoint operator across an inner product. -/
theorem inner_apply_of_isSelfAdjoint {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) (x y : E) :
    ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ := by
  rw [← ContinuousLinearMap.adjoint_inner_right A x y,
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hA]

/-- The inner product of two centered vectors, for self-adjoint
operators at a unit vector: the uncentered inner product minus the
product of the mean values. -/
theorem inner_centered {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {x : E} (hx : ‖x‖ = 1) :
    ⟪centered A x, centered B x⟫_ℂ
      = ⟪A x, B x⟫_ℂ - (meanValue A x : ℂ) * (meanValue B x : ℂ) := by
  rw [centered, centered, inner_sub_left, inner_sub_right, inner_sub_right,
    inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
    inner_self_of_isSelfAdjoint hA x, inner_right_of_isSelfAdjoint hB x,
    inner_self_eq_norm_sq_to_K, hx]
  simp [Complex.conj_ofReal]
  ring

/-- The commutator expectation is the skew part of the inner product of
the centered vectors. -/
theorem commutator_inner {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {x : E} (hx : ‖x‖ = 1) :
    ⟪(A ∘L B - B ∘L A) x, x⟫_ℂ
      = ⟪centered B x, centered A x⟫_ℂ - ⟪centered A x, centered B x⟫_ℂ := by
  rw [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, inner_sub_left,
    inner_apply_of_isSelfAdjoint hA (B x) x, inner_apply_of_isSelfAdjoint hB (A x) x,
    inner_centered hB hA hx, inner_centered hA hB hx]
  ring

/-- The commutator expectation of two self-adjoint operators is purely
imaginary: its real part vanishes. -/
theorem commutator_inner_re {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {x : E} (hx : ‖x‖ = 1) :
    (⟪(A ∘L B - B ∘L A) x, x⟫_ℂ).re = 0 := by
  rw [commutator_inner hA hB hx, Complex.sub_re]
  have h := congrArg Complex.re
    (inner_conj_symm (𝕜 := ℂ) (centered A x) (centered B x))
  rw [Complex.conj_re] at h
  rw [h]
  exact sub_self _

/-- The squared norm of the commutator expectation is four times the
squared imaginary part of the centered inner product. -/
theorem norm_sq_commutator_inner {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    (hB : IsSelfAdjoint B) {x : E} (hx : ‖x‖ = 1) :
    ‖⟪(A ∘L B - B ∘L A) x, x⟫_ℂ‖ ^ 2
      = 4 * (⟪centered A x, centered B x⟫_ℂ).im ^ 2 := by
  have hconj : ⟪centered B x, centered A x⟫_ℂ
      = starRingEnd ℂ ⟪centered A x, centered B x⟫_ℂ :=
    (inner_conj_symm (𝕜 := ℂ) (centered B x) (centered A x)).symm
  rw [commutator_inner hA hB hx, hconj, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- The commutator expectation has norm twice the absolute imaginary
part of the centered inner product. -/
theorem norm_commutator_inner_eq {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A)
    (hB : IsSelfAdjoint B) {x : E} (hx : ‖x‖ = 1) :
    ‖⟪(A ∘L B - B ∘L A) x, x⟫_ℂ‖
      = 2 * |(⟪centered A x, centered B x⟫_ℂ).im| := by
  have hsq := norm_sq_commutator_inner hA hB hx
  have h2 : (2 * |(⟪centered A x, centered B x⟫_ℂ).im|) ^ 2
      = 4 * (⟪centered A x, centered B x⟫_ℂ).im ^ 2 := by
    rw [mul_pow, sq_abs]
    norm_num
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp (hsq.trans h2.symm)

/-- The **Robertson–Schrödinger uncertainty principle**: the product of
the variances is at least the squared covariance plus a quarter of the
squared norm of the commutator expectation. -/
theorem schrodinger {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {x : E} (hx : ‖x‖ = 1) :
    (⟪centered A x, centered B x⟫_ℂ).re ^ 2
        + (1 / 4) * ‖⟪(A ∘L B - B ∘L A) x, x⟫_ℂ‖ ^ 2
      ≤ variance A x * variance B x := by
  have hCS : ‖⟪centered A x, centered B x⟫_ℂ‖ ≤ ‖centered A x‖ * ‖centered B x‖ :=
    norm_inner_le_norm _ _
  have hCS2 : ‖⟪centered A x, centered B x⟫_ℂ‖ ^ 2 ≤ variance A x * variance B x := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hCS 2
    rwa [mul_pow] at h
  have hnormSq : ‖⟪centered A x, centered B x⟫_ℂ‖ ^ 2
      = (⟪centered A x, centered B x⟫_ℂ).re ^ 2
        + (⟪centered A x, centered B x⟫_ℂ).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  rw [norm_sq_commutator_inner hA hB hx]
  linarith [hCS2, hnormSq]

/-- **Robertson's uncertainty principle**: the product of the variances
is at least a quarter of the squared norm of the commutator
expectation. -/
theorem robertson {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {x : E} (hx : ‖x‖ = 1) :
    (1 / 4) * ‖⟪(A ∘L B - B ∘L A) x, x⟫_ℂ‖ ^ 2
      ≤ variance A x * variance B x := by
  have h := schrodinger hA hB hx
  have h0 : 0 ≤ (⟪centered A x, centered B x⟫_ℂ).re ^ 2 := sq_nonneg _
  linarith

omit [CompleteSpace E] in
/-- The commutator of commuting operators vanishes. -/
theorem commutator_eq_zero_of_commute {A B : E →L[ℂ] E} (h : Commute A B) :
    A ∘L B - B ∘L A = 0 := by
  rw [sub_eq_zero]
  ext x
  have h2 : (A ∘L B) x = (B ∘L A) x := by
    have hcongr := congrArg (fun T : E →L[ℂ] E => T x) h.eq
    simpa [mul_apply_eq_comp] using hcongr
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  exact h2

/-- The variance is the second moment minus the squared mean. -/
theorem variance_eq {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {x : E} (hx : ‖x‖ = 1) :
    variance A x = (⟪(A * A) x, x⟫_ℂ).re - (meanValue A x) ^ 2 := by
  have hAA : ⟪A x, A x⟫_ℂ = ⟪(A * A) x, x⟫_ℂ := by
    rw [mul_apply_eq_comp,
      ← ContinuousLinearMap.adjoint_inner_left A x (A x),
      ContinuousLinearMap.isSelfAdjoint_iff'.mp hA]
  have hinner : ⟪centered A x, centered A x⟫_ℂ
      = ⟪(A * A) x, x⟫_ℂ - (meanValue A x : ℂ) ^ 2 := by
    rw [centered, inner_sub_left, inner_sub_right, inner_sub_right,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
      inner_self_of_isSelfAdjoint hA x, inner_right_of_isSelfAdjoint hA x,
      hAA, inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x, hx]
    simp [Complex.conj_ofReal]
    ring
  rw [variance, ← inner_self_eq_norm_sq (𝕜 := ℂ), hinner]
  show (⟪(A * A) x, x⟫_ℂ - (meanValue A x : ℂ) ^ 2).re
      = (⟪(A * A) x, x⟫_ℂ).re - (meanValue A x) ^ 2
  rw [Complex.sub_re]
  simp [← Complex.ofReal_pow]

end MathlibExt.Analysis.InnerProductSpace.RobertsonUncertainty
