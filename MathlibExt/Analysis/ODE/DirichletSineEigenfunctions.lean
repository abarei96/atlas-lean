/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

namespace MathlibExt.Analysis.ODE.DirichletSineEigenfunctions

/-!
# Sine eigenfunctions of the Dirichlet Laplacian on `[0, 1]`

For `k : ℕ+`, the function `u_k(x) = √2 sin(kπx)` satisfies the
homogeneous Sturm-Liouville (Dirichlet eigenvalue) problem

  `-u_k'' = (kπ)² u_k` on `ℝ`,  `u_k(0) = u_k(1) = 0`,

and the family `{u_k}` is orthonormal for the `L²` inner product on
`[0, 1]`, in the concrete interval-integral form
`∫₀¹ u_j u_k = δ_{jk}`.

This is the differential-operator side of the Green's operator story.
Batch 6 (`GreensOperator`) proved the integral-operator side: the Green's
operator for `-d²/dx²` with Dirichlet boundary conditions has eigenvalues
`1 / (k²π²)` with these same functions as eigenvectors. The eigenvalue
equation for the differential operator itself, the Dirichlet boundary
values, nonvanishing, and the orthonormality were not proved there, and
the Sturm-Liouville batches (Batch 4 uniqueness, Batch 14 existence)
prove existence and uniqueness for the inhomogeneous problem with a
general potential `V`, without exhibiting any eigenfunctions. Nothing
here is in the pinned Mathlib: Mathlib has the derivatives of `sin` and
`cos` and the fundamental theorem of calculus, but no sine-eigenfunction
statement for the Dirichlet Laplacian.

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`,
the Green's operator / sine-basis material (the target stating that the
Green's operator has orthonormal eigenvectors `u_k(x) = √2 sin(kπx)`
with eigenvalues `λ_k = 1 / (k²π²)`) and the Sturm-Liouville section
(`-u'' + Vu = f` with `u(0) = u(1) = 0`). The statements below are the
`V = 0`, `f = 0` eigenvalue problem for that operator, proved from
scratch.
-/

/-- The `k`-th sine eigenfunction for the Dirichlet Laplacian on `[0, 1]`:
`u_k(x) = √2 sin(kπx)`. -/
noncomputable def dirichletSine (k : ℕ+) : ℝ → ℝ :=
  fun x => Real.sqrt 2 * Real.sin ((k : ℝ) * Real.pi * x)

/-- The `k`-th Dirichlet eigenvalue: `λ_k = (kπ)²`, the eigenvalue of
`-d²/dx²` for the eigenfunction `dirichletSine k`. -/
noncomputable def dirichletLaplacianEigenvalue (k : ℕ+) : ℝ :=
  ((k : ℝ) * Real.pi) ^ 2

/-- First derivative of the `k`-th sine eigenfunction. -/
theorem dirichletSine_hasDerivAt (k : ℕ+) (x : ℝ) :
    HasDerivAt (dirichletSine k)
      (Real.sqrt 2 * ((k : ℝ) * Real.pi) * Real.cos ((k : ℝ) * Real.pi * x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => (k : ℝ) * Real.pi * y) ((k : ℝ) * Real.pi) x := by
    simpa using (hasDerivAt_id x).const_mul ((k : ℝ) * Real.pi)
  have h3 := (h1.sin).const_mul (Real.sqrt 2)
  convert h3 using 1
  · ext y
    simp [dirichletSine, mul_assoc]
  · ring

/-- The derivative of the `k`-th sine eigenfunction, as a function. -/
theorem dirichletSine_deriv (k : ℕ+) (x : ℝ) :
    deriv (dirichletSine k) x =
      Real.sqrt 2 * ((k : ℝ) * Real.pi) * Real.cos ((k : ℝ) * Real.pi * x) :=
  (dirichletSine_hasDerivAt k x).deriv

/-- Second-derivative (eigenvalue) equation for the `k`-th sine
eigenfunction: `u_k'' = -(kπ)² u_k`. -/
theorem dirichletSine_iteratedDeriv_two (k : ℕ+) (x : ℝ) :
    iteratedDeriv 2 (dirichletSine k) x =
      -dirichletLaplacianEigenvalue k * dirichletSine k x := by
  have h2 : iteratedDeriv 2 (dirichletSine k) = deriv (deriv (dirichletSine k)) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2]
  have hderiv : deriv (dirichletSine k) =
      fun y => Real.sqrt 2 * ((k : ℝ) * Real.pi) * Real.cos ((k : ℝ) * Real.pi * y) := by
    funext y
    exact dirichletSine_deriv k y
  rw [hderiv]
  have h1 : HasDerivAt (fun y : ℝ => (k : ℝ) * Real.pi * y) ((k : ℝ) * Real.pi) x := by
    simpa using (hasDerivAt_id x).const_mul ((k : ℝ) * Real.pi)
  have hcos : HasDerivAt (fun y : ℝ => Real.cos ((k : ℝ) * Real.pi * y))
      (-Real.sin ((k : ℝ) * Real.pi * x) * ((k : ℝ) * Real.pi)) x := h1.cos
  have h := hcos.const_mul (Real.sqrt 2 * ((k : ℝ) * Real.pi))
  rw [h.deriv]
  simp [dirichletSine, dirichletLaplacianEigenvalue]
  ring

/-- The Dirichlet eigenvalue equation in Sturm-Liouville form:
`-u_k'' = λ_k u_k` with `λ_k = (kπ)²`. -/
theorem neg_iteratedDeriv_two_eq (k : ℕ+) (x : ℝ) :
    -iteratedDeriv 2 (dirichletSine k) x =
      dirichletLaplacianEigenvalue k * dirichletSine k x := by
  rw [dirichletSine_iteratedDeriv_two]
  ring

/-- Left Dirichlet boundary value: `u_k(0) = 0`. -/
theorem dirichletSine_zero (k : ℕ+) : dirichletSine k 0 = 0 := by
  simp [dirichletSine]

/-- Right Dirichlet boundary value: `u_k(1) = 0`. -/
theorem dirichletSine_one (k : ℕ+) : dirichletSine k 1 = 0 := by
  simp only [dirichletSine]
  have h : (k : ℝ) * Real.pi * (1 : ℝ) = (k : ℝ) * Real.pi := by ring
  rw [h, Real.sin_nat_mul_pi]
  simp

/-- The sine eigenfunctions are smooth. -/
theorem dirichletSine_contDiff (k : ℕ+) : ContDiff ℝ ⊤ (dirichletSine k) := by
  unfold dirichletSine
  exact contDiff_const.mul
    (ContDiff.sin ((contDiff_const (c := (k : ℝ) * Real.pi)).mul contDiff_id))

/-- The sine eigenfunctions are nonzero (so they are genuine
eigenfunctions, not the trivial solution). The witness point is
`x = 1 / (2k)`, where `u_k = √2`. -/
theorem dirichletSine_ne_zero (k : ℕ+) : dirichletSine k ≠ 0 := by
  intro h
  have hk : (0 : ℝ) < (k : ℝ) := by exact_mod_cast k.pos
  have hval : dirichletSine k (1 / (2 * (k : ℝ))) = Real.sqrt 2 := by
    have harg : (k : ℝ) * Real.pi * (1 / (2 * (k : ℝ))) = Real.pi / 2 := by
      rw [mul_one_div, div_eq_iff (ne_of_gt (by positivity : (0 : ℝ) < 2 * (k : ℝ)))]
      ring
    unfold dirichletSine
    rw [harg, Real.sin_pi_div_two, mul_one]
  have h0 : dirichletSine k (1 / (2 * (k : ℝ))) = 0 := by
    rw [h]
    rfl
  rw [hval] at h0
  exact (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne' h0

/-- Integral of `cos(mπx)` over `[0, 1]` for an integer `m`: it is `1`
for `m = 0` and `0` otherwise, since `sin(mπ) = 0`. -/
theorem integral_cos_int_mul_pi (m : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.cos ((m : ℝ) * Real.pi * x) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp
  · have hc : (m : ℝ) * Real.pi ≠ 0 := by
      apply mul_ne_zero _ Real.pi_ne_zero
      exact_mod_cast hm
    have hcont : Continuous (fun x : ℝ => Real.cos ((m : ℝ) * Real.pi * x)) :=
      Real.continuous_cos.comp (continuous_const.mul continuous_id)
    have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun y : ℝ => Real.sin ((m : ℝ) * Real.pi * y) / ((m : ℝ) * Real.pi))
          (Real.cos ((m : ℝ) * Real.pi * x)) x := by
      intro x _
      have h1 : HasDerivAt (fun y : ℝ => (m : ℝ) * Real.pi * y) ((m : ℝ) * Real.pi) x := by
        simpa using (hasDerivAt_id x).const_mul ((m : ℝ) * Real.pi)
      have h3 := (h1.sin).div_const ((m : ℝ) * Real.pi)
      convert h3 using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable 0 1)]
    simp [hm]

/-- Orthonormality of the sine eigenfunctions on `[0, 1]`:
`∫₀¹ u_j u_k = δ_{jk}`. The proof is the product-to-sum identity
`2 sin A sin B = cos(A - B) - cos(A + B)` plus `integral_cos_int_mul_pi`. -/
theorem dirichletSine_orthogonal (j k : ℕ+) :
    ∫ x in (0 : ℝ)..1, dirichletSine j x * dirichletSine k x =
      if j = k then 1 else 0 := by
  have hsub : ∀ x : ℝ, (j : ℝ) * Real.pi * x - (k : ℝ) * Real.pi * x =
      (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * Real.pi * x := by
    intro x
    push_cast
    ring
  have hadd : ∀ x : ℝ, (j : ℝ) * Real.pi * x + (k : ℝ) * Real.pi * x =
      (((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * Real.pi * x := by
    intro x
    push_cast
    ring
  have hpoint : ∀ x : ℝ, dirichletSine j x * dirichletSine k x =
      Real.cos ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * Real.pi * x) -
        Real.cos ((((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * Real.pi * x) := by
    intro x
    simp only [dirichletSine]
    have h := Real.two_mul_sin_mul_sin ((j : ℝ) * Real.pi * x) ((k : ℝ) * Real.pi * x)
    rw [hsub x, hadd x] at h
    have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    calc Real.sqrt 2 * Real.sin ((j : ℝ) * Real.pi * x) *
          (Real.sqrt 2 * Real.sin ((k : ℝ) * Real.pi * x))
        = (Real.sqrt 2 * Real.sqrt 2) *
          (Real.sin ((j : ℝ) * Real.pi * x) * Real.sin ((k : ℝ) * Real.pi * x)) := by ring
      _ = 2 * Real.sin ((j : ℝ) * Real.pi * x) * Real.sin ((k : ℝ) * Real.pi * x) := by
          rw [hsqrt]
          ring
      _ = Real.cos ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * Real.pi * x) -
            Real.cos ((((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * Real.pi * x) := h
  have hcont1 : Continuous
      (fun x : ℝ => Real.cos ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * Real.pi * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hcont2 : Continuous
      (fun x : ℝ => Real.cos ((((j : ℤ) + (k : ℤ) : ℤ) : ℝ) * Real.pi * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  rw [intervalIntegral.integral_congr (fun x _ => hpoint x),
    intervalIntegral.integral_sub (hcont1.intervalIntegrable 0 1)
      (hcont2.intervalIntegrable 0 1),
    integral_cos_int_mul_pi ((j : ℤ) - (k : ℤ)),
    integral_cos_int_mul_pi ((j : ℤ) + (k : ℤ))]
  by_cases hjk : j = k
  · subst hjk
    simp
  · have hne1 : (j : ℤ) - (k : ℤ) ≠ 0 := by
      intro h
      apply hjk
      have hcast : (j : ℤ) = (k : ℤ) := by omega
      exact_mod_cast hcast
    have hne2 : (j : ℤ) + (k : ℤ) ≠ 0 := by
      have hj : (0 : ℤ) < (j : ℤ) := by exact_mod_cast j.pos
      have hk : (0 : ℤ) < (k : ℤ) := by exact_mod_cast k.pos
      omega
    simp [hjk, hne1, hne2]

/-- Normalization: `∫₀¹ u_k² = 1`. -/
theorem dirichletSine_sq_integral (k : ℕ+) :
    ∫ x in (0 : ℝ)..1, (dirichletSine k x) ^ 2 = 1 := by
  have h := dirichletSine_orthogonal k k
  simpa [pow_two] using h

end MathlibExt.Analysis.ODE.DirichletSineEigenfunctions
