/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Circulant matrices are diagonalized by the Fourier basis

A circulant matrix `Matrix.circulant v` over `ZMod n` is the convolution
operator with `v` on the finite cyclic group `ZMod n`: its `(i, j)` entry is
`v (i - j)`. The Fourier vectors
`fourierVec n j = fun i => zeta n ^ (i.val * j.val)`, where
`zeta n = exp (2 * π * I / n)`, are eigenvectors, with eigenvalues
`circulantEigenvalue n v j = ∑ k, v k * zeta n ^ (-(k.val * j.val : ℤ))`.
Consequently the determinant of a circulant matrix is the product of its
Fourier eigenvalues, and the eigenvalues sum to `n * v 0`.

This is the finite-dimensional analogue of the Fourier-series diagonalization
of convolution operators on the circle: in `IntroductionToFunctionalAnalysis`,
Fourier series (Fejér's theorem, Bessel's inequality, Parseval's identity)
play the same role for `L² ([-π, π])`, and the companion slice on Young's
convolution inequality for finite groups treats the same convolution product.
-/

@[expose] public section

namespace MathlibExt.LinearAlgebra.Matrix.CirculantSpectrum

variable {n : ℕ} [NeZero n]

/-- The primitive `n`-th root of unity `exp (2 * π * I / n)`. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

omit [NeZero n] in
private theorem zeta_ne_zero : zeta n ≠ 0 := Complex.exp_ne_zero _

private theorem zeta_isPrimitiveRoot : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n (NeZero.ne n)

private theorem zeta_pow_n : zeta n ^ n = 1 := zeta_isPrimitiveRoot.pow_eq_one

/-- Powers of a root of unity depend only on the exponent modulo `n`. -/
private theorem zeta_pow_eq_of_modEq {a b : ℕ} (h : a ≡ b [MOD n]) :
    zeta n ^ a = zeta n ^ b := by
  have hmod : ∀ m : ℕ, zeta n ^ m = zeta n ^ (m % n) := fun m => by
    conv_lhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, zeta_pow_n, one_pow, one_mul]
  rw [hmod a, hmod b, h]

/-- Integer powers of a root of unity depend only on the exponent modulo `n`. -/
private theorem zeta_zpow_eq_of_intModEq {a b : ℤ} (h : a ≡ b [ZMOD (n : ℤ)]) :
    zeta n ^ a = zeta n ^ b := by
  obtain ⟨c, hc⟩ : (n : ℤ) ∣ b - a := h.dvd
  have ha : a = b - (n : ℤ) * c := by rw [← hc]; ring
  rw [ha, zpow_sub₀ zeta_ne_zero, zpow_mul, zpow_natCast, zeta_pow_n, one_zpow, div_one]

/-- The `val` of a difference in `ZMod n` is congruent to the difference of the
`val`s, as integers modulo `n`. -/
private theorem val_sub_intModEq (a b : ZMod n) :
    ((a - b).val : ℤ) ≡ ((a.val : ℤ) - (b.val : ℤ)) [ZMOD (n : ℤ)] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  push_cast
  simp [ZMod.natCast_val]

/-- Orthogonality of the Fourier characters: summing `zeta ^ (k * d)` over
`k : ZMod n` gives `n` when `n ∣ d` and `0` otherwise. -/
private theorem sum_zeta_zpow_mul_eq (d : ℤ) :
    ∑ k : ZMod n, zeta n ^ (k.val * d) = if (n : ℤ) ∣ d then (n : ℂ) else 0 := by
  by_cases hd : (n : ℤ) ∣ d
  · simp only [hd, ite_true]
    have hterm : ∀ k : ZMod n, zeta n ^ (k.val * d) = 1 := fun k => by
      have hz : zeta n ^ (d : ℤ) = 1 :=
        (zeta_isPrimitiveRoot.zpow_eq_one_iff_dvd d).mpr hd
      calc zeta n ^ (k.val * d) = (zeta n ^ (d : ℤ)) ^ (k.val : ℤ) := by
            rw [← zpow_mul, mul_comm]
        _ = 1 := by rw [hz, one_zpow]
    rw [Finset.sum_congr rfl fun k _ => hterm k]
    simp [ZMod.card]
  · simp only [hd, ite_false]
    have hne : zeta n ^ (d : ℤ) ≠ 1 := by
      rw [Ne, zeta_isPrimitiveRoot.zpow_eq_one_iff_dvd]
      exact hd
    have hsum : ∑ k : ZMod n, zeta n ^ (k.val * d) =
        ∑ k ∈ Finset.range n, (zeta n ^ (d : ℤ)) ^ k := by
      apply Finset.sum_bij (fun k _ => k.val)
      · intro k _
        exact Finset.mem_range.mpr (ZMod.val_lt k)
      · intro a _ b _ h
        exact ZMod.val_injective _ h
      · intro k hk
        exact ⟨(k : ZMod n), Finset.mem_univ _,
          ZMod.val_cast_of_lt (Finset.mem_range.mp hk)⟩
      · intro k _
        rw [← zpow_natCast (zeta n ^ (d : ℤ)) k.val, ← zpow_mul, mul_comm]
    rw [hsum]
    have hgeom := geom_sum_mul (zeta n ^ (d : ℤ)) n
    have hpow : (zeta n ^ (d : ℤ)) ^ n = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm d (n : ℤ), zpow_mul, zpow_natCast,
        zeta_pow_n, one_zpow]
    rw [hpow, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hne)

/-- The `j`-th Fourier vector on `ZMod n`. -/
noncomputable def fourierVec (n : ℕ) [NeZero n] (j : ZMod n) : ZMod n → ℂ :=
  fun i => zeta n ^ (i.val * j.val)

/-- The `j`-th Fourier eigenvalue of the circulant matrix with first column `v`. -/
noncomputable def circulantEigenvalue (n : ℕ) [NeZero n] (v : ZMod n → ℂ) (j : ZMod n) : ℂ :=
  ∑ k : ZMod n, v k * zeta n ^ (-(k.val * j.val : ℤ))

/-- The key exponent identity: the Fourier vector at `i - k` is the Fourier
vector at `i` times the inverse Fourier factor at `k`. -/
private theorem zeta_pow_sub_val (i k j : ZMod n) :
    zeta n ^ ((i - k).val * j.val) =
      zeta n ^ (i.val * j.val) * (zeta n ^ (k.val * j.val))⁻¹ := by
  have hcong : (((i - k).val * j.val : ℕ) : ℤ) ≡
      ((i.val : ℤ) * j.val - (k.val : ℤ) * j.val) [ZMOD (n : ℤ)] := by
    push_cast
    simpa only [sub_mul] using (val_sub_intModEq i k).mul_right (j.val : ℤ)
  calc zeta n ^ ((i - k).val * j.val)
      = zeta n ^ ((((i - k).val * j.val : ℕ) : ℤ)) := (zpow_natCast _ _).symm
    _ = zeta n ^ (((i.val : ℤ) * j.val - (k.val : ℤ) * j.val)) :=
        zeta_zpow_eq_of_intModEq hcong
    _ = zeta n ^ (((i.val * j.val : ℕ) : ℤ)) / zeta n ^ (((k.val * j.val : ℕ) : ℤ)) := by
        rw [← zpow_sub₀ zeta_ne_zero]
        congr 1
    _ = zeta n ^ (i.val * j.val) * (zeta n ^ (k.val * j.val))⁻¹ := by
        rw [zpow_natCast (zeta n) (i.val * j.val), zpow_natCast (zeta n) (k.val * j.val),
          div_eq_mul_inv]

/-- Every Fourier vector is an eigenvector of every circulant matrix. -/
public theorem circulant_mulVec_fourierVec (v : ZMod n → ℂ) (j : ZMod n) :
    Matrix.mulVec (Matrix.circulant v) (fourierVec n j) =
      circulantEigenvalue n v j • fourierVec n j := by
  funext i
  simp only [Matrix.mulVec_apply_eq_sum, Matrix.circulant_apply, Pi.smul_apply, smul_eq_mul,
    fourierVec, circulantEigenvalue]
  have hreindex : ∑ i' : ZMod n, v (i - i') * zeta n ^ (i'.val * j.val) =
      ∑ k : ZMod n, v k * zeta n ^ ((i - k).val * j.val) := by
    refine Fintype.sum_bijective (fun i' => i - i') (Equiv.subLeft i).bijective _ _ ?_
    intro i'
    rw [sub_sub_cancel]
  rw [hreindex,
    Finset.sum_congr rfl (fun k _ => by rw [zeta_pow_sub_val i k j]), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hz : zeta n ^ (-(k.val * j.val : ℤ)) = (zeta n ^ (k.val * j.val))⁻¹ := by
    rw [zpow_neg, show (↑k.val * ↑j.val : ℤ) = ((k.val * j.val : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast]
  rw [hz]
  ring

/-- The Fourier matrix `F i j = zeta ^ (i.val * j.val)`. -/
noncomputable def fourierMatrix (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  fun i j => zeta n ^ (i.val * j.val)

/-- The inverse Fourier matrix, `(1 / n)` times the conjugate Fourier matrix. -/
noncomputable def fourierMatrixInv (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  fun i j => (1 / (n : ℂ)) * zeta n ^ (-(i.val * j.val : ℤ))

/-- The Fourier matrix is invertible, with inverse `fourierMatrixInv`. -/
public theorem fourierMatrix_mul_inv :
    fourierMatrix n * fourierMatrixInv n = (1 : Matrix (ZMod n) (ZMod n) ℂ) := by
  funext i j
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  simp only [Matrix.mul_apply, fourierMatrix, fourierMatrixInv, Matrix.one_apply]
  have hterm : ∀ k : ZMod n,
      zeta n ^ (i.val * k.val) * ((1 / (n : ℂ)) * zeta n ^ (-(k.val * j.val : ℤ))) =
        (1 / (n : ℂ)) * zeta n ^ (((i.val : ℤ) - j.val) * k.val) := by
    intro k
    have h1 : zeta n ^ (i.val * k.val) * zeta n ^ (-(k.val * j.val : ℤ)) =
        zeta n ^ (((i.val : ℤ) - j.val) * k.val) := by
      rw [← zpow_natCast (zeta n) (i.val * k.val), ← zpow_add₀ zeta_ne_zero]
      congr 1
      push_cast
      ring
    calc zeta n ^ (i.val * k.val) * ((1 / (n : ℂ)) * zeta n ^ (-(k.val * j.val : ℤ)))
        = (1 / (n : ℂ)) * (zeta n ^ (i.val * k.val) * zeta n ^ (-(k.val * j.val : ℤ))) := by
          ring
      _ = (1 / (n : ℂ)) * zeta n ^ (((i.val : ℤ) - j.val) * k.val) := by rw [h1]
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum]
  by_cases hij : i = j
  · subst hij
    have hsum : ∑ k : ZMod n, zeta n ^ (((i.val : ℤ) - i.val) * k.val) = (n : ℂ) := by
      simp [ZMod.card]
    rw [ite_eq_left rfl, hsum]
    exact one_div_mul_cancel hn
  · rw [ite_eq_right hij]
    have hdvd : ¬ (n : ℤ) ∣ ((i.val : ℤ) - j.val) := by
      intro h
      apply hij
      have hcast : (((i.val : ℤ) - (j.val : ℤ) : ℤ) : ZMod n) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
      have hcast2 : (i - j : ZMod n) = 0 := by
        have h2 := hcast
        push_cast at h2
        simpa [ZMod.natCast_val] using h2
      exact sub_eq_zero.mp hcast2
    have hsum : ∑ k : ZMod n, zeta n ^ (((i.val : ℤ) - j.val) * k.val) = 0 := by
      have h := sum_zeta_zpow_mul_eq (n := n) ((i.val : ℤ) - j.val)
      rw [ite_eq_right hdvd] at h
      exact (Finset.sum_congr rfl fun k _ => by congr 1; ring).trans h
    rw [hsum, mul_zero]

/-- Circulant matrices are diagonalized by the Fourier matrix. -/
public theorem circulant_mul_fourierMatrix (v : ZMod n → ℂ) :
    Matrix.circulant v * fourierMatrix n =
      fourierMatrix n * Matrix.diagonal (circulantEigenvalue n v) := by
  funext i j
  have h := congrFun (circulant_mulVec_fourierVec (n := n) v j) i
  calc (Matrix.circulant v * fourierMatrix n) i j
      = ∑ k : ZMod n, v (i - k) * zeta n ^ (k.val * j.val) := by
        simp [Matrix.mul_apply, fourierMatrix, Matrix.circulant_apply]
    _ = circulantEigenvalue n v j * zeta n ^ (i.val * j.val) := by
        simpa [Matrix.mulVec_apply_eq_sum, fourierVec, Pi.smul_apply, smul_eq_mul] using h
    _ = (fourierMatrix n * Matrix.diagonal (circulantEigenvalue n v)) i j := by
        rw [Matrix.mul_apply]
        rw [Finset.sum_eq_single j
          (f := fun k => fourierMatrix n i k *
            Matrix.diagonal (circulantEigenvalue n v) k j)
          (fun k _ hk => by rw [Matrix.diagonal_apply, ite_eq_right hk, mul_zero])
          (fun hmem => absurd (Finset.mem_univ j) hmem)]
        simp only [fourierMatrix, Matrix.diagonal_apply]
        rw [ite_true, mul_comm]

/-- The determinant of a circulant matrix is the product of its Fourier eigenvalues. -/
public theorem det_circulant (v : ZMod n → ℂ) :
    (Matrix.circulant v).det = ∏ j, circulantEigenvalue n v j := by
  have hC : Matrix.circulant v =
      fourierMatrix n * Matrix.diagonal (circulantEigenvalue n v) * fourierMatrixInv n := by
    calc Matrix.circulant v = Matrix.circulant v * (fourierMatrix n * fourierMatrixInv n) := by
          rw [fourierMatrix_mul_inv, Matrix.mul_one]
      _ = (Matrix.circulant v * fourierMatrix n) * fourierMatrixInv n := by
          rw [Matrix.mul_assoc]
      _ = (fourierMatrix n * Matrix.diagonal (circulantEigenvalue n v)) * fourierMatrixInv n := by
          rw [circulant_mul_fourierMatrix]
  rw [hC, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    mul_comm (fourierMatrix n).det, mul_assoc, ← Matrix.det_mul, fourierMatrix_mul_inv,
    Matrix.det_one, mul_one]

/-- The Fourier eigenvalue at `j = 0` is the sum of the entries of `v`. -/
public theorem circulantEigenvalue_zero (v : ZMod n → ℂ) :
    circulantEigenvalue n v 0 = ∑ k, v k := by
  show (∑ k, v k * zeta n ^ (-(k.val * (0 : ZMod n).val : ℤ))) = ∑ k, v k
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ZMod.val_zero]
  simp

/-- The Fourier eigenvalues sum to `n * v 0`. -/
public theorem sum_circulantEigenvalue (v : ZMod n → ℂ) :
    ∑ j, circulantEigenvalue n v j = (n : ℂ) * v 0 := by
  simp only [circulantEigenvalue]
  rw [Finset.sum_comm]
  have hinner : ∀ k : ZMod n,
      ∑ j : ZMod n, v k * zeta n ^ (-(k.val * j.val : ℤ)) =
        v k * (if k = 0 then (n : ℂ) else 0) := by
    intro k
    rw [← Finset.mul_sum]
    congr 1
    have h := sum_zeta_zpow_mul_eq (n := n) (-(k.val : ℤ))
    have hdvd : (n : ℤ) ∣ (-(k.val : ℤ)) ↔ k = 0 := by
      constructor
      · intro hd
        have hlt : k.val < n := ZMod.val_lt k
        have hdvd' : n ∣ k.val := by
          exact_mod_cast (dvd_neg.mp hd)
        have hk0 : k.val = 0 := by
          rcases Nat.eq_zero_or_pos k.val with h0 | hpos
          · exact h0
          · exact absurd (Nat.le_of_dvd hpos hdvd') (by omega)
        exact k.val_eq_zero.mp hk0
      · intro hk
        rw [hk]
        simp
    rw [if_congr hdvd rfl rfl] at h
    exact (Finset.sum_congr rfl fun j _ => by congr 1; ring).trans h
  rw [Finset.sum_congr rfl fun k _ => hinner k]
  rw [Finset.sum_congr rfl (fun k _ => by rw [mul_ite, mul_zero])]
  rw [Finset.sum_ite_eq']
  rw [ite_eq_left (Finset.mem_univ _), mul_comm]

end MathlibExt.LinearAlgebra.Matrix.CirculantSpectrum
