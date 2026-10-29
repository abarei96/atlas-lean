/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.HilbertSchmidt
import MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm

open MathlibExt.Analysis.InnerProductSpace.HilbertSchmidt
open scoped lp ENNReal

namespace MathlibExtTest.Analysis.InnerProductSpace.HilbertSchmidtCanonicalTests

-- Each finite identity block has squared entry sum N, including N=0.
example (N : ℕ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      ‖hsDiagonal (fun _ : ℕ => (1 : ℝ)) i j‖ ^ 2) = (N : ℝ) := by
  have hf : (Finset.range N).filter (fun x => x < N) = Finset.range N :=
    Finset.filter_eq_self.mpr (fun x hx => Finset.mem_range.mp hx)
  simp [hsDiagonal, hf]

-- The infinite identity cannot supply a witness for the finite real norm.
example : ¬ IsHilbertSchmidt (hsDiagonal (fun _ : ℕ => (1 : ℝ))) := by
  intro ha
  have hd : Summable ((fun p : ℕ × ℕ => ‖hsDiagonal (fun _ : ℕ => (1 : ℝ)) p.1 p.2‖ ^ 2)
      ∘ fun n : ℕ => (n, n)) :=
    ha.comp_injective (fun i j h => congrArg Prod.fst h)
  have h1 : Summable (fun _ : ℕ => (1 : ℝ)) := by
    simpa [hsDiagonal, Function.comp_def] using hd
  exact one_ne_zero ((summable_const_iff (1 : ℝ)).mp h1)

-- The actual bounded identity in the standard ℓ² basis has extended value top.
example : MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm.hsNormSq
    (ContinuousLinearMap.id ℝ ℓ²(ℕ, ℝ)) (fun j => lp.single 2 j (1 : ℝ)) = ⊤ := by
  simp only [MathlibExt.Analysis.OperatorTheory.HilbertSchmidtNorm.hsNormSq,
    ContinuousLinearMap.id_apply, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2),
    norm_one, one_pow, ENNReal.ofReal_one]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

example : hsMatrix (ContinuousLinearMap.id ℝ ℓ²(ℕ, ℝ)) =
    hsDiagonal (fun _ : ℕ => (1 : ℝ)) := by
  funext i j
  simp [hsMatrix, hsDiagonal, lp.single_apply, Pi.single_apply]

-- Use the standard Mathlib single-coordinate vectors, with no new basis object.
example : Orthonormal ℝ (fun j : ℕ => lp.single 2 j (1 : ℝ)) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp [lp.inner_single_left, lp.single_apply, Pi.single_apply]

private def d : ℕ → ℝ := fun n => if n = 0 then 2 else if n = 1 then 3 else 0

private theorem d_summable : Summable fun n => ‖d n‖ ^ 2 := by
  apply summable_of_ne_finset_zero (s := Finset.range 2)
  intro n hn
  have hn0 : n ≠ 0 := by simp only [Finset.mem_range] at hn; omega
  have hn1 : n ≠ 1 := by simp only [Finset.mem_range] at hn; omega
  simp [d, hn0, hn1]

private noncomputable abbrev u : ℓ²(ℕ, ℝ) := lp.single 2 0 (2 : ℝ)
private noncomputable abbrev v : ℓ²(ℕ, ℝ) := lp.single 2 1 (3 : ℝ)

example : IsHilbertSchmidt (hsDiagonal d) := isHilbertSchmidt_hsDiagonal d_summable
example : IsHilbertSchmidt (hsRankOne u v) := isHilbertSchmidt_hsRankOne

end MathlibExtTest.Analysis.InnerProductSpace.HilbertSchmidtCanonicalTests
