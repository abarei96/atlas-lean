/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteMarkovChain
import Mathlib.Tactic.FinCases

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal

namespace MathlibExt.Probability.FiniteMarkovChainTest

open MathlibExt.Probability.FiniteMarkovChain

/-- The identity stochastic matrix on `Fin 2`: every state stays put. -/
def identityMatrix : StochasticMatrix 1 where
  prob i j := if j = i then 1 else 0
  nonneg := by intro i j; by_cases h : j = i <;> simp [h]
  row_sum := by
    intro i
    fin_cases i <;> simp

/-- The flip stochastic matrix on `Fin 2`: every state moves to the other one. -/
def flipMatrix : StochasticMatrix 1 where
  prob i j := if j = i then 0 else 1
  nonneg := by intro i j; by_cases h : j = i <;> simp [h]
  row_sum := by
    intro i
    fin_cases i <;> simp

/-- The constant `⊤` filtration on `Unit`: every time slice is the full
σ-algebra. Constant processes are adapted to it. -/
def topFiltration : Filtration ℕ (inferInstance : MeasurableSpace Unit) where
  seq _ := ⊤
  mono' _ _ _ := le_rfl
  le' _ := le_rfl

/-- The constant process at `0`. -/
def constProcess : ℕ → Unit → Fin 2 := fun _ _ => 0

/-- The alternating process `0, 1, 0, 1, …`. -/
def altProcess : ℕ → Unit → Fin 2 := fun n _ => if Even n then (0 : Fin 2) else 1

/-- The constant chain at `0` is a finite Markov chain for the identity matrix. -/
theorem constChain_isFiniteMarkovChain :
    IsFiniteMarkovChain constProcess identityMatrix topFiltration
      (Measure.dirac ()) := by
  refine ⟨fun n => measurable_const, fun n j => ?_⟩
  calc (Measure.dirac ())[(fun ω : Unit => if (0 : Fin 2) = j then (1 : ℝ) else 0)
        | topFiltration n]
      = fun _ => (if (0 : Fin 2) = j then (1 : ℝ) else 0) :=
        condExp_const (μ := Measure.dirac ()) le_rfl _
    _ =ᵐ[Measure.dirac ()] fun _ => identityMatrix.prob (0 : Fin 2) j :=
        Filter.EventuallyEq.of_eq (by
          funext ω
          fin_cases j <;> simp [identityMatrix, Fin.ext_iff])

/-- The alternating chain `0, 1, 0, 1, …` is a finite Markov chain for the
flip matrix. -/
theorem altChain_isFiniteMarkovChain :
    IsFiniteMarkovChain altProcess flipMatrix
      topFiltration (Measure.dirac ()) := by
  refine ⟨fun n => measurable_const, fun n j => ?_⟩
  calc (Measure.dirac ())[(fun ω : Unit =>
        if (if Even (n + 1) then (0 : Fin 2) else 1) = j then (1 : ℝ) else 0)
        | topFiltration n]
      = fun _ => (if (if Even (n + 1) then (0 : Fin 2) else 1) = j
          then (1 : ℝ) else 0) :=
        condExp_const (μ := Measure.dirac ()) le_rfl _
    _ =ᵐ[Measure.dirac ()]
        fun _ => flipMatrix.prob (if Even n then (0 : Fin 2) else 1) j :=
        Filter.EventuallyEq.of_eq (by
          funext ω
          by_cases hn : Even n
          · have hnp1 : ¬ Even (n + 1) := by
              simpa [Nat.even_add_one] using hn
            rw [ite_eq_right hnp1, ite_eq_left hn]
            fin_cases j <;> simp [flipMatrix, Fin.ext_iff]
          · have hnp1 : Even (n + 1) := by
              simpa [Nat.even_add_one] using hn
            rw [ite_eq_left hnp1, ite_eq_right hn]
            fin_cases j <;> simp [flipMatrix, Fin.ext_iff])

/-- Kernel evaluation for the identity matrix: from `0`, the mass of `{0}` is `1`. -/
example : finiteChainKernel identityMatrix 0 ↑({0} : Finset (Fin 2)) = 1 := by
  rw [finiteChainKernel_apply]
  simp [identityMatrix]

/-- Kernel evaluation for the flip matrix: from `0`, the mass of `{1}` is `1`. -/
example : finiteChainKernel flipMatrix 0 ↑({1} : Finset (Fin 2)) = 1 := by
  rw [finiteChainKernel_apply]
  simp [flipMatrix]

/-- Kernel evaluation for the flip matrix: from `0`, the mass of `{0}` is `0`. -/
example : finiteChainKernel flipMatrix 0 ↑({0} : Finset (Fin 2)) = 0 := by
  rw [finiteChainKernel_apply]
  simp [flipMatrix]

/-- The kernel of a stochastic matrix is a Markov kernel. -/
example : IsMarkovKernel (finiteChainKernel flipMatrix) := inferInstance

/-- The bridge theorem applied to the constant chain. -/
example (B : Set (Fin 2)) :
    (Measure.dirac ())[(B.indicator (fun _ => (1 : ℝ))) ∘ constProcess (0 + 1)
        | topFiltration 0]
      =ᵐ[Measure.dirac ()] fun _ => (finiteChainKernel identityMatrix 0 B).toReal :=
  constChain_isFiniteMarkovChain.condExp_indicator

/-- The bridge theorem applied to the alternating chain. -/
example (B : Set (Fin 2)) :
    (Measure.dirac ())[(B.indicator (fun _ => (1 : ℝ))) ∘ altProcess (0 + 1)
        | topFiltration 0]
      =ᵐ[Measure.dirac ()] fun _ => (finiteChainKernel flipMatrix 0 B).toReal :=
  altChain_isFiniteMarkovChain.condExp_indicator

/-- The one-step forward equation applied to the constant chain. -/
example : (Measure.dirac ()).map (constProcess (0 + 1))
    = ((Measure.dirac ()).map (constProcess 0)).bind
        (finiteChainKernel identityMatrix) :=
  constChain_isFiniteMarkovChain.map_succ_eq_bind 0

/-- The one-step forward equation applied to the alternating chain: after one
step the mass is on `1`. -/
example : (Measure.dirac ()).map (altProcess (0 + 1))
    = ((Measure.dirac ()).map (altProcess 0)).bind
        (finiteChainKernel flipMatrix) :=
  altChain_isFiniteMarkovChain.map_succ_eq_bind 0

-- `#print axioms` check: the bridge theorem rests only on the standard axioms.
#print axioms IsFiniteMarkovChain.condExp_indicator
#print axioms IsFiniteMarkovChain.map_succ_eq_bind

end MathlibExt.Probability.FiniteMarkovChainTest
