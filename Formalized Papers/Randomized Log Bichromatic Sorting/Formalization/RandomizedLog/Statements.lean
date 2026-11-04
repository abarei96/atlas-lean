import RandomizedLog.TotalCost

/-!
# Randomized paper: statements

`Papers/randomized_log_final_draft.tex`, "From Log-Cubed to Log in
Bichromatic Sorting". The sorter below is SpliceSort itself: on an
arrival ranking `τF` it produces the final runs of the produced
execution read in order (`spliceRun`), and its total cost on `τF`
is the paper's total comparison cost of that same execution
(`totalExecCost`: mixed scan and binary-search comparisons, blue
monochromatic Mergesort, red own and foreign comparisons). The
`expectedCost` is the expectation of that total cost over the
uniform arrival ranking. `spliceSort_main` is the paper's
Theorem 1 with absolute constant `100`.
-/

namespace Bichromatic.Randomized

open Bichromatic

variable {X : Type*} [LinearOrder X] [Fintype X]

/-- A randomized comparison sorter on the instance `X`: on each
arrival ranking it outputs a list, with a total comparison cost
for that ranking, and `expectedCost` is the expectation of the
total cost over the uniform arrival ranking. The link between
output, cost, and expectation is part of the structure. -/
structure RandomizedSorter (X : Type*) [LinearOrder X] [Fintype X] where
  run : (X → Color) → (X → Fin (Fintype.card X)) → List X
  totalCost : (α β : ℝ) → (X → Color) →
    (X → Fin (Fintype.card X)) → ℝ
  expectedCost : (α β : ℝ) → (X → Color) → ℝ
  expectedCost_def : ∀ (α β : ℝ) (color : X → Color),
    expectedCost α β color
      = ((∑ τF ∈ InjRanks X, totalCost α β color τF)
        / (InjRanks X).card)
  sorted : ∀ (color : X → Color) (τF : X → Fin (Fintype.card X)),
    (run color τF).Pairwise (· ≤ ·)
  perm : ∀ (color : X → Color) (τF : X → Fin (Fintype.card X)),
    (run color τF).Perm (sortedList X)

/-- The SpliceSort sorter of the paper. -/
noncomputable def spliceSorter : RandomizedSorter X where
  run := spliceRun
  totalCost := totalExecCost
  expectedCost := fun α β color =>
    ((∑ τF ∈ InjRanks X, totalExecCost α β color τF)
      / (InjRanks X).card)
  expectedCost_def := fun α β color => rfl
  sorted := fun color τF => spliceRun_sorted (color := color) τF
  perm := fun color τF => spliceRun_perm (color := color) τF

/-- The expected total cost of SpliceSort itself is at most an
absolute constant times `H log N`, for all `α, β > 1`. The
constant here is `100`, assembled from the scan bound
(`cor:mixedcost`), the binary-search bound, `lem:bluecost`,
`lem:ownred`, and `lem:foreignred`, each charged to `H` by
`lem:Hbounds`. -/
theorem spliceSorter_expected_le (α β : ℝ) (color : X → Color)
    (hα : 1 < α) (hβ : 1 < β) :
    spliceSorter.expectedCost α β color
      ≤ 100 * benchmarkH α β color * Real.logb 2 (instSize X) := by
  classical
  show ((∑ τF ∈ InjRanks X, totalExecCost α β color τF)
      / (InjRanks X).card)
    ≤ 100 * benchmarkH α β color * Real.logb 2 (instSize X)
  by_cases hN : 2 ≤ Fintype.card X
  · have h := expected_totalExecCost_le (color := color) α β
      (le_of_lt hα) (le_of_lt hβ) hN
    exact h
  · -- At most one element: every cost component is zero.
    have hlen : (sortedList X).length ≤ 1 := by
      have h : (sortedList X).length = Fintype.card X := by
        simp [sortedList, Finset.length_sort]
      omega
    have hzero : ∀ τF, totalExecCost α β color τF = 0 := by
      intro τF
      cases hSL : sortedList X with
      | nil =>
        have hb : blueList color = [] := by simp [blueList, hSL]
        have hr : redList color = [] := by simp [redList, hSL]
        unfold totalExecCost
        rw [dif_pos hb, if_pos hr]
      | cons x t =>
        cases t with
        | nil =>
          have hruns : runsOf color (sortedList X) = [[x]] := by
            rw [hSL]
            rfl
          by_cases hc : color x = Color.red
          · have hb : blueList color = [] := by
              simp [blueList, hSL, hc]
            have hr : redList color = [x] := by
              simp [redList, hSL, hc]
            unfold totalExecCost
            rw [dif_pos hb, if_neg (by simp [hr]), hSL]
            simp [msort]
          · have hcb : color x = Color.blue := by
              cases h : color x with
              | red => exact absurd h hc
              | blue => rfl
            have hr : redList color = [] := by
              simp [redList, hSL, hcb]
            have hb : blueList color = [x] := by
              simp [blueList, hSL, hcb]
            have harr : arrivalsOf color τF = [] := by
              simp [arrivalsOf, hr]
            have hev : ∀ (L : List X)
                (hb' : blueList color ≠ [])
                (hp : L.Perm (redList color)), L = [] →
                execEvents color hb' L hp = [] := by
              intro L hb' hp hL
              subst hL
              show (executionOf color hb' [] hp).events = []
              cases h : (executionOf color hb' [] hp).events with
              | nil => rfl
              | cons e es =>
                exfalso
                have hmem := events_fst_mem color
                  (executionOf color hb' ([] : List X) hp) e (by
                    rw [h]
                    simp)
                simp at hmem
            unfold totalExecCost
            rw [dif_neg (by simp [hb])]
            have hbcharge : blueCostCharge color = 0 := by
              unfold blueCostCharge
              rw [hruns]
              simp [msort]
            have hredsum : redRunSum color = 0 := by
              unfold redRunSum
              rw [hruns]
              simp [hcb]
            have hown : redOwnCharge color = 0 := by
              simp [redOwnCharge, hredsum]
            have hforeign : foreignCharge color τF = 0 := by
              unfold foreignCharge
              rw [hruns]
              simp [foreignAt, hcb]
            rw [hev _ _ _ harr, hbcharge, hown, hforeign, hr]
            simp [scanCost]
        | cons y t =>
          exfalso
          simp [hSL] at hlen
    rw [Finset.sum_congr rfl (fun τF _ => hzero τF)]
    simp
    have hlog : Real.logb 2 (instSize X) = 0 ∨ benchmarkH α β color = 0 := by
      by_cases h0 : Fintype.card X = 0
      · right
        have hSL : sortedList X = [] := by
          have h : (sortedList X).length = 0 := by
            simp [sortedList, Finset.length_sort, h0]
          cases hSL : sortedList X with
          | nil => rfl
          | cons x t => simp [hSL] at h
        unfold benchmarkH
        rw [hSL]
        rfl
      · left
        have h1 : instSize X = 1 := by
          unfold instSize
          omega
        rw [h1]
        simp
    rcases hlog with hlog | hH
    · rw [hlog]
      simp
    · rw [hH]
      simp

/-- **Main theorem of the randomized paper (Theorem 1).**
There is a randomized sorter — SpliceSort — whose expected total
cost is `O(H log N)` with an absolute constant (here `100`), for
all `α, β > 1`. -/
theorem spliceSort_main (α β : ℝ) (color : X → Color)
    (hα : 1 < α) (hβ : 1 < β) :
    ∃ S : RandomizedSorter X,
      S.expectedCost α β color
        ≤ 100 * benchmarkH α β color * Real.logb 2 (instSize X) :=
  ⟨spliceSorter, spliceSorter_expected_le α β color hα hβ⟩

/-- **Competitive-ratio form of Theorem 1.** The competitive
ratio of SpliceSort (worst case over colourings of expected total
cost divided by `H`, as defined on page 2 of the paper) is at
most `100 log₂ N`. -/
theorem spliceSort_competitiveRatio (α β : ℝ)
    (hα : 1 < α) (hβ : 1 < β) (hN : 2 ≤ Fintype.card X) :
    competitiveRatio (X := X)
        ((spliceSorter (X := X)).expectedCost α β) α β
      ≤ 100 * Real.logb 2 (instSize X) := by
  classical
  unfold competitiveRatio
  haveI : Nonempty (X → Color) := ⟨fun _ => Color.red⟩
  apply ciSup_le
  intro color
  have hHpos : (0 : ℝ) < benchmarkH α β color := by
    have hge := benchmarkH_ge (α := α) (β := β) (color := color)
      (le_of_lt hα) (le_of_lt hβ)
    have hN' : (2 : ℝ) ≤ (instSize X : ℝ) := by
      unfold instSize
      exact_mod_cast hN
    linarith
  have hmain := spliceSorter_expected_le α β color hα hβ
  rw [div_le_iff₀ hHpos]
  have e : 100 * benchmarkH α β color * Real.logb 2 (instSize X)
      = (100 * Real.logb 2 (instSize X)) * benchmarkH α β color := by
    ring
  rwa [e] at hmain

end Bichromatic.Randomized
