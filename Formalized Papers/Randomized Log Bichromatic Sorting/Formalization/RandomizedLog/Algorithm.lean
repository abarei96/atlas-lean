import RandomizedLog.Definitions

/-!
# SpliceSort: algorithm core (randomized paper, §2)

Formalizes the two operations the randomized paper's analysis rests on:

* `locate`: the index `k = min {j : ρⱼ > r}` (or `q` if none) over the
  current blue-run representatives — the binary-search location step,
  here as a linear scan with the same specification; and
* `splice`: replacing one blue run by its two pieces around a new red
  singleton, so the run count grows by exactly one
  (`q_t = q_{t-1} + 1` of the paper).

Both key lemmas are proved: everything before `k` is below `r`,
the representative at `k` (if any) is above `r`, and splicing
increments the number of blue runs by one.
-/

namespace Bichromatic.Randomized

open Bichromatic

variable {X : Type*} [LinearOrder X]

/-- Location index: `k = min {j : reps[j] > r}`, or `reps.length` if
no representative exceeds `r`. This is the specification of the paper's
binary-search step, realized here by `List.findIdx`. -/
def locate (reps : List X) (r : X) : ℕ :=
  reps.findIdx (fun y => r < y)

theorem locate_le_length (reps : List X) (r : X) : locate reps r ≤ reps.length :=
  List.findIdx_le_length

/-- Every representative before the location index is `< r`
(using `r ≠ reps[j]`, which holds in the paper since `r` is red and
representatives are blue elements, hence distinct elements). -/
theorem getElem_lt_of_lt_locate (reps : List X) (r : X)
    (hne : ∀ y ∈ reps, y ≠ r) :
    ∀ (j : ℕ) (hj : j < reps.length) (hjk : j < locate reps r),
      reps[j] < r := by
  intro j hj hjk
  have hfalse : ¬ (r < reps[j]) := by
    have h := List.not_of_lt_findIdx (p := fun y => r < y) hjk
    simpa using h
  exact lt_of_le_of_ne (le_of_not_gt hfalse) (hne reps[j] (List.getElem_mem hj))

/-- The representative at the location index, if it exists, exceeds `r`. -/
theorem lt_getElem_locate (reps : List X) (r : X)
    (h : locate reps r < reps.length) : r < reps[locate reps r] := by
  have hspec := List.findIdx_getElem (p := fun y => r < y) (xs := reps) (w := h)
  unfold locate
  exact of_decide_eq_true hspec

/-- Splicing blue run `j` into its below/above pieces around a new red
singleton: the run list with position `j` replaced by two runs.
`below` and `above` are `C_{<r}` and `C_{>r}` of the paper. -/
def splice (runs : List (List X)) (j : ℕ) (below above : List X) : List (List X) :=
  (runs.take j) ++ below :: above :: (runs.drop (j + 1))

/-- Splice evolution, count form: if `j` is a valid run index, splicing
increases the number of blue runs by exactly one (`q_t = q_{t-1} + 1`). -/
theorem splice_length (runs : List (List X)) (j : ℕ) (below above : List X)
    (hj : j < runs.length) : (splice runs j below above).length = runs.length + 1 := by
  unfold splice
  simp only [List.length_append, List.length_cons, List.length_take, List.length_drop]
  omega

/-- Splice evolution, content form: runs before `j` are untouched. -/
theorem splice_take (runs : List (List X)) (j : ℕ) (below above : List X)
    (hj : j ≤ runs.length) :
    (splice runs j below above).take j = runs.take j := by
  unfold splice
  rw [List.take_append_of_le_length (by simp [List.length_take, Nat.min_eq_left hj])]
  simp [List.take_take]

end Bichromatic.Randomized
