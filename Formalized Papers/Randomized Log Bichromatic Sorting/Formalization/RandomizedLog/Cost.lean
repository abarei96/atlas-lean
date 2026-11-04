import RandomizedLog.Step

/-!
# SpliceSort cost accounting: scans and records (randomized paper, §3)

The mixed-comparison cost is counted by scan incidences: scanning a
blue run `C` with `r` compares `r` against every element of `C` once.
The charging argument attributes each incidence to a record for the
blue element it touches, where records are defined by the arrival
permutation `τ` (paper, `lem:records`): a red `r < b` is a predecessor
record for a blue `b` when `τ(r)` precedes the arrival of every red
element strictly between `r` and `b`; successor records symmetrically.

This file formalizes the definitions and proves the deterministic
half of the splice accounting: when the scan verdict is mixed, the
two splice pieces are exactly the elements of `C` below and above `r`
(filter partition). The expected `O(log N)` record bound
(`lem:records`, harmonic sum over the uniform permutation) is stated
below with its proof deferred to the probability stage.
-/

namespace Bichromatic.Randomized

open Bichromatic

variable {X : Type*} [LinearOrder X] [Fintype X] (color : X → Color)

/-- Predecessor record (paper §3): red `r < b` arriving before every
red element strictly between `r` and `b`. `τ` is the arrival rank. -/
def IsPredRecord (τ : X → ℕ) (b r : X) : Prop :=
  color r = Color.red ∧ r < b ∧
    ∀ r' : X, color r' = Color.red → r < r' → r' < b → τ r < τ r'

/-- Successor record: red `r > b` arriving before every red element
strictly between `b` and `r`. -/
def IsSuccRecord (τ : X → ℕ) (b r : X) : Prop :=
  color r = Color.red ∧ b < r ∧
    ∀ r' : X, color r' = Color.red → b < r' → r' < r → τ r < τ r'

/-- A record for `b` is either kind. -/
def IsRecord (τ : X → ℕ) (b r : X) : Prop :=
  IsPredRecord color τ b r ∨ IsSuccRecord color τ b r

/-- The elements of `C` below `r` and above `r`: the two splice pieces
produced by a mixed scan. -/
def belowPiece (C : List X) (r : X) : List X := C.filter (· < r)
def abovePiece (C : List X) (r : X) : List X := C.filter (r < ·)

/-- Every element of the below piece is an old element of `C` below `r`
(the `hsub_b`/`hbr` certificates of `runsOrdered_splice_runs`). -/
theorem belowPiece_mem {C : List X} {r x : X} (hx : x ∈ belowPiece C r) :
    x ∈ C ∧ x < r := by
  simp [belowPiece, List.mem_filter] at hx; exact hx

theorem abovePiece_mem {C : List X} {r x : X} (hx : x ∈ abovePiece C r) :
    x ∈ C ∧ r < x := by
  simp [abovePiece, List.mem_filter] at hx; exact hx

/-- The splice pieces partition the scanned run: as a permutation,
`below ++ above` is `C`, provided no element of `C` equals `r` (true
in the paper since `C` is blue and `r` is red). This is the
deterministic content of "a mixed scan splits its run". -/
theorem below_append_above_perm {C : List X} {r : X} (hne : ∀ x ∈ C, x ≠ r) :
    (belowPiece C r ++ abovePiece C r).Perm C := by
  have h1 := List.filter_append_perm (fun x => decide (x < r)) C
  have h2 : C.filter (fun x => ¬ x < r) = C.filter (fun a => !decide (a < r)) := by
    apply List.filter_congr
    intro x _
    exact decide_not
  have h3 : C.filter (r < ·) = C.filter (fun x => ¬ x < r) := by
    apply List.filter_congr
    intro x hx
    rw [decide_eq_decide]
    constructor
    · intro h; exact not_lt.mpr (le_of_lt h)
    · intro h; exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (hne x hx))
  unfold belowPiece abovePiece
  rw [h3, h2]
  exact h1

-- The `RecordsExpectedBound` statement now lives in
-- `Records.lean`, where it is stated over `InjRanks X`
-- directly (and proved as `recordsExpectedBound_holds`).

end Bichromatic.Randomized
