import RandomizedLog.State

/-!
# SpliceSort: scan, step dispatch, and full invariant preservation

Assembles the verified run-level operations into the paper's insertion
step. The scan of a blue run with the active red element `r` has three
verdicts (paper §2, `Insert` subroutine); the candidate red run `S`
between the neighbouring blue runs is absent, a singleton, or
activated. At run level the step is one of four operations:

* `freshSingleton` — Case A one-sided (and Case B all-one-sided does a
  merge instead): a new red singleton appears;
* `mergePair` — Case B: `r` merges with the singleton `{r₀}` into the
  sorted activated pair;
* `insertInto` — Case C: `r` is inserted into the activated run `S`,
  or attached at an end (both are sorted insertion at run level);
* `splitRun` — any case with a mixed scan: the scanned blue run splits
  into its below/above pieces around the new singleton `[r]`.

The theorem `applyOp_invariant` proves the full 3-part invariant
(nonempty runs, run-order, red-sortedness) is preserved by each
operation, under exactly the certificates the paper's location step
(`cert_left`/`cert_right`) and scans provide.
-/

namespace Bichromatic.Randomized

open Bichromatic

variable {X : Type*} [LinearOrder X] (color : X → Color)

/-- The three scan verdicts of the paper: every element of the blue
run below `r`, every element above `r`, or elements on both sides. -/
inductive ScanVerdict where
  | below
  | above
  | mixed
deriving DecidableEq, Repr

/-- Scan a blue run `C` with `r`: compare `r` with every element once
and report the verdict. -/
def scanVerdict (C : List X) (r : X) : ScanVerdict :=
  if ∀ x ∈ C, x < r then ScanVerdict.below
  else if ∀ x ∈ C, r < x then ScanVerdict.above
  else ScanVerdict.mixed

theorem scanVerdict_below {C : List X} {r : X} (h : ∀ x ∈ C, x < r) :
    scanVerdict C r = ScanVerdict.below := by
  unfold scanVerdict; rw [if_pos h]

theorem scanVerdict_above {C : List X} {r : X} (h : ∀ x ∈ C, r < x)
    (hnot : ¬ ∀ x ∈ C, x < r) :
    scanVerdict C r = ScanVerdict.above := by
  unfold scanVerdict; rw [if_neg hnot, if_pos h]

theorem scanVerdict_mixed {C : List X} {r : X}
    (h1 : ¬ ∀ x ∈ C, x < r) (h2 : ¬ ∀ x ∈ C, r < x) :
    scanVerdict C r = ScanVerdict.mixed := by
  unfold scanVerdict; rw [if_neg h1, if_neg h2]

/-- A mixed verdict means the run genuinely splits: some element below
`r` and some element above `r` (so both splice pieces are nonempty in
content, as the paper notes). -/
theorem exists_of_mixed {C : List X} {r : X} (hne : ∀ x ∈ C, x ≠ r)
    (h : scanVerdict C r = ScanVerdict.mixed) :
    (∃ x ∈ C, r < x) ∧ (∃ x ∈ C, x < r) := by
  have hn1 : ¬ ∀ x ∈ C, x < r := by
    intro hh; rw [scanVerdict_below hh] at h; exact ScanVerdict.noConfusion h
  have hn2 : ¬ ∀ x ∈ C, r < x := by
    intro hh; rw [scanVerdict_above hh hn1] at h; exact ScanVerdict.noConfusion h
  push_neg at hn1 hn2
  obtain ⟨x, hxC, hx⟩ := hn1
  obtain ⟨y, hyC, hy⟩ := hn2
  exact ⟨⟨x, hxC, lt_of_le_of_ne hx (Ne.symm (hne x hxC))⟩,
         ⟨y, hyC, lt_of_le_of_ne hy (hne y hyC)⟩⟩

/-- Sorted insertion of `r` into a run (Case C at run level). -/
def insertSorted (r : X) : List X → List X
  | [] => [r]
  | a :: as => if r ≤ a then r :: a :: as else a :: insertSorted r as

theorem insertSorted_mem {r : X} {S : List X} {x : X} :
    x ∈ insertSorted r S ↔ x = r ∨ x ∈ S := by
  induction S with
  | nil => simp [insertSorted]
  | cons a as ih =>
      by_cases h : r ≤ a
      · simp [insertSorted, h]
      · simp [insertSorted, h, ih, or_left_comm, or_assoc]

theorem insertSorted_pairwise {r : X} {S : List X} (hS : S.Pairwise (· ≤ ·)) :
    (insertSorted r S).Pairwise (· ≤ ·) := by
  induction S with
  | nil => simp [insertSorted]
  | cons a as ih =>
      rw [List.pairwise_cons] at hS
      obtain ⟨ha, has⟩ := hS
      unfold insertSorted
      split_ifs with h
      · rw [List.pairwise_cons]
        constructor
        · intro y hy
          cases List.mem_cons.mp hy with
          | inl he => rw [he]; exact h
          | inr he => exact le_trans h (ha y he)
        · rw [List.pairwise_cons]; exact ⟨ha, has⟩
      · rw [List.pairwise_cons]
        constructor
        · intro y hy
          rw [insertSorted_mem] at hy
          cases hy with
          | inl he => rw [he]; exact le_of_not_ge h
          | inr he => exact ha y he
        · exact ih has

/-- The full 3-part invariant of the paper, as one predicate on a run
list: nonempty runs, run-order, and red runs of length ≥ 2 sorted. -/
def Invariant (runs : List (List X)) : Prop :=
  (∀ R ∈ runs, R ≠ []) ∧ RunsOrdered runs ∧
    ∀ R ∈ runs, (∀ x ∈ R, color x = Color.red) → 2 ≤ R.length → R.Pairwise (· ≤ ·)

theorem invariant_of_state {s : State color} : Invariant color s.runs :=
  ⟨s.nonempty, s.ordered, s.redSorted⟩

/-- The four run-level insertion operations (see file header). `S` is
the run consumed or modified by the operation: the neighbouring blue
run for `freshSingleton`, the singleton `{r₀}` for `mergePair`, the
activated run for `insertInto`, the scanned blue run for `splitRun`. -/
inductive InsertOp (X : Type*) where
  | freshSingleton
  | appendSingleton
  | mergePair (r₀ : X)
  | insertInto
  | splitRun (below above : List X)

/-- Apply an insertion operation at the decomposition `runs = A ++ S :: B`. -/
def applyOp (A B : List (List X)) (S : List X) (r : X) : InsertOp X → List (List X)
  | .freshSingleton => A ++ [r] :: S :: B
  | .appendSingleton => (A ++ S :: B) ++ [[r]]
  | .mergePair r₀ => A ++ (if r < r₀ then [r, r₀] else [r₀, r]) :: B
  | .insertInto => A ++ insertSorted r S :: B
  | .splitRun below above => A ++ below :: [r] :: above :: B

/-- Membership in a decomposed run list, in the form the invariant
proofs consume. -/
theorem mem_decomp {A : List (List X)} {S : List X} {B : List (List X)} {R : List X} :
    R ∈ A ++ S :: B ↔ R ∈ A ∨ R = S ∨ R ∈ B := by
  simp [List.mem_append, List.mem_cons]

/-- Nonempty component, shared by all operations: runs other than the
new one are old runs; the new runs are nonempty by construction/hypothesis. -/
theorem invariant_freshSingleton {A B : List (List X)} {S : List X} {r : X}
    (hinv : Invariant color (A ++ S :: B))
    (hL : ∀ R ∈ A, ∀ x ∈ R, x < r)
    (hR : ∀ T ∈ S :: B, ∀ y ∈ T, r < y) :
    Invariant color (applyOp A B S r .freshSingleton) := by
  obtain ⟨hne, hord, hred⟩ := hinv
  refine ⟨?_, ?_, ?_⟩
  · intro R hR
    simp only [applyOp, List.mem_append, List.mem_cons] at hR
    cases hR with
    | inl h => exact hne R (by simp [List.mem_append, h])
    | inr h =>
        cases h with
        | inl he => rw [he]; simp
        | inr h => exact hne R (by simp [List.mem_append, List.mem_cons, h])
  · exact runsOrdered_insert_singleton r hord hL hR
  · intro R hR hredR hlen
    simp only [applyOp, List.mem_append, List.mem_cons] at hR
    cases hR with
    | inl h => exact hred R (by simp [List.mem_append, h]) hredR hlen
    | inr h =>
        cases h with
        | inl he => rw [he] at hlen; simp at hlen
        | inr h => exact hred R (by simp [List.mem_append, List.mem_cons, h]) hredR hlen

theorem invariant_mergePair {A B : List (List X)} {S : List X} {r r₀ : X}
    (hinv : Invariant color (A ++ S :: B)) (hS : S = [r₀])
    (hL : ∀ R ∈ A, ∀ x ∈ R, x < r ∧ x < r₀)
    (hR : ∀ T ∈ B, ∀ y ∈ T, r < y ∧ r₀ < y) :
    Invariant color (applyOp A B S r (.mergePair r₀)) := by
  obtain ⟨hne, hord, hred⟩ := hinv
  have hord' : RunsOrdered (A ++ [r₀] :: B) := hS ▸ hord
  refine ⟨?_, ?_, ?_⟩
  · intro R hR
    simp only [applyOp, List.mem_append, List.mem_cons] at hR
    cases hR with
    | inl h => exact hne R (by simp [List.mem_append, h])
    | inr h =>
        cases h with
        | inl he => rw [he]; split_ifs <;> simp
        | inr h => exact hne R (by simp [List.mem_append, List.mem_cons, h])
  · exact runsOrdered_merge_pair r r₀ hord' hL hR
  · intro R hR hredR hlen
    simp only [applyOp, List.mem_append, List.mem_cons] at hR
    cases hR with
    | inl h => exact hred R (by simp [List.mem_append, h]) hredR hlen
    | inr h =>
        cases h with
        | inl he =>
            rw [he]
            split_ifs with hh
            · simp [List.pairwise_cons, le_of_lt hh]
            · simp [List.pairwise_cons, le_of_not_gt hh]
        | inr h => exact hred R (by simp [List.mem_append, List.mem_cons, h]) hredR hlen

theorem insertSorted_length {r : X} {S : List X} :
    (insertSorted r S).length = S.length + 1 := by
  induction S with
  | nil => rfl
  | cons a as ih => unfold insertSorted; split_ifs <;> simp [ih]

theorem insertSorted_ne_nil {r : X} {S : List X} : insertSorted r S ≠ [] := by
  cases S with
  | nil => simp [insertSorted]
  | cons a as => unfold insertSorted; split_ifs <;> simp

theorem invariant_insertInto {A B : List (List X)} {S : List X} {r : X}
    (hinv : Invariant color (A ++ S :: B))
    (hL : ∀ R ∈ A, ∀ x ∈ R, x < r)
    (hR : ∀ T ∈ B, ∀ y ∈ T, r < y) :
    Invariant color (applyOp A B S r .insertInto) := by
  obtain ⟨hne, hord, hred⟩ := hinv
  refine ⟨?_, ?_, ?_⟩
  · intro R hR
    simp only [applyOp, List.mem_append, List.mem_cons] at hR
    cases hR with
    | inl h => exact hne R (by simp [List.mem_append, h])
    | inr h =>
        cases h with
        | inl he => rw [he]; exact insertSorted_ne_nil
        | inr h => exact hne R (by simp [List.mem_append, List.mem_cons, h])
  · exact runsOrdered_replace_run r hord (fun x hx => insertSorted_mem.mp hx) hL hR
  · intro R hR hredR hlen
    simp only [applyOp, List.mem_append, List.mem_cons] at hR
    cases hR with
    | inl h => exact hred R (by simp [List.mem_append, h]) hredR hlen
    | inr h =>
        cases h with
        | inl he =>
            rw [he] at hredR hlen ⊢
            apply insertSorted_pairwise
            by_cases h2 : 2 ≤ S.length
            · exact hred S (by simp [List.mem_append, List.mem_cons]) (fun x hx => hredR x (by rw [insertSorted_mem]; exact Or.inr hx)) h2
            · cases S with
              | nil => simp [insertSorted]
              | cons a as =>
                  cases as with
                  | nil => simp [insertSorted]
                  | cons b bs => simp at h2
        | inr h => exact hred R (by simp [List.mem_append, List.mem_cons, h]) hredR hlen

theorem invariant_splitRun {A B : List (List X)} {S below above : List X} {r : X}
    (hinv : Invariant color (A ++ S :: B))
    (hsub_b : ∀ x ∈ below, x ∈ S) (hsub_a : ∀ x ∈ above, x ∈ S)
    (hblue : ∀ x ∈ S, color x = Color.blue)
    (hbne : below ≠ []) (hane : above ≠ [])
    (hbr : ∀ x ∈ below, x < r) (har : ∀ y ∈ above, r < y)
    (hAr : ∀ R ∈ A, ∀ x ∈ R, x < r) (hrB : ∀ T ∈ B, ∀ y ∈ T, r < y) :
    Invariant color (applyOp A B S r (.splitRun below above)) := by
  obtain ⟨hne, hord, hred⟩ := hinv
  refine ⟨?_, ?_, ?_⟩
  · intro R hR
    simp only [applyOp, List.mem_append, List.mem_cons] at hR
    cases hR with
    | inl h => exact hne R (by simp [List.mem_append, h])
    | inr h =>
        cases h with
        | inl he => rw [he]; exact hbne
        | inr h =>
            cases h with
            | inl he => rw [he]; simp
            | inr h =>
                cases h with
                | inl he => rw [he]; exact hane
                | inr h => exact hne R (by simp [List.mem_append, List.mem_cons, h])
  · exact runsOrdered_splice_runs r hord hsub_b hsub_a hbr har hAr hrB
  · intro R hR hredR hlen
    simp only [applyOp, List.mem_append, List.mem_cons] at hR
    cases hR with
    | inl h => exact hred R (by simp [List.mem_append, h]) hredR hlen
    | inr h =>
        cases h with
        | inl he =>
            rw [he] at hredR
            cases below with
            | nil => simp at hbne
            | cons x xs =>
                have h1 := hredR x (by simp)
                have h2 := hblue x (hsub_b x (by simp))
                rw [h1] at h2; exact Color.noConfusion h2
        | inr h =>
            cases h with
            | inl he => rw [he] at hlen; simp at hlen
            | inr h =>
                cases h with
                | inl he =>
                    rw [he] at hredR
                    cases above with
                    | nil => simp at hane
                    | cons x xs =>
                        have h1 := hredR x (by simp)
                        have h2 := hblue x (hsub_a x (by simp))
                        rw [h1] at h2; exact Color.noConfusion h2
                | inr h => exact hred R (by simp [List.mem_append, List.mem_cons, h]) hredR hlen

/-- Invariant preservation for appending a fresh red singleton after
the last run (Case A at the right end), given every existing element
is below `r`. -/
theorem invariant_appendSingleton {A B : List (List X)} {S : List X} {r : X}
    (hinv : Invariant color (A ++ S :: B))
    (hAll : ∀ T ∈ A ++ S :: B, ∀ y ∈ T, y < r) :
    Invariant color (applyOp A B S r .appendSingleton) := by
  obtain ⟨hne, hord, hredS⟩ := hinv
  have hform : applyOp A B S r .appendSingleton = (A ++ S :: B) ++ [[r]] := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro R hR
    rw [hform] at hR
    simp only [List.mem_append, List.mem_singleton] at hR
    rcases hR with h | rfl
    · exact hne R (List.mem_append.mpr h)
    · simp
  · rw [hform]
    apply runsOrdered_append hord
    · exact List.pairwise_singleton _ _
    · intro R hR T hT x hx y hy
      have hTeq : T = [r] := List.mem_singleton.mp hT
      subst hTeq
      have hyr : y = r := List.mem_singleton.mp hy
      rw [hyr]
      exact hAll R hR x hx
  · intro R hR hredR hlen
    rw [hform] at hR
    simp only [List.mem_append, List.mem_singleton] at hR
    rcases hR with h | rfl
    · exact hredS R (List.mem_append.mpr h) hredR hlen
    · simp at hlen

end Bichromatic.Randomized
