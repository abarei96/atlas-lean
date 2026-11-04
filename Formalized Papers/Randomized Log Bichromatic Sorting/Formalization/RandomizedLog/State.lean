import RandomizedLog.Algorithm

/-!
# SpliceSort working state and its invariant (randomized paper, §2)

The working sequence is decomposed into monochromatic runs. The paper's
3-part invariant, at the level of the run list, is:

(i)   runs are ordered relative to one another: every element of an
      earlier run is smaller than every element of a later run;
(ii)  every red run with at least two elements is sorted (it is
      "activated and stored in increasing order");
(iii) red singletons are the "unactivated" runs — no condition.

This file defines the run decomposition and the invariant, and proves
that the run-level insertion operations of the paper preserve (i):
inserting a fresh red singleton between two parts (Case A, one-sided
scan), and merging `r` with a red singleton into a sorted activated
pair (Case B).
-/

namespace Bichromatic.Randomized

open Bichromatic

variable {X : Type*} [LinearOrder X] (color : X → Color)

/-- Prepend an element to a run list, merging with the first run when
the colours agree. -/
def consRun (a : X) : List (List X) → List (List X)
  | [] => [[a]]
  | [] :: rs => [a] :: rs
  | (b :: bs) :: rs => if color a = color b then (a :: b :: bs) :: rs else [a] :: (b :: bs) :: rs

/-- The monochromatic run decomposition of a sequence. -/
def runsOf (l : List X) : List (List X) := l.foldr (consRun color) []

theorem consRun_flatten (a : X) (rs : List (List X)) :
    (consRun color a rs).flatten = a :: rs.flatten := by
  cases rs with
  | nil => rfl
  | cons R rs =>
      cases R with
      | nil => rfl
      | cons b bs =>
          by_cases hc : color a = color b <;> simp [consRun, hc, List.flatten_cons]

theorem runsOf_flatten (l : List X) : (runsOf color l).flatten = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      unfold runsOf at *
      rw [List.foldr_cons, consRun_flatten, ih]

theorem consRun_nonempty (a : X) {rs : List (List X)} (h : ∀ R ∈ rs, R ≠ []) :
    ∀ R ∈ consRun color a rs, R ≠ [] := by
  cases rs with
  | nil => intro R hR; simp only [consRun, List.mem_singleton] at hR; rw [hR]; simp
  | cons R rs =>
      cases R with
      | nil => exact absurd rfl (h [] (by simp))
      | cons b bs =>
          intro S hS
          by_cases hc : color a = color b
          · rw [consRun, if_pos hc] at hS
            cases hS with
            | head => simp
            | tail _ hS => exact h S (List.mem_cons_of_mem _ hS)
          · rw [consRun, if_neg hc] at hS
            cases hS with
            | head => simp
            | tail _ hS => exact h S hS

theorem runsOf_nonempty (l : List X) : ∀ R ∈ runsOf color l, R ≠ [] := by
  induction l with
  | nil => intro R hR; simp [runsOf] at hR
  | cons a t ih =>
      unfold runsOf at *
      rw [List.foldr_cons]
      exact consRun_nonempty color a ih

/-- Invariant (i): runs ordered relative to one another. -/
def RunsOrdered (rs : List (List X)) : Prop :=
  rs.Pairwise (fun R S => ∀ x ∈ R, ∀ y ∈ S, x < y)

theorem runsOrdered_append {rs₁ rs₂ : List (List X)}
    (h₁ : RunsOrdered rs₁) (h₂ : RunsOrdered rs₂)
    (hcross : ∀ R ∈ rs₁, ∀ S ∈ rs₂, ∀ x ∈ R, ∀ y ∈ S, x < y) :
    RunsOrdered (rs₁ ++ rs₂) :=
  List.pairwise_append.mpr ⟨h₁, h₂, hcross⟩

/-- Case A at run level: inserting a fresh red singleton `[r]` between
two parts of an ordered run list preserves run-order, provided every
element before is `< r` and `r` is below every element after. In the
paper these two facts are exactly what the binary search over
representatives and the one-sided scan certify. -/
theorem runsOrdered_insert_singleton {rs₁ rs₂ : List (List X)} (r : X)
    (h : RunsOrdered (rs₁ ++ rs₂))
    (hL : ∀ R ∈ rs₁, ∀ x ∈ R, x < r)
    (hR : ∀ S ∈ rs₂, ∀ y ∈ S, r < y) :
    RunsOrdered (rs₁ ++ [r] :: rs₂) := by
  obtain ⟨h₁, h₂, hcross⟩ := List.pairwise_append.mp h
  apply runsOrdered_append h₁
  · apply List.Pairwise.cons
    · intro S hS x hx y hy
      simp only [List.mem_singleton] at hx
      subst hx
      exact hR S hS y hy
    · exact h₂
  · intro R hR' S hS x hx y hy
    cases List.mem_cons.mp hS with
    | inl he =>
        subst he
        simp only [List.mem_singleton] at hy
        subst hy
        exact hL R hR' x hx
    | inr he => exact hcross R hR' S he x hx y hy

/-- Case B at run level: merging `r` with a red singleton `[r₀]` into
the sorted activated pair preserves run-order, provided both new
elements sit strictly between the surrounding parts (in the paper,
certified by the neighbours' one-sided scans and the single red-red
comparison that orders the pair). -/
theorem runsOrdered_merge_pair {rs₁ rs₂ : List (List X)} (r r₀ : X)
    (h : RunsOrdered (rs₁ ++ [r₀] :: rs₂))
    (hL : ∀ R ∈ rs₁, ∀ x ∈ R, x < r ∧ x < r₀)
    (hR : ∀ S ∈ rs₂, ∀ y ∈ S, r < y ∧ r₀ < y) :
    RunsOrdered (rs₁ ++ (if r < r₀ then [r, r₀] else [r₀, r]) :: rs₂) := by
  obtain ⟨h₁, h₂, hcross⟩ := List.pairwise_append.mp h
  obtain ⟨_, h₂tail⟩ := List.pairwise_cons.mp h₂
  apply runsOrdered_append h₁
  · apply List.Pairwise.cons
    · intro S hS x hx y hy
      split_ifs at hx with hr
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        cases hx with
        | inl he => rw [he]; exact (hR S hS y hy).1
        | inr he => rw [he]; exact (hR S hS y hy).2
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        cases hx with
        | inl he => rw [he]; exact (hR S hS y hy).2
        | inr he => rw [he]; exact (hR S hS y hy).1
    · exact h₂tail
  · intro R hR' S hS x hx y hy
    cases List.mem_cons.mp hS with
    | inl he =>
        cases he
        split_ifs at hy with hr
        · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
          cases hy with
          | inl he => rw [he]; exact (hL R hR' x hx).1
          | inr he => rw [he]; exact (hL R hR' x hx).2
        · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
          cases hy with
          | inl he => rw [he]; exact (hL R hR' x hx).2
          | inr he => rw [he]; exact (hL R hR' x hx).1
    | inr he => exact hcross R hR' S (List.mem_cons_of_mem _ he) x hx y hy

/-- The SpliceSort working state: a run decomposition of the working
sequence, with the paper's 3-part invariant as fields. -/
structure State where
  /-- Monochromatic runs of the working sequence, in order. -/
  runs : List (List X)
  /-- Every run is nonempty. -/
  nonempty : ∀ R ∈ runs, R ≠ []
  /-- Invariant (i): runs are ordered relative to one another. -/
  ordered : RunsOrdered runs
  /-- Invariant (ii): every red run with at least two elements is
  sorted increasingly (activated). (iii) constrains singletons only by
  absence of a condition. -/
  redSorted : ∀ R ∈ runs, (∀ x ∈ R, color x = Color.red) → 2 ≤ R.length →
    R.Pairwise (· ≤ ·)

/-- Element comparison from run order: in an ordered run list, every
element of an earlier run is below every element of a later run. -/
theorem runsOrdered_getElem {rs : List (List X)} (h : RunsOrdered rs)
    {i j : ℕ} (hi : i < rs.length) (hj : j < rs.length) (hij : i < j)
    {x y : X} (hx : x ∈ rs[i]) (hy : y ∈ rs[j]) : x < y := by
  have hrel := (List.pairwise_iff_getElem.mp h) i j hi hj hij
  exact hrel x hx y hy

/-- **Location certificates, left side.** This is the paper's
`lem:location` in the form the invariant proof consumes: if `k` is the
location index of `r` over representatives aligned with the runs, then
every element of a run at least two positions before `k` is below `r`.
(The run immediately before `k` is handled by the candidate analysis,
not by location alone.) Proof: an element of run `i` is below the
representative of run `i+1` by run-order, and that representative is
below `r` by the location property. -/
theorem cert_left {runs : List (List X)} {reps : List X} {r : X}
    (hord : RunsOrdered runs)
    (hlen : reps.length = runs.length)
    (hmem : ∀ (i : ℕ) (hi : i < reps.length), reps[i] ∈ runs[i]'(hlen ▸ hi))
    (hne : ∀ y ∈ reps, y ≠ r)
    {i : ℕ} (hi : i + 1 < locate reps r) {x : X}
    (hi_len : i < runs.length) (hx : x ∈ runs[i]) : x < r := by
  have hi1_len : i + 1 < reps.length := lt_of_lt_of_le hi (locate_le_length reps r)
  have hrep : reps[i + 1] ∈ runs[i + 1]'(by omega) := hmem (i + 1) hi1_len
  have h1 : x < reps[i + 1] :=
    runsOrdered_getElem hord (i := i) (j := i + 1) (by omega) (by omega)
      (by omega) hx hrep
  have h2 : reps[i + 1] < r :=
    getElem_lt_of_lt_locate reps r hne (i + 1) hi1_len hi
  exact lt_trans h1 h2

/-- **Location certificates, right side.** Every element of a run after
the location index `k` exceeds `r`: `r` is below the representative of
run `k` by the location property, and that representative is below
every element of a later run by run-order. -/
theorem cert_right {runs : List (List X)} {reps : List X} {r : X}
    (hord : RunsOrdered runs)
    (hlen : reps.length = runs.length)
    (hmem : ∀ (i : ℕ) (hi : i < reps.length), reps[i] ∈ runs[i]'(hlen ▸ hi))
    {i : ℕ} (hi : locate reps r < i)
    (hi_len : i < runs.length) {y : X} (hy : y ∈ runs[i]) : r < y := by
  have hk_len : locate reps r < reps.length := by omega
  have h1 : r < reps[locate reps r] := lt_getElem_locate reps r hk_len
  have hrep : reps[locate reps r] ∈ runs[locate reps r]'(by omega) :=
    hmem (locate reps r) hk_len
  have h2 : reps[locate reps r] < y :=
    runsOrdered_getElem hord (i := locate reps r) (j := i) (by omega)
      hi_len hi hrep hy
  exact lt_trans h1 h2

/-- Case C / replacement at run level: replacing a run `S` by a new run
`S'` whose elements are `r` or old elements of `S` preserves run-order,
provided `r` separates the two sides. Case C of the paper (insertion
into an activated run, or attachment at its end) has exactly this form,
with `S'` the sorted insertion of `r` into `S`. -/
theorem runsOrdered_replace_run {rs₁ rs₂ : List (List X)} {S S' : List X} (r : X)
    (h : RunsOrdered (rs₁ ++ S :: rs₂))
    (hmem : ∀ x ∈ S', x = r ∨ x ∈ S)
    (hL : ∀ R ∈ rs₁, ∀ x ∈ R, x < r)
    (hR : ∀ T ∈ rs₂, ∀ y ∈ T, r < y) :
    RunsOrdered (rs₁ ++ S' :: rs₂) := by
  obtain ⟨h₁, h₂, hcross⟩ := List.pairwise_append.mp h
  obtain ⟨hSrel, h₂tail⟩ := List.pairwise_cons.mp h₂
  apply runsOrdered_append h₁
  · apply List.Pairwise.cons
    · intro T hT x hx y hy
      cases hmem x hx with
      | inl he => rw [he]; exact hR T hT y hy
      | inr he => exact hSrel T hT x he y hy
    · exact h₂tail
  · intro R hR' T hT x hx y hy
    cases List.mem_cons.mp hT with
    | inl he =>
        cases he
        cases hmem y hy with
        | inl he => rw [he]; exact hL R hR' x hx
        | inr he => exact hcross R hR' _ (List.mem_cons_self) x hx y he
    | inr he => exact hcross R hR' T (List.mem_cons_of_mem _ he) x hx y hy

/-- Mixed-scan split at run level: replacing a run `C` by
`below :: [r] :: above` (the pieces of `C` around a new red singleton,
as in `splice`) preserves run-order, provided `below` and `above`
consist of old elements of `C`, `r` separates them, and `r` separates
the surrounding parts. These are exactly the facts the mixed scan and
the location step certify in the paper. -/
theorem runsOrdered_splice_runs {A B : List (List X)} {C below above : List X} (r : X)
    (h : RunsOrdered (A ++ C :: B))
    (hsub_b : ∀ x ∈ below, x ∈ C) (hsub_a : ∀ x ∈ above, x ∈ C)
    (hbr : ∀ x ∈ below, x < r) (har : ∀ y ∈ above, r < y)
    (hAr : ∀ R ∈ A, ∀ x ∈ R, x < r) (hrB : ∀ T ∈ B, ∀ y ∈ T, r < y) :
    RunsOrdered (A ++ below :: [r] :: above :: B) := by
  obtain ⟨hA, hCB, hcrossA⟩ := List.pairwise_append.mp h
  obtain ⟨hCrel, hB⟩ := List.pairwise_cons.mp hCB
  have hC_B : ∀ x ∈ C, ∀ T ∈ B, ∀ y ∈ T, x < y := by
    intro x hx T hT y hy; exact hCrel T hT x hx y hy
  have hA_C : ∀ R ∈ A, ∀ x ∈ R, ∀ z ∈ C, x < z := by
    intro R hR x hx z hz; exact hcrossA R hR _ (List.mem_cons_self) x hx z hz
  apply runsOrdered_append hA
  · -- Pairwise (below :: [r] :: above :: B)
    apply List.Pairwise.cons
    · intro S hS x hx y hy
      cases List.mem_cons.mp hS with
      | inl he =>
          cases he; simp only [List.mem_singleton] at hy; rw [hy]; exact hbr x hx
      | inr he =>
          cases List.mem_cons.mp he with
          | inl he2 =>
              cases he2; exact lt_trans (hbr x hx) (har y hy)
          | inr he2 => exact hC_B x (hsub_b x hx) _ he2 y hy
    · apply List.Pairwise.cons
      · intro S hS x hx y hy
        simp only [List.mem_singleton] at hx; rw [hx]
        cases List.mem_cons.mp hS with
        | inl he => cases he; exact har y hy
        | inr he => exact hrB _ he y hy
      · apply List.Pairwise.cons
        · intro T hT x hx y hy; exact hC_B x (hsub_a x hx) T hT y hy
        · exact hB
  · -- cross: A against below :: [r] :: above :: B
    intro R hR S hS x hx y hy
    cases List.mem_cons.mp hS with
    | inl he => cases he; exact hA_C R hR x hx y (hsub_b y hy)
    | inr he =>
        cases List.mem_cons.mp he with
        | inl he2 =>
            cases he2; simp only [List.mem_singleton] at hy; rw [hy]; exact hAr R hR x hx
        | inr he2 =>
            cases List.mem_cons.mp he2 with
            | inl he3 => cases he3; exact hA_C R hR x hx y (hsub_a y hy)
            | inr he3 =>
                exact hcrossA R hR _ (List.mem_cons_of_mem _ he3) x hx y hy

end Bichromatic.Randomized
