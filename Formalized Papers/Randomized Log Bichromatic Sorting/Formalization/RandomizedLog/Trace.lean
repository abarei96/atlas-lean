import RandomizedLog.Cost
import RandomizedLog.Records

/-!
# SpliceSort execution trace and the ordinary-record lemma

An execution is a sequence of run-list states, one per inserted red
element (arrivals, in arrival order). A step is one of the four
verified operations, *together with its certificates* — the separation
facts that the paper's location step (`cert_left`/`cert_right`) and
scans produce. This file proves:

* every step preserves the full invariant bundle (3-part invariant,
  monochromatic runs, and the element provenance
  `flatten σ' ~ r :: flatten σ`);
* hence every state of every trace satisfies the bundle, with
  `flatten σ ~ arrivals ++ flatten σ₀` (provenance by induction);
* the paper's `lem:ordinaryrecord` for split incidences: if the
  insertion of `r` splits a blue run `C ∋ b` with a mixed verdict,
  then `r` is a record for `b` — earlier red elements sit in runs
  before or after `C`, hence outside `[min C, max C]`, while the
  interval between `r` and `b` lies inside it.
-/

namespace Bichromatic.Randomized

open Bichromatic

variable {X : Type*} [LinearOrder X] (color : X → Color)

/-- Every run is monochromatic. -/
def MonoRuns (runs : List (List X)) : Prop :=
  ∀ R ∈ runs, (∀ x ∈ R, color x = Color.red) ∨ (∀ x ∈ R, color x = Color.blue)

/-- One insertion step: an operation at decomposition `A ++ S :: B`,
with the certificates its invariant proof consumes. -/
inductive Step : List (List X) → X → List (List X) → Prop where
  | freshSingleton (A B : List (List X)) (S : List X) (r : X)
      (hL : ∀ R ∈ A, ∀ x ∈ R, x < r)
      (hR : ∀ T ∈ S :: B, ∀ y ∈ T, r < y) :
      Step (A ++ S :: B) r (applyOp A B S r .freshSingleton)
  | appendSingleton (A B : List (List X)) (S : List X) (r : X)
      (hAll : ∀ T ∈ A ++ S :: B, ∀ y ∈ T, y < r) :
      Step (A ++ S :: B) r (applyOp A B S r .appendSingleton)
  | mergePair (A B : List (List X)) (S : List X) (r r₀ : X) (hS : S = [r₀])
      (hSred : ∀ x ∈ S, color x = Color.red)
      (hL : ∀ R ∈ A, ∀ x ∈ R, x < r ∧ x < r₀)
      (hR : ∀ T ∈ B, ∀ y ∈ T, r < y ∧ r₀ < y) :
      Step (A ++ S :: B) r (applyOp A B S r (.mergePair r₀))
  | insertInto (A B : List (List X)) (S : List X) (r : X)
      (hSred : ∀ x ∈ S, color x = Color.red)
      (hL : ∀ R ∈ A, ∀ x ∈ R, x < r)
      (hR : ∀ T ∈ B, ∀ y ∈ T, r < y) :
      Step (A ++ S :: B) r (applyOp A B S r .insertInto)
  | splitRun (A B : List (List X)) (S below above : List X) (r : X)
      (hsub_b : ∀ x ∈ below, x ∈ S) (hsub_a : ∀ x ∈ above, x ∈ S)
      (hblue : ∀ x ∈ S, color x = Color.blue)
      (hbne : below ≠ []) (hane : above ≠ [])
      (hbr : ∀ x ∈ below, x < r) (har : ∀ y ∈ above, r < y)
      (hAr : ∀ R ∈ A, ∀ x ∈ R, x < r) (hrB : ∀ T ∈ B, ∀ y ∈ T, r < y)
      (hpart : (below ++ above).Perm S) :
      Step (A ++ S :: B) r (applyOp A B S r (.splitRun below above))

/-- A trace: states linked by steps, processing arrivals in order. -/
inductive TraceFrom : List (List X) → List X → List (List X) → Prop where
  | nil (σ : List (List X)) : TraceFrom σ [] σ
  | cons {σ σ' σ'' : List (List X)} {r : X} {rest : List X} :
      Step color σ r σ' → TraceFrom σ' rest σ'' → TraceFrom σ (r :: rest) σ''

/-- Move the second element of an appended pair to the front. -/
theorem perm_move2 (l1 l2 : List X) (a b : X) :
    (l1 ++ a :: b :: l2).Perm (b :: (l1 ++ a :: l2)) :=
  List.perm_middle.trans
    ((List.Perm.cons a List.perm_middle).trans
      ((List.Perm.swap b a _).trans (List.Perm.cons b List.perm_middle.symm)))

/-- Sorted insertion permutes with cons: the multiset of elements is
the old run plus `r`. -/
theorem insertSorted_perm {r : X} {S : List X} : (insertSorted r S).Perm (r :: S) := by
  induction S with
  | nil => rfl
  | cons a as ih =>
      unfold insertSorted
      split_ifs with h
      · rfl
      · have h1 : (a :: insertSorted r as).Perm (a :: r :: as) := List.Perm.cons a ih
        exact h1.trans (List.Perm.swap r a as)

theorem flatten_freshSingleton {A B : List (List X)} {S : List X} {r : X} :
    (applyOp A B S r .freshSingleton).flatten.Perm (r :: (A ++ S :: B).flatten) := by
  have h1 : (applyOp A B S r .freshSingleton).flatten
      = A.flatten ++ r :: (S ++ B.flatten) := by
    simp [applyOp, List.flatten_append, List.flatten_cons]
  have h2 : (A ++ S :: B).flatten = A.flatten ++ (S ++ B.flatten) := by
    simp [List.flatten_append, List.flatten_cons]
  rw [h1, h2]
  exact List.perm_middle

theorem flatten_mergePair {A B : List (List X)} {S : List X} {r r₀ : X} (hS : S = [r₀]) :
    (applyOp A B S r (.mergePair r₀)).flatten.Perm (r :: (A ++ S :: B).flatten) := by
  have h1 : (applyOp A B S r (.mergePair r₀)).flatten
      = A.flatten ++ (if r < r₀ then [r, r₀] else [r₀, r]) ++ B.flatten := by
    simp [applyOp, List.flatten_append, List.flatten_cons]
  have h2 : (A ++ S :: B).flatten = A.flatten ++ (S ++ B.flatten) := by
    simp [List.flatten_append, List.flatten_cons]
  rw [h1, h2, hS]
  split_ifs with h
  · simp only [List.append_assoc]
    exact List.perm_middle
  · simp only [List.append_assoc]
    have : A.flatten ++ ([r₀, r] ++ B.flatten) = A.flatten ++ (r₀ :: r :: B.flatten) := by
      simp [List.append_assoc]
    rw [this]
    exact perm_move2 A.flatten B.flatten r₀ r

theorem flatten_insertInto {A B : List (List X)} {S : List X} {r : X} :
    (applyOp A B S r .insertInto).flatten.Perm (r :: (A ++ S :: B).flatten) := by
  have h1 : (applyOp A B S r .insertInto).flatten
      = A.flatten ++ (insertSorted r S) ++ B.flatten := by
    simp [applyOp, List.flatten_append, List.flatten_cons]
  have h2 : (A ++ S :: B).flatten = A.flatten ++ (S ++ B.flatten) := by
    simp [List.flatten_append, List.flatten_cons]
  rw [h1, h2]
  have hp := insertSorted_perm (r := r) (S := S)
  have := (List.Perm.append_left A.flatten hp).append_right B.flatten
  exact this.trans (by simp [List.append_assoc, List.perm_middle])

theorem flatten_splitRun {A B : List (List X)} {S below above : List X} {r : X}
    (hpart : (below ++ above).Perm S) :
    (applyOp A B S r (.splitRun below above)).flatten.Perm (r :: (A ++ S :: B).flatten) := by
  have h1 : (applyOp A B S r (.splitRun below above)).flatten
      = A.flatten ++ (below ++ r :: above) ++ B.flatten := by
    simp [applyOp, List.flatten_append, List.flatten_cons, List.append_assoc]
  have h2 : (A ++ S :: B).flatten = A.flatten ++ (S ++ B.flatten) := by
    simp [List.flatten_append, List.flatten_cons]
  rw [h1, h2]
  have hp : (below ++ r :: above).Perm (r :: S) :=
    (List.perm_middle).trans (List.Perm.cons r hpart)
  have := (List.Perm.append_left A.flatten hp).append_right B.flatten
  exact this.trans (by simp [List.append_assoc, List.perm_middle])

/-- Provenance for an appended singleton: the new flattening is the
old one with `r` at the end, hence a permutation of `r` consed. -/
theorem flatten_appendSingleton {A B : List (List X)} {S : List X} {r : X} :
    (applyOp A B S r .appendSingleton).flatten.Perm (r :: (A ++ S :: B).flatten) := by
  have h1 : (applyOp A B S r .appendSingleton).flatten
      = (A ++ S :: B).flatten ++ [r] := by
    simp [applyOp, List.flatten_append]
  rw [h1]
  exact List.perm_append_comm

/-- A step's element provenance: the new state's elements are the old
ones plus `r`. -/
theorem step_flatten {σ : List (List X)} {r : X} {σ' : List (List X)}
    (h : Step color σ r σ') : σ'.flatten.Perm (r :: σ.flatten) := by
  cases h with
  | freshSingleton A B S r hL hR => exact flatten_freshSingleton
  | appendSingleton A B S r hAll => exact flatten_appendSingleton
  | mergePair A B S r r₀ hS hSred hL hR => exact flatten_mergePair hS
  | insertInto A B S r hSred hL hR => exact flatten_insertInto
  | splitRun A B S below above r hsub_b hsub_a hblue hbne hane hbr har hAr hrB hpart =>
      exact flatten_splitRun hpart

/-- Monochromaticity is preserved by each operation: the new runs are
`[r]` (red), the merged pair (both red), the sorted insertion into a
red run, or pieces of a blue run. -/
theorem step_mono {σ : List (List X)} {r : X} {σ' : List (List X)}
    (h : Step color σ r σ') (hmono : MonoRuns color σ) (hred : color r = Color.red) :
    MonoRuns color σ' := by
  cases h with
  | freshSingleton A B S r hL hR =>
      intro R hR
      simp only [applyOp, List.mem_append, List.mem_cons] at hR
      cases hR with
      | inl h => exact hmono R (by simp [List.mem_append, h])
      | inr h =>
          cases h with
          | inl he => rw [he]; left; intro x hx; simp at hx; rw [hx]; exact hred
          | inr h => exact hmono R (by simp [List.mem_append, List.mem_cons, h])
  | appendSingleton A B S r hAll =>
      intro R hR
      simp only [applyOp, List.mem_append, List.mem_singleton] at hR
      rcases hR with h | rfl
      · exact hmono R (List.mem_append.mpr h)
      · left; intro x hx; simp at hx; rw [hx]; exact hred
  | mergePair A B S r r₀ hS hSred hL hR =>
      intro R hR
      simp only [applyOp, List.mem_append, List.mem_cons] at hR
      cases hR with
      | inl h => exact hmono R (by simp [List.mem_append, h])
      | inr h =>
          cases h with
          | inl he =>
              rw [he]; left
              intro x hx
              have hr0 : color r₀ = Color.red := hSred r₀ (by rw [hS]; simp)
              split_ifs at hx
              · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
                cases hx with
                | inl hxx => rw [hxx]; exact hred
                | inr hxx => rw [hxx]; exact hr0
              · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
                cases hx with
                | inl hxx => rw [hxx]; exact hr0
                | inr hxx => rw [hxx]; exact hred
          | inr h => exact hmono R (by simp [List.mem_append, List.mem_cons, h])
  | insertInto A B S r hSred hL hR =>
      intro R hR
      simp only [applyOp, List.mem_append, List.mem_cons] at hR
      cases hR with
      | inl h => exact hmono R (by simp [List.mem_append, h])
      | inr h =>
          cases h with
          | inl he =>
              rw [he]; left
              intro x hx
              rw [insertSorted_mem] at hx
              cases hx with
              | inl hxx => rw [hxx]; exact hred
              | inr hxx => exact hSred x hxx
          | inr h => exact hmono R (by simp [List.mem_append, List.mem_cons, h])
  | splitRun A B S below above r hsub_b hsub_a hblue hbne hane hbr har hAr hrB hpart =>
      intro R hR
      simp only [applyOp, List.mem_append, List.mem_cons] at hR
      cases hR with
      | inl h => exact hmono R (by simp [List.mem_append, h])
      | inr h =>
          cases h with
          | inl he => rw [he]; right; intro x hx; exact hblue x (hsub_b x hx)
          | inr h =>
              cases h with
              | inl he => rw [he]; left; intro x hx; simp at hx; rw [hx]; exact hred
              | inr h =>
                  cases h with
                  | inl he => rw [he]; right; intro x hx; exact hblue x (hsub_a x hx)
                  | inr h => exact hmono R (by simp [List.mem_append, List.mem_cons, h])

/-- A step preserves the invariant bundle. -/
theorem step_invariant {σ : List (List X)} {r : X} {σ' : List (List X)}
    (h : Step color σ r σ') (hinv : Invariant color σ) (hmono : MonoRuns color σ)
    (hred : color r = Color.red) :
    Invariant color σ' ∧ MonoRuns color σ' := by
  refine ⟨?_, step_mono color h hmono hred⟩
  cases h with
  | freshSingleton A B S r hL hR => exact invariant_freshSingleton color hinv hL hR
  | appendSingleton A B S r hAll => exact invariant_appendSingleton color hinv hAll
  | mergePair A B S r r₀ hS hSred hL hR => exact invariant_mergePair color hinv hS hL hR
  | insertInto A B S r hSred hL hR => exact invariant_insertInto color hinv hL hR
  | splitRun A B S below above r hsub_b hsub_a hblue hbne hane hbr har hAr hrB hpart =>
      exact invariant_splitRun color hinv hsub_b hsub_a hblue hbne hane hbr har hAr hrB

/-- Every state of a trace satisfies the bundle, and the elements are
exactly the initial elements plus the arrivals (provenance). -/
theorem trace_invariant {σ0 : List (List X)} {L : List X} {σ' : List (List X)}
    (htr : TraceFrom color σ0 L σ') (hinv : Invariant color σ0) (hmono : MonoRuns color σ0)
    (hred : ∀ r ∈ L, color r = Color.red) :
    Invariant color σ' ∧ MonoRuns color σ' ∧ σ'.flatten.Perm (L ++ σ0.flatten) := by
  induction htr with
  | nil σ => exact ⟨hinv, hmono, List.Perm.refl _⟩
  | cons hstep _ ih =>
      have hredr : color _ = Color.red := hred _ (List.mem_cons_self)
      obtain ⟨hinv', hmono'⟩ := step_invariant color hstep hinv hmono hredr
      obtain ⟨hinv'', hmono'', hperm⟩ := ih hinv' hmono'
        (fun r hr => hred r (List.mem_cons_of_mem _ hr))
      refine ⟨hinv'', hmono'', ?_⟩
      have hf := step_flatten color hstep
      exact hperm.trans ((List.Perm.append_left _ hf).trans (by
        simp [List.perm_middle]))

/-- **Ordinary-record lemma, split case** (paper `lem:ordinaryrecord`).
If the insertion of `r` splits a blue run `C ∋ b` with a mixed verdict
(the `below`/`above` pieces, both nonempty), and every earlier-arriving
red element is present in the current state, then `r` is a record for
`b`: earlier red elements sit in runs before or after `C`, hence
outside `[min C, max C]`, while the interval between `r` and `b` lies
inside it. -/
theorem split_record {A B : List (List X)} {C below above : List X} {r b : X}
    (hord : RunsOrdered (A ++ C :: B))
    (hsub_b : ∀ x ∈ below, x ∈ C) (hsub_a : ∀ x ∈ above, x ∈ C)
    (hbne : below ≠ []) (hane : above ≠ [])
    (hbr : ∀ x ∈ below, x < r) (har : ∀ y ∈ above, r < y)
    (hb : b ∈ C) (hblue : ∀ x ∈ C, color x = Color.blue) (hred : color r = Color.red)
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (hpresent : ∀ r' : X, color r' = Color.red → τ r' < τ r → r' ∈ (A ++ C :: B).flatten) :
    IsRecord color τ b r := by
  classical
  obtain ⟨c1, hc1b, hc1r⟩ : ∃ c ∈ below, c < r := by
    cases below with
    | nil => simp at hbne
    | cons x xs => exact ⟨x, by simp, hbr x (by simp)⟩
  obtain ⟨c2, hc2a, hc2r⟩ : ∃ c ∈ above, r < c := by
    cases above with
    | nil => simp at hane
    | cons x xs => exact ⟨x, by simp, har x (by simp)⟩
  have hc1 : c1 ∈ C := hsub_b c1 hc1b
  have hc2 : c2 ∈ C := hsub_a c2 hc2a
  have hne : r ≠ b := by
    intro hcon
    have h1 : color r = Color.blue := by rw [hcon]; exact hblue b hb
    rw [hred] at h1
    exact Color.noConfusion h1
  -- index of C in the run list
  have hCidx : (A ++ C :: B)[A.length]'(by simp) = C := by simp
  have key : ∀ r' : X, color r' = Color.red → (r < r' ∧ r' < b) ∨ (b < r' ∧ r' < r) →
      τ r < τ r' := by
    intro r' hr' hinter
    by_contra hcon
    have hlt : τ r' < τ r := by
      have hle : τ r' ≤ τ r := Nat.le_of_not_lt hcon
      exact lt_of_le_of_ne hle (fun hcon2 => by
        have heq : r' = r := hinj hcon2
        subst heq
        cases hinter with
        | inl h => exact lt_irrefl _ h.1
        | inr h => exact lt_irrefl _ h.2)
    have hmem := hpresent r' hr' hlt
    rw [List.mem_flatten] at hmem
    obtain ⟨R, hRruns, hRr⟩ := hmem
    obtain ⟨i, hi, hRi⟩ := List.mem_iff_getElem.mp hRruns
    have hiC : i ≠ A.length := by
      intro hcon
      subst hcon
      have hCC : (A ++ C :: B)[A.length]'hi = C := hCidx
      rw [hCC] at hRi
      rw [← hRi] at hRr
      have hcb : color r' = Color.blue := hblue r' hRr
      rw [hr'] at hcb
      exact Color.noConfusion hcb
    cases lt_trichotomy i A.length with
    | inl hi_lt =>
        have hlt1 : r' < c1 :=
          runsOrdered_getElem hord hi (by simp) hi_lt (by rw [hRi]; exact hRr)
            (by rw [hCidx]; exact hc1)
        have hr'lt : r' < r := lt_trans hlt1 hc1r
        cases hinter with
        | inl h => exact absurd h.1 (not_lt.mpr (le_of_lt hr'lt))
        | inr h =>
            have hltb : r' < b :=
              runsOrdered_getElem hord hi (by simp) hi_lt (by rw [hRi]; exact hRr)
                (by rw [hCidx]; exact hb)
            exact absurd h.1 (not_lt.mpr (le_of_lt hltb))
    | inr hgt =>
        cases hgt with
        | inl hcon => exact absurd hcon hiC
        | inr hi_gt =>
            have hlt2 : c2 < r' :=
              runsOrdered_getElem hord (by simp) hi hi_gt (by rw [hCidx]; exact hc2)
                (by rw [hRi]; exact hRr)
            have hlt3 : b < r' :=
              runsOrdered_getElem hord (by simp) hi hi_gt (by rw [hCidx]; exact hb)
                (by rw [hRi]; exact hRr)
            cases hinter with
            | inl h => exact absurd h.2 (not_lt.mpr (le_of_lt hlt3))
            | inr h => exact absurd h.2 (not_lt.mpr (le_of_lt (lt_trans hc2r hlt2)))
  cases lt_trichotomy r b with
  | inl h =>
      exact Or.inl ⟨hred, h, fun r' hr' h1 h2 => key r' hr' (Or.inl ⟨h1, h2⟩)⟩
  | inr hgt =>
      cases hgt with
      | inl hcon => exact absurd hcon hne
      | inr h =>
          exact Or.inr ⟨hred, h, fun r' hr' h1 h2 => key r' hr' (Or.inr ⟨h1, h2⟩)⟩

/-- The τ-half of every ordinary-record argument, extracted: if every
earlier-arriving red element in the interval between `r` and `b` is
excluded geometrically (the separation hypothesis), then `r` is a
record for `b`. -/
theorem record_key {r b : X} (hred : color r = Color.red) (hne : r ≠ b)
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (key : ∀ r' : X, color r' = Color.red →
      (r < r' ∧ r' < b) ∨ (b < r' ∧ r' < r) → τ r < τ r') :
    IsRecord color τ b r := by
  cases lt_trichotomy r b with
  | inl h => exact Or.inl ⟨hred, h, fun r' hr' h1 h2 => key r' hr' (Or.inl ⟨h1, h2⟩)⟩
  | inr hgt =>
      cases hgt with
      | inl hcon => exact absurd hcon hne
      | inr h => exact Or.inr ⟨hred, h, fun r' hr' h1 h2 => key r' hr' (Or.inr ⟨h1, h2⟩)⟩

/-- Separation implies the record key, given provenance: an earlier
red element in the interval would be present in the state, and the
separation hypothesis excludes present red elements from the interval. -/
theorem record_key_of_separation {runs : List (List X)} {r b : X}
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (hpresent : ∀ r' : X, color r' = Color.red → τ r' < τ r → r' ∈ runs.flatten)
    (hsep : ∀ r' : X, color r' = Color.red → r' ∈ runs.flatten →
      ¬ ((r < r' ∧ r' < b) ∨ (b < r' ∧ r' < r))) :
    ∀ r' : X, color r' = Color.red →
      (r < r' ∧ r' < b) ∨ (b < r' ∧ r' < r) → τ r < τ r' := by
  intro r' hr' hinter
  by_contra hcon
  have hlt : τ r' < τ r := by
    have hle : τ r' ≤ τ r := Nat.le_of_not_lt hcon
    exact lt_of_le_of_ne hle (fun hcon2 => by
      have heq : r' = r := hinj hcon2
      subst heq
      cases hinter with
      | inl h => exact lt_irrefl _ h.1
      | inr h => exact lt_irrefl _ h.2)
  exact hsep r' hr' (hpresent r' hr' hlt) hinter

/-- **Ordinary-record lemma, creator case.** A creator scan at an end:
`C` is the last run, the scan is one-sided with every element of `C`
below `r`, and `b ∈ C`. Earlier red elements sit in runs before `C`,
hence below `b`, so the interval `(b, r)` contains no earlier red:
`r` is a successor record for `b`. (The mirror configuration is
symmetric.) -/
theorem creator_record {A : List (List X)} {C : List X} {r b : X}
    (hord : RunsOrdered (A ++ [C]))
    (hbelow : ∀ x ∈ C, x < r)
    (hb : b ∈ C) (hblue : ∀ x ∈ C, color x = Color.blue) (hred : color r = Color.red)
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (hpresent : ∀ r' : X, color r' = Color.red → τ r' < τ r → r' ∈ (A ++ [C]).flatten) :
    IsRecord color τ b r := by
  have hne : r ≠ b := by
    intro hcon
    have h1 : color r = Color.blue := by rw [hcon]; exact hblue b hb
    rw [hred] at h1
    exact Color.noConfusion h1
  apply record_key color hred hne τ hinj
  apply record_key_of_separation color τ hinj hpresent
  intro r' hr' hmem hinter
  rw [List.mem_flatten] at hmem
  obtain ⟨R, hRruns, hRr⟩ := hmem
  obtain ⟨i, hi, hRi⟩ := List.mem_iff_getElem.mp hRruns
  have hCidx : (A ++ [C])[A.length]'(by simp) = C := by simp
  have hiC : i ≠ A.length := by
    intro hcon
    subst hcon
    have hCC : (A ++ [C])[A.length]'hi = C := hCidx
    rw [hCC] at hRi
    rw [← hRi] at hRr
    have hcb : color r' = Color.blue := hblue r' hRr
    rw [hr'] at hcb
    exact Color.noConfusion hcb
  cases lt_or_gt_of_ne hiC with
  | inl hi_lt =>
      have hlt : r' < b :=
        runsOrdered_getElem hord hi (by simp) hi_lt (by rw [hRi]; exact hRr)
          (by rw [hCidx]; exact hb)
      cases hinter with
      | inl h => exact absurd h.1 (not_lt.mpr (le_of_lt (lt_trans hlt (hbelow b hb))))
      | inr h => exact absurd h.1 (not_lt.mpr (le_of_lt hlt))
  | inr hi_gt =>
      -- no run after the last run: i < length = A.length + 1 and i ≠ A.length gives i < A.length, contradiction
      have hlen : (A ++ [C]).length = A.length + 1 := by simp
      omega

/-- **Ordinary-record lemma, activated-merger case.** `C` is the blue
run adjacent below the activated red run `S`, with `b < r < min S` for
all `b ∈ C`. Earlier red elements before `C` are below `b`; those in
`S` or later are above `r`; so `r` is a successor record for `b`. -/
theorem merger_record {A B : List (List X)} {C S : List X} {r b : X}
    (hord : RunsOrdered (A ++ C :: S :: B))
    (hbC : ∀ x ∈ C, x < r) (hrS : ∀ x ∈ S, r < x)
    (hSne : S ≠ [])
    (hb : b ∈ C) (hblue : ∀ x ∈ C, color x = Color.blue) (hred : color r = Color.red)
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (hpresent : ∀ r' : X, color r' = Color.red → τ r' < τ r → r' ∈ (A ++ C :: S :: B).flatten) :
    IsRecord color τ b r := by
  have hne : r ≠ b := by
    intro hcon
    have h1 : color r = Color.blue := by rw [hcon]; exact hblue b hb
    rw [hred] at h1
    exact Color.noConfusion h1
  apply record_key color hred hne τ hinj
  apply record_key_of_separation color τ hinj hpresent
  intro r' hr' hmem hinter
  rw [List.mem_flatten] at hmem
  obtain ⟨R, hRruns, hRr⟩ := hmem
  obtain ⟨i, hi, hRi⟩ := List.mem_iff_getElem.mp hRruns
  have hCidx : (A ++ C :: S :: B)[A.length]'(by simp) = C := by simp
  have hSidx : (A ++ C :: S :: B)[A.length + 1]'(by simp) = S := by simp
  have hiC : i ≠ A.length := by
    intro hcon
    subst hcon
    have hCC : (A ++ C :: S :: B)[A.length]'hi = C := hCidx
    rw [hCC] at hRi
    rw [← hRi] at hRr
    have hcb : color r' = Color.blue := hblue r' hRr
    rw [hr'] at hcb
    exact Color.noConfusion hcb
  cases lt_trichotomy i A.length with
  | inl hi_lt =>
      have hlt : r' < b :=
        runsOrdered_getElem hord hi (by simp) hi_lt (by rw [hRi]; exact hRr)
          (by rw [hCidx]; exact hb)
      cases hinter with
      | inl h => exact absurd h.1 (not_lt.mpr (le_of_lt (lt_trans hlt (hbC b hb))))
      | inr h => exact absurd h.1 (not_lt.mpr (le_of_lt hlt))
  | inr hgt =>
      cases hgt with
      | inl hcon => exact absurd hcon hiC
      | inr hi_gt =>
          by_cases hiS : i = A.length + 1
          · subst hiS
            have hSS : (A ++ C :: S :: B)[A.length + 1]'hi = S := hSidx
            rw [hSS] at hRi
            rw [← hRi] at hRr
            have hrr : r < r' := hrS r' hRr
            cases hinter with
            | inl h => exact absurd h.2 (not_lt.mpr (le_of_lt (lt_trans (hbC b hb) hrr)))
            | inr h => exact absurd h.2 (not_lt.mpr (le_of_lt hrr))
          · have hi_gt2 : A.length + 1 < i := by omega
            obtain ⟨s0, hs0⟩ : ∃ s0, s0 ∈ S := by
              cases S with
              | nil => simp at hSne
              | cons x xs => exact ⟨x, by simp⟩
            have hlt : s0 < r' :=
              runsOrdered_getElem hord (by simp) hi hi_gt2 (by rw [hSidx]; exact hs0)
                (by rw [hRi]; exact hRr)
            have hrr : r < r' := lt_trans (hrS s0 hs0) hlt
            cases hinter with
            | inl h => exact absurd h.2 (not_lt.mpr (le_of_lt (lt_trans (hbC b hb) hrr)))
            | inr h => exact absurd h.2 (not_lt.mpr (le_of_lt hrr))


/-- **Threshold-record lemma, predecessor case** (paper
`lem:foreignred`, geometric core). A foreign red `r` arrives below
the activated red run `S`, splitting the blue run `C` just below
`S` (witnessed by `c₀ ∈ C` with `c₀ < r`). Then `r` is a threshold
predecessor record for `a = min S`: earlier red elements in runs
before `C` are below `c₀ < r`, those in `S` are at least `a`, and
those after `S` exceed `a`. The passage from the *tested* run `S`
to the *final* run `F` (so that `a = min F`) is the trace argument
of the paper; this is its state-level content at the testing
step. -/
theorem threshold_record {A B : List (List X)} {C S : List X} {r a : X}
    (hord : RunsOrdered (A ++ C :: S :: B))
    (hc₀ : ∃ c ∈ C, c < r)
    (hblue : ∀ x ∈ C, color x = Color.blue)
    (hSne : S ≠ []) (hamin : ∀ y ∈ S, a ≤ y)
    (hra : r < a) (hred : color r = Color.red)
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (hpresent : ∀ r' : X, color r' = Color.red → τ r' < τ r →
      r' ∈ (A ++ C :: S :: B).flatten) :
    IsPredRecord color τ a r := by
  obtain ⟨c₀, hc₀C, hc₀r⟩ := hc₀
  refine ⟨hred, hra, ?_⟩
  intro r' hr' h1 h2
  have key := record_key_of_separation color τ hinj hpresent
    (runs := A ++ C :: S :: B) (b := a) (by
    intro r' hr' hmem hinter
    rw [List.mem_flatten] at hmem
    obtain ⟨R, hRruns, hRr⟩ := hmem
    obtain ⟨i, hi, hRi⟩ := List.mem_iff_getElem.mp hRruns
    have hCidx : (A ++ C :: S :: B)[A.length]'(by simp) = C := by simp
    have hSidx : (A ++ C :: S :: B)[A.length + 1]'(by simp) = S := by simp
    have hiC : i ≠ A.length := by
      intro hcon
      subst hcon
      have hCC : (A ++ C :: S :: B)[A.length]'hi = C := hCidx
      rw [hCC] at hRi
      rw [← hRi] at hRr
      have hcb : color r' = Color.blue := hblue r' hRr
      rw [hr'] at hcb
      exact Color.noConfusion hcb
    cases lt_trichotomy i A.length with
    | inl hi_lt =>
        have hlt : r' < c₀ :=
          runsOrdered_getElem hord hi (by simp) hi_lt (by rw [hRi]; exact hRr)
            (by rw [hCidx]; exact hc₀C)
        have hr'lt : r' < r := lt_trans hlt hc₀r
        cases hinter with
        | inl h => exact absurd h.1 (not_lt.mpr (le_of_lt hr'lt))
        | inr h => exact absurd h.1 (not_lt.mpr (le_of_lt (lt_trans hr'lt hra)))
    | inr hgt =>
        cases hgt with
        | inl hcon => exact absurd hcon hiC
        | inr hi_gt =>
            by_cases hiS : i = A.length + 1
            · subst hiS
              have hSS : (A ++ C :: S :: B)[A.length + 1]'hi = S := hSidx
              rw [hSS] at hRi
              rw [← hRi] at hRr
              have hale : a ≤ r' := hamin r' hRr
              cases hinter with
              | inl h => exact absurd h.2 (not_lt.mpr hale)
              | inr h => exact absurd h.2 (not_lt.mpr (le_trans (le_of_lt hra) hale))
            · have hi_gt2 : A.length + 1 < i := by omega
              obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
                cases S with
                | nil => simp at hSne
                | cons x xs => exact ⟨x, by simp⟩
              have hs₀lt : s₀ < r' :=
                runsOrdered_getElem hord (by simp) hi hi_gt2
                  (by rw [hSidx]; exact hs₀) (by rw [hRi]; exact hRr)
              have hlt : a < r' := lt_of_le_of_lt (hamin s₀ hs₀) hs₀lt
              cases hinter with
              | inl h => exact absurd h.2 (not_lt.mpr (le_of_lt hlt))
              | inr h => exact absurd h.2 (not_lt.mpr (le_of_lt (lt_trans hra hlt))))
  exact key r' hr' (Or.inl ⟨h1, h2⟩)

/-- **Threshold-record lemma, successor case** (mirror). A foreign
red `r` arrives above the activated red run `S`, splitting the blue
run `C` just above `S` (witnessed by `c₀ ∈ C` with `r < c₀`). Then
`r` is a threshold successor record for `z = max S`. -/
theorem threshold_record_succ {A B : List (List X)} {C S : List X} {r z : X}
    (hord : RunsOrdered (A ++ S :: C :: B))
    (hc₀ : ∃ c ∈ C, r < c)
    (hblue : ∀ x ∈ C, color x = Color.blue)
    (hSne : S ≠ []) (hzmax : ∀ y ∈ S, y ≤ z)
    (hzr : z < r) (hred : color r = Color.red)
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (hpresent : ∀ r' : X, color r' = Color.red → τ r' < τ r →
      r' ∈ (A ++ S :: C :: B).flatten) :
    IsSuccRecord color τ z r := by
  obtain ⟨c₀, hc₀C, hc₀r⟩ := hc₀
  refine ⟨hred, hzr, ?_⟩
  intro r' hr' h1 h2
  have key := record_key_of_separation color τ hinj hpresent
    (runs := A ++ S :: C :: B) (b := z) (by
    intro r' hr' hmem hinter
    rw [List.mem_flatten] at hmem
    obtain ⟨R, hRruns, hRr⟩ := hmem
    obtain ⟨i, hi, hRi⟩ := List.mem_iff_getElem.mp hRruns
    have hSidx : (A ++ S :: C :: B)[A.length]'(by simp) = S := by simp
    have hCidx : (A ++ S :: C :: B)[A.length + 1]'(by simp) = C := by simp
    have hiC : i ≠ A.length + 1 := by
      intro hcon
      subst hcon
      have hCC : (A ++ S :: C :: B)[A.length + 1]'hi = C := hCidx
      rw [hCC] at hRi
      rw [← hRi] at hRr
      have hcb : color r' = Color.blue := hblue r' hRr
      rw [hr'] at hcb
      exact Color.noConfusion hcb
    cases lt_trichotomy i A.length with
    | inl hi_lt =>
        obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
          cases S with
          | nil => simp at hSne
          | cons x xs => exact ⟨x, by simp⟩
        have hs₀lt : r' < s₀ :=
          runsOrdered_getElem hord hi (by simp) hi_lt (by rw [hRi]; exact hRr)
            (by rw [hSidx]; exact hs₀)
        have hlt : r' < z := lt_of_lt_of_le hs₀lt (hzmax s₀ hs₀)
        cases hinter with
        | inl h => exact absurd h.1 (not_lt.mpr (le_of_lt (lt_trans hlt hzr)))
        | inr h => exact absurd h.1 (not_lt.mpr (le_of_lt hlt))
    | inr hgt =>
        cases hgt with
        | inl hiS =>
            subst hiS
            have hSS : (A ++ S :: C :: B)[A.length]'hi = S := hSidx
            rw [hSS] at hRi
            rw [← hRi] at hRr
            have hle : r' ≤ z := hzmax r' hRr
            cases hinter with
            | inl h => exact absurd h.1 (not_lt.mpr (le_trans hle (le_of_lt hzr)))
            | inr h => exact absurd h.1 (not_lt.mpr hle)
        | inr hi_gt =>
            by_cases hiC' : i = A.length + 1
            · exact absurd hiC' hiC
            · have hi_gt2 : A.length + 1 < i := by omega
              have hlt : c₀ < r' :=
                runsOrdered_getElem hord (by simp) hi hi_gt2
                  (by rw [hCidx]; exact hc₀C) (by rw [hRi]; exact hRr)
              have hrr : r < r' := lt_trans hc₀r hlt
              cases hinter with
              | inl h => exact absurd h.2 (not_lt.mpr (le_of_lt (lt_trans hzr hrr)))
              | inr h => exact absurd h.2 (not_lt.mpr (le_of_lt hrr)))
  exact key r' hr' (Or.inr ⟨h1, h2⟩)


/-- **Creator-record lemma, left end** (mirror of `creator_record`).
`r` is below the first (blue) run `C`; then it is a record for
every `b ∈ C`: earlier red elements in runs after `C` exceed `b`. -/
theorem creator_record_left {B : List (List X)} {C : List X} {r b : X}
    (hord : RunsOrdered (C :: B))
    (habove : ∀ x ∈ C, r < x)
    (hb : b ∈ C) (hblue : ∀ x ∈ C, color x = Color.blue) (hred : color r = Color.red)
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (hpresent : ∀ r' : X, color r' = Color.red → τ r' < τ r →
      r' ∈ (C :: B).flatten) :
    IsRecord color τ b r := by
  have hne : r ≠ b := by
    intro hcon
    have h1 : color r = Color.blue := by rw [hcon]; exact hblue b hb
    rw [hred] at h1
    exact Color.noConfusion h1
  apply record_key color hred hne τ hinj
  apply record_key_of_separation color τ hinj hpresent
  intro r' hr' hmem hinter
  rw [List.mem_flatten] at hmem
  obtain ⟨R, hRruns, hRr⟩ := hmem
  simp only [List.mem_cons] at hRruns
  rcases hRruns with rfl | hB
  · have hcb : color r' = Color.blue := hblue r' hRr
    rw [hr'] at hcb
    exact Color.noConfusion hcb
  · have hlt : b < r' :=
      (List.pairwise_cons.mp hord).1 R hB b hb r' hRr
    cases hinter with
    | inl h => exact absurd h.2 (not_lt.mpr (le_of_lt hlt))
    | inr h => exact absurd h.2 (not_lt.mpr (le_of_lt (lt_trans (habove b hb) hlt)))

/-- **Merger-record lemma, from above** (mirror of `merger_record`).
`r` arrives above the red run `S`, splitting the blue run `C` just
above it; then `r` is a record for every `b ∈ C`: earlier red
elements are in runs before `S` (below `r` via `S`), in `S`
(below `r`), or in runs after `C` (above `b`). -/
theorem merger_record_succ {A B : List (List X)} {C S : List X} {r b : X}
    (hord : RunsOrdered (A ++ S :: C :: B))
    (hbC : ∀ x ∈ C, r < x) (hrS : ∀ x ∈ S, x < r)
    (hSne : S ≠ [])
    (hb : b ∈ C) (hblue : ∀ x ∈ C, color x = Color.blue) (hred : color r = Color.red)
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (hpresent : ∀ r' : X, color r' = Color.red → τ r' < τ r →
      r' ∈ (A ++ S :: C :: B).flatten) :
    IsRecord color τ b r := by
  have hne : r ≠ b := by
    intro hcon
    have h1 : color r = Color.blue := by rw [hcon]; exact hblue b hb
    rw [hred] at h1
    exact Color.noConfusion h1
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
    cases S with
    | nil => simp at hSne
    | cons x xs => exact ⟨x, by simp⟩
  apply record_key color hred hne τ hinj
  apply record_key_of_separation color τ hinj hpresent
  intro r' hr' hmem hinter
  rw [List.mem_flatten] at hmem
  obtain ⟨R, hRruns, hRr⟩ := hmem
  simp only [List.mem_append, List.mem_cons] at hRruns
  have hrb : r < b := hbC b hb
  rcases hRruns with hA | rfl | rfl | hB
  · have hr'lt : r' < r := by
      have hcross := (List.pairwise_append.mp hord).2.2
      exact lt_trans (hcross R hA S (by simp) r' hRr s₀ hs₀) (hrS s₀ hs₀)
    cases hinter with
    | inl h => exact absurd h.1 (not_lt.mpr (le_of_lt hr'lt))
    | inr h => exact absurd h.1 (not_lt.mpr (le_of_lt (lt_trans hr'lt hrb)))
  · have hr'lt : r' < r := hrS r' hRr
    have hr'b : r' < b := by
      have e : A ++ R :: C :: B = (A ++ [R]) ++ C :: B := by
        simp [List.append_assoc]
      have hcross := (List.pairwise_append.mp (e ▸ hord)).2.2
      exact hcross R (by simp) C (by simp) r' hRr b hb
    cases hinter with
    | inl h => exact absurd h.1 (not_lt.mpr (le_of_lt hr'lt))
    | inr h => exact absurd h.1 (not_lt.mpr (le_of_lt hr'b))
  · have hcb : color r' = Color.blue := hblue r' hRr
    rw [hr'] at hcb
    exact Color.noConfusion hcb
  · have hlt : b < r' := by
      have e : A ++ S :: C :: B = (A ++ [S, C]) ++ B := by
        simp [List.append_assoc]
      have hcross := (List.pairwise_append.mp (e ▸ hord)).2.2
      exact hcross C (by simp) R hB b hb r' hRr
    cases hinter with
    | inl h => exact absurd h.2 (not_lt.mpr (le_of_lt hlt))
    | inr h => exact absurd h.2 (not_lt.mpr (le_of_lt (lt_trans hrb hlt)))

/-- Blue refinement across a step: every blue run of the new state is
a subset of some blue run of the old state. Split pieces are subsets
of the split run; all other operations leave blue runs untouched.
This is the trace content of the founder property's "later adjacent
runs are subsets of those". -/
theorem step_blue_refines {σ : List (List X)} {r : X} {σ' : List (List X)}
    (h : Step color σ r σ') (hmono : MonoRuns color σ) (hred : color r = Color.red) :
    ∀ R' ∈ σ', (∀ x ∈ R', color x = Color.blue) →
      ∃ R ∈ σ, (∀ x ∈ R, color x = Color.blue) ∧ ∀ x ∈ R', x ∈ R := by
  cases h with
  | freshSingleton A B S r hL hR =>
      intro R' hR' hblue'
      simp only [applyOp, List.mem_append, List.mem_cons] at hR'
      cases hR' with
      | inl h => exact ⟨R', by simp [List.mem_append, h], hblue', fun x hx => hx⟩
      | inr h =>
          cases h with
          | inl he =>
              rw [he] at hblue'
              have hbb := hblue' r (by simp)
              rw [hred] at hbb
              exact False.elim (Color.noConfusion hbb)
          | inr h => exact ⟨R', by simp [List.mem_append, List.mem_cons, h], hblue', fun x hx => hx⟩
  | mergePair A B S r r₀ hS hSred hL hR =>
      intro R' hR' hblue'
      simp only [applyOp, List.mem_append, List.mem_cons] at hR'
      cases hR' with
      | inl h => exact ⟨R', by simp [List.mem_append, h], hblue', fun x hx => hx⟩
      | inr h =>
          cases h with
          | inl he =>
              rw [he] at hblue'
              have hbb := hblue' r₀ (by split_ifs <;> simp)
              have hred0 : color r₀ = Color.red := hSred r₀ (by rw [hS]; simp)
              rw [hred0] at hbb
              exact False.elim (Color.noConfusion hbb)
          | inr h => exact ⟨R', by simp [List.mem_append, List.mem_cons, h], hblue', fun x hx => hx⟩
  | insertInto A B S r hSred hL hR =>
      intro R' hR' hblue'
      simp only [applyOp, List.mem_append, List.mem_cons] at hR'
      cases hR' with
      | inl h => exact ⟨R', by simp [List.mem_append, h], hblue', fun x hx => hx⟩
      | inr h =>
          cases h with
          | inl he =>
              rw [he] at hblue'
              have hbb := hblue' r (by rw [insertSorted_mem]; exact Or.inl rfl)
              rw [hred] at hbb
              exact False.elim (Color.noConfusion hbb)
          | inr h => exact ⟨R', by simp [List.mem_append, List.mem_cons, h], hblue', fun x hx => hx⟩
  | appendSingleton A B S r hAll =>
      intro R' hR' hblue'
      simp only [applyOp, List.mem_append, List.mem_singleton] at hR'
      rcases hR' with h | rfl
      · exact ⟨R', List.mem_append.mpr h, hblue', fun x hx => hx⟩
      · have hbb := hblue' r (by simp)
        rw [hred] at hbb
        exact False.elim (Color.noConfusion hbb)
  | splitRun A B S below above r hsub_b hsub_a hblue hbne hane hbr har hAr hrB hpart =>
      intro R' hR' hblue'
      simp only [applyOp, List.mem_append, List.mem_cons] at hR'
      cases hR' with
      | inl h => exact ⟨R', by simp [List.mem_append, h], hblue', fun x hx => hx⟩
      | inr h =>
          cases h with
          | inl he => exact ⟨S, by simp [List.mem_append, List.mem_cons], hblue, fun x hx => hsub_b x (he ▸ hx)⟩
          | inr h =>
              cases h with
              | inl he =>
                  rw [he] at hblue'
                  have hbb := hblue' r (by simp)
                  rw [hred] at hbb
                  exact False.elim (Color.noConfusion hbb)
              | inr h =>
                  cases h with
                  | inl he => exact ⟨S, by simp [List.mem_append, List.mem_cons], hblue, fun x hx => hsub_a x (he ▸ hx)⟩
                  | inr h => exact ⟨R', by simp [List.mem_append, List.mem_cons, h], hblue', fun x hx => hx⟩

/-- Blue refinement along a whole trace: every nonempty blue run of
the final state is contained in some blue run of the initial state. -/
theorem trace_blue_refines {σ0 : List (List X)} {L : List X}
    {σf : List (List X)} (htr : TraceFrom color σ0 L σf) :
    MonoRuns color σ0 → (∀ r ∈ L, color r = Color.red) →
    ∀ {Cfin : List X}, Cfin ∈ σf → Cfin ≠ [] →
    (∀ x ∈ Cfin, color x = Color.blue) →
    ∃ C₀ ∈ σ0, ∀ x ∈ Cfin, x ∈ C₀ := by
  induction htr with
  | nil σ =>
    intro _ _ Cfin hC _ hblue
    exact ⟨Cfin, hC, fun x hx => hx⟩
  | @cons σ σ' σ'' r rest hstep htrest ih =>
    intro hmono hred Cfin hC hne hblue
    have hredr : color r = Color.red := hred r (by simp)
    have hmono' : MonoRuns color σ' := step_mono color hstep hmono hredr
    obtain ⟨Cmid, hCmid, hsub⟩ := ih hmono'
      (fun x hx => hred x (by simp [hx])) hC hne hblue
    have hbluemid : ∀ x ∈ Cmid, color x = Color.blue := by
      obtain ⟨x₀, hx₀⟩ : ∃ x, x ∈ Cfin := by
        cases Cfin with
        | nil => exact absurd rfl hne
        | cons a l => exact ⟨a, by simp⟩
      have hx₀mid : x₀ ∈ Cmid := hsub x₀ hx₀
      rcases hmono' Cmid hCmid with hr | hb
      · have h1 := hr x₀ hx₀mid
        rw [hblue x₀ hx₀] at h1
        exact absurd h1 (by simp)
      · exact hb
    obtain ⟨C₀, hC₀, -, hsub₀⟩ :=
      step_blue_refines color hstep hmono hredr Cmid hCmid hbluemid
    exact ⟨C₀, hC₀, fun x hx => hsub₀ x (hsub x hx)⟩

/-- The founder corollary, creator case: the creator is a record for
every element `b` of the created blue run `C`, hence for every `b`
in any later blue sub-run `C' ⊆ C` (the founder property). -/
theorem founder_record {A : List (List X)} {C C' : List X} {r b : X}
    (hord : RunsOrdered (A ++ [C]))
    (hbelow : ∀ x ∈ C, x < r)
    (hblue : ∀ x ∈ C, color x = Color.blue) (hred : color r = Color.red)
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (hpresent : ∀ r' : X, color r' = Color.red → τ r' < τ r →
      r' ∈ (A ++ [C]).flatten)
    (hsub : ∀ x ∈ C', x ∈ C) (hb : b ∈ C') :
    IsRecord color τ b r :=
  creator_record color hord hbelow (hsub b hb) hblue hred τ hinj hpresent

/-- The founder corollary, merger case: the merger is a record for
every element of the adjacent blue run, hence of any later blue
sub-run of it. -/
theorem merger_founder {A B : List (List X)} {C S C' : List X} {r b : X}
    (hord : RunsOrdered (A ++ C :: S :: B))
    (hbC : ∀ x ∈ C, x < r) (hrS : ∀ x ∈ S, r < x) (hSne : S ≠ [])
    (hblue : ∀ x ∈ C, color x = Color.blue) (hred : color r = Color.red)
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (hpresent : ∀ r' : X, color r' = Color.red → τ r' < τ r →
      r' ∈ (A ++ C :: S :: B).flatten)
    (hsub : ∀ x ∈ C', x ∈ C) (hb : b ∈ C') :
    IsRecord color τ b r :=
  merger_record color hord hbC hrS hSne (hsub b hb) hblue hred τ hinj hpresent


/-- Red runs never split, one step: a run containing a red element
`x` is carried into a single run of the new state containing all
its elements. (Blue runs may split; a red one cannot be the split
run, and the other operations only adjoin `r`.) -/
theorem step_red_run_grows {σ : List (List X)} {r : X} {σ' : List (List X)}
    {R : List X} {x₀ : X}
    (h : Step color σ r σ') (hR : R ∈ σ) (hx₀ : x₀ ∈ R)
    (hred : color x₀ = Color.red) :
    ∃ R' ∈ σ', ∀ x ∈ R, x ∈ R' := by
  cases h with
  | freshSingleton A B S r hL hR' =>
      refine ⟨R, ?_, fun x hx => hx⟩
      simp only [applyOp, List.mem_append, List.mem_cons] at hR ⊢
      tauto
  | appendSingleton A B S r hAll =>
      refine ⟨R, ?_, fun x hx => hx⟩
      exact List.mem_append.mpr (Or.inl hR)
  | mergePair A B S r r₀ hS hSred hL hR' =>
      by_cases hRS : R = S
      · subst hRS
        refine ⟨if r < r₀ then [r, r₀] else [r₀, r], by simp [applyOp], ?_⟩
        intro x hx
        have hx0 : x = r₀ := by
          rw [hS] at hx
          simpa using hx
        subst hx0
        split_ifs <;> simp
      · refine ⟨R, ?_, fun x hx => hx⟩
        simp only [applyOp, List.mem_append, List.mem_cons] at hR ⊢
        tauto
  | insertInto A B S r hSred hL hR' =>
      by_cases hRS : R = S
      · subst hRS
        refine ⟨insertSorted r R, by simp [applyOp], ?_⟩
        intro x hx
        rw [insertSorted_mem]
        exact Or.inr hx
      · refine ⟨R, ?_, fun x hx => hx⟩
        simp only [applyOp, List.mem_append, List.mem_cons] at hR ⊢
        tauto
  | splitRun A B S below above r hsub_b hsub_a hblue hbne hane hbr har hAr hrB hpart =>
      by_cases hRS : R = S
      · subst hRS
        have hcb : color x₀ = Color.blue := hblue x₀ hx₀
        rw [hred] at hcb
        exact Color.noConfusion hcb
      · refine ⟨R, ?_, fun x hx => hx⟩
        simp only [applyOp, List.mem_append, List.mem_cons] at hR ⊢
        tauto

/-- Red runs never split, whole trace: the run containing a red
element `x₀` in the initial state grows into a single run of the
final state containing all its elements. -/
theorem trace_red_run_grows {σ0 : List (List X)} {L : List X}
    {σf : List (List X)} {R : List X} {x₀ : X}
    (htr : TraceFrom color σ0 L σf) :
    R ∈ σ0 → x₀ ∈ R → color x₀ = Color.red →
    ∃ R' ∈ σf, ∀ x ∈ R, x ∈ R' := by
  induction htr generalizing R with
  | nil σ =>
      intro hR hx₀ hred
      exact ⟨R, hR, fun x hx => hx⟩
  | @cons σ σ' σ'' r rest hstep htrest ih =>
      intro hR hx₀ hred
      obtain ⟨R₁, hR₁, hsub₁⟩ := step_red_run_grows color hstep hR hx₀ hred
      obtain ⟨R₂, hR₂, hsub₂⟩ := ih hR₁ (hsub₁ x₀ hx₀) hred
      exact ⟨R₂, hR₂, fun x hx => hsub₂ x (hsub₁ x hx)⟩


/-- Monochromaticity along a whole trace (red arrivals). -/
theorem trace_mono {σ0 : List (List X)} {L : List X} {σf : List (List X)}
    (htr : TraceFrom color σ0 L σf) :
    MonoRuns color σ0 → (∀ r ∈ L, color r = Color.red) →
    MonoRuns color σf := by
  induction htr with
  | nil σ => intro hmono _; exact hmono
  | @cons σ σ' σ'' r rest hstep htrest ih =>
      intro hmono hredL
      have hredr : color r = Color.red := hredL r (by simp)
      exact ih (step_mono color hstep hmono hredr)
        (fun x hx => hredL x (by simp [hx]))

/-- The tested run grows into a final red run: under a trace with
red arrivals from a monochromatic state, any run containing a red
element is contained in a single all-red run of the final state.
This is the run-level half of "`S` becomes the final run `F`" in
`lem:foreignred`; the endpoint half (`min S = min F`) is next. -/
theorem final_red_run_of {σ0 : List (List X)} {L : List X}
    {σf : List (List X)} {R : List X} {x₀ : X}
    (htr : TraceFrom color σ0 L σf) (hmono : MonoRuns color σ0)
    (hredL : ∀ r ∈ L, color r = Color.red)
    (hR : R ∈ σ0) (hx₀ : x₀ ∈ R) (hred : color x₀ = Color.red) :
    ∃ F ∈ σf, (∀ x ∈ R, x ∈ F) ∧ (∀ x ∈ F, color x = Color.red) := by
  obtain ⟨F, hF, hsub⟩ := trace_red_run_grows color htr hR hx₀ hred
  have hmono_f : MonoRuns color σf := trace_mono color htr hmono hredL
  refine ⟨F, hF, hsub, ?_⟩
  rcases hmono_f F hF with hr | hb
  · exact hr
  · have h1 := hb x₀ (hsub x₀ hx₀)
    rw [hred] at h1
    exact absurd h1 (by simp)


/-- Split a trace at a chosen arrival: the trace factors through
the state just before `j` arrives and the step that inserts it. -/
theorem trace_split {σ0 : List (List X)} {L₁ : List X} {j : X}
    {L₂ : List X} {σf : List (List X)}
    (htr : TraceFrom color σ0 (L₁ ++ j :: L₂) σf) :
    ∃ σ₁ σ₂, TraceFrom color σ0 L₁ σ₁ ∧ Step color σ₁ j σ₂ ∧
      TraceFrom color σ₂ L₂ σf := by
  induction L₁ generalizing σ0 with
  | nil =>
      cases htr with
      | cons hs ht => exact ⟨σ0, _, TraceFrom.nil _, hs, ht⟩
  | cons a L₁ ih =>
      cases htr with
      | cons hs ht =>
          obtain ⟨σ₁, σ₂, h1, h2, h3⟩ := ih ht
          exact ⟨σ₁, σ₂, TraceFrom.cons hs h1, h2, h3⟩

/-- Joiner barrier, insertion case: if a blue run `D` sits among the
runs before the target run `S` in the located decomposition, and
`d ∈ D` exceeds `r`, then the joining element `j` exceeds `r`. This
is the one-step content of "the joiner clears the blue run adjacent
below `S`", in the form the location stage will supply. -/
theorem insertInto_joiner_above {A : List (List X)} {D : List X}
    {r j d : X}
    (hL : ∀ R ∈ A, ∀ x ∈ R, x < j)
    (hD : D ∈ A) (hdD : d ∈ D) (hrd : r < d) : r < j :=
  lt_trans hrd (hL D hD d hdD)

/-- Joiner barrier, merger case: the same barrier conclusion for a
merging joiner. -/
theorem mergePair_joiner_above {A : List (List X)} {D : List X}
    {r j d r₀ : X}
    (hL : ∀ R ∈ A, ∀ x ∈ R, x < j ∧ x < r₀)
    (hD : D ∈ A) (hdD : d ∈ D) (hrd : r < d) : r < j :=
  lt_trans hrd (hL D hD d hdD).1


/-- Minimum of a nonempty list, as a member bounding all members. -/
theorem exists_min_mem {l : List X} (hl : l ≠ []) :
    ∃ a ∈ l, ∀ y ∈ l, a ≤ y := by
  induction l with
  | nil => simp at hl
  | cons f fs ih =>
      cases fs with
      | nil => exact ⟨f, by simp, by simp⟩
      | cons g gs =>
          obtain ⟨a, ha, hmin⟩ := ih (by simp)
          by_cases h : f ≤ a
          · exact ⟨f, by simp, fun y hy => by
              rcases List.mem_cons.mp hy with rfl | hy'
              · exact le_refl _
              · exact le_trans h (hmin y hy')⟩
          · exact ⟨a, by simp [ha], fun y hy => by
              rcases List.mem_cons.mp hy with rfl | hy'
              · exact le_of_not_ge h
              · exact hmin y hy'⟩

/-- Maximum of a nonempty list, as a member bounding all members. -/
theorem exists_max_mem {l : List X} (hl : l ≠ []) :
    ∃ z ∈ l, ∀ y ∈ l, y ≤ z := by
  induction l with
  | nil => simp at hl
  | cons f fs ih =>
      cases fs with
      | nil => exact ⟨f, by simp, by simp⟩
      | cons g gs =>
          obtain ⟨z, hz, hmax⟩ := ih (by simp)
          by_cases h : f ≤ z
          · exact ⟨z, by simp [hz], fun y hy => by
              rcases List.mem_cons.mp hy with rfl | hy'
              · exact h
              · exact hmax y hy'⟩
          · exact ⟨f, by simp, fun y hy => by
              rcases List.mem_cons.mp hy with rfl | hy'
              · exact le_refl _
              · exact le_trans (hmax y hy') (le_of_not_ge h)⟩

/-- **Endpoint passage for foreign records** (paper `lem:foreignred`,
assembly form). The threshold record proved at the testing step for
the tested run `S` transfers to the minimum `a` of the final red
run `F ⊇ S`, provided every element of `F` either already lies in
`S` or exceeds the foreign element `r`. That proviso is the
remaining trace invariant: later joiners exceed `r` by the blue
barrier (`insertInto_joiner_above`/`mergePair_joiner_above` at
their joining step, with the barrier run a descendant of the split
run's upper piece), and old elements of other runs never merge
into `F` (red runs only grow by adjoining arrivals). -/
theorem threshold_record_at_final {A B : List (List X)} {C S F : List X}
    {r : X}
    (hord : RunsOrdered (A ++ C :: S :: B))
    (hc₀ : ∃ c ∈ C, c < r)
    (hblue : ∀ x ∈ C, color x = Color.blue)
    (hSne : S ≠ [])
    (hrS : ∀ y ∈ S, r < y) (hred : color r = Color.red)
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (hpresent : ∀ r' : X, color r' = Color.red → τ r' < τ r →
      r' ∈ (A ++ C :: S :: B).flatten)
    (hFne : F ≠ []) (hSF : ∀ x ∈ S, x ∈ F)
    (hsepF : ∀ x ∈ F, x ∈ S ∨ r < x) :
    ∃ a ∈ F, IsPredRecord color τ a r ∧ ∀ y ∈ F, a ≤ y := by
  obtain ⟨a, haF, haminF⟩ := exists_min_mem hFne
  refine ⟨a, haF, ?_, haminF⟩
  have hra : r < a := by
    cases hsepF a haF with
    | inl h => exact hrS a h
    | inr h => exact h
  exact threshold_record color hord hc₀ hblue hSne
    (fun y hy => haminF y (hSF y hy)) hra hred τ hinj hpresent

/-- Successor form of the endpoint passage, for the tested run's
maximum and the final run above it. -/
theorem threshold_record_succ_at_final {A B : List (List X)}
    {C S F : List X} {r : X}
    (hord : RunsOrdered (A ++ S :: C :: B))
    (hc₀ : ∃ c ∈ C, r < c)
    (hblue : ∀ x ∈ C, color x = Color.blue)
    (hSne : S ≠ [])
    (hrS : ∀ y ∈ S, y < r) (hred : color r = Color.red)
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (hpresent : ∀ r' : X, color r' = Color.red → τ r' < τ r →
      r' ∈ (A ++ S :: C :: B).flatten)
    (hFne : F ≠ []) (hSF : ∀ x ∈ S, x ∈ F)
    (hsepF : ∀ x ∈ F, x ∈ S ∨ x < r) :
    ∃ z ∈ F, IsSuccRecord color τ z r ∧ ∀ y ∈ F, y ≤ z := by
  obtain ⟨z, hzF, hzmaxF⟩ := exists_max_mem hFne
  refine ⟨z, hzF, ?_, hzmaxF⟩
  have hzr : z < r := by
    cases hsepF z hzF with
    | inl h => exact hrS z h
    | inr h => exact h
  exact threshold_record_succ color hord hc₀ hblue hSne
    (fun y hy => hzmaxF y (hSF y hy)) hzr hred τ hinj hpresent


/-- Runs of a state with duplicate-free flattening are unique: an
element lies in at most one run. -/
theorem run_unique {σ : List (List X)} (hnd : σ.flatten.Nodup)
    {x : X} {R₁ R₂ : List X}
    (h₁ : R₁ ∈ σ) (h₂ : R₂ ∈ σ) (hx₁ : x ∈ R₁) (hx₂ : x ∈ R₂) :
    R₁ = R₂ := by
  by_contra hne
  obtain ⟨i, hi, hRi⟩ := List.mem_iff_getElem.mp h₁
  obtain ⟨k, hk, hRk⟩ := List.mem_iff_getElem.mp h₂
  have hik : i ≠ k := by
    intro hcon
    subst hcon
    exact hne (hRi.symm.trans hRk)
  rcases lt_trichotomy i k with h | h | h
  · have hdisj := (List.pairwise_iff_getElem.mp
      (List.nodup_flatten.mp hnd).2) i k hi hk h
    rw [hRi] at hdisj
    rw [hRk] at hdisj
    exact hdisj hx₁ hx₂
  · exact hik h
  · have hdisj := (List.pairwise_iff_getElem.mp
      (List.nodup_flatten.mp hnd).2) k i hk hi h
    rw [hRi] at hdisj
    rw [hRk] at hdisj
    exact hdisj hx₂ hx₁

/-- Element provenance along a trace: the final flattening is the
arrivals followed by the initial flattening, up to permutation. -/
theorem trace_flatten_perm {σ0 : List (List X)} {L : List X}
    {σf : List (List X)} (htr : TraceFrom color σ0 L σf) :
    σf.flatten.Perm (L ++ σ0.flatten) := by
  induction htr with
  | nil σ => exact List.Perm.refl _
  | @cons σ σ' σ'' r rest hstep htrest ih =>
      have h1 : σ'.flatten.Perm (r :: σ.flatten) := step_flatten color hstep
      have h2 : (rest ++ σ'.flatten).Perm ((r :: rest) ++ σ.flatten) :=
        (List.Perm.append_left rest h1).trans List.perm_middle
      exact ih.trans h2

/-- One step never merges old runs: two old elements in one run of
the new state were already in one run of the old state. -/
theorem step_same_run_old {σ : List (List X)} {j : X} {σ' : List (List X)}
    (h : Step color σ j σ') (hj : j ∉ σ.flatten)
    {R' : List X} (hR' : R' ∈ σ') {x y : X}
    (hx : x ∈ R') (hy : y ∈ R')
    (hxold : x ∈ σ.flatten) (hyold : y ∈ σ.flatten) :
    ∃ R ∈ σ, x ∈ R ∧ y ∈ R := by
  cases h with
  | freshSingleton A B S r hL hR =>
      simp only [applyOp, List.mem_append, List.mem_cons] at hR'
      rcases hR' with hA | rfl | hS | hB
      · exact ⟨R', by simp [List.mem_append, hA], hx, hy⟩
      · simp at hx
        rw [hx] at hxold
        exact absurd hxold hj
      · exact ⟨R', by simp [List.mem_append, List.mem_cons, hS], hx, hy⟩
      · exact ⟨R', by simp [List.mem_append, hB], hx, hy⟩
  | mergePair A B S r r₀ hS hSred hL hR =>
      simp only [applyOp, List.mem_append, List.mem_cons] at hR'
      rcases hR' with hA | rfl | hB
      · exact ⟨R', by simp [List.mem_append, hA], hx, hy⟩
      · have hxr : x = r₀ := by
          split_ifs at hx
          · simp at hx
            rcases hx with hx1 | hx1
            · rw [hx1] at hxold; exact absurd hxold hj
            · exact hx1
          · simp at hx
            rcases hx with hx1 | hx1
            · exact hx1
            · rw [hx1] at hxold; exact absurd hxold hj
        have hyr : y = r₀ := by
          split_ifs at hy
          · simp at hy
            rcases hy with hy1 | hy1
            · rw [hy1] at hyold; exact absurd hyold hj
            · exact hy1
          · simp at hy
            rcases hy with hy1 | hy1
            · exact hy1
            · rw [hy1] at hyold; exact absurd hyold hj
        refine ⟨S, by simp [List.mem_append], ?_, ?_⟩
        · rw [hxr, hS]; simp
        · rw [hyr, hS]; simp
      · exact ⟨R', by simp [List.mem_append, hB], hx, hy⟩
  | insertInto A B S r hSred hL hR =>
      simp only [applyOp, List.mem_append, List.mem_cons] at hR'
      rcases hR' with hA | rfl | hB
      · exact ⟨R', by simp [List.mem_append, hA], hx, hy⟩
      · rw [insertSorted_mem] at hx hy
        rcases hx with rfl | hxS
        · exact absurd hxold hj
        · rcases hy with rfl | hyS
          · exact absurd hyold hj
          · exact ⟨S, by simp [List.mem_append], hxS, hyS⟩
      · exact ⟨R', by simp [List.mem_append, hB], hx, hy⟩
  | appendSingleton A B S r hAll =>
      simp only [applyOp, List.mem_append, List.mem_singleton] at hR'
      rcases hR' with h | rfl
      · exact ⟨R', List.mem_append.mpr h, hx, hy⟩
      · simp at hx
        rw [hx] at hxold
        exact absurd hxold hj
  | splitRun A B S below above r hsub_b hsub_a hblue hbne hane hbr har hAr hrB hpart =>
      simp only [applyOp, List.mem_append, List.mem_cons] at hR'
      rcases hR' with hA | rfl | rfl | rfl | hB
      · exact ⟨R', by simp [List.mem_append, hA], hx, hy⟩
      · exact ⟨S, by simp [List.mem_append], hsub_b x hx, hsub_b y hy⟩
      · simp at hx
        rw [hx] at hxold
        exact absurd hxold hj
      · exact ⟨S, by simp [List.mem_append], hsub_a x hx, hsub_a y hy⟩
      · exact ⟨R', by simp [List.mem_append, hB], hx, hy⟩

/-- Along a whole trace, two elements present initially that end in
one final run were already in one initial run: distinct old runs
never merge (operations only adjoin the arriving element). -/
theorem trace_same_run_old {σ0 : List (List X)} {L : List X}
    {σf : List (List X)} (htr : TraceFrom color σ0 L σf)
    (hnd : L.Nodup) (hfresh : ∀ j ∈ L, j ∉ σ0.flatten)
    {x y : X} (hxold : x ∈ σ0.flatten) (hyold : y ∈ σ0.flatten)
    {F : List X} (hF : F ∈ σf) (hxF : x ∈ F) (hyF : y ∈ F) :
    ∃ R ∈ σ0, x ∈ R ∧ y ∈ R := by
  induction htr with
  | nil σ => exact ⟨F, hF, hxF, hyF⟩
  | @cons σ σ' σ'' r rest hstep htrest ih =>
      have hstepflat : σ'.flatten.Perm (r :: σ.flatten) :=
        step_flatten color hstep
      have hx' : x ∈ σ'.flatten := hstepflat.mem_iff.mpr (List.mem_cons_of_mem r hxold)
      have hy' : y ∈ σ'.flatten := hstepflat.mem_iff.mpr (List.mem_cons_of_mem r hyold)
      have hnd' : rest.Nodup := by
        rw [List.nodup_cons] at hnd
        exact hnd.2
      have hfresh' : ∀ j ∈ rest, j ∉ σ'.flatten := by
        intro j hj hjf
        have hjx : j = r ∨ j ∈ σ.flatten := by
          have h := (List.Perm.mem_iff hstepflat).mp hjf
          simpa using h
        rcases hjx with rfl | hjold
        · rw [List.nodup_cons] at hnd
          exact hnd.1 hj
        · exact hfresh j (by simp [hj]) hjold
      obtain ⟨R, hR, hxR, hyR⟩ := ih hnd' hfresh' hx' hy' hF
      exact step_same_run_old color hstep (hfresh r (by simp)) hR hxR hyR
        hxold hyold


/-- Forward persistence of a shared run: if two elements lie in
one run of `σ`, and the first is red, then after any step they
lie in one run of `σ'`. Every operation either leaves the run
unchanged, inserts the arrival into it, or merges a singleton
into a pair; the only operation that splits a run splits a blue
run, which cannot contain a red element. -/
theorem step_same_run_forward {σ : List (List X)} {r : X}
    {σ' : List (List X)} (h : Step color σ r σ')
    {x y : X} (hxred : color x = Color.red)
    {R : List X} (hR : R ∈ σ) (hx : x ∈ R) (hy : y ∈ R) :
    ∃ R' ∈ σ', x ∈ R' ∧ y ∈ R' := by
  cases h with
  | freshSingleton A B S r hL hRr =>
      simp only [mem_decomp] at hR
      refine ⟨R, ?_, hx, hy⟩
      simp only [applyOp, List.mem_append, List.mem_cons]
      rcases hR with hA | rfl | hB
      · exact Or.inl hA
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr hB))
  | appendSingleton A B S r hAll =>
      exact ⟨R, by
        simp only [applyOp]
        exact List.mem_append.mpr (Or.inl hR), hx, hy⟩
  | mergePair A B S r r₀ hS hSred hL hRr =>
      simp only [mem_decomp] at hR
      rcases hR with hA | rfl | hB
      · exact ⟨R, by
          simp only [applyOp, List.mem_append]
          exact Or.inl hA, hx, hy⟩
      · have hxr : x = r₀ := by
          rw [hS] at hx
          simpa using hx
        have hyr : y = r₀ := by
          rw [hS] at hy
          simpa using hy
        refine ⟨if r < r₀ then [r, r₀] else [r₀, r], ?_, ?_, ?_⟩
        · simp [applyOp]
        · rw [hxr]
          split_ifs <;> simp
        · rw [hyr]
          split_ifs <;> simp
      · exact ⟨R, by
          simp only [applyOp, List.mem_append, List.mem_cons]
          exact Or.inr (Or.inr hB), hx, hy⟩
  | insertInto A B S r hSred hL hRr =>
      simp only [mem_decomp] at hR
      rcases hR with hA | rfl | hB
      · exact ⟨R, by
          simp only [applyOp, List.mem_append]
          exact Or.inl hA, hx, hy⟩
      · refine ⟨insertSorted r R, by simp [applyOp], ?_, ?_⟩ <;>
        · rw [insertSorted_mem]
          exact Or.inr (by assumption)
      · exact ⟨R, by
          simp only [applyOp, List.mem_append, List.mem_cons]
          exact Or.inr (Or.inr hB), hx, hy⟩
  | splitRun A B S below above r hsub_b hsub_a hblue hbne hane hbr har
      hAr hrB hpart =>
      simp only [mem_decomp] at hR
      rcases hR with hA | rfl | hB
      · exact ⟨R, by
          simp only [applyOp, List.mem_append]
          exact Or.inl hA, hx, hy⟩
      · have hxb : color x = Color.blue := hblue x hx
        exact False.elim (Color.noConfusion (hxred.symm.trans hxb))
      · exact ⟨R, by
          simp only [applyOp, List.mem_append, List.mem_cons]
          exact Or.inr (Or.inr (Or.inr (Or.inr hB))), hx, hy⟩

/-- Forward persistence along a whole trace: two elements in one
initial run, the first red, end in one final run. -/
theorem trace_same_run_forward {σ0 : List (List X)} {L : List X}
    {σf : List (List X)} (htr : TraceFrom color σ0 L σf)
    {x y : X} (hxred : color x = Color.red) :
    ∀ {R : List X}, R ∈ σ0 → x ∈ R → y ∈ R →
    ∃ R' ∈ σf, x ∈ R' ∧ y ∈ R' := by
  induction htr with
  | nil σ =>
      intro R hR hx hy
      exact ⟨R, hR, hx, hy⟩
  | @cons σ σ' σ'' r rest hstep htrest ih =>
      intro R hR hx hy
      obtain ⟨R', hR', hx', hy'⟩ :=
        step_same_run_forward color hstep hxred hR hx hy
      exact ih hR' hx' hy'

/-- Split a list at a member. -/
theorem mem_split_list {x : X} {l : List X} (hx : x ∈ l) :
    ∃ L₁ L₂, l = L₁ ++ x :: L₂ := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ⟨[], l, rfl⟩
      · obtain ⟨L₁, L₂, h⟩ := ih hx'
        exact ⟨a :: L₁, L₂, by simp [h]⟩

/-- Cross-run comparison in membership form: in `A ++ C :: S :: B`
ordered, every element of `S` is below every element of a run in
`B`. -/
theorem runsOrdered_mem_lt {A B : List (List X)} {C S R : List X}
    (h : RunsOrdered (A ++ C :: S :: B)) (hR : R ∈ B)
    {x y : X} (hx : x ∈ S) (hy : y ∈ R) : x < y := by
  have e1 : A ++ C :: S :: B = (A ++ [C, S]) ++ B := by
    simp [List.append_assoc]
  have h2 : RunsOrdered ((A ++ [C, S]) ++ B) := e1 ▸ h
  have hcross := (List.pairwise_append.mp h2).2.2
  exact hcross S (by simp) R hR x hx y hy

/-- **Discharged endpoint passage, predecessor case** (paper
`lem:foreignred`). In the foreign configuration — `r` splits the
blue run `C` just below the red run `S`, then arbitrary red
arrivals follow — every element of the final red run `F` growing
out of `S` either lies in `S` or exceeds `r`. Hence (`threshold_
record_at_final`) `r` is a threshold predecessor record for
`min F`. The joiner case is the blue barrier: at the joining step
the descendant blue run containing an upper-piece element `d₀ > r`
sits before the joined run, so the joiner's own step certificate
forces it above `d₀`; old elements of other runs are excluded by
`trace_same_run_old` (distinct old runs never merge). -/
theorem foreign_record_final {A B : List (List X)} {C S : List X}
    {below above : List X} {r : X} {σr σf : List (List X)}
    {L : List X}
    (hinv : Invariant color (A ++ C :: S :: B))
    (hmono : MonoRuns color (A ++ C :: S :: B))
    (hnod : (A ++ C :: S :: B).flatten.Nodup)
    (hord : RunsOrdered (A ++ C :: S :: B))
    (hc₀ : ∃ c ∈ C, c < r)
    (hblue : ∀ x ∈ C, color x = Color.blue)
    (hSne : S ≠ []) (hsred : ∀ x ∈ S, color x = Color.red)
    (hrS : ∀ y ∈ S, r < y) (hred : color r = Color.red)
    (hstep_r : Step color (A ++ C :: S :: B) r σr)
    (hσr : σr = A ++ below :: [r] :: above :: S :: B)
    (hsub_a : ∀ x ∈ above, x ∈ C) (hane : above ≠ [])
    (har : ∀ y ∈ above, r < y)
    (htr : TraceFrom color σr L σf)
    (hnd : (r :: L).Nodup)
    (hfresh : ∀ j ∈ r :: L, j ∉ (A ++ C :: S :: B).flatten)
    (hredL : ∀ j ∈ L, color j = Color.red)
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (hpresent : ∀ r' : X, color r' = Color.red → τ r' < τ r →
      r' ∈ (A ++ C :: S :: B).flatten) :
    ∃ F ∈ σf, (∀ x ∈ S, x ∈ F) ∧
      ∃ a ∈ F, IsPredRecord color τ a r ∧ ∀ y ∈ F, a ≤ y := by
  classical
  -- a red witness in S, and the final red run F growing out of S
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
    cases S with
    | nil => simp at hSne
    | cons x xs => exact ⟨x, by simp⟩
  have hs₀red : color s₀ = Color.red := hsred s₀ hs₀
  have hs₀flat_t : s₀ ∈ (A ++ C :: S :: B).flatten :=
    List.mem_flatten.mpr ⟨S, by simp, hs₀⟩
  have hmono_r : MonoRuns color σr := step_mono color hstep_r hmono hred
  obtain ⟨hinv_r, -⟩ := step_invariant color hstep_r hinv hmono hred
  obtain ⟨F, hF, hSF, hFred⟩ := final_red_run_of color
    (σ0 := σr) (L := L) (σf := σf) (R := S) (x₀ := s₀) htr hmono_r
    hredL (by rw [hσr]; simp) hs₀ hs₀red
  -- provenance and duplicate-freeness of the final flattening
  have htr_t : TraceFrom color (A ++ C :: S :: B) (r :: L) σf :=
    TraceFrom.cons hstep_r htr
  have hperm : σf.flatten.Perm ((r :: L) ++ (A ++ C :: S :: B).flatten) :=
    trace_flatten_perm color htr_t
  have hnod_append : ((r :: L) ++ (A ++ C :: S :: B).flatten).Nodup := by
    rw [List.nodup_append]
    exact ⟨hnd, hnod, fun a ha b hb hab => hfresh a ha (hab ▸ hb)⟩
  have hnod_f : σf.flatten.Nodup := hperm.nodup_iff.mpr hnod_append
  have hnod_r : σr.flatten.Nodup := by
    have hp : σr.flatten.Perm (r :: (A ++ C :: S :: B).flatten) :=
      step_flatten color hstep_r
    exact hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨hfresh r (by simp), hnod⟩)
  have hndL : L.Nodup := (List.nodup_cons.mp hnd).2
  have hrL : r ∉ L := (List.nodup_cons.mp hnd).1
  -- order fact at σr: upper-piece elements are below S elements
  have hord_r : RunsOrdered (A ++ below :: [r] :: above :: S :: B) := by
    have h := hinv_r.2.1
    rwa [hσr] at h
  have hCidx_r : (A ++ below :: [r] :: above :: S :: B)[A.length + 2]'(by simp)
      = above := by simp
  have hSidx_r : (A ++ below :: [r] :: above :: S :: B)[A.length + 3]'(by simp)
      = S := by simp
  have hs₀flat_r : s₀ ∈ σr.flatten :=
    List.mem_flatten.mpr ⟨S, by rw [hσr]; simp, hs₀⟩
  have hfresh_r : ∀ j ∈ L, j ∉ σr.flatten := by
    intro j hj hjf
    have hp : σr.flatten.Perm (r :: (A ++ C :: S :: B).flatten) :=
      step_flatten color hstep_r
    have h := (List.Perm.mem_iff hp).mp hjf
    simp only [List.mem_cons] at h
    rcases h with rfl | h2
    · exact hrL hj
    · exact hfresh j (by simp [hj]) h2
  -- the separation proviso
  have hsepF : ∀ x ∈ F, x ∈ S ∨ r < x := by
    intro x hxF
    have hxflat : x ∈ σf.flatten := List.mem_flatten.mpr ⟨F, hF, hxF⟩
    have hmem : x ∈ (r :: L) ++ (A ++ C :: S :: B).flatten :=
      (List.Perm.mem_iff hperm).mp hxflat
    simp only [List.mem_append, List.mem_cons] at hmem
    have hcases : x = r ∨ x ∈ (A ++ C :: S :: B).flatten ∨ x ∈ L := by
      rcases hmem with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    rcases hcases with hxr | hxold | hxL
    · -- x = r: excluded, since [r] and S never merge
      exfalso
      rw [hxr] at hxF
      have hrflat_r : r ∈ σr.flatten := by
        rw [hσr]
        refine List.mem_flatten.mpr ⟨[r], ?_, by simp⟩
        simp [List.mem_append, List.mem_cons]
      obtain ⟨Rr, hRr, hrR, hsR⟩ := trace_same_run_old color htr hndL
        hfresh_r hrflat_r hs₀flat_r hF hxF (hSF s₀ hs₀)
      have hRreq : Rr = [r] := run_unique hnod_r hRr
        (by rw [hσr]; simp [List.mem_append, List.mem_cons]) hrR (by simp)
      rw [hRreq] at hsR
      simp at hsR
      rw [hsR] at hs₀
      exact lt_irrefl r (hrS r hs₀)
    · -- x old: trichotomy on its run at the testing state
      have hxred : color x = Color.red := hFred x hxF
      obtain ⟨R₀, hR₀, hxR₀⟩ := List.mem_flatten.mp hxold
      simp only [List.mem_append, List.mem_cons] at hR₀
      rcases hR₀ with hA | rfl | rfl | hB
      · -- run before C: no-merge puts x in S anyway
        obtain ⟨R, hR, hxR, hsR⟩ := trace_same_run_old color htr_t hnd
          (x := x) (y := s₀) hxold hs₀flat_t hF hxF (hSF s₀ hs₀)
          (hfresh := hfresh)
        have hRS : R = S := run_unique hnod hR (by simp) hsR hs₀
        exact Or.inl (hRS ▸ hxR)
      · -- C is blue, x is red
        exact absurd (hblue x hxR₀) (by rw [hxred]; simp)
      · exact Or.inl hxR₀
      · -- run after S: exceeds s₀, hence exceeds r
        right
        exact lt_trans (hrS s₀ hs₀) (runsOrdered_mem_lt hord hB hs₀ hxR₀)
    · -- x a later arrival: the blue barrier at its joining step
      obtain ⟨L₁, L₂, hLsplit⟩ := mem_split_list hxL
      obtain ⟨σ₁, σ₂, htr₁, hstep_x, htr₂⟩ := trace_split color
        (σ0 := σr) (L₁ := L₁) (j := x) (L₂ := L₂)
        (by rw [← hLsplit]; exact htr)
      have hinv₁ : Invariant color σ₁ := by
        have h := trace_invariant color htr₁ hinv_r hmono_r
          (fun j hj => hredL j (by rw [hLsplit]; simp [hj]))
        exact h.1
      have hmono₁ : MonoRuns color σ₁ := by
        have h := trace_invariant color htr₁ hinv_r hmono_r
          (fun j hj => hredL j (by rw [hLsplit]; simp [hj]))
        exact h.2.1
      have hord₁ : RunsOrdered σ₁ := hinv₁.2.1
      have hndL' : (L₁ ++ x :: L₂).Nodup := hLsplit ▸ hndL
      have hxL₁ : x ∉ L₁ := by
        have h := (List.nodup_append.mp hndL').2.2
        intro hx1
        exact h x hx1 x (by simp) rfl
      have hxL₂ : x ∉ L₂ := by
        have h := (List.nodup_append.mp hndL').2.1
        exact (List.nodup_cons.mp h).1
      have hnd₂ : L₂.Nodup := by
        have h := (List.nodup_append.mp hndL').2.1
        exact (List.nodup_cons.mp h).2
      have hperm₁ : σ₁.flatten.Perm (L₁ ++ σr.flatten) :=
        trace_flatten_perm color htr₁
      have hperm_r : σr.flatten.Perm (r :: (A ++ C :: S :: B).flatten) :=
        step_flatten color hstep_r
      have hperm₁' : σ₁.flatten.Perm
          (L₁ ++ r :: (A ++ C :: S :: B).flatten) :=
        hperm₁.trans (List.Perm.append_left L₁ hperm_r)
      have hs₀flat₁ : s₀ ∈ σ₁.flatten :=
        (List.Perm.mem_iff hperm₁).mpr (List.mem_append.mpr (Or.inr hs₀flat_r))
      have hxfresh₁ : x ∉ σ₁.flatten := by
        intro hx1
        have h := (List.Perm.mem_iff hperm₁').mp hx1
        simp only [List.mem_append, List.mem_cons] at h
        rcases h with h1 | rfl | h3
        · exact hxL₁ h1
        · exact hrL (by rw [hLsplit]; simp)
        · exact hfresh x (by simp [hLsplit]) h3
      -- s₀ and x in a common run of σ₂ (no-merge on the tail trace)
      have hs₀flat₂ : s₀ ∈ σ₂.flatten := by
        have hp : σ₂.flatten.Perm (x :: σ₁.flatten) := step_flatten color hstep_x
        exact hp.mem_iff.mpr (List.mem_cons_of_mem x hs₀flat₁)
      have hxflat₂ : x ∈ σ₂.flatten := by
        have hp : σ₂.flatten.Perm (x :: σ₁.flatten) := step_flatten color hstep_x
        exact hp.mem_iff.mpr (List.mem_cons_self)
      have hfresh₂ : ∀ j ∈ L₂, j ∉ σ₂.flatten := by
        intro j hj hjf
        have hp : σ₂.flatten.Perm (x :: σ₁.flatten) := step_flatten color hstep_x
        have h1 : j = x ∨ j ∈ σ₁.flatten := by
          have h := (List.Perm.mem_iff hp).mp hjf
          simpa using h
        rcases h1 with rfl | h2
        · exact hxL₂ hj
        · have h3 := (List.Perm.mem_iff hperm₁').mp h2
          simp only [List.mem_append, List.mem_cons] at h3
          rcases h3 with h4 | rfl | h5
          · have hd := (List.nodup_append.mp hndL').2.2
            exact hd j h4 j (by simp [hj]) rfl
          · exact hrL (by rw [hLsplit]; simp [hj])
          · exact hfresh j (by simp [hLsplit, hj]) h5
      obtain ⟨R₂, hR₂, hxR₂, hsR₂⟩ := trace_same_run_old color htr₂ hnd₂
        hfresh₂ hs₀flat₂ hxflat₂ hF (hSF s₀ hs₀) hxF
      -- the barrier run at σ₁: the run containing an upper-piece element
      obtain ⟨d₀, hd₀⟩ : ∃ d₀, d₀ ∈ above := by
        cases above with
        | nil => simp at hane
        | cons d ds => exact ⟨d, by simp⟩
      have hd₀C : d₀ ∈ C := hsub_a d₀ hd₀
      have hd₀blue : color d₀ = Color.blue := hblue d₀ hd₀C
      have hd₀flat_r : d₀ ∈ σr.flatten :=
        List.mem_flatten.mpr ⟨above, by rw [hσr]; simp, hd₀⟩
      have hd₀flat₁ : d₀ ∈ σ₁.flatten :=
        (List.Perm.mem_iff hperm₁).mpr (List.mem_append.mpr (Or.inr hd₀flat_r))
      obtain ⟨D, hD, hd₀D⟩ := List.mem_flatten.mp hd₀flat₁
      have hDblue : ∀ z ∈ D, color z = Color.blue := by
        rcases hmono₁ D hD with hr | hb
        · rw [hr d₀ hd₀D] at hd₀blue
          exact absurd hd₀blue (by simp)
        · exact hb
      have hrd₀ : r < d₀ := har d₀ hd₀
      have hd₀s₀ : d₀ < s₀ :=
        runsOrdered_getElem hord_r (i := A.length + 2) (j := A.length + 3)
          (by simp only [List.length_append, List.length_cons]; omega)
          (by simp only [List.length_append, List.length_cons]; omega) (by omega)
          (by rw [hCidx_r]; exact hd₀) (by rw [hSidx_r]; exact hs₀)
      -- joining-step case analysis
      cases hstep_x with
      | freshSingleton Aₓ Bₓ Sₓ j hL hR =>
          simp only [applyOp, List.mem_append, List.mem_cons] at hR₂
          rcases hR₂ with h1 | rfl | h3 | h4
          · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inl h1), hsR₂⟩) hxfresh₁
          · have hs₀eq : s₀ = x := List.mem_singleton.mp hxR₂
            rw [hs₀eq] at hs₀flat_t
            exact absurd hs₀flat_t (hfresh x (by simp [hLsplit]))
          · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl h3))), hsR₂⟩) hxfresh₁
          · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h4))), hsR₂⟩) hxfresh₁
      | mergePair Aₓ Bₓ Sₓ j r₀ hSₓ hSredₓ hL hR =>
          have hs₀Sₓ : s₀ ∈ Sₓ := by
            simp only [applyOp, List.mem_append, List.mem_cons] at hR₂
            rcases hR₂ with h1 | rfl | h4
            · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inl h1), hsR₂⟩) hxfresh₁
            · have hs₀eq : s₀ = r₀ := by
                split_ifs at hxR₂
                · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxR₂
                  rcases hxR₂ with h | h
                  · rw [h] at hs₀flat_t
                    exact absurd hs₀flat_t (hfresh x (by simp [hLsplit]))
                  · exact h
                · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxR₂
                  rcases hxR₂ with h | h
                  · exact h
                  · rw [h] at hs₀flat_t
                    exact absurd hs₀flat_t (hfresh x (by simp [hLsplit]))
              rw [hs₀eq, hSₓ]
              simp
            · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h4))), hsR₂⟩) hxfresh₁
          right
          obtain ⟨k, hk, hDk⟩ := List.mem_iff_getElem.mp hD
          have hSₓidx : (Aₓ ++ Sₓ :: Bₓ)[Aₓ.length]'(by simp) = Sₓ := by simp
          rcases lt_trichotomy k Aₓ.length with hlt | heq | hgt
          · have hDA : (Aₓ ++ Sₓ :: Bₓ)[k]'hk = Aₓ[k]'(by omega) := by
              simp [List.getElem_append, hlt]
            have hDAx : D ∈ Aₓ :=
              List.mem_iff_getElem.mpr ⟨k, by omega, hDA.symm.trans hDk⟩
            exact lt_trans hrd₀ (hL D hDAx d₀ hd₀D).1
          · subst heq
            rw [hSₓidx] at hDk
            have hDS : D = Sₓ := hDk.symm
            rw [hDS] at hd₀D
            rcases hmono₁ Sₓ (by simp [List.mem_append]) with hr | hb
            · rw [hr d₀ hd₀D] at hd₀blue
              exact absurd hd₀blue (by simp)
            · rw [hb s₀ hs₀Sₓ] at hs₀red
              exact absurd hs₀red (by simp)
          · have hlt2 : s₀ < d₀ :=
              runsOrdered_getElem hord₁
                (by simp only [List.length_append, List.length_cons]; omega)
                hk hgt
                (by rw [hSₓidx]; exact hs₀Sₓ) (by rw [hDk]; exact hd₀D)
            exact absurd hlt2 (not_lt.mpr (le_of_lt hd₀s₀))
      | insertInto Aₓ Bₓ Sₓ j hSredₓ hL hR =>
          have hs₀Sₓ : s₀ ∈ Sₓ := by
            simp only [applyOp, List.mem_append, List.mem_cons] at hR₂
            rcases hR₂ with h1 | rfl | h4
            · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inl h1), hsR₂⟩) hxfresh₁
            · rw [insertSorted_mem] at hxR₂
              rcases hxR₂ with h | h
              · rw [h] at hs₀flat_t
                exact absurd hs₀flat_t (hfresh x (by simp [hLsplit]))
              · exact h
            · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h4))), hsR₂⟩) hxfresh₁
          right
          obtain ⟨k, hk, hDk⟩ := List.mem_iff_getElem.mp hD
          have hSₓidx : (Aₓ ++ Sₓ :: Bₓ)[Aₓ.length]'(by simp) = Sₓ := by simp
          rcases lt_trichotomy k Aₓ.length with hlt | heq | hgt
          · have hDA : (Aₓ ++ Sₓ :: Bₓ)[k]'hk = Aₓ[k]'(by omega) := by
              simp [List.getElem_append, hlt]
            have hDAx : D ∈ Aₓ :=
              List.mem_iff_getElem.mpr ⟨k, by omega, hDA.symm.trans hDk⟩
            exact lt_trans hrd₀ (hL D hDAx d₀ hd₀D)
          · subst heq
            rw [hSₓidx] at hDk
            have hDS : D = Sₓ := hDk.symm
            rw [hDS] at hd₀D
            rcases hmono₁ Sₓ (by simp [List.mem_append]) with hr | hb
            · rw [hr d₀ hd₀D] at hd₀blue
              exact absurd hd₀blue (by simp)
            · rw [hb s₀ hs₀Sₓ] at hs₀red
              exact absurd hs₀red (by simp)
          · have hlt2 : s₀ < d₀ :=
              runsOrdered_getElem hord₁
                (by simp only [List.length_append, List.length_cons]; omega)
                hk hgt
                (by rw [hSₓidx]; exact hs₀Sₓ) (by rw [hDk]; exact hd₀D)
            exact absurd hlt2 (not_lt.mpr (le_of_lt hd₀s₀))
      | splitRun Aₓ Bₓ Sₓ belowₓ aboveₓ j hsub_bₓ hsub_aₓ hblueₓ hbneₓ haneₓ hbrₓ harₓ hArₓ hrBₓ hpartₓ =>
          simp only [applyOp, List.mem_append, List.mem_cons] at hR₂
          rcases hR₂ with h1 | rfl | rfl | rfl | h5
          · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inl h1), hsR₂⟩) hxfresh₁
          · have h1 : color s₀ = Color.blue := hblueₓ s₀ (hsub_bₓ s₀ hxR₂)
            rw [hs₀red] at h1
            exact Color.noConfusion h1
          · have hs₀eq : s₀ = x := List.mem_singleton.mp hxR₂
            rw [hs₀eq] at hs₀flat_t
            exact absurd hs₀flat_t (hfresh x (by simp [hLsplit]))
          · have h1 : color s₀ = Color.blue := hblueₓ s₀ (hsub_aₓ s₀ hxR₂)
            rw [hs₀red] at h1
            exact Color.noConfusion h1
          · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h5))), hsR₂⟩) hxfresh₁
      | appendSingleton Aₓ Bₓ Sₓ j hAll =>
          simp only [applyOp, List.mem_append, List.mem_singleton] at hR₂
          rcases hR₂ with h1 | rfl
          · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr h1, hsR₂⟩) hxfresh₁
          · have hs₀eq : s₀ = x := List.mem_singleton.mp hxR₂
            rw [hs₀eq] at hs₀flat_t
            exact absurd hs₀flat_t (hfresh x (by simp [hLsplit]))
  exact ⟨F, hF, hSF, threshold_record_at_final color hord hc₀ hblue
    hSne hrS hred τ hinj hpresent (List.ne_nil_of_mem (hSF s₀ hs₀))
    hSF hsepF⟩


/-- Cross-run comparison, left form: in `A ++ S :: C :: B` ordered,
every element of a run in `A` is below every element of `S`. -/
theorem runsOrdered_mem_lt_left {A B : List (List X)} {S C R : List X}
    (h : RunsOrdered (A ++ S :: C :: B)) (hR : R ∈ A)
    {x y : X} (hx : x ∈ R) (hy : y ∈ S) : x < y := by
  have hcross := (List.pairwise_append.mp h).2.2
  exact hcross R hR S (by simp) x hx y hy


/-- If the run at index `k` of `Aₓ ++ Sₓ :: Bₓ` lies past `Sₓ`,
it is a run of `Bₓ`. -/
theorem mem_run_after {Aₓ Bₓ : List (List X)} {Sₓ D : List X} {k : ℕ}
    (hk : k < (Aₓ ++ Sₓ :: Bₓ).length) (hgt : Aₓ.length < k)
    (hDk : (Aₓ ++ Sₓ :: Bₓ)[k]'hk = D) : D ∈ Bₓ := by
  induction Aₓ generalizing k with
  | nil =>
      simp only [List.length_nil] at hgt
      have hkB : k - 1 < Bₓ.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hk
        omega
      refine List.mem_iff_getElem.mpr ⟨k - 1, hkB, ?_⟩
      have h2 : (Sₓ :: Bₓ)[k]'(by
          simp only [List.length_cons]; omega) = Bₓ[k - 1]'hkB := by
        cases k with
        | zero => omega
        | succ m => simp [List.getElem_cons]
      exact h2.symm.trans hDk
  | cons a A' ih =>
      cases k with
      | zero =>
          simp only [List.length_cons] at hgt
          omega
      | succ m =>
          have hk' : m < (A' ++ Sₓ :: Bₓ).length := by
            simp only [List.length_cons, List.length_append] at hk ⊢
            omega
          have hgt' : A'.length < m := by
            simp only [List.length_cons] at hgt
            omega
          have hDk' : (A' ++ Sₓ :: Bₓ)[m]'hk' = D := hDk
          exact ih hk' hgt' hDk'

/-- **Discharged endpoint passage, successor case** (paper
`lem:foreignred`, mirror). In the foreign configuration from above
— `r` splits the blue run `C` just above the red run `S`, then
arbitrary red arrivals follow — every element of the final red run
`F` growing out of `S` either lies in `S` or is below `r`. Hence
(`threshold_record_succ_at_final`) `r` is a threshold successor
record for `max F`. The joiner case is the blue barrier from
above: the descendant blue run containing a lower-piece element
`d₀ < r` sits after the joined run, so the joiner's step
certificate forces it below `d₀`. -/
theorem foreign_record_final_succ {A B : List (List X)} {C S : List X}
    {below above : List X} {r : X} {σr σf : List (List X)}
    {L : List X}
    (hinv : Invariant color (A ++ S :: C :: B))
    (hmono : MonoRuns color (A ++ S :: C :: B))
    (hnod : (A ++ S :: C :: B).flatten.Nodup)
    (hord : RunsOrdered (A ++ S :: C :: B))
    (hc₀ : ∃ c ∈ C, r < c)
    (hblue : ∀ x ∈ C, color x = Color.blue)
    (hSne : S ≠ []) (hsred : ∀ x ∈ S, color x = Color.red)
    (hrS : ∀ y ∈ S, y < r) (hred : color r = Color.red)
    (hstep_r : Step color (A ++ S :: C :: B) r σr)
    (hσr : σr = A ++ S :: below :: [r] :: above :: B)
    (hsub_b : ∀ x ∈ below, x ∈ C) (hbne : below ≠ [])
    (hbl : ∀ y ∈ below, y < r)
    (htr : TraceFrom color σr L σf)
    (hnd : (r :: L).Nodup)
    (hfresh : ∀ j ∈ r :: L, j ∉ (A ++ S :: C :: B).flatten)
    (hredL : ∀ j ∈ L, color j = Color.red)
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (hpresent : ∀ r' : X, color r' = Color.red → τ r' < τ r →
      r' ∈ (A ++ S :: C :: B).flatten) :
    ∃ F ∈ σf, (∀ x ∈ S, x ∈ F) ∧
      ∃ z ∈ F, IsSuccRecord color τ z r ∧ ∀ y ∈ F, y ≤ z := by
  classical
  obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
    cases S with
    | nil => simp at hSne
    | cons x xs => exact ⟨x, by simp⟩
  have hs₀red : color s₀ = Color.red := hsred s₀ hs₀
  have hs₀flat_t : s₀ ∈ (A ++ S :: C :: B).flatten :=
    List.mem_flatten.mpr ⟨S, by simp, hs₀⟩
  have hmono_r : MonoRuns color σr := step_mono color hstep_r hmono hred
  obtain ⟨hinv_r, -⟩ := step_invariant color hstep_r hinv hmono hred
  obtain ⟨F, hF, hSF, hFred⟩ := final_red_run_of color
    (σ0 := σr) (L := L) (σf := σf) (R := S) (x₀ := s₀) htr hmono_r
    hredL (by rw [hσr]; simp) hs₀ hs₀red
  have htr_t : TraceFrom color (A ++ S :: C :: B) (r :: L) σf :=
    TraceFrom.cons hstep_r htr
  have hperm : σf.flatten.Perm ((r :: L) ++ (A ++ S :: C :: B).flatten) :=
    trace_flatten_perm color htr_t
  have hnod_r : σr.flatten.Nodup := by
    have hp : σr.flatten.Perm (r :: (A ++ S :: C :: B).flatten) :=
      step_flatten color hstep_r
    exact hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨hfresh r (by simp), hnod⟩)
  have hndL : L.Nodup := (List.nodup_cons.mp hnd).2
  have hrL : r ∉ L := (List.nodup_cons.mp hnd).1
  have hs₀flat_r : s₀ ∈ σr.flatten :=
    List.mem_flatten.mpr ⟨S, by rw [hσr]; simp, hs₀⟩
  have hfresh_r : ∀ j ∈ L, j ∉ σr.flatten := by
    intro j hj hjf
    have hp : σr.flatten.Perm (r :: (A ++ S :: C :: B).flatten) :=
      step_flatten color hstep_r
    have h := (List.Perm.mem_iff hp).mp hjf
    simp only [List.mem_cons] at h
    rcases h with rfl | h2
    · exact hrL hj
    · exact hfresh j (by simp [hj]) h2
  have hord_r : RunsOrdered (A ++ S :: below :: [r] :: above :: B) := by
    have h := hinv_r.2.1
    rwa [hσr] at h
  have hSidx_r : (A ++ S :: below :: [r] :: above :: B)[A.length]'(by simp)
      = S := by simp
  have hBidx_r : (A ++ S :: below :: [r] :: above :: B)[A.length + 1]'(by simp)
      = below := by simp
  have hsepF : ∀ x ∈ F, x ∈ S ∨ x < r := by
    intro x hxF
    have hxflat : x ∈ σf.flatten := List.mem_flatten.mpr ⟨F, hF, hxF⟩
    have hmem : x ∈ (r :: L) ++ (A ++ S :: C :: B).flatten :=
      (List.Perm.mem_iff hperm).mp hxflat
    have hcases : x = r ∨ x ∈ (A ++ S :: C :: B).flatten ∨ x ∈ L := by
      rcases (by simpa using hmem : x = r ∨ x ∈ L ∨
          x ∈ (A ++ S :: C :: B).flatten) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    rcases hcases with hxr | hxold | hxL
    · exfalso
      rw [hxr] at hxF
      have hrflat_r : r ∈ σr.flatten := by
        rw [hσr]
        refine List.mem_flatten.mpr ⟨[r], ?_, by simp⟩
        simp [List.mem_append, List.mem_cons]
      obtain ⟨Rr, hRr, hrR, hsR⟩ := trace_same_run_old color htr hndL
        hfresh_r hrflat_r hs₀flat_r hF hxF (hSF s₀ hs₀)
      have hRreq : Rr = [r] := run_unique hnod_r hRr
        (by rw [hσr]; simp [List.mem_append, List.mem_cons]) hrR (by simp)
      rw [hRreq] at hsR
      simp at hsR
      rw [hsR] at hs₀
      exact lt_irrefl r (hrS r hs₀)
    · have hxred : color x = Color.red := hFred x hxF
      obtain ⟨R₀, hR₀, hxR₀⟩ := List.mem_flatten.mp hxold
      simp only [List.mem_append, List.mem_cons] at hR₀
      rcases hR₀ with hA | rfl | rfl | hB
      · right
        exact lt_trans (runsOrdered_mem_lt_left hord hA hxR₀ hs₀) (hrS s₀ hs₀)
      · exact Or.inl hxR₀
      · exact absurd (hblue x hxR₀) (by rw [hxred]; simp)
      · obtain ⟨R, hR, hxR, hsR⟩ := trace_same_run_old color htr_t hnd
          (x := x) (y := s₀) hxold hs₀flat_t hF hxF (hSF s₀ hs₀)
          (hfresh := hfresh)
        have hRS : R = S := run_unique hnod hR (by simp) hsR hs₀
        exact Or.inl (hRS ▸ hxR)
    · obtain ⟨L₁, L₂, hLsplit⟩ := mem_split_list hxL
      obtain ⟨σ₁, σ₂, htr₁, hstep_x, htr₂⟩ := trace_split color
        (σ0 := σr) (L₁ := L₁) (j := x) (L₂ := L₂)
        (by rw [← hLsplit]; exact htr)
      have hinv₁ : Invariant color σ₁ := by
        have h := trace_invariant color htr₁ hinv_r hmono_r
          (fun j hj => hredL j (by rw [hLsplit]; simp [hj]))
        exact h.1
      have hmono₁ : MonoRuns color σ₁ := by
        have h := trace_invariant color htr₁ hinv_r hmono_r
          (fun j hj => hredL j (by rw [hLsplit]; simp [hj]))
        exact h.2.1
      have hord₁ : RunsOrdered σ₁ := hinv₁.2.1
      have hndL' : (L₁ ++ x :: L₂).Nodup := hLsplit ▸ hndL
      have hxL₁ : x ∉ L₁ := by
        have h := (List.nodup_append.mp hndL').2.2
        intro hx1
        exact h x hx1 x (by simp) rfl
      have hxL₂ : x ∉ L₂ := by
        have h := (List.nodup_append.mp hndL').2.1
        exact (List.nodup_cons.mp h).1
      have hnd₂ : L₂.Nodup := by
        have h := (List.nodup_append.mp hndL').2.1
        exact (List.nodup_cons.mp h).2
      have hperm₁ : σ₁.flatten.Perm (L₁ ++ σr.flatten) :=
        trace_flatten_perm color htr₁
      have hperm_r : σr.flatten.Perm (r :: (A ++ S :: C :: B).flatten) :=
        step_flatten color hstep_r
      have hperm₁' : σ₁.flatten.Perm
          (L₁ ++ r :: (A ++ S :: C :: B).flatten) :=
        hperm₁.trans (List.Perm.append_left L₁ hperm_r)
      have hs₀flat₁ : s₀ ∈ σ₁.flatten :=
        (List.Perm.mem_iff hperm₁).mpr (List.mem_append.mpr (Or.inr hs₀flat_r))
      have hxfresh₁ : x ∉ σ₁.flatten := by
        intro hx1
        have h := (List.Perm.mem_iff hperm₁').mp hx1
        simp only [List.mem_append, List.mem_cons] at h
        rcases h with h1 | rfl | h3
        · exact hxL₁ h1
        · exact hrL (by rw [hLsplit]; simp)
        · exact hfresh x (by simp [hLsplit]) h3
      have hs₀flat₂ : s₀ ∈ σ₂.flatten := by
        have hp : σ₂.flatten.Perm (x :: σ₁.flatten) := step_flatten color hstep_x
        exact hp.mem_iff.mpr (List.mem_cons_of_mem x hs₀flat₁)
      have hxflat₂ : x ∈ σ₂.flatten := by
        have hp : σ₂.flatten.Perm (x :: σ₁.flatten) := step_flatten color hstep_x
        exact hp.mem_iff.mpr (List.mem_cons_self)
      have hfresh₂ : ∀ j ∈ L₂, j ∉ σ₂.flatten := by
        intro j hj hjf
        have hp : σ₂.flatten.Perm (x :: σ₁.flatten) := step_flatten color hstep_x
        have h1 : j = x ∨ j ∈ σ₁.flatten := by
          have h := (List.Perm.mem_iff hp).mp hjf
          simpa using h
        rcases h1 with rfl | h2
        · exact hxL₂ hj
        · have h3 := (List.Perm.mem_iff hperm₁').mp h2
          simp only [List.mem_append, List.mem_cons] at h3
          rcases h3 with h4 | rfl | h5
          · have hd := (List.nodup_append.mp hndL').2.2
            exact hd j h4 j (by simp [hj]) rfl
          · exact hrL (by rw [hLsplit]; simp [hj])
          · exact hfresh j (by simp [hLsplit, hj]) h5
      obtain ⟨R₂, hR₂, hxR₂, hsR₂⟩ := trace_same_run_old color htr₂ hnd₂
        hfresh₂ hs₀flat₂ hxflat₂ hF (hSF s₀ hs₀) hxF
      obtain ⟨d₀, hd₀⟩ : ∃ d₀, d₀ ∈ below := by
        cases below with
        | nil => simp at hbne
        | cons d ds => exact ⟨d, by simp⟩
      have hd₀C : d₀ ∈ C := hsub_b d₀ hd₀
      have hd₀blue : color d₀ = Color.blue := hblue d₀ hd₀C
      have hd₀flat_r : d₀ ∈ σr.flatten :=
        List.mem_flatten.mpr ⟨below, by rw [hσr]; simp, hd₀⟩
      have hd₀flat₁ : d₀ ∈ σ₁.flatten :=
        (List.Perm.mem_iff hperm₁).mpr (List.mem_append.mpr (Or.inr hd₀flat_r))
      obtain ⟨D, hD, hd₀D⟩ := List.mem_flatten.mp hd₀flat₁
      have hDblue : ∀ z ∈ D, color z = Color.blue := by
        rcases hmono₁ D hD with hr | hb
        · rw [hr d₀ hd₀D] at hd₀blue
          exact absurd hd₀blue (by simp)
        · exact hb
      have hd₀r : d₀ < r := hbl d₀ hd₀
      have hs₀d₀ : s₀ < d₀ :=
        runsOrdered_getElem hord_r (i := A.length) (j := A.length + 1)
          (by simp only [List.length_append, List.length_cons]; omega)
          (by simp only [List.length_append, List.length_cons]; omega) (by omega)
          (by rw [hSidx_r]; exact hs₀) (by rw [hBidx_r]; exact hd₀)
      cases hstep_x with
      | freshSingleton Aₓ Bₓ Sₓ j hL hR =>
          simp only [applyOp, List.mem_append, List.mem_cons] at hR₂
          rcases hR₂ with h1 | rfl | h3 | h4
          · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inl h1), hsR₂⟩) hxfresh₁
          · have hs₀eq : s₀ = x := List.mem_singleton.mp hxR₂
            rw [hs₀eq] at hs₀flat_t
            exact absurd hs₀flat_t (hfresh x (by simp [hLsplit]))
          · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl h3))), hsR₂⟩) hxfresh₁
          · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h4))), hsR₂⟩) hxfresh₁
      | mergePair Aₓ Bₓ Sₓ j r₀ hSₓ hSredₓ hL hR =>
          have hs₀Sₓ : s₀ ∈ Sₓ := by
            simp only [applyOp, List.mem_append, List.mem_cons] at hR₂
            rcases hR₂ with h1 | rfl | h4
            · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inl h1), hsR₂⟩) hxfresh₁
            · have hs₀eq : s₀ = r₀ := by
                split_ifs at hxR₂
                · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxR₂
                  rcases hxR₂ with h | h
                  · rw [h] at hs₀flat_t
                    exact absurd hs₀flat_t (hfresh x (by simp [hLsplit]))
                  · exact h
                · simp only [List.mem_cons, List.not_mem_nil, or_false] at hxR₂
                  rcases hxR₂ with h | h
                  · exact h
                  · rw [h] at hs₀flat_t
                    exact absurd hs₀flat_t (hfresh x (by simp [hLsplit]))
              rw [hs₀eq, hSₓ]
              simp
            · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h4))), hsR₂⟩) hxfresh₁
          right
          obtain ⟨k, hk, hDk⟩ := List.mem_iff_getElem.mp hD
          have hSₓidx : (Aₓ ++ Sₓ :: Bₓ)[Aₓ.length]'(by simp) = Sₓ := by simp
          have barrier : ∀ (hDB : D ∈ Bₓ), x < r := by
            intro hDB
            exact lt_trans (hR D hDB d₀ hd₀D).1 hd₀r
          rcases lt_trichotomy k Aₓ.length with hlt | heq | hgt
          · have hlt2 : d₀ < s₀ :=
              runsOrdered_getElem hord₁ (i := k) (j := Aₓ.length) hk
                (by simp only [List.length_append, List.length_cons]; omega)
                hlt (by rw [hDk]; exact hd₀D) (by rw [hSₓidx]; exact hs₀Sₓ)
            exact absurd hlt2 (not_lt.mpr (le_of_lt hs₀d₀))
          · subst heq
            rw [hSₓidx] at hDk
            have hDS : D = Sₓ := hDk.symm
            rw [hDS] at hd₀D
            rcases hmono₁ Sₓ (by simp [List.mem_append]) with hr | hb
            · rw [hr d₀ hd₀D] at hd₀blue
              exact absurd hd₀blue (by simp)
            · rw [hb s₀ hs₀Sₓ] at hs₀red
              exact absurd hs₀red (by simp)
          · have hDB : D ∈ Bₓ := mem_run_after hk hgt hDk
            exact barrier hDB
      | insertInto Aₓ Bₓ Sₓ j hSredₓ hL hR =>
          have hs₀Sₓ : s₀ ∈ Sₓ := by
            simp only [applyOp, List.mem_append, List.mem_cons] at hR₂
            rcases hR₂ with h1 | rfl | h4
            · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inl h1), hsR₂⟩) hxfresh₁
            · rw [insertSorted_mem] at hxR₂
              rcases hxR₂ with h | h
              · rw [h] at hs₀flat_t
                exact absurd hs₀flat_t (hfresh x (by simp [hLsplit]))
              · exact h
            · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h4))), hsR₂⟩) hxfresh₁
          right
          obtain ⟨k, hk, hDk⟩ := List.mem_iff_getElem.mp hD
          have hSₓidx : (Aₓ ++ Sₓ :: Bₓ)[Aₓ.length]'(by simp) = Sₓ := by simp
          have barrier : ∀ (hDB : D ∈ Bₓ), x < r := by
            intro hDB
            exact lt_trans (hR D hDB d₀ hd₀D) hd₀r
          rcases lt_trichotomy k Aₓ.length with hlt | heq | hgt
          · have hlt2 : d₀ < s₀ :=
              runsOrdered_getElem hord₁ (i := k) (j := Aₓ.length) hk
                (by simp only [List.length_append, List.length_cons]; omega)
                hlt (by rw [hDk]; exact hd₀D) (by rw [hSₓidx]; exact hs₀Sₓ)
            exact absurd hlt2 (not_lt.mpr (le_of_lt hs₀d₀))
          · subst heq
            rw [hSₓidx] at hDk
            have hDS : D = Sₓ := hDk.symm
            rw [hDS] at hd₀D
            rcases hmono₁ Sₓ (by simp [List.mem_append]) with hr | hb
            · rw [hr d₀ hd₀D] at hd₀blue
              exact absurd hd₀blue (by simp)
            · rw [hb s₀ hs₀Sₓ] at hs₀red
              exact absurd hs₀red (by simp)
          · have hDB : D ∈ Bₓ := mem_run_after hk hgt hDk
            exact barrier hDB
      | splitRun Aₓ Bₓ Sₓ belowₓ aboveₓ j hsub_bₓ hsub_aₓ hblueₓ hbneₓ haneₓ hbrₓ harₓ hArₓ hrBₓ hpartₓ =>
          simp only [applyOp, List.mem_append, List.mem_cons] at hR₂
          rcases hR₂ with h1 | rfl | rfl | rfl | h5
          · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inl h1), hsR₂⟩) hxfresh₁
          · have h1 : color s₀ = Color.blue := hblueₓ s₀ (hsub_bₓ s₀ hxR₂)
            rw [hs₀red] at h1
            exact Color.noConfusion h1
          · have hs₀eq : s₀ = x := List.mem_singleton.mp hxR₂
            rw [hs₀eq] at hs₀flat_t
            exact absurd hs₀flat_t (hfresh x (by simp [hLsplit]))
          · have h1 : color s₀ = Color.blue := hblueₓ s₀ (hsub_aₓ s₀ hxR₂)
            rw [hs₀red] at h1
            exact Color.noConfusion h1
          · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr h5))), hsR₂⟩) hxfresh₁
      | appendSingleton Aₓ Bₓ Sₓ j hAll =>
          simp only [applyOp, List.mem_append, List.mem_singleton] at hR₂
          rcases hR₂ with h1 | rfl
          · exact absurd (List.mem_flatten.mpr ⟨R₂, List.mem_append.mpr h1, hsR₂⟩) hxfresh₁
          · have hs₀eq : s₀ = x := List.mem_singleton.mp hxR₂
            rw [hs₀eq] at hs₀flat_t
            exact absurd hs₀flat_t (hfresh x (by simp [hLsplit]))
  exact ⟨F, hF, hSF, threshold_record_succ_at_final color hord hc₀ hblue
    hSne hrS hred τ hinj hpresent (List.ne_nil_of_mem (hSF s₀ hs₀))
    hSF hsepF⟩

end Bichromatic.Randomized
