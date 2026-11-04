import RandomizedLog.Trace

/-!
# Producing steps from locate and scan (randomized paper, §2–§3)

The Step model of `RandomizedTrace` is certificate-based: a step
exists when the separation facts its invariant proof consumes are
in hand. This file shows the algorithm's locate-and-scan actually
produces those certificates in the mixed-scan case, with no extra
hypotheses: the two mixed-scan witnesses (an element of the scanned
blue run on each side of `r`) bound every other run through
run-order. The remaining operations are the Step constructors
themselves, named here as the production interface the assembly
consumes.
-/

namespace Bichromatic.Randomized

open Bichromatic

variable {X : Type*} [LinearOrder X] [Fintype X] (color : X → Color)

/-- A mixed scan of the blue run `C` at the located decomposition
`A ++ C :: B` produces a split step, with the splice pieces the
scan's filter partition. Every Step certificate is derived: the
pieces and their bounds from the filter, nonemptiness from the
mixed verdict, and the separation of the outer runs from run-order
chained through the two scan witnesses. -/
theorem scan_split_step {A B : List (List X)} {C : List X} {r : X}
    (hord : RunsOrdered (A ++ C :: B))
    (hblue : ∀ x ∈ C, color x = Color.blue) (hred : color r = Color.red)
    (hmixed : scanVerdict C r = ScanVerdict.mixed) :
    Step color (A ++ C :: B) r
      (applyOp A B C r (.splitRun (belowPiece C r) (abovePiece C r))) := by
  classical
  have hne : ∀ x ∈ C, x ≠ r := by
    intro x hx hcon
    have h1 : color r = Color.blue := by rw [← hcon]; exact hblue x hx
    rw [hred] at h1
    exact Color.noConfusion h1
  obtain ⟨⟨c₂, hc₂C, hc₂r⟩, ⟨c₁, hc₁C, hc₁r⟩⟩ := exists_of_mixed hne hmixed
  have hcross1 := (List.pairwise_append.mp hord).2.2
  have hAr : ∀ R ∈ A, ∀ x ∈ R, x < r := fun R hR x hx =>
    lt_trans (hcross1 R hR C (by simp) x hx c₁ hc₁C) hc₁r
  have hcross2 : ∀ R ∈ A ++ [C], ∀ T ∈ B, ∀ x ∈ R, ∀ y ∈ T, x < y := by
    have e : A ++ C :: B = (A ++ [C]) ++ B := by simp [List.append_assoc]
    exact (List.pairwise_append.mp (e ▸ hord)).2.2
  have hrB : ∀ T ∈ B, ∀ y ∈ T, r < y := fun T hT y hy =>
    lt_trans hc₂r (hcross2 C (by simp) T hT c₂ hc₂C y hy)
  exact Step.splitRun A B C (belowPiece C r) (abovePiece C r) r
    (fun x hx => (belowPiece_mem hx).1)
    (fun x hx => (abovePiece_mem hx).1)
    hblue
    (List.ne_nil_of_mem (show c₁ ∈ belowPiece C r by
      simp [belowPiece, List.mem_filter, hc₁C, hc₁r]))
    (List.ne_nil_of_mem (show c₂ ∈ abovePiece C r by
      simp [abovePiece, List.mem_filter, hc₂C, hc₂r]))
    (fun x hx => (belowPiece_mem hx).2)
    (fun x hx => (abovePiece_mem hx).2)
    hAr hrB (below_append_above_perm hne)

/-- Production interface, Case A: a fresh singleton step from its
two separation certificates (supplied by location: everything
before the insertion interval is below `r`, everything after
exceeds `r`). -/
theorem step_freshSingleton_of {A B : List (List X)} {S : List X} {r : X}
    (hL : ∀ R ∈ A, ∀ x ∈ R, x < r)
    (hR : ∀ T ∈ S :: B, ∀ y ∈ T, r < y) :
    Step color (A ++ S :: B) r (applyOp A B S r .freshSingleton) :=
  Step.freshSingleton A B S r hL hR

/-- Production interface, Case B: a merger step from the singleton
fact and its certificates. -/
theorem step_mergePair_of {A B : List (List X)} {S : List X} {r r₀ : X}
    (hS : S = [r₀]) (hSred : ∀ x ∈ S, color x = Color.red)
    (hL : ∀ R ∈ A, ∀ x ∈ R, x < r ∧ x < r₀)
    (hR : ∀ T ∈ B, ∀ y ∈ T, r < y ∧ r₀ < y) :
    Step color (A ++ S :: B) r (applyOp A B S r (.mergePair r₀)) :=
  Step.mergePair A B S r r₀ hS hSred hL hR

/-- Production interface, Case C: an insertion-into-red-run step
from its certificates. -/
theorem step_insertInto_of {A B : List (List X)} {S : List X} {r : X}
    (hSred : ∀ x ∈ S, color x = Color.red)
    (hL : ∀ R ∈ A, ∀ x ∈ R, x < r)
    (hR : ∀ T ∈ B, ∀ y ∈ T, r < y) :
    Step color (A ++ S :: B) r (applyOp A B S r .insertInto) :=
  Step.insertInto A B S r hSred hL hR


/-- Charging a mixed scan: the scan of `C` by `r` makes `|C|`
incidences (counted as the two splice pieces), and `r` is a record
for every blue element it touches. This is the incidence-level
content the expected-cost assembly sums over the trace. -/
theorem split_scan_charged {A B : List (List X)} {C : List X} {r : X}
    (hord : RunsOrdered (A ++ C :: B))
    (hblue : ∀ x ∈ C, color x = Color.blue) (hred : color r = Color.red)
    (hmixed : scanVerdict C r = ScanVerdict.mixed)
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (hpresent : ∀ r' : X, color r' = Color.red → τ r' < τ r →
      r' ∈ (A ++ C :: B).flatten) :
    (belowPiece C r).length + (abovePiece C r).length = C.length ∧
      ∀ b ∈ C, IsRecord color τ b r := by
  classical
  have hne : ∀ x ∈ C, x ≠ r := by
    intro x hx hcon
    have h1 : color r = Color.blue := by rw [← hcon]; exact hblue x hx
    rw [hred] at h1
    exact Color.noConfusion h1
  obtain ⟨⟨c₂, hc₂C, hc₂r⟩, ⟨c₁, hc₁C, hc₁r⟩⟩ := exists_of_mixed hne hmixed
  refine ⟨?_, fun b hb => ?_⟩
  · have hp := below_append_above_perm hne (C := C) (r := r)
    have h := List.Perm.length_eq hp
    rw [List.length_append] at h
    exact h
  · exact split_record color hord
      (fun x hx => (belowPiece_mem hx).1)
      (fun x hx => (abovePiece_mem hx).1)
      (List.ne_nil_of_mem (show c₁ ∈ belowPiece C r by
        simp [belowPiece, List.mem_filter, hc₁C, hc₁r]))
      (List.ne_nil_of_mem (show c₂ ∈ abovePiece C r by
        simp [abovePiece, List.mem_filter, hc₂C, hc₂r]))
      (fun x hx => (belowPiece_mem hx).2)
      (fun x hx => (abovePiece_mem hx).2)
      hb hblue hred τ hinj hpresent


/-- Case A at the left end: a one-sided-above scan of the first blue
run (`r` below everything, the binary search's `k = 0` side)
produces a fresh singleton step before it. Runs after the scanned
run exceed it by run-order, chained through a scanned element. -/
theorem scan_fresh_step {B : List (List X)} {C : List X} {r : X}
    (hord : RunsOrdered (C :: B))
    (hCne : C ≠ []) (hverdict : ∀ x ∈ C, r < x) :
    Step color (C :: B) r (applyOp [] B C r .freshSingleton) := by
  classical
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ ∈ C := by
    cases C with
    | nil => simp at hCne
    | cons c cs => exact ⟨c, by simp⟩
  show Step color ([] ++ C :: B) r (applyOp [] B C r .freshSingleton)
  apply Step.freshSingleton
  · intro R hR
    simp at hR
  · intro T hT y hy
    simp only [List.mem_cons] at hT
    rcases hT with rfl | h
    · exact hverdict y hy
    · exact lt_trans (hverdict c₀ hc₀)
        ((List.pairwise_cons.mp hord).1 T h c₀ hc₀ y hy)

/-- Case A at the right end: a one-sided-below scan of the last
blue run, with everything before it below `r` (the binary search's
`k = q` side, supplied as `hA`), produces an appended singleton
step. This is the configuration of `creator_record`. -/
theorem scan_append_step {A : List (List X)} {C : List X} {r : X}
    (hA : ∀ R ∈ A, ∀ x ∈ R, x < r)
    (hverdict : ∀ x ∈ C, x < r) :
    Step color (A ++ C :: []) r (applyOp A [] C r .appendSingleton) := by
  apply Step.appendSingleton
  intro T hT y hy
  simp only [List.append_nil, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hT
  rcases hT with h | rfl
  · exact hA T h y hy
  · exact hverdict y hy


/-- Case C, attach below: the blue run `C` just below the activated
red run `S` scans one-sided below (`r` above all of `C`), and `r`
is below an element of `S` (the min-probe). Then `r` attaches at
the bottom of `S`: an `insertInto` step at the decomposition with
`C` folded into the left part. -/
theorem scan_attach_below {A B : List (List X)} {C S : List X} {r s₀ : X}
    (hord : RunsOrdered (A ++ C :: S :: B))
    (hsred : ∀ x ∈ S, color x = Color.red)
    (hCne : C ≠ []) (hverdict : ∀ x ∈ C, x < r)
    (hs₀ : s₀ ∈ S) (hrs₀ : r < s₀) :
    Step color (A ++ C :: S :: B) r
      (applyOp (A ++ [C]) B S r .insertInto) := by
  classical
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ ∈ C := by
    cases C with
    | nil => simp at hCne
    | cons c cs => exact ⟨c, by simp⟩
  have e : (A ++ [C]) ++ S :: B = A ++ C :: S :: B := by
    simp [List.append_assoc]
  rw [← e]
  apply Step.insertInto
  · exact hsred
  · intro R hR x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with h | rfl
    · have hcross := (List.pairwise_append.mp hord).2.2
      exact lt_trans (hcross R h C (by simp) x hx c₀ hc₀) (hverdict c₀ hc₀)
    · exact hverdict x hx
  · intro T hT y hy
    exact lt_trans hrs₀ (runsOrdered_mem_lt hord hT hs₀ hy)

/-- Case C, attach above: the blue run `C` just above the activated
red run `S` scans one-sided above (`r` below all of `C`), and `r`
is above an element of `S` (the max-probe). Then `r` attaches at
the top of `S`. -/
theorem scan_attach_above {A B : List (List X)} {C S : List X} {r s₀ : X}
    (hord : RunsOrdered (A ++ S :: C :: B))
    (hsred : ∀ x ∈ S, color x = Color.red)
    (hCne : C ≠ []) (hverdict : ∀ x ∈ C, r < x)
    (hs₀ : s₀ ∈ S) (hs₀r : s₀ < r) :
    Step color (A ++ S :: C :: B) r
      (applyOp A (C :: B) S r .insertInto) := by
  classical
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ ∈ C := by
    cases C with
    | nil => simp at hCne
    | cons c cs => exact ⟨c, by simp⟩
  apply Step.insertInto
  · exact hsred
  · intro R hR x hx
    exact lt_trans (runsOrdered_mem_lt_left hord hR hx hs₀) hs₀r
  · intro T hT y hy
    simp only [List.mem_cons] at hT
    rcases hT with rfl | h
    · exact hverdict y hy
    · have hCcross : ∀ T ∈ B, ∀ y ∈ T, c₀ < y := by
        intro T hT y hy
        have e : A ++ S :: C :: B = (A ++ [S, C]) ++ B := by
          simp [List.append_assoc]
        have h2 := (List.pairwise_append.mp (e ▸ hord)).2.2
        exact h2 C (by simp) T hT c₀ hc₀ y hy
      exact lt_trans (hverdict c₀ hc₀) (hCcross T h y hy)

/-- Case B: the candidate `S = {r₀}` has both blue neighbors
scanned one-sided (below neighbor `L` entirely below `r`, above
neighbor `U` entirely above `r`). Then the single red--red
comparison merges `r` with `r₀`: a `mergePair` step at the
decomposition with `L` folded into the left part. -/
theorem scan_activation_step {A B : List (List X)} {L S U : List X}
    {r r₀ : X}
    (hord : RunsOrdered (A ++ L :: S :: U :: B))
    (hS : S = [r₀]) (hr₀red : color r₀ = Color.red)
    (hLne : L ≠ []) (hUne : U ≠ [])
    (hLv : ∀ x ∈ L, x < r) (hUv : ∀ x ∈ U, r < x) :
    Step color (A ++ L :: S :: U :: B) r
      (applyOp (A ++ [L]) (U :: B) S r (.mergePair r₀)) := by
  classical
  obtain ⟨l₀, hl₀⟩ : ∃ l₀, l₀ ∈ L := by
    cases L with
    | nil => simp at hLne
    | cons c cs => exact ⟨c, by simp⟩
  obtain ⟨u₀, hu₀⟩ : ∃ u₀, u₀ ∈ U := by
    cases U with
    | nil => simp at hUne
    | cons c cs => exact ⟨c, by simp⟩
  have e : (A ++ [L]) ++ S :: (U :: B) = A ++ L :: S :: U :: B := by
    simp [List.append_assoc]
  rw [← e]
  have hLS : ∀ x ∈ L, ∀ y ∈ S, x < y := by
    have e2 : A ++ L :: S :: U :: B = (A ++ [L]) ++ S :: U :: B := by
      simp [List.append_assoc]
    exact (List.pairwise_append.mp (e2 ▸ hord)).2.2 L (by simp) S (by simp)
  have hl₀r₀ : l₀ < r₀ := hLS l₀ hl₀ r₀ (by rw [hS]; simp)
  have hr₀u₀ : r₀ < u₀ := by
    have e2 : A ++ L :: S :: U :: B = (A ++ [L, S]) ++ U :: B := by
      simp [List.append_assoc]
    have h2 := (List.pairwise_append.mp (e2 ▸ hord)).2.2
    exact h2 S (by simp) U (by simp) r₀ (by rw [hS]; simp) u₀ hu₀
  apply Step.mergePair
  · exact hS
  · intro x hx
    rw [hS] at hx
    simp at hx
    rw [hx]
    exact hr₀red
  · intro R hR x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hR
    rcases hR with h | rfl
    · have hcross := (List.pairwise_append.mp hord).2.2
      have hxl : x < l₀ := hcross R h L (by simp) x hx l₀ hl₀
      exact ⟨lt_trans hxl (hLv l₀ hl₀), lt_trans hxl hl₀r₀⟩
    · exact ⟨hLv x hx, hLS x hx r₀ (by rw [hS]; simp)⟩
  · intro T hT y hy
    simp only [List.mem_cons] at hT
    rcases hT with rfl | h
    · refine ⟨hUv y hy, ?_⟩
      have hSU : ∀ x ∈ S, ∀ y ∈ T, x < y := by
        have e2 : A ++ L :: S :: T :: B = (A ++ [L, S]) ++ T :: B := by
          simp [List.append_assoc]
        have h2 : ∀ R ∈ A ++ [L, S], ∀ T' ∈ T :: B, ∀ x ∈ R, ∀ y ∈ T', x < y :=
          (List.pairwise_append.mp (e2 ▸ hord)).2.2
        intro x hx y hy
        exact h2 S (by simp) T (by simp) x hx y hy
      exact hSU r₀ (by rw [hS]; simp) y hy
    · have hUT : ∀ x ∈ U, ∀ y ∈ T, x < y := by
        have e2 : A ++ L :: S :: U :: B = (A ++ [L, S, U]) ++ B := by
          simp [List.append_assoc]
        have h2 : ∀ R ∈ A ++ [L, S, U], ∀ T' ∈ B, ∀ x ∈ R, ∀ y ∈ T', x < y :=
          (List.pairwise_append.mp (e2 ▸ hord)).2.2
        intro x hx y hy
        exact h2 U (by simp) T h x hx y hy
      have hyu : u₀ < y := hUT u₀ hu₀ y hy
      exact ⟨lt_trans (hUv u₀ hu₀) hyu, lt_trans hr₀u₀ hyu⟩

end Bichromatic.Randomized
