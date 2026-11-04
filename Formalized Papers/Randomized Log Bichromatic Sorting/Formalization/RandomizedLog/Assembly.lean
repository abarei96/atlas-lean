import RandomizedLog.Execution

/-!
# Expected mixed-cost assembly (randomized paper, §3, `cor:mixedcost`
in counting form)

A scan event list assigns to each arrival `r` the blue runs it
scanned. Its mixed cost is the sum of the scanned runs' lengths —
one incidence per element touched. Summing incidences per blue
element instead of per event, each blue element `b` is charged at
most its number of records (the arrivals touching `b` are distinct
records for `b`, by the charging lemmas). Averaging over the
uniform arrival order via `lem:records` gives the expected bound:
at most `N * (2 + 2 log N)` incidences in expectation.

The event list itself — which runs each arrival scans — is
produced by the execution; that extraction, and the final-runs
lemma, are the remaining operational steps. Everything about the
counting and the averaging is proved here.
-/

namespace Bichromatic.Randomized

open Bichromatic

variable {X : Type*} [LinearOrder X] [Fintype X] (color : X → Color)

/-- Mixed cost of a scan event list: one incidence per element of
each scanned run. -/
def scanCost (events : List (X × List X)) : ℕ :=
  (events.map (fun e => e.2.length)).sum

/-- Incidence swap: the total scan cost counts, for each blue
element `b`, the events whose scanned run contains `b`. -/
theorem scanCost_eq (events : List (X × List X))
    (hndC : ∀ e ∈ events, e.2.Nodup) :
    scanCost events
      = ∑ b : X, (events.filter (fun e => b ∈ e.2)).length := by
  classical
  induction events with
  | nil => simp [scanCost]
  | cons e ev ih =>
      obtain ⟨r, C⟩ := e
      have hC : C.Nodup := hndC (r, C) (by exact List.mem_cons_self)
      have hrest : ∀ e' ∈ ev, e'.2.Nodup := fun e' h => hndC e' (List.mem_cons_of_mem (r, C) h)
      have h := ih hrest
      have hClen : C.length = ∑ b : X, (if b ∈ C then 1 else 0) := by
        rw [← List.toFinset_card_of_nodup hC, Finset.sum_boole]
        congr 1
        ext b
        simp [List.mem_toFinset]
      have hlen : ∀ b : X,
          (((r, C) :: ev).filter (fun e => b ∈ e.2)).length
            = (if b ∈ C then 1 else 0)
              + (ev.filter (fun e => b ∈ e.2)).length := by
        intro b
        by_cases hb : b ∈ C
        · rw [List.filter_cons]
          split_ifs with hcond
          · rw [List.length_cons]
            omega
          · simp [hb] at hcond
        · rw [List.filter_cons]
          split_ifs with hcond
          · simp [hb] at hcond
          · omega
      have hgoal : scanCost ((r, C) :: ev) = C.length + scanCost ev := rfl
      rw [hgoal, hClen, h, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro b _
      rw [hlen b]

/-- An arrival touching `b` in a charged event is a record for `b`,
in the Fin-rank form of the records bound. -/
theorem mem_records_of_isRecord {τF : X → Fin (Fintype.card X)} {b r : X}
    (h : IsRecord color (fun x => (τF x).val) b r) :
    r ∈ predRecords color τF b ∨ r ∈ succRecords color τF b := by
  cases h with
  | inl hp =>
      exact Or.inl (Finset.mem_filter.mpr
        ⟨by rw [mem_redsBelow]; exact ⟨hp.1, hp.2.1⟩, hp⟩)
  | inr hs =>
      exact Or.inr (Finset.mem_filter.mpr
        ⟨by rw [mem_redsAbove]; exact ⟨hs.1, hs.2.1⟩, hs⟩)

/-- Per-element counting: the events touching `b` are at most the
records of `b` (their arrivals are distinct records). -/
theorem filter_length_le_records {τF : X → Fin (Fintype.card X)}
    (events : List (X × List X)) (b : X)
    (hfst : ((events.filter (fun e => b ∈ e.2)).map Prod.fst).Nodup)
    (hrec : ∀ e ∈ events, ∀ b' ∈ e.2,
      IsRecord color (fun x => (τF x).val) b' e.1) :
    (events.filter (fun e => b ∈ e.2)).length
      ≤ (predRecords color τF b).card + (succRecords color τF b).card := by
  classical
  have hndarr : ((events.filter (fun e => b ∈ e.2)).map Prod.fst).Nodup :=
    hfst
  have hlen : (events.filter (fun e => b ∈ e.2)).length
      = ((events.filter (fun e => b ∈ e.2)).map Prod.fst).length :=
    (List.length_map Prod.fst).symm
  rw [hlen]
  have hmem : ∀ a ∈ (events.filter (fun e => b ∈ e.2)).map Prod.fst,
      a ∈ predRecords color τF b ∪ succRecords color τF b := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    rw [List.mem_filter] at he
    have hrecb := hrec e he.1 b (of_decide_eq_true he.2)
    cases mem_records_of_isRecord color hrecb with
    | inl h => exact Finset.mem_union_left _ h
    | inr h => exact Finset.mem_union_right _ h
  calc ((events.filter (fun e => b ∈ e.2)).map Prod.fst).length
      = (((events.filter (fun e => b ∈ e.2)).map Prod.fst).toFinset).card :=
        (List.toFinset_card_of_nodup hndarr).symm
    _ ≤ (predRecords color τF b ∪ succRecords color τF b).card := by
        apply Finset.card_le_card
        intro a ha
        rw [List.mem_toFinset] at ha
        exact hmem a ha
    _ ≤ (predRecords color τF b).card + (succRecords color τF b).card :=
        (Finset.card_union_le _ _)

/-- Pointwise total: a charged event list costs at most the total
record count. -/
theorem scanCost_le {τF : X → Fin (Fintype.card X)}
    (events : List (X × List X))
    (hfst : ∀ b : X, ((events.filter (fun e => b ∈ e.2)).map Prod.fst).Nodup)
    (hndC : ∀ e ∈ events, e.2.Nodup)
    (hrec : ∀ e ∈ events, ∀ b ∈ e.2,
      IsRecord color (fun x => (τF x).val) b e.1) :
    scanCost events
      ≤ ∑ b : X, ((predRecords color τF b).card
          + (succRecords color τF b).card) := by
  rw [scanCost_eq events hndC]
  apply Finset.sum_le_sum
  intro b _
  exact filter_length_le_records color events b (hfst b) hrec

/-- The expected total scan cost over the uniform arrival order:
at most `N * (2 + 2 log N)` incidences in expectation, for any
assignment of charged scan events to arrival orders. -/
theorem expected_scanCost_le
    (eventsOf : (X → Fin (Fintype.card X)) → List (X × List X))
    (hfst : ∀ τF ∈ InjRanks X, ∀ b : X,
      (((eventsOf τF).filter (fun e => b ∈ e.2)).map Prod.fst).Nodup)
    (hndC : ∀ τF ∈ InjRanks X, ∀ e ∈ eventsOf τF, e.2.Nodup)
    (hrec : ∀ τF ∈ InjRanks X, ∀ e ∈ eventsOf τF, ∀ b ∈ e.2,
      IsRecord color (fun x => (τF x).val) b e.1) :
    ((∑ τF ∈ InjRanks X, (scanCost (eventsOf τF) : ℝ))
      / (InjRanks X).card)
      ≤ (Fintype.card X : ℝ) * (2 + 2 * Real.log (Fintype.card X)) := by
  classical
  have hcardpos : 0 < (InjRanks X).card := by
    rw [Finset.card_pos]
    exact ⟨(Fintype.equivFin X : X → Fin (Fintype.card X)), by
      rw [InjRanks]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Fintype.equivFin X).injective⟩⟩
  have hpoint : ∀ τF ∈ InjRanks X, (scanCost (eventsOf τF) : ℝ)
      ≤ (∑ b : X, (((predRecords color τF b).card : ℝ) + ((succRecords color τF b).card : ℝ))) := by
    intro τF hτF
    have h := scanCost_le color (eventsOf τF) (hfst τF hτF)
      (hndC τF hτF) (hrec τF hτF)
    have hcast : (scanCost (eventsOf τF) : ℝ)
        ≤ ((∑ b : X, ((predRecords color τF b).card + (succRecords color τF b).card) : ℕ) : ℝ) :=
      Nat.cast_le.mpr h
    refine le_trans hcast ?_
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro b _
    push_cast
    exact le_refl _
  have hsum : (∑ τF ∈ InjRanks X, (scanCost (eventsOf τF) : ℝ))
      ≤ (∑ b : X, (∑ τF ∈ InjRanks X, (((predRecords color τF b).card : ℝ) + ((succRecords color τF b).card : ℝ)))) := by
    refine le_trans (Finset.sum_le_sum hpoint) ?_
    rw [Finset.sum_comm]
  have hper : ∀ b : X,
      ((∑ τF ∈ InjRanks X, (((predRecords color τF b).card : ℝ) + ((succRecords color τF b).card : ℝ))) / (InjRanks X).card)
        ≤ 2 + 2 * Real.log (Fintype.card X) := by
    intro b
    have hneX : Nonempty X := ⟨b⟩
    have hsplit : (∑ τF ∈ InjRanks X, (((predRecords color τF b).card : ℝ) + ((succRecords color τF b).card : ℝ)))
        = (∑ τF ∈ InjRanks X, ((predRecords color τF b).card : ℝ))
          + (∑ τF ∈ InjRanks X, ((succRecords color τF b).card : ℝ)) :=
      Finset.sum_add_distrib
    rw [hsplit, add_div]
    have hp := expected_pred_le color b
    have hs := expected_succ_le color b
    have hlog1 : Real.log (redsBelow color b).card
        ≤ Real.log (Fintype.card X) := by
      have hle : ((redsBelow color b).card : ℝ) ≤ (Fintype.card X : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      rcases eq_or_ne (redsBelow color b).card 0 with h0 | h0
      · rw [h0]
        simp only [Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg (by
          have h1 : 1 ≤ Fintype.card X := Fintype.card_pos_iff.mpr hneX
          exact_mod_cast h1)
      · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h0) hle
    have hlog2 : Real.log (redsAbove color b).card
        ≤ Real.log (Fintype.card X) := by
      have hle : ((redsAbove color b).card : ℝ) ≤ (Fintype.card X : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      rcases eq_or_ne (redsAbove color b).card 0 with h0 | h0
      · rw [h0]
        simp only [Nat.cast_zero, Real.log_zero]
        exact Real.log_nonneg (by
          have h1 : 1 ≤ Fintype.card X := Fintype.card_pos_iff.mpr hneX
          exact_mod_cast h1)
      · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h0) hle
    have h := add_le_add hp hs
    linarith [h, hlog1, hlog2]
  calc ((∑ τF ∈ InjRanks X, (scanCost (eventsOf τF) : ℝ))
        / (InjRanks X).card)
      ≤ ((∑ b : X, (∑ τF ∈ InjRanks X, (((predRecords color τF b).card : ℝ) + ((succRecords color τF b).card : ℝ))))
          / (InjRanks X).card) := by
        gcongr
    _ = ∑ b : X, ((∑ τF ∈ InjRanks X, (((predRecords color τF b).card : ℝ) + ((succRecords color τF b).card : ℝ)))
          / (InjRanks X).card) := by rw [Finset.sum_div]
    _ ≤ ∑ _b : X, (2 + 2 * Real.log (Fintype.card X)) :=
        Finset.sum_le_sum (fun b _ => hper b)
    _ = (Fintype.card X : ℝ) * (2 + 2 * Real.log (Fintype.card X)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Total scan cost splits into the ordinarily charged events
and the founder-charged activation events: charging changes
only the first component of each event, never its length. -/
theorem scanCost_events_eq {σ : List (List X)} {L : List X}
    {σf : List (List X)} (e : ExecFrom color σ L σf) :
    scanCost e.events
      = scanCost e.ordinaryEvents + scanCost e.activationEvents := by
  have happend : ∀ (ev₁ ev₂ : List (X × List X)),
      scanCost (ev₁ ++ ev₂) = scanCost ev₁ + scanCost ev₂ := by
    intro ev₁ ev₂
    simp [scanCost, List.map_append, List.sum_append]
  have hlen : ∀ (q : X) (l : List (List X)),
      scanCost (l.map fun C => (q, C)) = (l.map (fun C => C.length)).sum := by
    intro q l
    rw [scanCost, List.map_map]
    congr 1
  induction e with
  | nil σ => rfl
  | @cons σ σ' σf r rest step scans hsc tail ih =>
      rw [ExecFrom.events, happend, ih]
      cases hb : stepIsActivation color σ r scans with
      | true =>
          have hact : StepActivation color σ r scans :=
            activation_of_stepIsActivation (color := color) hb
          obtain ⟨q, hq, hactevents⟩ :=
            activationEvents_cons_of_activation (color := color) step scans
              hsc tail hact
          have hord : (ExecFrom.cons r step scans hsc tail).ordinaryEvents
              = tail.ordinaryEvents := by
            simp [ExecFrom.ordinaryEvents, hb]
          rw [hord, hactevents, happend, hlen, hlen]
          omega
      | false =>
          have hnot : ¬ StepActivation color σ r scans := by
            intro hact
            rw [stepIsActivation_of_activation (color := color) hact] at hb
            simp at hb
          have hactevents :=
            activationEvents_cons_of_not_activation (color := color) step
              scans hsc tail hnot
          have hord : (ExecFrom.cons r step scans hsc tail).ordinaryEvents
              = (scans.map fun C => (r, C)) ++ tail.ordinaryEvents := by
            simp [ExecFrom.ordinaryEvents, hb]
          rw [hord, hactevents, happend, hlen]
          omega
/-- Blue elements in increasing order: the initial blue sequence
of the paper. -/
def blueList (color : X → Color) : List X :=
  (sortedList X).filter (fun x => color x = Color.blue)

/-- Red elements in increasing order. -/
def redList (color : X → Color) : List X :=
  (sortedList X).filter (fun x => color x = Color.red)

theorem mem_redList {x : X} : x ∈ redList color ↔ color x = Color.red := by
  simp [redList, sortedList, Finset.mem_sort]

theorem redList_nodup : (redList color).Nodup := by
  unfold redList sortedList
  exact List.Nodup.filter _ (Finset.sort_nodup _ _)

/-- The arrival order induced by an injective ranking: red
elements in increasing rank order. This is the uniform random
permutation of the paper, in counting form. -/
def arrivalsOf (color : X → Color) (τF : X → Fin (Fintype.card X)) :
    List X :=
  (redList color).mergeSort (fun a b => (τF a).val ≤ (τF b).val)

/-- The initial state: all blue elements as a single blue run,
in increasing order (or the empty state if there are none). -/
def initialRuns (color : X → Color) : List (List X) :=
  if blueList color = [] then [] else [blueList color]

theorem blueList_pairwise : (blueList color).Pairwise (· ≤ ·) := by
  have h : (sortedList X).Pairwise (· ≤ ·) :=
    Finset.pairwise_sort Finset.univ (· ≤ ·)
  exact List.Pairwise.sublist List.filter_sublist h

theorem blueList_nodup : (blueList color).Nodup := by
  unfold blueList sortedList
  exact List.Nodup.filter _ (Finset.sort_nodup _ _)

theorem mem_blueList {x : X} : x ∈ blueList color ↔ color x = Color.blue := by
  simp [blueList, sortedList, Finset.mem_sort]

theorem initialRuns_flatten :
    (initialRuns color).flatten = blueList color := by
  by_cases h : blueList color = []
  · simp [initialRuns, h]
  · simp [initialRuns, h]

theorem initial_invariant : Invariant color (initialRuns color) := by
  by_cases h : blueList color = []
  · refine ⟨?_, ?_, ?_⟩ <;> simp [initialRuns, h, RunsOrdered]
  · have hform : initialRuns color = [blueList color] := by
      simp [initialRuns, h]
    refine ⟨?_, ?_, ?_⟩
    · intro R hR
      rw [hform] at hR
      simp at hR
      rw [hR]
      exact h
    · rw [hform]
      simp [RunsOrdered]
    · intro R hR hred hlen
      rw [hform] at hR
      simp at hR
      obtain ⟨x, hx⟩ : ∃ x, x ∈ blueList color := by
        cases hb : blueList color with
        | nil => simp [hb] at h
        | cons y ys => exact ⟨y, by simp⟩
      have hxR : x ∈ R := hR.symm ▸ hx
      have hxb : color x = Color.blue := (mem_blueList (color := color)).mp hx
      have hxr : color x = Color.red := hred x hxR
      rw [hxr] at hxb
      exact False.elim (Color.noConfusion hxb)

theorem initial_mono : MonoRuns color (initialRuns color) := by
  intro R hR
  by_cases h : blueList color = []
  · simp [initialRuns, h] at hR
  · have hRb : R = blueList color := by
      simp [initialRuns, h] at hR
      exact hR
    exact Or.inr (fun x hx => (mem_blueList (color := color)).mp (hRb ▸ hx))

theorem initial_alt : AltRuns color (initialRuns color) := by
  by_cases h : blueList color = []
  · simp only [initialRuns, h]
    exact AltRuns.nil
  · simp only [initialRuns, if_neg h]
    exact AltRuns.single _

theorem initial_sorted : RunsInternallySorted color (initialRuns color) := by
  intro R hR
  by_cases h : blueList color = []
  · simp [initialRuns, h] at hR
  · have hRb : R = blueList color := by
      simp [initialRuns, h] at hR
      exact hR
    rw [hRb]
    exact blueList_pairwise (color := color)

theorem initial_blue (h : blueList color ≠ []) :
    ∃ C ∈ initialRuns color, ∀ x ∈ C, color x = Color.blue := by
  have hform : initialRuns color = [blueList color] := by
    simp [initialRuns, h]
  exact ⟨blueList color, by rw [hform]; simp,
    fun x hx => (mem_blueList (color := color)).mp hx⟩

theorem initial_nodup : (initialRuns color).flatten.Nodup := by
  rw [initialRuns_flatten]
  exact blueList_nodup (color := color)

theorem initial_flatten_blue :
    ∀ x ∈ (initialRuns color).flatten, color x = Color.blue := by
  intro x hx
  rw [initialRuns_flatten] at hx
  exact (mem_blueList (color := color)).mp hx

theorem arrivalsOf_perm (τF : X → Fin (Fintype.card X)) :
    (arrivalsOf color τF).Perm (redList color) :=
  List.mergeSort_perm _ _

theorem arrivalsOf_mem_red {τF : X → Fin (Fintype.card X)} {r : X}
    (h : r ∈ arrivalsOf color τF) : color r = Color.red := by
  have h1 : r ∈ redList color :=
    (arrivalsOf_perm color τF).mem_iff.mp h
  exact (mem_redList (color := color)).mp h1

theorem arrivalsOf_mem {τF : X → Fin (Fintype.card X)} {r : X}
    (hr : color r = Color.red) : r ∈ arrivalsOf color τF :=
  (arrivalsOf_perm color τF).mem_iff.mpr ((mem_redList (color := color)).mpr hr)

theorem arrivalsOf_nodup (τF : X → Fin (Fintype.card X)) :
    (arrivalsOf color τF).Nodup :=
  (arrivalsOf_perm color τF).nodup_iff.mpr (redList_nodup (color := color))

theorem arrivalsOf_fresh {τF : X → Fin (Fintype.card X)} {r : X}
    (hr : r ∈ arrivalsOf color τF) : r ∉ (initialRuns color).flatten := by
  intro hcon
  have hb : color r = Color.blue := initial_flatten_blue color r hcon
  have hr2 : color r = Color.red := arrivalsOf_mem_red color hr
  rw [hr2] at hb
  exact Color.noConfusion hb

/-- The order hypothesis of the records assembly, for the
rank-sorted arrival list: an earlier-ranked red element is an
earlier arrival (it cannot be an initial element, since the
initial state is all blue). -/
theorem arrivalsOf_order (τF : X → Fin (Fintype.card X)) :
    ∀ (L₁ : List X) (r : X) (L₂ : List X),
      arrivalsOf color τF = L₁ ++ r :: L₂ → ∀ r' : X,
      color r' = Color.red → (τF r').val < (τF r).val →
      r' ∈ L₁ ∨ r' ∈ (initialRuns color).flatten := by
  intro L₁ r L₂ hΛ r' hr' hlt
  have hr'mem : r' ∈ arrivalsOf color τF := arrivalsOf_mem color hr'
  rw [hΛ] at hr'mem
  rcases List.mem_append.mp hr'mem with h | h
  · exact Or.inl h
  · rcases List.mem_cons.mp h with rfl | hL2
    · exact absurd hlt (lt_irrefl _)
    · have hsorted : (arrivalsOf color τF).Pairwise
          (fun a b => (τF a).val ≤ (τF b).val) := List.pairwise_mergeSort' _ _
      have e : arrivalsOf color τF = (L₁ ++ [r]) ++ L₂ := by
        rw [hΛ]
        simp [List.append_assoc]
      rw [e] at hsorted
      have hle : (τF r).val ≤ (τF r').val :=
        (List.pairwise_append.mp hsorted).2.2 r (by simp) r' hL2
      exact absurd hle (not_le.mpr hlt)

/-- The produced execution from the paper's initial state, for a
given arrival ranking. -/
theorem exists_execution_initial (hblue : blueList color ≠ [])
    (τF : X → Fin (Fintype.card X)) :
    ∃ σf, ∃ e : ExecFrom color (initialRuns color)
        (arrivalsOf color τF) σf,
      ExecStepsClassified (color := color) e ∧ Invariant color σf ∧
      MonoRuns color σf ∧ AltRuns color σf ∧
      ExecActivationGrows (color := color) e ∧
      RunsInternallySorted color σf ∧
      σf.flatten.Perm ((arrivalsOf color τF) ++ blueList color) := by
  obtain ⟨σf, e, hc, hinv, hmono, halt, hg, hsrt, hperm⟩ :=
    exists_execution (color := color) (arrivalsOf color τF)
      (initialRuns color) (initial_invariant (color := color))
      (initial_mono (color := color)) (initial_alt (color := color))
      (initial_sorted (color := color)) (initial_blue (color := color) hblue)
      (fun r hr => arrivalsOf_mem_red color hr) (arrivalsOf_nodup color τF)
      (fun r hr => arrivalsOf_fresh color hr)
  refine ⟨σf, e, hc, hinv, hmono, halt, hg, hsrt, ?_⟩
  rwa [initialRuns_flatten] at hperm

/-- The final state of the produced execution, chosen. -/
noncomputable def chosenState (hblue : blueList color ≠ [])
    (τF : X → Fin (Fintype.card X)) : List (List X) :=
  Classical.choose (exists_execution_initial (color := color) hblue τF)

/-- The produced execution itself, chosen. -/
noncomputable def chosenExecution (hblue : blueList color ≠ [])
    (τF : X → Fin (Fintype.card X)) :
    ExecFrom color (initialRuns color) (arrivalsOf color τF)
      (chosenState color hblue τF) :=
  Classical.choose (Classical.choose_spec
    (exists_execution_initial (color := color) hblue τF))

/-- The full specification of the chosen execution. -/
theorem chosenExecution_spec (hblue : blueList color ≠ [])
    (τF : X → Fin (Fintype.card X)) :
    ExecStepsClassified (color := color)
        (chosenExecution (color := color) hblue τF) ∧
      Invariant color (chosenState color hblue τF) ∧
      MonoRuns color (chosenState color hblue τF) ∧
      AltRuns color (chosenState color hblue τF) ∧
      ExecActivationGrows (color := color)
        (chosenExecution (color := color) hblue τF) ∧
      RunsInternallySorted color (chosenState color hblue τF) ∧
      (chosenState color hblue τF).flatten.Perm
        ((arrivalsOf color τF) ++ blueList color) :=
  Classical.choose_spec (Classical.choose_spec
    (exists_execution_initial (color := color) hblue τF))

/-- Final runs of the produced execution: reading the final runs
in order gives the sorted list of all arrivals followed by the
initial blue sequence — a sorted permutation of the whole
instance. -/
theorem chosenExecution_final (hblue : blueList color ≠ [])
    (τF : X → Fin (Fintype.card X)) :
    (chosenState color hblue τF).flatten.Pairwise (· ≤ ·) ∧
      (chosenState color hblue τF).flatten.Perm
        ((arrivalsOf color τF) ++ blueList color) := by
  have hspec := chosenExecution_spec (color := color) hblue τF
  exact ⟨flatten_pairwise_le (color := color) hspec.2.1.2.1 hspec.2.2.2.2.2.1,
    hspec.2.2.2.2.2.2⟩

/-- The scan events of the produced execution for a ranking; if
there are no blue elements there is nothing to scan. -/
noncomputable def executionEvents (color : X → Color)
    (τF : X → Fin (Fintype.card X)) : List (X × List X) :=
  if h : blueList color = [] then []
  else (chosenExecution (color := color) h τF).events

/-- The expected scan cost of the produced execution, averaged
over the uniform arrival ranking, is at most twice the records
bound: ordinary events and activation events each cost at most
the total record count. This is the paper's `cor:mixedcost` with
the execution constructed. -/
theorem expected_executionEvents_le (color : X → Color) :
    ((∑ τF ∈ InjRanks X, (scanCost (executionEvents color τF) : ℝ))
      / (InjRanks X).card)
      ≤ 2 * ((Fintype.card X : ℝ) * (2 + 2 * Real.log (Fintype.card X))) := by
  by_cases hblue : blueList color = []
  · have hsum : (∑ τF ∈ InjRanks X,
        (scanCost (executionEvents color τF) : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro τF _
      rw [executionEvents, dif_pos hblue]
      simp [scanCost]
    rw [hsum, zero_div]
    cases Nat.eq_zero_or_pos (Fintype.card X) with
    | inl h0 =>
        rw [h0]
        simp
    | inr hpos =>
        have hlog : (0:ℝ) ≤ Real.log (Fintype.card X) :=
          Real.log_nonneg (by exact_mod_cast hpos)
        have hc : (0:ℝ) ≤ (Fintype.card X : ℝ) := Nat.cast_nonneg _
        positivity
  · have hspec : ∀ τF ∈ InjRanks X,
        ExecStepsClassified (color := color)
            (chosenExecution (color := color) hblue τF) ∧
          Invariant color (chosenState color hblue τF) ∧
          MonoRuns color (chosenState color hblue τF) ∧
          AltRuns color (chosenState color hblue τF) ∧
          ExecActivationGrows (color := color)
            (chosenExecution (color := color) hblue τF) ∧
          RunsInternallySorted color (chosenState color hblue τF) ∧
          (chosenState color hblue τF).flatten.Perm
            ((arrivalsOf color τF) ++ blueList color) :=
      fun τF _ => chosenExecution_spec (color := color) hblue τF
    have hord_bound := expected_scanCost_le (color := color)
      (fun τF => (chosenExecution (color := color) hblue τF).ordinaryEvents)
      (fun τF hτ b => ordinaryEvents_fst_nodup (color := color)
        (arrivalsOf color τF) (initialRuns color)
        (fun r hr => arrivalsOf_mem_red color hr)
        (arrivalsOf_nodup color τF)
        (fun r hr => arrivalsOf_fresh color hr)
        (chosenExecution (color := color) hblue τF) (hspec τF hτ).1 []
        (by simp) (initial_invariant (color := color))
        (initial_mono (color := color)) (initial_nodup (color := color))
        (by simp) b)
      (fun τF hτ ev hev =>
        (events_snd_nodup (color := color) (arrivalsOf color τF)
          (initialRuns color) (arrivalsOf_nodup color τF)
          (fun r hr => arrivalsOf_fresh color hr)
          (chosenExecution (color := color) hblue τF) [] (by simp)
          (initial_nodup (color := color)) (by simp)).2.1 ev hev)
      (fun τF hτ ev hev =>
        ordinary_events_records (color := color) τF
          (Finset.mem_filter.mp hτ).2 (arrivalsOf color τF)
          (initialRuns color)
          (fun r hr => arrivalsOf_mem_red color hr)
          (arrivalsOf_order color τF)
          (chosenExecution (color := color) hblue τF) (hspec τF hτ).1 []
          (by simp) (initial_invariant (color := color))
          (initial_mono (color := color)) (by simp) ev hev)
    have hact_bound := expected_scanCost_le (color := color)
      (fun τF => (chosenExecution (color := color) hblue τF).activationEvents)
      (fun τF hτ b => activationEvents_fst_nodup (color := color)
        (arrivalsOf color τF) (initialRuns color)
        (fun r hr => arrivalsOf_mem_red color hr)
        (arrivalsOf_nodup color τF)
        (fun r hr => arrivalsOf_fresh color hr)
        (chosenExecution (color := color) hblue τF) (hspec τF hτ).1
        (hspec τF hτ).2.2.2.2.1 [] (by simp) (initial_invariant (color := color))
        (initial_mono (color := color)) (initial_nodup (color := color))
        (by simp) b)
      (fun τF hτ ev hev =>
        (events_snd_nodup (color := color) (arrivalsOf color τF)
          (initialRuns color) (arrivalsOf_nodup color τF)
          (fun r hr => arrivalsOf_fresh color hr)
          (chosenExecution (color := color) hblue τF) [] (by simp)
          (initial_nodup (color := color)) (by simp)).2.2 ev hev)
      (fun τF hτ ev hev =>
        activation_events_records (color := color) τF
          (Finset.mem_filter.mp hτ).2 (arrivalsOf color τF)
          (initialRuns color)
          (fun r hr => arrivalsOf_mem_red color hr)
          (arrivalsOf_order color τF) (initial_flatten_blue (color := color))
          (chosenExecution (color := color) hblue τF) (hspec τF hτ).1 []
          (by simp) (initial_invariant (color := color))
          (initial_mono (color := color)) (by simp) ev hev)
    have htot : ∀ τF ∈ InjRanks X,
        (scanCost (executionEvents color τF) : ℝ)
          = (scanCost (chosenExecution (color := color) hblue
              τF).ordinaryEvents : ℝ)
            + (scanCost (chosenExecution (color := color) hblue
              τF).activationEvents : ℝ) := by
      intro τF _
      have h : scanCost (chosenExecution (color := color) hblue τF).events
          = scanCost (chosenExecution (color := color) hblue
              τF).ordinaryEvents
            + scanCost (chosenExecution (color := color) hblue
              τF).activationEvents :=
        scanCost_events_eq (color := color)
          (chosenExecution (color := color) hblue τF)
      rw [executionEvents, dif_neg hblue]
      rw [h]
      push_cast
      rfl
    calc ((∑ τF ∈ InjRanks X, (scanCost (executionEvents color τF) : ℝ))
          / (InjRanks X).card)
        = (((∑ τF ∈ InjRanks X,
              (scanCost (chosenExecution (color := color) hblue
                τF).ordinaryEvents : ℝ))
            + (∑ τF ∈ InjRanks X,
              (scanCost (chosenExecution (color := color) hblue
                τF).activationEvents : ℝ)))
          / (InjRanks X).card) := by
          rw [← Finset.sum_add_distrib]
          exact congrArg (· / _) (Finset.sum_congr rfl htot)
      _ = ((∑ τF ∈ InjRanks X,
              (scanCost (chosenExecution (color := color) hblue
                τF).ordinaryEvents : ℝ)) / (InjRanks X).card)
            + ((∑ τF ∈ InjRanks X,
              (scanCost (chosenExecution (color := color) hblue
                τF).activationEvents : ℝ)) / (InjRanks X).card) :=
          add_div _ _ _
      _ ≤ ((Fintype.card X : ℝ) * (2 + 2 * Real.log (Fintype.card X)))
            + ((Fintype.card X : ℝ)
              * (2 + 2 * Real.log (Fintype.card X))) :=
          add_le_add hord_bound hact_bound
      _ = 2 * ((Fintype.card X : ℝ)
            * (2 + 2 * Real.log (Fintype.card X))) := by ring

end Bichromatic.Randomized
