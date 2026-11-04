import RandomizedLog.Assembly
import RandomizedLog.MonoCost
import RandomizedLog.MergeSortCount

/-!
# Total cost of SpliceSort (randomized paper, full assembly)

The produced execution is parametrized by the arrival list itself,
so the sorting output and every cost component are read off the
same execution. The total cost of an execution is the paper's:

* mixed comparisons: scan incidences (with pre-split scans charged
  to the split scan of the same insertion, as in `lem:scancost`,
  hence twice the counted incidences) plus one binary search per
  red arrival over at most `m` blue-run representatives
  (`cor:mixedcost`, via `SpliceSort.searchCost_le`);
* blue monochromatic comparisons: counted mergesort of each final
  blue run (`lem:bluecost`, count by `msort_count_le`);
* red monochromatic comparisons: for each final red run `F`, the
  own charge `( |F| - 1 ) * (log₂ N + 3)` (one activation comparison,
  or at most two probes plus a binary search, per joiner;
  `lem:ownred`) plus twice the number of threshold records at the
  endpoints of `F` (each foreign tester makes at most two
  comparisons and is a threshold record at an endpoint by
  `foreign_record_final`; `lem:foreignred`).
-/

namespace Bichromatic.Randomized

open Bichromatic

variable {X : Type*} [LinearOrder X] [Fintype X] (color : X → Color)

/-- Executing from the paper's initial state along any arrival
list that is a permutation of the red elements. -/
theorem exists_execution_of_list (hblue : blueList color ≠ [])
    (L : List X) (hperm : L.Perm (redList color)) :
    ∃ σf, ∃ e : ExecFrom color (initialRuns color) L σf,
      ExecStepsClassified (color := color) e ∧ Invariant color σf ∧
      MonoRuns color σf ∧ AltRuns color σf ∧
      ExecActivationGrows (color := color) e ∧
      RunsInternallySorted color σf ∧
      σf.flatten.Perm (L ++ blueList color) := by
  have hred : ∀ r ∈ L, color r = Color.red := by
    intro r hr
    have h1 : r ∈ redList color := hperm.mem_iff.mp hr
    exact (mem_redList (color := color)).mp h1
  have hnd : L.Nodup :=
    hperm.nodup_iff.mpr (redList_nodup (color := color))
  have hfresh : ∀ r ∈ L, r ∉ (initialRuns color).flatten := by
    intro r hr
    have hr2 : color r = Color.red := hred r hr
    intro hcon
    have hb : color r = Color.blue := initial_flatten_blue color r hcon
    rw [hr2] at hb
    exact Color.noConfusion hb
  obtain ⟨σf, e, hc, hinv, hmono, halt, hg, hsrt, hpermf⟩ :=
    exists_execution (color := color) L (initialRuns color)
      (initial_invariant (color := color))
      (initial_mono (color := color)) (initial_alt (color := color))
      (initial_sorted (color := color))
      (initial_blue (color := color) hblue) hred hnd hfresh
  exact ⟨σf, e, hc, hinv, hmono, halt, hg, hsrt, by
    rwa [initialRuns_flatten] at hpermf⟩

/-- The final state of the produced execution along `L`. -/
noncomputable def finalState (hblue : blueList color ≠ []) (L : List X)
    (hperm : L.Perm (redList color)) : List (List X) :=
  Classical.choose (exists_execution_of_list (color := color) hblue L hperm)

/-- The produced execution along `L`. -/
noncomputable def executionOf (hblue : blueList color ≠ []) (L : List X)
    (hperm : L.Perm (redList color)) :
    ExecFrom color (initialRuns color) L (finalState color hblue L hperm) :=
  Classical.choose (Classical.choose_spec
    (exists_execution_of_list (color := color) hblue L hperm))

/-- The full specification of the produced execution. -/
theorem executionOf_spec (hblue : blueList color ≠ []) (L : List X)
    (hperm : L.Perm (redList color)) :
    ExecStepsClassified (color := color) (executionOf color hblue L hperm) ∧
      Invariant color (finalState color hblue L hperm) ∧
      MonoRuns color (finalState color hblue L hperm) ∧
      AltRuns color (finalState color hblue L hperm) ∧
      ExecActivationGrows (color := color) (executionOf color hblue L hperm) ∧
      RunsInternallySorted color (finalState color hblue L hperm) ∧
      (finalState color hblue L hperm).flatten.Perm
        (L ++ blueList color) :=
  Classical.choose_spec (Classical.choose_spec
    (exists_execution_of_list (color := color) hblue L hperm))

/-- The final state does not depend on the permutation proof. -/
theorem finalState_irrel (hblue : blueList color ≠ []) (L : List X)
    (h1 h2 : L.Perm (redList color)) :
    finalState color hblue L h1 = finalState color hblue L h2 :=
  rfl

/-- Final runs of the produced execution: reading them in order
gives a sorted list — the output of the algorithm. -/
theorem finalState_flatten_sorted (hblue : blueList color ≠ [])
    (L : List X) (hperm : L.Perm (redList color)) :
    (finalState color hblue L hperm).flatten.Pairwise (· ≤ ·) ∧
      (finalState color hblue L hperm).flatten.Perm
        (L ++ blueList color) := by
  have hspec := executionOf_spec (color := color) hblue L hperm
  exact ⟨flatten_pairwise_le (color := color) hspec.2.1.2.1
    hspec.2.2.2.2.2.1, hspec.2.2.2.2.2.2⟩

/-- The scan events of the produced execution along `L`. -/
noncomputable def execEvents (hblue : blueList color ≠ []) (L : List X)
    (hperm : L.Perm (redList color)) : List (X × List X) :=
  (executionOf color hblue L hperm).events

/-- The expected scan cost of the produced execution, averaged over
the uniform arrival ranking: ordinary and activation events each
cost at most the total record count. -/
theorem expected_execEvents_le (hblue : blueList color ≠ []) :
    ((∑ τF ∈ InjRanks X,
        (scanCost (execEvents color hblue (arrivalsOf color τF)
          (arrivalsOf_perm color τF)) : ℝ))
      / (InjRanks X).card)
      ≤ 2 * ((Fintype.card X : ℝ) * (2 + 2 * Real.log (Fintype.card X))) := by
  have hspec : ∀ τF ∈ InjRanks X,
      ExecStepsClassified (color := color)
          (executionOf color hblue (arrivalsOf color τF)
            (arrivalsOf_perm color τF)) ∧
        Invariant color (finalState color hblue (arrivalsOf color τF)
          (arrivalsOf_perm color τF)) ∧
        MonoRuns color (finalState color hblue (arrivalsOf color τF)
          (arrivalsOf_perm color τF)) ∧
        AltRuns color (finalState color hblue (arrivalsOf color τF)
          (arrivalsOf_perm color τF)) ∧
        ExecActivationGrows (color := color)
          (executionOf color hblue (arrivalsOf color τF)
            (arrivalsOf_perm color τF)) ∧
        RunsInternallySorted color (finalState color hblue
          (arrivalsOf color τF) (arrivalsOf_perm color τF)) ∧
        (finalState color hblue (arrivalsOf color τF)
          (arrivalsOf_perm color τF)).flatten.Perm
          ((arrivalsOf color τF) ++ blueList color) :=
    fun τF _ => executionOf_spec (color := color) hblue _ _
  have hord_bound := expected_scanCost_le (color := color)
    (fun τF => (executionOf color hblue (arrivalsOf color τF)
      (arrivalsOf_perm color τF)).ordinaryEvents)
    (fun τF hτ b => ordinaryEvents_fst_nodup (color := color)
      (arrivalsOf color τF) (initialRuns color)
      (fun r hr => arrivalsOf_mem_red color hr)
      (arrivalsOf_nodup color τF)
      (fun r hr => arrivalsOf_fresh color hr)
      (executionOf color hblue (arrivalsOf color τF)
        (arrivalsOf_perm color τF)) (hspec τF hτ).1 []
      (by simp) (initial_invariant (color := color))
      (initial_mono (color := color)) (initial_nodup (color := color))
      (by simp) b)
    (fun τF hτ ev hev =>
      (events_snd_nodup (color := color) (arrivalsOf color τF)
        (initialRuns color) (arrivalsOf_nodup color τF)
        (fun r hr => arrivalsOf_fresh color hr)
        (executionOf color hblue (arrivalsOf color τF)
          (arrivalsOf_perm color τF)) [] (by simp)
        (initial_nodup (color := color)) (by simp)).2.1 ev hev)
    (fun τF hτ ev hev =>
      ordinary_events_records (color := color) τF
        (Finset.mem_filter.mp hτ).2 (arrivalsOf color τF)
        (initialRuns color)
        (fun r hr => arrivalsOf_mem_red color hr)
        (arrivalsOf_order color τF)
        (executionOf color hblue (arrivalsOf color τF)
          (arrivalsOf_perm color τF)) (hspec τF hτ).1 []
        (by simp) (initial_invariant (color := color))
        (initial_mono (color := color)) (by simp) ev hev)
  have hact_bound := expected_scanCost_le (color := color)
    (fun τF => (executionOf color hblue (arrivalsOf color τF)
      (arrivalsOf_perm color τF)).activationEvents)
    (fun τF hτ b => activationEvents_fst_nodup (color := color)
      (arrivalsOf color τF) (initialRuns color)
      (fun r hr => arrivalsOf_mem_red color hr)
      (arrivalsOf_nodup color τF)
      (fun r hr => arrivalsOf_fresh color hr)
      (executionOf color hblue (arrivalsOf color τF)
        (arrivalsOf_perm color τF)) (hspec τF hτ).1
      (hspec τF hτ).2.2.2.2.1 [] (by simp)
      (initial_invariant (color := color))
      (initial_mono (color := color)) (initial_nodup (color := color))
      (by simp) b)
    (fun τF hτ ev hev =>
      (events_snd_nodup (color := color) (arrivalsOf color τF)
        (initialRuns color) (arrivalsOf_nodup color τF)
        (fun r hr => arrivalsOf_fresh color hr)
        (executionOf color hblue (arrivalsOf color τF)
          (arrivalsOf_perm color τF)) [] (by simp)
        (initial_nodup (color := color)) (by simp)).2.2 ev hev)
    (fun τF hτ ev hev =>
      activation_events_records (color := color) τF
        (Finset.mem_filter.mp hτ).2 (arrivalsOf color τF)
        (initialRuns color)
        (fun r hr => arrivalsOf_mem_red color hr)
        (arrivalsOf_order color τF) (initial_flatten_blue (color := color))
        (executionOf color hblue (arrivalsOf color τF)
          (arrivalsOf_perm color τF)) (hspec τF hτ).1 []
        (by simp) (initial_invariant (color := color))
        (initial_mono (color := color)) (by simp) ev hev)
  have htot : ∀ τF ∈ InjRanks X,
      (scanCost (execEvents color hblue (arrivalsOf color τF)
          (arrivalsOf_perm color τF)) : ℝ)
        = (scanCost (executionOf color hblue (arrivalsOf color τF)
            (arrivalsOf_perm color τF)).ordinaryEvents : ℝ)
          + (scanCost (executionOf color hblue (arrivalsOf color τF)
            (arrivalsOf_perm color τF)).activationEvents : ℝ) := by
    intro τF _
    have h : scanCost (executionOf color hblue (arrivalsOf color τF)
          (arrivalsOf_perm color τF)).events
        = scanCost (executionOf color hblue (arrivalsOf color τF)
            (arrivalsOf_perm color τF)).ordinaryEvents
          + scanCost (executionOf color hblue (arrivalsOf color τF)
            (arrivalsOf_perm color τF)).activationEvents :=
      scanCost_events_eq (color := color)
        (executionOf color hblue (arrivalsOf color τF)
          (arrivalsOf_perm color τF))
    rw [execEvents, h]
    push_cast
    rfl
  calc ((∑ τF ∈ InjRanks X,
          (scanCost (execEvents color hblue (arrivalsOf color τF)
            (arrivalsOf_perm color τF)) : ℝ))
        / (InjRanks X).card)
      = (((∑ τF ∈ InjRanks X,
            (scanCost (executionOf color hblue (arrivalsOf color τF)
              (arrivalsOf_perm color τF)).ordinaryEvents : ℝ))
          + (∑ τF ∈ InjRanks X,
            (scanCost (executionOf color hblue (arrivalsOf color τF)
              (arrivalsOf_perm color τF)).activationEvents : ℝ)))
        / (InjRanks X).card) := by
        rw [← Finset.sum_add_distrib]
        exact congrArg (· / _) (Finset.sum_congr rfl htot)
    _ = ((∑ τF ∈ InjRanks X,
            (scanCost (executionOf color hblue (arrivalsOf color τF)
              (arrivalsOf_perm color τF)).ordinaryEvents : ℝ))
          / (InjRanks X).card)
          + ((∑ τF ∈ InjRanks X,
            (scanCost (executionOf color hblue (arrivalsOf color τF)
              (arrivalsOf_perm color τF)).activationEvents : ℝ))
          / (InjRanks X).card) :=
        add_div _ _ _
    _ ≤ ((Fintype.card X : ℝ) * (2 + 2 * Real.log (Fintype.card X)))
          + ((Fintype.card X : ℝ)
            * (2 + 2 * Real.log (Fintype.card X))) :=
        add_le_add hord_bound hact_bound
    _ = 2 * ((Fintype.card X : ℝ)
          * (2 + 2 * Real.log (Fintype.card X))) := by ring

/-- One step of the run decomposition. -/
theorem runsOf_cons (a : X) (t : List X) :
    runsOf color (a :: t) = consRun color a (runsOf color t) :=
  rfl

/-- Runs of `runsOf` are monochromatic. -/
theorem runsOf_mono (l : List X) :
    ∀ R ∈ runsOf color l, ∃ c, ∀ x ∈ R, color x = c := by
  induction l with
  | nil => simp [runsOf]
  | cons a t ih =>
    rw [runsOf_cons]
    intro R hR
    cases hRs : runsOf color t with
    | nil =>
      rw [hRs] at hR
      have e : consRun color a [] = [[a]] := rfl
      rw [e] at hR
      simp only [List.mem_singleton] at hR
      exact ⟨color a, by rw [hR]; simp⟩
    | cons S rs =>
      cases S with
      | nil =>
        exfalso
        have hne := runsOf_nonempty (color := color) t
        rw [hRs] at hne
        exact hne [] (by simp) rfl
      | cons b bs =>
        have hSmono : ∃ c, ∀ x ∈ (b :: bs), color x = c :=
          ih (b :: bs) (by rw [hRs]; simp)
        obtain ⟨c, hc⟩ := hSmono
        have hcb : color b = c := hc b (by simp)
        rw [hRs] at hR
        by_cases hcc : color a = color b
        · rw [consRun, if_pos hcc] at hR
          cases hR with
          | head =>
            exact ⟨c, by
              intro x hx
              cases hx with
              | head => rw [← hcb]; exact hcc
              | tail _ hx => exact hc x hx⟩
          | tail _ hR =>
            exact ih R (by rw [hRs]; exact List.mem_cons_of_mem _ hR)
        · rw [consRun, if_neg hcc] at hR
          cases hR with
          | head => exact ⟨color a, by simp⟩
          | tail _ hR =>
            exact ih R (by rw [hRs]; exact hR)

/-- `runsOf` is alternating. -/
theorem runsOf_alt (l : List X) : AltRuns color (runsOf color l) := by
  induction l with
  | nil => exact AltRuns.nil
  | cons a t ih =>
    rw [runsOf_cons]
    cases hRs : runsOf color t with
    | nil =>
      exact AltRuns.single [a]
    | cons S rs =>
      cases S with
      | nil =>
        exfalso
        have hne := runsOf_nonempty (color := color) t
        rw [hRs] at hne
        exact hne [] (by simp) rfl
      | cons b bs =>
        have hSmono : ∃ c, ∀ x ∈ (b :: bs), color x = c :=
          runsOf_mono (color := color) t (b :: bs) (by rw [hRs]; simp)
        obtain ⟨c, hc⟩ := hSmono
        have hcb : color b = c := hc b (by simp)
        rw [hRs] at ih
        by_cases hcc : color a = color b
        · have e : consRun color a ((b :: bs) :: rs)
              = (a :: b :: bs) :: rs := by
            rw [consRun, if_pos hcc]
          rw [e]
          cases rs with
          | nil => exact AltRuns.single _
          | cons T rs =>
            cases ih with
            | cons hseam htail =>
              apply AltRuns.cons _ htail
              intro x hx y hy
              have hxS : color x = c := by
                cases hx with
                | head => rw [← hcb]; exact hcc
                | tail _ hx => exact hc x hx
              have hbT : ∀ z ∈ (b :: bs), color z ≠ color y :=
                fun z hz => hseam z hz y hy
              have hb2 := hbT b (by simp)
              rw [hcb] at hb2
              rw [hxS]
              exact hb2
        · have e : consRun color a ((b :: bs) :: rs)
              = [a] :: (b :: bs) :: rs := by
            rw [consRun, if_neg hcc]
          rw [e]
          apply AltRuns.cons _ ih
          intro x hx y hy
          simp only [List.mem_singleton] at hx
          rw [hx]
          have hyS : color y = c := hc y hy
          rw [hyS, ← hcb]
          exact hcc

/-- The seam weight between two lists. -/
def seam (w : X → X → ℝ) (l₁ l₂ : List X) : ℝ :=
  match l₁.getLast?, l₂.head? with
  | some a, some b => w a b
  | _, _ => 0

theorem adjCostWith_append (w : X → X → ℝ) :
    ∀ (l₁ l₂ : List X), adjCostWith w (l₁ ++ l₂)
      = adjCostWith w l₁ + seam w l₁ l₂ + adjCostWith w l₂ := by
  intro l₁
  induction l₁ with
  | nil => intro l₂; simp [adjCostWith, seam]
  | cons a t ih =>
    intro l₂
    cases t with
    | nil =>
      cases l₂ with
      | nil => simp [adjCostWith, seam]
      | cons b s => simp [adjCostWith, seam]
    | cons b t =>
      have e1 : (a :: b :: t) ++ l₂ = a :: ((b :: t) ++ l₂) := rfl
      have e2 : adjCostWith w ((a :: b :: t) ++ l₂)
          = w a b + adjCostWith w ((b :: t) ++ l₂) := by
        rw [e1]
        rfl
      have e3 : adjCostWith w (a :: b :: t)
          = w a b + adjCostWith w (b :: t) := rfl
      have e4 : seam w (a :: b :: t) l₂ = seam w (b :: t) l₂ := rfl
      rw [e2, ih, e3, e4]
      ring

/-- Adjacent cost over a monochromatic alternating run list: the
seams vanish and each run contributes its own adjacent cost. -/
theorem adjCostWith_flatten_of_alt (w : X → X → ℝ) (g : List X → ℝ)
    (σ : List (List X)) (hmono : MonoRuns color σ)
    (halt : AltRuns color σ) (hne : ∀ R ∈ σ, R ≠ [])
    (hcross : ∀ x y, color x ≠ color y → w x y = 0)
    (hval : ∀ R ∈ σ, adjCostWith w R = g R) :
    adjCostWith w σ.flatten = (σ.map g).sum := by
  induction σ with
  | nil => simp [adjCostWith]
  | cons R σ ih =>
    have hRne : R ≠ [] := hne R (by simp)
    have hmonoR : MonoRuns color (R :: σ) := hmono
    have hmono' : MonoRuns color σ :=
      fun S hS => hmono S (List.mem_cons_of_mem R hS)
    have hne' : ∀ S ∈ σ, S ≠ [] := fun S hS => hne S (List.mem_cons_of_mem R hS)
    have hval' : ∀ S ∈ σ, adjCostWith w S = g S :=
      fun S hS => hval S (List.mem_cons_of_mem R hS)
    cases σ with
    | nil =>
      simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact hval R (by simp)
    | cons T σ =>
      have halt' : AltRuns color (T :: σ) := by
        cases halt with
        | cons _ htail => exact htail
      have ih' := ih hmono' halt' hne' hval'
      have hTne : T ≠ [] := hne T (by simp)
      rw [List.flatten_cons, adjCostWith_append, ih',
        hval R (by simp)]
      simp only [List.map_cons, List.sum_cons]
      have hseam : seam w R ((T :: σ).flatten) = 0 := by
        obtain ⟨b, t', hT⟩ : ∃ b t', T = b :: t' :=
          List.exists_cons_of_ne_nil hTne
        have hhead : ((T :: σ).flatten).head? = some b := by
          rw [hT]
          simp [List.flatten_cons]
        have hlast : R.getLast? = some (R.getLast hRne) :=
          List.getLast?_eq_getLast hRne
        have haR : R.getLast hRne ∈ R := List.getLast_mem hRne
        have hbT : b ∈ T := by rw [hT]; simp
        have hab : color (R.getLast hRne) ≠ color b := by
          cases halt with
          | cons hseam _ => exact hseam _ haR _ hbT
        show seam w R ((T :: σ).flatten) = 0
        unfold seam
        rw [hlast, hhead]
        exact hcross _ _ hab
      rw [hseam]
      ring

/-- Adjacent cost over a monochromatic list with a weight that is
constant `K` on pairs of that colour. -/
theorem adjCostWith_of_mono (w : X → X → ℝ) (K : ℝ) (c : Color)
    (l : List X) (hmono : ∀ x ∈ l, color x = c)
    (hw : ∀ x y, color x = c → color y = c → w x y = K) :
    adjCostWith w l = K * (((l.length - 1 : ℕ)) : ℝ) := by
  induction l with
  | nil => simp [adjCostWith]
  | cons a t ih =>
    cases t with
    | nil => simp [adjCostWith]
    | cons b t =>
      have ha : color a = c := hmono a (by simp)
      have hb : color b = c := hmono b (by simp)
      have ht : ∀ x ∈ (b :: t), color x = c :=
        fun x hx => hmono x (List.mem_cons_of_mem a hx)
      have e : adjCostWith w (a :: b :: t)
          = w a b + adjCostWith w (b :: t) := rfl
      rw [e, ih ht, hw a b ha hb]
      have hlen : ((a :: b :: t).length - 1 : ℕ) = (b :: t).length := by
        simp
      rw [hlen]
      have hcast : (((b :: t).length - 1 : ℕ) : ℝ)
          = ((b :: t).length : ℝ) - 1 := by
        rw [Nat.cast_sub (by simp), Nat.cast_one]
      rw [hcast]
      push_cast
      ring

/-- The total `|R| - 1` over the red runs of the sorted order. -/
def redRunSum (color : X → Color) : ℕ :=
  ((runsOf color (sortedList X)).map
    (fun R => if (∀ x ∈ R, color x = Color.red) then R.length - 1
      else 0)).sum

/-- The total `|R| - 1` over the blue runs of the sorted order. -/
def blueRunSum (color : X → Color) : ℕ :=
  ((runsOf color (sortedList X)).map
    (fun R => if (∀ x ∈ R, color x = Color.blue) then R.length - 1
      else 0)).sum

private theorem sum_map_factor (σ : List (List X)) (K : ℝ)
    (f : List X → ℕ) :
    (σ.map (fun R => K * (f R : ℝ))).sum
      = K * ((σ.map f).sum : ℝ) := by
  induction σ with
  | nil => simp
  | cons R σ ih =>
    simp only [List.map_cons, List.sum_cons, ih, Nat.cast_sum,
      List.map_cons]
    rw [Nat.cast_add]
    ring

/-- The red weighted sum of `lem:Hbounds` is `α` times the total
red run excess of the sorted order. -/
theorem redAdjWeight_eq (α : ℝ) :
    redAdjWeight α color = α * (redRunSum color : ℝ) := by
  have hmono : MonoRuns color (runsOf color (sortedList X)) := by
    intro R hR
    obtain ⟨c, hc⟩ := runsOf_mono (color := color) (sortedList X) R hR
    cases c with
    | red => exact Or.inl hc
    | blue => exact Or.inr hc
  have h := adjCostWith_flatten_of_alt (color := color)
    (fun x y => if color x = Color.red ∧ color y = Color.red then α else 0)
    (fun R => α * ((if (∀ x ∈ R, color x = Color.red)
      then R.length - 1 else 0 : ℕ) : ℝ))
    (runsOf color (sortedList X)) hmono
    (runsOf_alt (color := color) (sortedList X))
    (fun R hR => runsOf_nonempty (color := color) _ R hR)
    (by
      intro x y hxy
      rw [if_neg]
      intro hcon
      exact hxy (by rw [hcon.1, hcon.2]))
    (by
      intro R hR
      obtain ⟨c, hc⟩ := runsOf_mono (color := color) (sortedList X) R hR
      have hRne : R ≠ [] :=
        runsOf_nonempty (color := color) _ R hR
      cases c with
      | red =>
        rw [adjCostWith_of_mono (color := color) _ α Color.red R hc (by
          intro x y hx hy
          rw [if_pos ⟨hx, hy⟩])]
        rw [if_pos hc]
      | blue =>
        have hnot : ¬ (∀ x ∈ R, color x = Color.red) := by
          intro hall
          obtain ⟨x, hx⟩ : ∃ x, x ∈ R := by
            cases R with
            | nil => exact absurd rfl hRne
            | cons y ys => exact ⟨y, by simp⟩
          have h1 : color x = Color.blue := hc x hx
          have h2 : color x = Color.red := hall x hx
          rw [h2] at h1
          exact Color.noConfusion h1
        rw [if_neg hnot]
        simp only [Nat.cast_zero, mul_zero]
        rw [adjCostWith_of_mono (color := color) _ 0 Color.blue R hc (by
          intro x y hx hy
          rw [if_neg]
          intro hcon
          rw [hx] at hcon
          exact Color.noConfusion hcon.1)]
        simp)
  unfold redAdjWeight
  rw [← runsOf_flatten (color := color) (sortedList X)]
  rw [h, sum_map_factor]
  rfl

/-- The blue weighted sum of `lem:Hbounds` is `β` times the total
blue run excess of the sorted order. -/
theorem blueAdjWeight_eq (β : ℝ) :
    blueAdjWeight β color = β * (blueRunSum color : ℝ) := by
  have hmono : MonoRuns color (runsOf color (sortedList X)) := by
    intro R hR
    obtain ⟨c, hc⟩ := runsOf_mono (color := color) (sortedList X) R hR
    cases c with
    | red => exact Or.inl hc
    | blue => exact Or.inr hc
  have h := adjCostWith_flatten_of_alt (color := color)
    (fun x y => if color x = Color.blue ∧ color y = Color.blue then β else 0)
    (fun R => β * ((if (∀ x ∈ R, color x = Color.blue)
      then R.length - 1 else 0 : ℕ) : ℝ))
    (runsOf color (sortedList X)) hmono
    (runsOf_alt (color := color) (sortedList X))
    (fun R hR => runsOf_nonempty (color := color) _ R hR)
    (by
      intro x y hxy
      rw [if_neg]
      intro hcon
      exact hxy (by rw [hcon.1, hcon.2]))
    (by
      intro R hR
      obtain ⟨c, hc⟩ := runsOf_mono (color := color) (sortedList X) R hR
      have hRne : R ≠ [] :=
        runsOf_nonempty (color := color) _ R hR
      cases c with
      | blue =>
        rw [adjCostWith_of_mono (color := color) _ β Color.blue R hc (by
          intro x y hx hy
          rw [if_pos ⟨hx, hy⟩])]
        rw [if_pos hc]
      | red =>
        have hnot : ¬ (∀ x ∈ R, color x = Color.blue) := by
          intro hall
          obtain ⟨x, hx⟩ : ∃ x, x ∈ R := by
            cases R with
            | nil => exact absurd rfl hRne
            | cons y ys => exact ⟨y, by simp⟩
          have h1 : color x = Color.red := hc x hx
          have h2 : color x = Color.blue := hall x hx
          rw [h2] at h1
          exact Color.noConfusion h1
        rw [if_neg hnot]
        simp only [Nat.cast_zero, mul_zero]
        rw [adjCostWith_of_mono (color := color) _ 0 Color.red R hc (by
          intro x y hx hy
          rw [if_neg]
          intro hcon
          rw [hx] at hcon
          exact Color.noConfusion hcon.1)]
        simp)
  unfold blueAdjWeight
  rw [← runsOf_flatten (color := color) (sortedList X)]
  rw [h, sum_map_factor]
  rfl

/-- Counted mergesort comparisons are at most `mergeCost`. -/
theorem msort_count_le_mergeCost (l : List X) :
    (msort l).2 ≤ mergeCost l.length := by
  rcases Nat.lt_or_ge l.length 2 with h | h
  · have hmc : mergeCost l.length = 0 := by
      simp [mergeCost, h]
    rw [hmc]
    cases l with
    | nil => simp [msort]
    | cons a t =>
      cases t with
      | nil => simp [msort]
      | cons b t => simp at h
  · unfold mergeCost
    rw [if_neg (by omega : ¬ l.length < 2)]
    rw [Nat.log2_eq_log_two]
    refine le_trans (msort_count_le l) ?_
    apply Nat.mul_le_mul_left
    have h1 : Nat.log 2 (l.length - 1) ≤ Nat.log 2 l.length :=
      Nat.log_mono_right (by omega)
    omega

private theorem sum_if_eq_filter (σ : List (List X))
    (p : List X → Prop) [DecidablePred p] (f : List X → ℕ) :
    (σ.map (fun R => if p R then f R else 0)).sum
      = ((σ.filter p).map f).sum := by
  induction σ with
  | nil => simp
  | cons R σ ih =>
    by_cases h : p R
    · simp [h, ih]
    · simp [h, ih]

/-- Blue cost charge: counted mergesort of each final blue run. -/
def blueCostCharge (color : X → Color) : ℕ :=
  ((runsOf color (sortedList X)).map
    (fun R => if (∀ x ∈ R, color x = Color.blue) then (msort R).2
      else 0)).sum

/-- `lem:bluecost`, counting form: the blue charge is at most
`2 (log₂ N + 1)` times the blue run excess. -/
theorem blueCostCharge_le :
    blueCostCharge color
      ≤ 2 * (Nat.log 2 (instSize X) + 1) * blueRunSum color := by
  have hlen : ∀ R ∈ runsOf color (sortedList X),
      R.length ≤ instSize X := by
    intro R hR
    have h1 : R.length ≤ (sortedList X).length := by
      rw [← runsOf_flatten (color := color) (sortedList X),
        List.length_flatten]
      exact List.single_le_sum (fun x _ => Nat.zero_le x) R.length
        (List.mem_map.mpr ⟨R, hR, rfl⟩)
    have h2 : (sortedList X).length = instSize X := by
      simp [sortedList, instSize, Finset.length_sort]
    omega
  have h1 : blueCostCharge color
      ≤ ((runsOf color (sortedList X)).map
        (fun R => if (∀ x ∈ R, color x = Color.blue)
          then mergeCost R.length else 0)).sum := by
    apply List.sum_le_sum
    intro R _
    by_cases h : ∀ x ∈ R, color x = Color.blue
    · rw [if_pos h, if_pos h]
      exact msort_count_le_mergeCost R
    · rw [if_neg h, if_neg h]
  refine le_trans h1 ?_
  unfold blueRunSum
  rw [sum_if_eq_filter, sum_if_eq_filter]
  have h := blueCost_le
    (((runsOf color (sortedList X)).filter
      (fun R => ∀ x ∈ R, color x = Color.blue)).map List.length)
    (instSize X) (fun t ht => by
      obtain ⟨R, hR, rfl⟩ := List.mem_map.mp ht
      exact hlen R (List.mem_filter.mp hR).1)
  rw [Nat.log2_eq_log_two, List.map_map, List.map_map] at h
  exact h

/-- Threshold records at one endpoint. -/
noncomputable def recordsAt (color : X → Color) (τF : X → Fin (Fintype.card X))
    (a : X) : ℕ :=
  (predRecords color τF a).card + (succRecords color τF a).card

/-- Foreign charge of one final red run: twice the threshold
records at its two endpoints, for runs of length at least two. -/
noncomputable def foreignAt (color : X → Color) (τF : X → Fin (Fintype.card X))
    (R : List X) : ℕ :=
  match R with
  | [] => 0
  | a :: t =>
    if (∀ x ∈ a :: t, color x = Color.red) ∧ 2 ≤ (a :: t).length
    then 2 * (recordsAt color τF a
      + recordsAt color τF ((a :: t).getLast (by simp)))
    else 0

/-- Total foreign red charge. -/
noncomputable def foreignCharge (color : X → Color)
    (τF : X → Fin (Fintype.card X)) : ℕ :=
  ((runsOf color (sortedList X)).map (foreignAt color τF)).sum

/-- Expected threshold records at one endpoint are `O(log N)`. -/
theorem expected_recordsAt_le (a : X) :
    ((∑ τF ∈ InjRanks X, (recordsAt color τF a : ℝ))
        / (InjRanks X).card)
      ≤ 2 + 2 * Real.log (Fintype.card X) := by
  have h := expected_threshold_le (color := color) a
  have hlog1 : Real.log ((redsBelow color a).card : ℝ)
      ≤ Real.log (Fintype.card X) := by
    have h1 : (redsBelow color a).card ≤ Fintype.card X := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    rcases Nat.eq_zero_or_pos (redsBelow color a).card with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      rcases Nat.eq_zero_or_pos (Fintype.card X) with h0' | hpos'
      · simp [h0']
      · exact Real.log_nonneg (by exact_mod_cast hpos')
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast h1)
  have hlog2 : Real.log ((redsAbove color a).card : ℝ)
      ≤ Real.log (Fintype.card X) := by
    have h1 : (redsAbove color a).card ≤ Fintype.card X := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    rcases Nat.eq_zero_or_pos (redsAbove color a).card with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      rcases Nat.eq_zero_or_pos (Fintype.card X) with h0' | hpos'
      · simp [h0']
      · exact Real.log_nonneg (by exact_mod_cast hpos')
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast h1)
  unfold recordsAt
  push_cast at h ⊢
  linarith

private theorem cast_map_sum (l : List (List X)) (f : List X → ℕ) :
    (((l.map f).sum : ℕ) : ℝ)
      = (l.map (fun R => (f R : ℝ))).sum := by
  induction l with
  | nil => simp
  | cons R l ih => simp [ih]

private theorem avg_list_map (l : List (List X))
    (g : (X → Fin (Fintype.card X)) → List X → ℝ) :
    ((∑ τF ∈ InjRanks X, (l.map (g τF)).sum) / (InjRanks X).card)
      = (l.map (fun R => (∑ τF ∈ InjRanks X, g τF R)
          / (InjRanks X).card)).sum := by
  induction l with
  | nil => simp
  | cons R l ih =>
    have e : (∑ τF ∈ InjRanks X,
          ((R :: l).map (g τF)).sum)
        = (∑ τF ∈ InjRanks X, g τF R)
          + (∑ τF ∈ InjRanks X, (l.map (g τF)).sum) := by
      rw [Finset.sum_congr rfl (fun τF _ => by
        rw [List.map_cons, List.sum_cons])]
      exact Finset.sum_add_distrib
    rw [e, add_div, ih]
    simp [List.map_cons, List.sum_cons]

/-- `lem:foreignred` assembled: the expected foreign charge is at
most a log factor times the red run excess. -/
theorem expected_foreignCharge_le :
    ((∑ τF ∈ InjRanks X, (foreignCharge color τF : ℝ))
        / (InjRanks X).card)
      ≤ (4 * (2 + 2 * Real.log (Fintype.card X))) * (redRunSum color : ℝ) := by
  have hK : (0:ℝ) ≤ 4 * (2 + 2 * Real.log (Fintype.card X)) := by
    rcases Nat.eq_zero_or_pos (Fintype.card X) with h0 | hpos
    · simp [h0]
    · have hlog : 0 ≤ Real.log (Fintype.card X) :=
        Real.log_nonneg (by exact_mod_cast hpos)
      linarith
  have havg : ((∑ τF ∈ InjRanks X, (foreignCharge color τF : ℝ))
        / (InjRanks X).card)
      = ((runsOf color (sortedList X)).map
          (fun R => (∑ τF ∈ InjRanks X,
            (foreignAt color τF R : ℝ)) / (InjRanks X).card)).sum := by
    calc ((∑ τF ∈ InjRanks X, (foreignCharge color τF : ℝ))
          / (InjRanks X).card)
        = ((∑ τF ∈ InjRanks X, ((runsOf color (sortedList X)).map
            (fun R => (foreignAt color τF R : ℝ))).sum)
          / (InjRanks X).card) := by
          congr 1
          apply Finset.sum_congr rfl
          intro τF _
          unfold foreignCharge
          exact cast_map_sum _ _
      _ = ((runsOf color (sortedList X)).map
            (fun R => (∑ τF ∈ InjRanks X,
              (foreignAt color τF R : ℝ)) / (InjRanks X).card)).sum :=
          avg_list_map _ _
  rw [havg]
  refine le_trans (List.sum_le_sum
    (g := fun R => (4 * (2 + 2 * Real.log (Fintype.card X)))
      * ((if (∀ x ∈ R, color x = Color.red)
        then R.length - 1 else 0 : ℕ) : ℝ)) (fun R hRmem => ?_)) ?_
  · show ((∑ τF ∈ InjRanks X, (foreignAt color τF R : ℝ))
        / (InjRanks X).card)
      ≤ (4 * (2 + 2 * Real.log (Fintype.card X)))
        * ((if (∀ x ∈ R, color x = Color.red)
          then R.length - 1 else 0 : ℕ) : ℝ)
    have hlenR : 1 ≤ R.length := by
      have hne := runsOf_nonempty (color := color) (sortedList X) R hRmem
      cases R with
      | nil => exact absurd rfl hne
      | cons a t => simp
    by_cases hcond : (∀ x ∈ R, color x = Color.red) ∧ 2 ≤ R.length
    · have hsplit : ((∑ τF ∈ InjRanks X, (foreignAt color τF R : ℝ))
          / (InjRanks X).card)
          ≤ 4 * (2 + 2 * Real.log (Fintype.card X)) := by
        cases R with
        | nil => simp at hcond
        | cons a t =>
          have hunfold : ∀ τF ∈ InjRanks X,
              (foreignAt color τF (a :: t) : ℝ)
                = 2 * (recordsAt color τF a
                  + recordsAt color τF ((a :: t).getLast (by simp))) := by
            intro τF _
            rw [foreignAt, if_pos hcond]
            push_cast
            ring
          have hsum : (∑ τF ∈ InjRanks X,
                (foreignAt color τF (a :: t) : ℝ))
              = 2 * ((∑ τF ∈ InjRanks X, (recordsAt color τF a : ℝ))
                + (∑ τF ∈ InjRanks X,
                  (recordsAt color τF ((a :: t).getLast (by simp)) : ℝ))) := by
            rw [Finset.sum_congr rfl hunfold,
              Finset.sum_congr rfl (fun τF _ => mul_add (2:ℝ) _ _),
              Finset.sum_add_distrib]
            simp only [← Finset.mul_sum]
            ring
          rw [hsum, mul_div_assoc]
          have e1 := expected_recordsAt_le (color := color) a
          have e2 := expected_recordsAt_le (color := color)
            ((a :: t).getLast (by simp))
          have hdiv : ((∑ τF ∈ InjRanks X, (recordsAt color τF a : ℝ))
                + (∑ τF ∈ InjRanks X,
                  (recordsAt color τF ((a :: t).getLast (by simp)) : ℝ)))
              / (InjRanks X).card
              ≤ (2 + 2 * Real.log (Fintype.card X))
                + (2 + 2 * Real.log (Fintype.card X)) := by
            rw [add_div]
            exact add_le_add e1 e2
          have hcast := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0:ℝ) ≤ 2)
          refine le_trans hcast (by linarith)
      refine le_trans hsplit ?_
      rw [if_pos hcond.1]
      have hcast : ((R.length - 1 : ℕ) : ℝ) = (R.length : ℝ) - 1 := by
        rw [Nat.cast_sub hlenR, Nat.cast_one]
      rw [hcast]
      have h2 : (2:ℝ) ≤ (R.length : ℝ) := by exact_mod_cast hcond.2
      exact le_mul_of_one_le_right hK (by linarith)
    · have hzero : ((∑ τF ∈ InjRanks X, (foreignAt color τF R : ℝ))
          / (InjRanks X).card) = 0 := by
        have hz : ∀ τF ∈ InjRanks X, foreignAt color τF R = 0 := by
          intro τF _
          cases R with
          | nil => rfl
          | cons a t =>
            rw [foreignAt, if_neg]
            exact hcond
        rw [Finset.sum_eq_zero (fun τF hτ => by rw [hz τF hτ]; simp)]
        simp
      rw [hzero]
      by_cases hred : ∀ x ∈ R, color x = Color.red
      · rw [if_pos hred]
        apply mul_nonneg hK
        rw [Nat.cast_sub hlenR, Nat.cast_one]
        have h1 : (1:ℝ) ≤ (R.length : ℝ) := by exact_mod_cast hlenR
        linarith
      · rw [if_neg hred]
        simp [hK]
  · have e : ((runsOf color (sortedList X)).map
        (fun R => (4 * (2 + 2 * Real.log (Fintype.card X)))
          * ((if (∀ x ∈ R, color x = Color.red)
            then R.length - 1 else 0 : ℕ) : ℝ))).sum
        = (4 * (2 + 2 * Real.log (Fintype.card X)))
          * (redRunSum color : ℝ) := by
      rw [sum_map_factor]
      rfl
    rw [e]

/-- Red own charge: `(log₂ N + 3)` per red run excess element. -/
def redOwnCharge (color : X → Color) : ℕ :=
  (Nat.log 2 (instSize X) + 3) * redRunSum color

/-- The total cost of SpliceSort on one arrival ranking: mixed
(scan times two for pre-split scans, plus binary searches), blue
monochromatic, red own, and red foreign, as in the paper. When
there are no blue elements, the input is one red run and the
algorithm is MergeSort (`prop:onecolor`). -/
noncomputable def totalExecCost (α β : ℝ) (color : X → Color)
    (τF : X → Fin (Fintype.card X)) : ℝ :=
  if h : blueList color = [] then
    if redList color = [] then 0
    else α * ((msort (sortedList X)).2 : ℝ)
  else
    (2 * (scanCost (execEvents color h (arrivalsOf color τF)
        (arrivalsOf_perm color τF)) : ℝ))
    + ((redList color).length
        * (Nat.log 2 (blueList color).length + 1) : ℝ)
    + β * (blueCostCharge color : ℝ)
    + α * (redOwnCharge color : ℝ)
    + α * (foreignCharge color τF : ℝ)

/-- The output of SpliceSort on one arrival ranking: the final
runs read in order (the sorted order when there are no blues). -/
noncomputable def spliceRun (color : X → Color)
    (τF : X → Fin (Fintype.card X)) : List X :=
  if h : blueList color = [] then sortedList X
  else (finalState color h (arrivalsOf color τF)
    (arrivalsOf_perm color τF)).flatten

/-- Reds followed by blues are all the elements, sorted. -/
theorem redList_append_blueList_perm :
    (redList color ++ blueList color).Perm (sortedList X) := by
  refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
  · refine List.nodup_append.mpr ⟨redList_nodup color, blueList_nodup color, ?_⟩
    intro a ha b hb hab
    have h1 : color a = Color.red := (mem_redList (color := color)).mp ha
    have h2 : color b = Color.blue := by
      simp only [blueList, List.mem_filter] at hb
      exact of_decide_eq_true hb.2
    subst hab
    rw [h1] at h2
    exact Color.noConfusion h2
  · simp [sortedList]
  · intro x
    simp only [List.mem_append]
    constructor
    · intro h
      cases h with
      | inl h => simp [sortedList, Finset.mem_sort]
      | inr h => simp [sortedList, Finset.mem_sort]
    · intro hx
      by_cases hc : color x = Color.red
      · exact Or.inl ((mem_redList (color := color)).mpr hc)
      · have hcb : color x = Color.blue := by
          cases h : color x with
          | red => exact absurd h hc
          | blue => rfl
        exact Or.inr (List.mem_filter.mpr ⟨hx, by simp [hcb]⟩)

/-- The output of SpliceSort is sorted. -/
theorem spliceRun_sorted (τF : X → Fin (Fintype.card X)) :
    (spliceRun color τF).Pairwise (· ≤ ·) := by
  unfold spliceRun
  by_cases h : blueList color = []
  · rw [dif_pos h]
    unfold sortedList
    apply Finset.pairwise_sort
  · rw [dif_neg h]
    exact (finalState_flatten_sorted (color := color) h
      (arrivalsOf color τF) (arrivalsOf_perm color τF)).1

/-- The output of SpliceSort is a permutation of the input. -/
theorem spliceRun_perm (τF : X → Fin (Fintype.card X)) :
    (spliceRun color τF).Perm (sortedList X) := by
  unfold spliceRun
  by_cases h : blueList color = []
  · rw [dif_pos h]
  · rw [dif_neg h]
    refine ((finalState_flatten_sorted (color := color) h
      (arrivalsOf color τF) (arrivalsOf_perm color τF)).2.trans ?_)
    have hperm1 : (arrivalsOf color τF ++ blueList color).Perm
        (redList color ++ blueList color) :=
      List.Perm.append (arrivalsOf_perm color τF) (List.Perm.refl _)
    refine hperm1.trans ?_
    exact redList_append_blueList_perm (color := color)

/-- `(Nat.log 2 n : ℝ) ≤ Real.logb 2 n`. -/
theorem natLog_le_logb {n : ℕ} (hn : n ≠ 0) :
    (Nat.log 2 n : ℝ) ≤ Real.logb 2 (n : ℝ) := by
  by_cases h1 : n = 1
  · simp [h1]
  · rw [Real.le_logb_iff_rpow_le (by norm_num)
      (by exact_mod_cast Nat.pos_of_ne_zero hn), Real.rpow_natCast]
    exact_mod_cast Nat.pow_log_le_self 2 hn

/-- When there are no blue elements, `H = α (N - 1)`. -/
theorem benchmarkH_of_blueList_empty (α β : ℝ)
    (h : blueList color = []) :
    benchmarkH α β color = α * (((instSize X - 1 : ℕ)) : ℝ) := by
  have hall : ∀ x, color x = Color.red := by
    intro x
    cases hcx : color x with
    | red => rfl
    | blue =>
      exfalso
      have hmem : x ∈ blueList color :=
        List.mem_filter.mpr ⟨by simp [sortedList], by simp [hcx]⟩
      rw [h] at hmem
      simp at hmem
  unfold benchmarkH
  rw [adjCost_eq_adjCostWith,
    adjCostWith_of_mono (color := color) (pairCost α β color) α
      Color.red (sortedList X) (fun x _ => hall x) (by
        intro x y hx hy
        unfold pairCost
        rw [if_pos (by rw [hx, hy]), hx])]
  have hlen : (sortedList X).length = instSize X := by
    simp [sortedList, instSize, Finset.length_sort]
  rw [hlen]

/-- The expected total cost of SpliceSort is `O(H log N)` with an
absolute constant (`100`), assembled from the scan, search, blue,
own, and foreign bounds. -/
theorem expected_totalExecCost_le (α β : ℝ) (hα : 1 ≤ α) (hβ : 1 ≤ β)
    (hN : 2 ≤ Fintype.card X) :
    ((∑ τF ∈ InjRanks X, totalExecCost α β color τF)
        / (InjRanks X).card)
      ≤ 100 * benchmarkH α β color * Real.logb 2 (Fintype.card X) := by
  classical
  have hcard : ((InjRanks X).card : ℝ) ≠ 0 := by
    have hpos : 0 < (InjRanks X).card := by
      apply Finset.card_pos.mpr
      refine ⟨Fintype.equivFin X, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Fintype.equivFin X).injective⟩
    exact_mod_cast hpos.ne'
  have hN2 : (2:ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hN
  have hHge : (Fintype.card X : ℝ) - 1 ≤ benchmarkH α β color :=
    benchmarkH_ge (α := α) (β := β) (color := color) hα hβ
  have hLb : (1:ℝ) ≤ Real.logb 2 (Fintype.card X) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by
      exact_mod_cast (by omega : 0 < Fintype.card X)), Real.rpow_one]
    exact_mod_cast hN
  have hlogN : Real.log (Fintype.card X)
      ≤ Real.logb 2 (Fintype.card X) := by
    have h1 : Real.log (Fintype.card X)
        = Real.logb 2 (Fintype.card X) * Real.log 2 := by
      unfold Real.logb
      field_simp
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have h3 : (0:ℝ) ≤ Real.logb 2 (Fintype.card X) := by linarith
    rw [h1]
    calc Real.logb 2 (Fintype.card X) * Real.log 2
        ≤ Real.logb 2 (Fintype.card X) * 1 :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = Real.logb 2 (Fintype.card X) := by ring
  have hnatlog : ∀ m : ℕ, m ≤ Fintype.card X →
      (Nat.log 2 m : ℝ) ≤ Real.logb 2 (Fintype.card X) := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0]
      simp
      linarith
    · refine le_trans (natLog_le_logb (by omega)) ?_
      exact (Real.logb_le_logb (by norm_num : (1:ℝ) < 2)
        (show (0:ℝ) < (m : ℝ) by exact_mod_cast hpos)
        (show (0:ℝ) < (Fintype.card X : ℝ) by
          exact_mod_cast (by omega : 0 < Fintype.card X))).mpr
        (by exact_mod_cast hm)
  have hNH : (Fintype.card X : ℝ) ≤ 2 * benchmarkH α β color := by
    have hH1 : (1:ℝ) ≤ benchmarkH α β color := by linarith
    linarith
  by_cases hblue : blueList color = []
  · -- No blue elements: MergeSort on one red run.
    by_cases hred : redList color = []
    · have hzero : ∀ τF ∈ InjRanks X,
          totalExecCost α β color τF = 0 := by
        intro τF _
        unfold totalExecCost
        rw [dif_pos hblue, if_pos hred]
      rw [Finset.sum_congr rfl hzero]
      simp
      have hH1 : (1:ℝ) ≤ benchmarkH α β color := by linarith
      have hnn : (0:ℝ) ≤ 100 * benchmarkH α β color
          * Real.logb 2 (Fintype.card X) :=
        mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
      exact hnn
    · have hconst : ∀ τF ∈ InjRanks X,
          totalExecCost α β color τF
            = α * ((msort (sortedList X)).2 : ℝ) := by
        intro τF _
        unfold totalExecCost
        rw [dif_pos hblue, if_neg hred]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const,
        nsmul_eq_mul, mul_div_cancel_left₀ _ hcard]
      have hH : benchmarkH α β color
          = α * ((Fintype.card X : ℝ) - 1) := by
        have h := benchmarkH_of_blueList_empty (color := color) α β hblue
        rwa [show (((instSize X - 1 : ℕ)) : ℝ)
            = (Fintype.card X : ℝ) - 1 by
          rw [Nat.cast_sub (show 1 ≤ instSize X from le_trans (by norm_num) hN), Nat.cast_one]
          rfl] at h
      have hmsort : ((msort (sortedList X)).2 : ℝ)
          ≤ (Fintype.card X : ℝ)
            * (Real.logb 2 (Fintype.card X) + 1) := by
        have h1 : (msort (sortedList X)).2
            ≤ (sortedList X).length
              * (Nat.log 2 ((sortedList X).length - 1) + 1) :=
          msort_count_le _
        have hlen : (sortedList X).length = Fintype.card X := by
          simp [sortedList, Finset.length_sort]
        rw [hlen] at h1
        have h2 : (Nat.log 2 (Fintype.card X - 1) : ℝ)
            ≤ Real.logb 2 (Fintype.card X) :=
          hnatlog _ (by omega)
        have hα0 : (0:ℝ) ≤ (Fintype.card X : ℝ) := by positivity
        calc ((msort (sortedList X)).2 : ℝ)
            ≤ ((Fintype.card X
              * (Nat.log 2 (Fintype.card X - 1) + 1) : ℕ) : ℝ) := by
              exact_mod_cast h1
          _ = (Fintype.card X : ℝ)
              * ((Nat.log 2 (Fintype.card X - 1) : ℝ) + 1) := by
              push_cast
              ring
          _ ≤ (Fintype.card X : ℝ)
              * (Real.logb 2 (Fintype.card X) + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) hα0
      calc α * ((msort (sortedList X)).2 : ℝ)
          ≤ α * ((Fintype.card X : ℝ)
            * (Real.logb 2 (Fintype.card X) + 1)) :=
            mul_le_mul_of_nonneg_left hmsort (by linarith)
        _ ≤ 100 * benchmarkH α β color
            * Real.logb 2 (Fintype.card X) := by
          rw [hH]
          have hαpos : (0:ℝ) < α := by linarith
          have hN1 : (1:ℝ) ≤ (Fintype.card X : ℝ) - 1 := by
            have : (2:ℝ) ≤ (Fintype.card X : ℝ) := by exact_mod_cast hN
            linarith
          have step1 : α * ((Fintype.card X : ℝ)
              * (Real.logb 2 (Fintype.card X) + 1))
              ≤ α * ((2 * ((Fintype.card X : ℝ) - 1))
                * (2 * Real.logb 2 (Fintype.card X))) := by
            apply mul_le_mul_of_nonneg_left _ hαpos.le
            have g1 : (Fintype.card X : ℝ)
                ≤ 2 * ((Fintype.card X : ℝ) - 1) := by
              have : (2:ℝ) ≤ (Fintype.card X : ℝ) := by
                exact_mod_cast hN
              linarith
            have g2 : Real.logb 2 (Fintype.card X) + 1
                ≤ 2 * Real.logb 2 (Fintype.card X) := by linarith
            exact mul_le_mul g1 g2 (by linarith) (by
              have : (2:ℝ) ≤ (Fintype.card X : ℝ) := by
                exact_mod_cast hN
              linarith)
          refine le_trans step1 ?_
          have e : α * ((2 * ((Fintype.card X : ℝ) - 1))
              * (2 * Real.logb 2 (Fintype.card X)))
              = 4 * (α * ((Fintype.card X : ℝ) - 1))
                * Real.logb 2 (Fintype.card X) := by ring
          rw [e]
          have hnn : (0:ℝ) ≤ (α * ((Fintype.card X : ℝ) - 1))
              * Real.logb 2 (Fintype.card X) :=
            mul_nonneg (mul_nonneg hαpos.le (by linarith)) (by linarith)
          linarith
  · -- General case: assemble the five components.
    have hsplit : ∀ τF, totalExecCost α β color τF
        = (2 * (scanCost (execEvents color hblue (arrivalsOf color τF)
              (arrivalsOf_perm color τF)) : ℝ))
          + (((redList color).length
              * (Nat.log 2 (blueList color).length + 1) : ℝ)
            + β * (blueCostCharge color : ℝ)
            + α * (redOwnCharge color : ℝ))
          + α * (foreignCharge color τF : ℝ) := by
      intro τF
      unfold totalExecCost
      rw [dif_neg hblue]
      ring
    have hE : ((∑ τF ∈ InjRanks X, totalExecCost α β color τF)
          / (InjRanks X).card)
        = (2 * ((∑ τF ∈ InjRanks X,
              (scanCost (execEvents color hblue (arrivalsOf color τF)
                (arrivalsOf_perm color τF)) : ℝ)) / (InjRanks X).card))
          + (((redList color).length
              * (Nat.log 2 (blueList color).length + 1) : ℝ)
            + β * (blueCostCharge color : ℝ)
            + α * (redOwnCharge color : ℝ))
          + α * ((∑ τF ∈ InjRanks X, (foreignCharge color τF : ℝ))
            / (InjRanks X).card) := by
      have hsum : (∑ τF ∈ InjRanks X, totalExecCost α β color τF)
          = (∑ τF ∈ InjRanks X,
              (2 * (scanCost (execEvents color hblue
                (arrivalsOf color τF) (arrivalsOf_perm color τF)) : ℝ)))
            + ((InjRanks X).card : ℝ)
              * (((redList color).length
                * (Nat.log 2 (blueList color).length + 1) : ℝ)
                + β * (blueCostCharge color : ℝ)
                + α * (redOwnCharge color : ℝ))
            + (∑ τF ∈ InjRanks X, α * (foreignCharge color τF : ℝ)) := by
        rw [Finset.sum_congr rfl (fun τF _ => hsplit τF)]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_const, nsmul_eq_mul]
      have h2scan : (∑ τF ∈ InjRanks X,
            (2:ℝ) * (scanCost (execEvents color hblue
              (arrivalsOf color τF) (arrivalsOf_perm color τF)) : ℝ))
          = 2 * (∑ τF ∈ InjRanks X,
            (scanCost (execEvents color hblue (arrivalsOf color τF)
              (arrivalsOf_perm color τF)) : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
      have haforeign : (∑ τF ∈ InjRanks X,
            α * (foreignCharge color τF : ℝ))
          = α * (∑ τF ∈ InjRanks X, (foreignCharge color τF : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
      rw [hsum, h2scan, haforeign]
      field_simp
    rw [hE]
    have hscan : 2 * ((∑ τF ∈ InjRanks X,
          (scanCost (execEvents color hblue (arrivalsOf color τF)
            (arrivalsOf_perm color τF)) : ℝ)) / (InjRanks X).card)
        ≤ 32 * (benchmarkH α β color
          * Real.logb 2 (Fintype.card X)) := by
      have h1 := expected_execEvents_le (color := color) hblue
      calc 2 * ((∑ τF ∈ InjRanks X,
              (scanCost (execEvents color hblue (arrivalsOf color τF)
                (arrivalsOf_perm color τF)) : ℝ)) / (InjRanks X).card)
          ≤ 2 * (2 * ((Fintype.card X : ℝ)
              * (2 + 2 * Real.log (Fintype.card X)))) :=
            mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 4 * (Fintype.card X : ℝ)
            * (2 + 2 * Real.log (Fintype.card X)) := by ring
        _ ≤ 4 * (Fintype.card X : ℝ)
            * (4 * Real.logb 2 (Fintype.card X)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have g1 : Real.log (Fintype.card X)
              ≤ Real.logb 2 (Fintype.card X) := hlogN
          linarith
        _ = 16 * ((Fintype.card X : ℝ)
            * Real.logb 2 (Fintype.card X)) := by ring
        _ ≤ 16 * ((2 * benchmarkH α β color)
            * Real.logb 2 (Fintype.card X)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hNH (by linarith)
        _ = 32 * (benchmarkH α β color
            * Real.logb 2 (Fintype.card X)) := by ring
    have hsearch : ((redList color).length
          * (Nat.log 2 (blueList color).length + 1) : ℝ)
        ≤ 4 * (benchmarkH α β color
          * Real.logb 2 (Fintype.card X)) := by
      have hredlen : (redList color).length ≤ Fintype.card X := by
        have h1 : (redList color).length ≤ (sortedList X).length := by
          unfold redList
          exact List.length_filter_le _ _
        have h2 : (sortedList X).length = Fintype.card X := by
          simp [sortedList, Finset.length_sort]
        omega
      have hbluelen : (blueList color).length ≤ Fintype.card X := by
        have h1 : (blueList color).length ≤ (sortedList X).length := by
          unfold blueList
          exact List.length_filter_le _ _
        have h2 : (sortedList X).length = Fintype.card X := by
          simp [sortedList, Finset.length_sort]
        omega
      have hlogb : (Nat.log 2 (blueList color).length : ℝ)
          ≤ Real.logb 2 (Fintype.card X) := hnatlog _ hbluelen
      calc ((redList color).length
            * (Nat.log 2 (blueList color).length + 1) : ℝ)
          = ((redList color).length : ℝ)
            * ((Nat.log 2 (blueList color).length : ℝ) + 1) := by
            push_cast
            ring
        _ ≤ (Fintype.card X : ℝ)
            * (Real.logb 2 (Fintype.card X) + 1) := by
          apply mul_le_mul (by exact_mod_cast hredlen) (by linarith)
            (by positivity) (by positivity)
        _ ≤ (2 * benchmarkH α β color)
            * (2 * Real.logb 2 (Fintype.card X)) := by
          apply mul_le_mul hNH (by linarith) (by linarith)
          · have hH1 : (1:ℝ) ≤ benchmarkH α β color := by linarith
            linarith
        _ = 4 * (benchmarkH α β color
            * Real.logb 2 (Fintype.card X)) := by ring
    have hblueBound : β * (blueCostCharge color : ℝ)
        ≤ 4 * (benchmarkH α β color
          * Real.logb 2 (Fintype.card X)) := by
      have h1 : (blueCostCharge color : ℝ)
          ≤ (2 * (Nat.log 2 (instSize X) + 1) * blueRunSum color : ℕ) := by
        exact_mod_cast blueCostCharge_le (color := color)
      have h2 : (Nat.log 2 (instSize X) : ℝ)
          ≤ Real.logb 2 (Fintype.card X) := hnatlog _ (le_refl _)
      have hbeq : β * (blueRunSum color : ℝ) = blueAdjWeight β color :=
        (blueAdjWeight_eq (color := color) β).symm
      have hble : blueAdjWeight β color ≤ benchmarkH α β color :=
        blueAdjWeight_le (α := α) (β := β) (color := color) hα hβ
      have hbnn : (0:ℝ) ≤ blueAdjWeight β color := by
        rw [blueAdjWeight_eq]
        exact mul_nonneg (by linarith) (Nat.cast_nonneg _)
      calc β * (blueCostCharge color : ℝ)
          ≤ β * ((2 * (Nat.log 2 (instSize X) + 1)
              * blueRunSum color : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = (2 * ((Nat.log 2 (instSize X) : ℝ) + 1))
            * (β * (blueRunSum color : ℝ)) := by
            push_cast
            ring
        _ = (2 * ((Nat.log 2 (instSize X) : ℝ) + 1))
            * blueAdjWeight β color := by rw [hbeq]
        _ ≤ (2 * (Real.logb 2 (Fintype.card X) + 1))
            * benchmarkH α β color := by
          apply mul_le_mul (by linarith) hble hbnn (by
            have hLbnn : (0:ℝ) ≤ Real.logb 2 (Fintype.card X) := by
              linarith
            positivity)
        _ ≤ (2 * (2 * Real.logb 2 (Fintype.card X)))
            * benchmarkH α β color := by
          apply mul_le_mul_of_nonneg_right _ (by
            have hH1 : (1:ℝ) ≤ benchmarkH α β color := by linarith
            linarith)
          linarith
        _ = 4 * (benchmarkH α β color
            * Real.logb 2 (Fintype.card X)) := by ring
    have hown : α * (redOwnCharge color : ℝ)
        ≤ 4 * (benchmarkH α β color
          * Real.logb 2 (Fintype.card X)) := by
      have h2 : (Nat.log 2 (instSize X) : ℝ)
          ≤ Real.logb 2 (Fintype.card X) := hnatlog _ (le_refl _)
      have hbeq : α * (redRunSum color : ℝ) = redAdjWeight α color :=
        (redAdjWeight_eq (color := color) α).symm
      have hble : redAdjWeight α color ≤ benchmarkH α β color :=
        redAdjWeight_le (α := α) (β := β) (color := color) hα hβ
      have hbnn : (0:ℝ) ≤ redAdjWeight α color := by
        rw [redAdjWeight_eq]
        exact mul_nonneg (by linarith) (Nat.cast_nonneg _)
      calc α * (redOwnCharge color : ℝ)
          = ((Nat.log 2 (instSize X) : ℝ) + 3)
            * (α * (redRunSum color : ℝ)) := by
            unfold redOwnCharge
            push_cast
            ring
        _ = ((Nat.log 2 (instSize X) : ℝ) + 3)
            * redAdjWeight α color := by rw [hbeq]
        _ ≤ (Real.logb 2 (Fintype.card X) + 3)
            * benchmarkH α β color := by
          apply mul_le_mul (by linarith) hble hbnn (by positivity)
        _ ≤ (4 * Real.logb 2 (Fintype.card X))
            * benchmarkH α β color := by
          apply mul_le_mul_of_nonneg_right _ (by
            have hH1 : (1:ℝ) ≤ benchmarkH α β color := by linarith
            linarith)
          linarith
        _ = 4 * (benchmarkH α β color
            * Real.logb 2 (Fintype.card X)) := by ring
    have hforeign : α * ((∑ τF ∈ InjRanks X,
          (foreignCharge color τF : ℝ)) / (InjRanks X).card)
        ≤ 16 * (benchmarkH α β color
          * Real.logb 2 (Fintype.card X)) := by
      have h1 := expected_foreignCharge_le (color := color)
      have hbeq : α * (redRunSum color : ℝ) = redAdjWeight α color :=
        (redAdjWeight_eq (color := color) α).symm
      have hble : redAdjWeight α color ≤ benchmarkH α β color :=
        redAdjWeight_le (α := α) (β := β) (color := color) hα hβ
      have hbnn : (0:ℝ) ≤ redAdjWeight α color := by
        rw [redAdjWeight_eq]
        exact mul_nonneg (by linarith) (Nat.cast_nonneg _)
      have hlognn : (0:ℝ) ≤ Real.log (Fintype.card X) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ Fintype.card X))
      calc α * ((∑ τF ∈ InjRanks X, (foreignCharge color τF : ℝ))
            / (InjRanks X).card)
          ≤ α * ((4 * (2 + 2 * Real.log (Fintype.card X)))
            * (redRunSum color : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 (by linarith)
        _ = (4 * (2 + 2 * Real.log (Fintype.card X)))
            * (α * (redRunSum color : ℝ)) := by ring
        _ = (4 * (2 + 2 * Real.log (Fintype.card X)))
            * redAdjWeight α color := by rw [hbeq]
        _ ≤ (4 * (2 + 2 * Real.logb 2 (Fintype.card X)))
            * benchmarkH α β color := by
          apply mul_le_mul (by
            have g1 : Real.log (Fintype.card X)
                ≤ Real.logb 2 (Fintype.card X) := hlogN
            linarith) hble hbnn (by linarith)
        _ ≤ (4 * (4 * Real.logb 2 (Fintype.card X)))
            * benchmarkH α β color := by
          apply mul_le_mul_of_nonneg_right _ (by
            have hH1 : (1:ℝ) ≤ benchmarkH α β color := by linarith
            linarith)
          linarith
        _ = 16 * (benchmarkH α β color
            * Real.logb 2 (Fintype.card X)) := by ring
    have hQnn : (0:ℝ) ≤ benchmarkH α β color
        * Real.logb 2 (Fintype.card X) :=
      mul_nonneg (by linarith) (by linarith)
    -- Combine: total = 2E[scan] + (search + blue + own) + αE[foreign],
    -- and search + blue + own ≤ 12 Q.
    have hmid : ((redList color).length
          * (Nat.log 2 (blueList color).length + 1) : ℝ)
          + β * (blueCostCharge color : ℝ)
          + α * (redOwnCharge color : ℝ)
        ≤ 12 * (benchmarkH α β color
          * Real.logb 2 (Fintype.card X)) := by
      have s1 := hsearch
      have s2 := hblueBound
      have s3 := hown
      linarith
    -- the hE decomposition writes mid as one summand; reassociate
    have htotal : (2 * ((∑ τF ∈ InjRanks X,
            (scanCost (execEvents color hblue (arrivalsOf color τF)
              (arrivalsOf_perm color τF)) : ℝ)) / (InjRanks X).card))
          + (((redList color).length
              * (Nat.log 2 (blueList color).length + 1) : ℝ)
            + β * (blueCostCharge color : ℝ)
            + α * (redOwnCharge color : ℝ))
          + α * ((∑ τF ∈ InjRanks X, (foreignCharge color τF : ℝ))
            / (InjRanks X).card)
        ≤ 100 * benchmarkH α β color
          * Real.logb 2 (Fintype.card X) := by
      have s1 := hscan
      have s2 := hmid
      have s3 := hforeign
      have e : (100:ℝ) * benchmarkH α β color
          * Real.logb 2 (Fintype.card X)
          = 100 * (benchmarkH α β color
            * Real.logb 2 (Fintype.card X)) := by ring
      rw [e]
      linarith
    exact htotal

end Bichromatic.Randomized
