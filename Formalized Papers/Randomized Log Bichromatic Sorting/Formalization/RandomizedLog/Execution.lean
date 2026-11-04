import RandomizedLog.StepProduction

/-!
# Executions as data (randomized paper, §2–§3)

`TraceFrom` is a proposition: it records that states are linked by
steps, but a cost accounting needs to *recurse* over the execution
and read off which blue runs each arrival scanned. `ExecFrom` is
the same chain as data: each step carries its `Step` certificate
plus the list of blue runs scanned during that arrival (each a run
of the pre-step state). `ExecFrom.events` reads off the scan
events; everything proved about `TraceFrom` transports along
`ExecFrom.toTrace`.
-/

namespace Bichromatic.Randomized

open Bichromatic

variable {X : Type*} [LinearOrder X] [Fintype X] (color : X → Color)

/-- An execution: a chain of steps from `σ` to `σf` processing the
arrivals `L` in order, with the blue runs scanned at each arrival
recorded. -/
inductive ExecFrom : List (List X) → List X → List (List X) → Type _ where
  | nil (σ : List (List X)) : ExecFrom σ [] σ
  | cons {σ σ' σf : List (List X)} (r : X) {rest : List X}
      (step : Step color σ r σ') (scans : List (List X))
      (hscans : ∀ C ∈ scans, C ∈ σ) (restExec : ExecFrom σ' rest σf) :
      ExecFrom σ (r :: rest) σf

/-- Every execution is a trace. -/
def ExecFrom.toTrace {σ : List (List X)} {L : List X} {σf : List (List X)} :
    ExecFrom color σ L σf → TraceFrom color σ L σf
  | .nil _ => TraceFrom.nil _
  | .cons _ hs _ _ t => TraceFrom.cons hs t.toTrace

/-- The scan events of an execution: each scanned blue run paired
with the arrival that scanned it. -/
def ExecFrom.events {σ : List (List X)} {L : List X} {σf : List (List X)} :
    ExecFrom color σ L σf → List (X × List X)
  | .nil _ => []
  | .cons r _ scans _ t => (scans.map fun C => (r, C)) ++ t.events

/-- Executions transport the trace invariant bundle. -/
theorem exec_invariant {σ0 : List (List X)} {L : List X}
    {σf : List (List X)} (e : ExecFrom color σ0 L σf)
    (hinv : Invariant color σ0) (hmono : MonoRuns color σ0)
    (hredL : ∀ r ∈ L, color r = Color.red) :
    Invariant color σf ∧ MonoRuns color σf
      ∧ σf.flatten.Perm (L ++ σ0.flatten) :=
  trace_invariant color e.toTrace hinv hmono hredL

/-- Every event's arrival is one of the execution's arrivals. -/
theorem events_fst_mem {σ0 : List (List X)} {L : List X}
    {σf : List (List X)} (e : ExecFrom color σ0 L σf) :
    ∀ ev ∈ e.events, ev.1 ∈ L := by
  induction e with
  | nil σ =>
      intro ev hev
      simp [ExecFrom.events] at hev
  | @cons σ σ' σf r rest hs scans hsc t ih =>
      intro ev hev
      simp only [ExecFrom.events, List.mem_append, List.mem_map] at hev
      rcases hev with ⟨C, _, rfl⟩ | hev
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem r (ih ev hev)

/-- Every event's scanned run was a run of the state at its
arrival step; its elements reach the final flattening by
provenance. -/
theorem events_run_mem_final {σ0 : List (List X)} {L : List X}
    {σf : List (List X)} (e : ExecFrom color σ0 L σf) :
    ∀ ev ∈ e.events, ∀ x ∈ ev.2, x ∈ σf.flatten := by
  induction e with
  | nil σ =>
      intro ev hev
      simp [ExecFrom.events] at hev
  | @cons σ σ' σf r rest hs scans hsc t ih =>
      intro ev hev x hx
      simp only [ExecFrom.events, List.mem_append, List.mem_map] at hev
      rcases hev with ⟨C, hC, rfl⟩ | hev
      · have hxσ : x ∈ σ.flatten := List.mem_flatten.mpr ⟨C, hsc C hC, hx⟩
        have hp : σ'.flatten.Perm (r :: σ.flatten) := step_flatten color hs
        have hx' : x ∈ σ'.flatten :=
          hp.mem_iff.mpr (List.mem_cons_of_mem r hxσ)
        have hperm' : σf.flatten.Perm (rest ++ σ'.flatten) :=
          trace_flatten_perm color t.toTrace
        exact hperm'.mem_iff.mpr (List.mem_append.mpr (Or.inr hx'))
      · exact ih ev hev x hx


/-- A single arrival's scans are charged if either it scans
nothing, or it scans exactly one blue run `C` in one of the
ordinary shapes: a mixed scan splitting `C` (any case), a creator
scan at the left end (`r` below all of `C`, the first run) or at
the right end (`r` above all of `C`, the last run), or an
activated-merger scan, with `C` just below an activated red run
`S` and `r` between them, or just above `S` (symmetric).
The Case-B activation scans charge through founders, not
records, and are not a charged shape here. -/
def StepCharged (σ : List (List X)) (r : X) (scans : List (List X)) :
    Prop :=
  scans = [] ∨
  (∃ A B C, σ = A ++ C :: B ∧
    (∀ x ∈ C, color x = Color.blue) ∧
    scanVerdict C r = ScanVerdict.mixed ∧ scans = [C]) ∨
  (∃ B C, σ = C :: B ∧
    (∀ x ∈ C, color x = Color.blue) ∧
    (∀ x ∈ C, r < x) ∧ scans = [C]) ∨
  (∃ A C, σ = A ++ [C] ∧
    (∀ x ∈ C, color x = Color.blue) ∧
    (∀ x ∈ C, x < r) ∧ scans = [C]) ∨
  (∃ A B C S, σ = A ++ C :: S :: B ∧
    (∀ x ∈ C, color x = Color.blue) ∧
    (∀ x ∈ C, x < r) ∧ (∀ x ∈ S, r < x) ∧ S ≠ [] ∧ scans = [C]) ∨
  (∃ A B C S, σ = A ++ S :: C :: B ∧
    (∀ x ∈ C, color x = Color.blue) ∧
    (∀ x ∈ C, r < x) ∧ (∀ x ∈ S, x < r) ∧ S ≠ [] ∧ scans = [C])


/-- Every step of an execution is charged. -/
def ExecChargedSteps {σ : List (List X)} {L : List X}
    {σf : List (List X)} : ExecFrom color σ L σf → Prop
  | .nil _ => True
  | .cons r _ scans _ tail => StepCharged color σ r scans ∧ ExecChargedSteps tail

/-- Charging split executions: in an execution whose steps are all
charged, whose arrival list `Λ` enumerates red elements in
increasing `τF`-order (the `horder` hypothesis: every
earlier-`τF` red element is an earlier arrival or was present
initially), every scan event is record-charged. This supplies the
`hrec` hypothesis of `expected_scanCost_le` for executions whose
scans are splits and quiet steps. -/
theorem charged_events_hrec
    (τF : X → Fin (Fintype.card X)) (hinjF : Function.Injective τF)
    (Λ : List X) (σ0 : List (List X))
    (hΛred : ∀ r ∈ Λ, color r = Color.red)
    (horder : ∀ (L₁ : List X) (r : X) (L₂ : List X),
      Λ = L₁ ++ r :: L₂ → ∀ r' : X, color r' = Color.red →
      (τF r').val < (τF r).val → r' ∈ L₁ ∨ r' ∈ σ0.flatten) :
    ∀ {σ : List (List X)} {L : List X} {σf : List (List X)}
      (e : ExecFrom color σ L σf), ExecChargedSteps (color := color) e →
      ∀ (past : List X), Λ = past ++ L →
      Invariant color σ → MonoRuns color σ →
      σ.flatten.Perm (past ++ σ0.flatten) →
      ∀ ev ∈ e.events, ∀ b ∈ ev.2,
        IsRecord color (fun x => (τF x).val) b ev.1 := by
  intro σ L σf e
  induction e with
  | nil σ =>
      intro _ _ _ _ _ _ ev hev
      simp [ExecFrom.events] at hev
  | @cons σ σ' σf r rest step scans hscans tail ih =>
      intro hch past hΛ hinv hmono hprov ev hev
      obtain ⟨hstepch, htailch⟩ := hch
      have hrred : color r = Color.red := hΛred r (by rw [hΛ]; simp)
      obtain ⟨hinv', hmono'⟩ := step_invariant color step hinv hmono hrred
      have hprov' : σ'.flatten.Perm ((past ++ [r]) ++ σ0.flatten) := by
        have hp1 : σ'.flatten.Perm (r :: σ.flatten) :=
          step_flatten color step
        have happ : ((past ++ [r]) ++ σ0.flatten).Perm
            (r :: (past ++ σ0.flatten)) := by
          rw [List.append_assoc]
          exact List.perm_middle
        exact (hp1.trans (List.Perm.cons r hprov)).trans happ.symm
      have hΛ' : Λ = (past ++ [r]) ++ rest := by
        rw [List.append_assoc]; exact hΛ
      simp only [ExecFrom.events, List.mem_append, List.mem_map] at hev
      rcases hev with ⟨C, hC, rfl⟩ | hev
      · intro b hb
        have hinj : Function.Injective (fun x => (τF x).val) := by
          intro x y h
          exact hinjF (Fin.ext h)
        have hpresent₀ : ∀ r' : X, color r' = Color.red →
            (fun x => (τF x).val) r' < (fun x => (τF x).val) r →
            r' ∈ σ.flatten := by
          intro r' hr' hlt
          rcases horder past r rest hΛ r' hr' hlt with h | h
          · exact hprov.mem_iff.mpr (List.mem_append.mpr (Or.inl h))
          · exact hprov.mem_iff.mpr (List.mem_append.mpr (Or.inr h))
        rcases hstepch with hquiet
          | ⟨A, B, C', hσ, hblue, hmixed, hscansEq⟩
          | ⟨B, C', hσ, hblue, habove, hscansEq⟩
          | ⟨A, C', hσ, hblue, hbelow, hscansEq⟩
          | ⟨A, B, C', S, hσ, hblue, hbC, hrS, hSne, hscansEq⟩
          | ⟨A, B, C', S, hσ, hblue, hbC, hrS, hSne, hscansEq⟩
        · rw [hquiet] at hC
          simp at hC
        · rw [hscansEq] at hC
          have hCeq : C = C' := List.mem_singleton.mp hC
          subst hCeq
          have hpresent : ∀ r' : X, color r' = Color.red →
              (fun x => (τF x).val) r' < (fun x => (τF x).val) r →
              r' ∈ (A ++ C :: B).flatten := by
            intro r' hr' hlt
            rw [← hσ]
            exact hpresent₀ r' hr' hlt
          exact (split_scan_charged color (hσ ▸ hinv).2.1 hblue hrred
            hmixed (fun x => (τF x).val) hinj hpresent).2 b hb
        · rw [hscansEq] at hC
          have hCeq : C = C' := List.mem_singleton.mp hC
          subst hCeq
          have hpresent : ∀ r' : X, color r' = Color.red →
              (fun x => (τF x).val) r' < (fun x => (τF x).val) r →
              r' ∈ (C :: B).flatten := by
            intro r' hr' hlt
            rw [← hσ]
            exact hpresent₀ r' hr' hlt
          exact creator_record_left color (hσ ▸ hinv).2.1 habove hb
            hblue hrred (fun x => (τF x).val) hinj hpresent
        · rw [hscansEq] at hC
          have hCeq : C = C' := List.mem_singleton.mp hC
          subst hCeq
          have hpresent : ∀ r' : X, color r' = Color.red →
              (fun x => (τF x).val) r' < (fun x => (τF x).val) r →
              r' ∈ (A ++ [C]).flatten := by
            intro r' hr' hlt
            rw [← hσ]
            exact hpresent₀ r' hr' hlt
          exact creator_record color (hσ ▸ hinv).2.1 hbelow hb
            hblue hrred (fun x => (τF x).val) hinj hpresent
        · rw [hscansEq] at hC
          have hCeq : C = C' := List.mem_singleton.mp hC
          subst hCeq
          have hpresent : ∀ r' : X, color r' = Color.red →
              (fun x => (τF x).val) r' < (fun x => (τF x).val) r →
              r' ∈ (A ++ C :: S :: B).flatten := by
            intro r' hr' hlt
            rw [← hσ]
            exact hpresent₀ r' hr' hlt
          exact merger_record color (hσ ▸ hinv).2.1 hbC hrS hSne hb
            hblue hrred (fun x => (τF x).val) hinj hpresent
        · rw [hscansEq] at hC
          have hCeq : C = C' := List.mem_singleton.mp hC
          subst hCeq
          have hpresent : ∀ r' : X, color r' = Color.red →
              (fun x => (τF x).val) r' < (fun x => (τF x).val) r →
              r' ∈ (A ++ S :: C :: B).flatten := by
            intro r' hr' hlt
            rw [← hσ]
            exact hpresent₀ r' hr' hlt
          exact merger_record_succ color (hσ ▸ hinv).2.1 hbC hrS hSne hb
            hblue hrred (fun x => (τF x).val) hinj hpresent
      · exact ih htailch (past ++ [r]) hΛ' hinv' hmono' hprov' ev hev

/-- An activation configuration with founder `r₀`: the blue
neighbours of the singleton candidate `S = [r₀]` scanned
one-sided — both neighbours at an interior gap, or the single
neighbour at an end (where the stated `r`–`r₀` comparison is
the one making `r` fail to be a record for that side). -/
def ActivationAt (σ : List (List X)) (r r₀ : X) (scans : List (List X)) :
    Prop :=
  (∃ A B L S U, σ = A ++ L :: S :: U :: B ∧ S = [r₀] ∧
    (∀ x ∈ S, color x = Color.red) ∧
    (∀ x ∈ L, color x = Color.blue) ∧
    (∀ x ∈ U, color x = Color.blue) ∧
    (∀ x ∈ L, x < r) ∧ (∀ x ∈ U, r < x) ∧ scans = [L, U]) ∨
  (∃ B S C, σ = S :: C :: B ∧ S = [r₀] ∧
    (∀ x ∈ S, color x = Color.red) ∧
    (∀ x ∈ C, color x = Color.blue) ∧
    (∀ x ∈ C, r < x) ∧ r < r₀ ∧ scans = [C]) ∨
  (∃ A C S, σ = A ++ [C, S] ∧ S = [r₀] ∧
    (∀ x ∈ S, color x = Color.red) ∧
    (∀ x ∈ C, color x = Color.blue) ∧
    (∀ x ∈ C, x < r) ∧ r₀ < r ∧ scans = [C])

/-- A Case-B activation step: an activation configuration for
some founder `r₀`. These scans do not all charge to `r` as
records; they charge through the founder (paper §3, founder
property), so they are not a `StepCharged` shape. -/
def StepActivation (σ : List (List X)) (r : X) (scans : List (List X)) :
    Prop :=
  ∃ r₀, ActivationAt color σ r r₀ scans


/-- Whether a step is an activation step (decided classically;
the classification proof in an execution decides which side
each step's scans are charged to). -/
noncomputable def stepIsActivation (σ : List (List X)) (r : X)
    (scans : List (List X)) : Bool :=
  match Classical.dec (StepActivation color σ r scans) with
  | isTrue _ => true
  | isFalse _ => false

/-- The scan events of an execution charged to arrivals:
activation steps contribute nothing here. -/
noncomputable def ExecFrom.ordinaryEvents {σ : List (List X)} {L : List X}
    {σf : List (List X)} : ExecFrom color σ L σf → List (X × List X)
  | .nil _ => []
  | .cons r _ scans _ tail =>
      (if stepIsActivation color σ r scans then []
       else scans.map fun C => (r, C)) ++ tail.ordinaryEvents

/-- The scan events of an execution charged to founders:
non-activation steps contribute nothing here. -/
noncomputable def ExecFrom.activationEvents {σ : List (List X)} {L : List X}
    {σf : List (List X)} : ExecFrom color σ L σf → List (X × List X)
  | .nil _ => []
  | .cons r _ scans _ tail =>
      (match Classical.dec (StepActivation color σ r scans) with
       | isTrue h => scans.map fun C => (Classical.choose h, C)
       | isFalse _ => []) ++ tail.activationEvents

theorem stepIsActivation_of_activation {σ : List (List X)} {r : X}
    {scans : List (List X)} (h : StepActivation color σ r scans) :
    stepIsActivation color σ r scans = true := by
  unfold stepIsActivation
  cases Classical.dec (StepActivation color σ r scans) with
  | isTrue _ => rfl
  | isFalse h' => exact absurd h h'

theorem stepIsActivation_of_not_activation {σ : List (List X)} {r : X}
    {scans : List (List X)} (h : ¬ StepActivation color σ r scans) :
    stepIsActivation color σ r scans = false := by
  unfold stepIsActivation
  cases Classical.dec (StepActivation color σ r scans) with
  | isTrue h' => exact absurd h' h
  | isFalse _ => rfl

theorem activation_of_stepIsActivation {σ : List (List X)} {r : X}
    {scans : List (List X)}
    (h : stepIsActivation color σ r scans = true) :
    StepActivation color σ r scans := by
  by_contra hnot
  rw [stepIsActivation_of_not_activation (color := color) hnot] at h
  exact Bool.noConfusion h


/-- At an activation step, the activation events are the scans
attributed to a founder satisfying the activation configuration. -/
theorem activationEvents_cons_of_activation {σ σ' σf : List (List X)}
    {r : X} {rest : List X} (step : Step color σ r σ')
    (scans : List (List X)) (hsc : ∀ C ∈ scans, C ∈ σ)
    (tail : ExecFrom color σ' rest σf)
    (h : StepActivation color σ r scans) :
    ∃ q, ActivationAt color σ r q scans ∧
      (ExecFrom.cons r step scans hsc tail).activationEvents
        = (scans.map fun C => (q, C)) ++ tail.activationEvents := by
  simp only [ExecFrom.activationEvents]
  cases Classical.dec (StepActivation color σ r scans) with
  | isTrue h' =>
      exact ⟨Classical.choose h', Classical.choose_spec h', rfl⟩
  | isFalse h' => exact absurd h h'

/-- At a non-activation step, the activation events skip it. -/
theorem activationEvents_cons_of_not_activation {σ σ' σf : List (List X)}
    {r : X} {rest : List X} (step : Step color σ r σ')
    (scans : List (List X)) (hsc : ∀ C ∈ scans, C ∈ σ)
    (tail : ExecFrom color σ' rest σf)
    (h : ¬ StepActivation color σ r scans) :
    (ExecFrom.cons r step scans hsc tail).activationEvents
      = tail.activationEvents := by
  simp only [ExecFrom.activationEvents]
  cases Classical.dec (StepActivation color σ r scans) with
  | isTrue h' => exact absurd h' h
  | isFalse _ => rfl


/-- Position uniqueness for a nonempty run under ordered runs:
if the same nonempty run `C` appears at two append positions,
the positions agree. Cross-order between the two occurrences
would give `c < c` for any `c ∈ C`, since `RunsOrdered` orders
every pair of runs. -/
theorem runsOrdered_append_inj {C : List X} (hC : C ≠ [])
    {A₁ A₂ B₁ B₂ : List (List X)}
    (hord : RunsOrdered (A₁ ++ C :: B₁))
    (h : A₁ ++ C :: B₁ = A₂ ++ C :: B₂) : A₁ = A₂ ∧ B₁ = B₂ := by
  obtain ⟨c, hc⟩ : ∃ c, c ∈ C := by
    cases C with
    | nil => simp at hC
    | cons x xs => exact ⟨x, by simp⟩
  rcases List.append_eq_append_iff.mp h with ⟨as, hA2, hxs⟩ | ⟨bs, hA1, hzs⟩
  · cases as with
    | nil =>
        simp only [List.append_nil] at hA2
        exact ⟨hA2.symm, congrArg List.tail hxs⟩
    | cons T as' =>
        injection hxs with _ hB1
        have hCmem : C ∈ B₁ := by
          rw [hB1]
          exact List.mem_append.mpr (Or.inr (by simp))
        have hcross := (List.pairwise_cons.mp
          (List.pairwise_append.mp hord).2.1).1 C hCmem
        exact absurd (hcross c hc c hc) (lt_irrefl c)
  · cases bs with
    | nil =>
        simp only [List.append_nil] at hA1
        exact ⟨hA1, (congrArg List.tail hzs).symm⟩
    | cons T bs' =>
        injection hzs with _ hB2
        have hord2 : RunsOrdered (A₂ ++ C :: B₂) := h ▸ hord
        have hCmem : C ∈ B₂ := by
          rw [hB2]
          exact List.mem_append.mpr (Or.inr (by simp))
        have hcross := (List.pairwise_cons.mp
          (List.pairwise_append.mp hord2).2.1).1 C hCmem
        exact absurd (hcross c hc c hc) (lt_irrefl c)

/-- The founder of an activation configuration is unique for a
given arrival and scan list: two founders would put the same
singleton run in two places, or demand a scanned run on both
sides of the arrival at once. -/
theorem activationAt_founder_unique {σ : List (List X)}
    (hord : RunsOrdered σ)
    (hne : ∀ R ∈ σ, R ≠ []) {r q₁ q₂ : X} {scans : List (List X)}
    (h₁ : ActivationAt color σ r q₁ scans)
    (h₂ : ActivationAt color σ r q₂ scans) : q₁ = q₂ := by
  rcases h₁ with ⟨A, B, L, S, U, hσ, hS, -, -, -, -, -, hs⟩
    | ⟨B, S, C, hσ, hS, -, -, haC, -, hs⟩
    | ⟨A, C, S, hσ, hS, -, -, hbC, -, hs⟩
  · rcases h₂ with ⟨A', B', L', S', U', hσ', hS', -, -, -, -, -, hs'⟩
      | ⟨B', S', C', hσ', hS', -, -, -, -, hs'⟩
      | ⟨A', C', S', hσ', hS', -, -, -, -, hs'⟩
    · have hLU : L = L' ∧ U = U' := by
        have e : [L, U] = [L', U'] := hs.symm.trans hs'
        simpa using e
      rcases hLU with ⟨rfl, rfl⟩
      have hord1 : RunsOrdered (A ++ L :: (S :: U :: B)) := hσ ▸ hord
      have heq : A ++ L :: (S :: U :: B) = A' ++ L :: (S' :: U :: B') :=
        hσ.symm.trans hσ'
      have happ := runsOrdered_append_inj (hne L (by rw [hσ]; simp))
        hord1 heq
      have hSS' : S = S' := by
        have e := happ.2
        have e2 : S = S' ∧ (U :: B) = (U :: B') := by
          simpa only [List.cons.injEq] using e
        exact e2.1
      have hqq : [q₁] = [q₂] := hS.symm.trans (hSS'.trans hS')
      simpa using hqq
    · have e : [L, U] = [C'] := hs.symm.trans hs'
      simp at e
    · have e : [L, U] = [C'] := hs.symm.trans hs'
      simp at e
  · rcases h₂ with ⟨A', B', L', S', U', hσ', hS', -, -, -, -, -, hs'⟩
      | ⟨B', S', C', hσ', hS', -, -, -, -, hs'⟩
      | ⟨A', C', S', hσ', hS', -, -, hbC', -, hs'⟩
    · have e : [C] = [L', U'] := hs.symm.trans hs'
      simp at e
    · have hSS' : S = S' := by
        have e : S :: C :: B = S' :: C' :: B' := hσ.symm.trans hσ'
        injection e with h _
      have hqq : [q₁] = [q₂] := hS.symm.trans (hSS'.trans hS')
      simpa using hqq
    · have hCC' : C = C' := by
        have e : [C] = [C'] := hs.symm.trans hs'
        simpa using e
      obtain ⟨c, hc⟩ : ∃ c, c ∈ C := by
        have hne : C ≠ [] := hne C (by rw [hσ]; simp)
        cases C with
        | nil => simp at hne
        | cons y ys => exact ⟨y, by simp⟩
      exact absurd (hbC' c (hCC' ▸ hc)) (not_lt.mpr (le_of_lt (haC c hc)))
  · rcases h₂ with ⟨A', B', L', S', U', hσ', hS', -, -, -, -, -, hs'⟩
      | ⟨B', S', C', hσ', hS', -, -, haC', -, hs'⟩
      | ⟨A', C', S', hσ', hS', -, -, -, -, hs'⟩
    · have e : [C] = [L', U'] := hs.symm.trans hs'
      simp at e
    · have hCC' : C = C' := by
        have e : [C] = [C'] := hs.symm.trans hs'
        simpa using e
      obtain ⟨c, hc⟩ : ∃ c, c ∈ C := by
        have hne : C ≠ [] := hne C (by rw [hσ]; simp)
        cases C with
        | nil => simp at hne
        | cons y ys => exact ⟨y, by simp⟩
      exact absurd (haC' c (hCC' ▸ hc)) (not_lt.mpr (le_of_lt (hbC c hc)))
    · have hCC' : C = C' := by
        have e : [C] = [C'] := hs.symm.trans hs'
        simpa using e
      rcases hCC' with rfl
      have hord1 : RunsOrdered (A ++ C :: [S]) := hσ ▸ hord
      have heq : A ++ C :: [S] = A' ++ C :: [S'] :=
        hσ.symm.trans hσ'
      have happ := runsOrdered_append_inj (hne C (by rw [hσ]; simp))
        hord1 heq
      have hSS' : S = S' := by
        have e := happ.2
        simpa using e
      have hqq : [q₁] = [q₂] := hS.symm.trans (hSS'.trans hS')
      simpa using hqq

/-- Strong classification of a produced step: either charged, or
an activation whose founder's run has grown to at least two
elements in the next state (the founder merges with the arrival).
A founder whose run has grown can never be a singleton founder
again, which is what makes activation charging count each
founder at most once. -/
def StepStrong (σ : List (List X)) (r : X) (σ' : List (List X))
    (scans : List (List X)) : Prop :=
  StepCharged color σ r scans ∨
    ∃ q, ActivationAt color σ r q scans ∧
      ∃ R ∈ σ', q ∈ R ∧ 2 ≤ R.length

/-- Alternating runs: consecutive runs have opposite colors, on
elements. The paper's invariant package includes alternation
("the row stays ordered and alternating"); the run model here
tracks it as a separate predicate, maintained by the produced
steps. -/
inductive AltRuns : List (List X) → Prop where
  | nil : AltRuns []
  | single (R : List X) : AltRuns [R]
  | cons {R T : List X} {rest : List (List X)}
      (h : ∀ x ∈ R, ∀ y ∈ T, color x ≠ color y) :
      AltRuns (T :: rest) → AltRuns (R :: T :: rest)

theorem alt_of_append_left {A B : List (List X)} :
    AltRuns color (A ++ B) → AltRuns color A := by
  induction A with
  | nil => intro _; exact AltRuns.nil
  | cons R A ih =>
      cases A with
      | nil => intro _; exact AltRuns.single R
      | cons T A' =>
          intro h
          cases h with
          | cons hseam htail => exact AltRuns.cons hseam (ih htail)

theorem alt_of_append_right {A B : List (List X)} :
    AltRuns color (A ++ B) → AltRuns color B := by
  induction A with
  | nil => intro h; exact h
  | cons R A ih =>
      intro h
      cases A with
      | nil =>
          simp only [List.nil_append, List.cons_append] at h
          cases h with
          | single => exact AltRuns.nil
          | cons _ htail => exact htail
      | cons T A' =>
          cases h with
          | cons _ htail => exact ih htail

/-- The seam at an explicit adjacent pair inside an append
decomposition. -/
theorem alt_seam {A B : List (List X)} {R T : List X} :
    AltRuns color (A ++ R :: T :: B) → ∀ x ∈ R, ∀ y ∈ T, color x ≠ color y := by
  induction A with
  | nil =>
      intro h
      cases h with
      | cons hseam _ => exact hseam
  | cons R' A ih =>
      intro h
      cases A with
      | nil =>
          cases h with
          | cons _ htail => exact ih htail
      | cons T' A' =>
          cases h with
          | cons _ htail => exact ih htail

/-- Replacing a run by another run of the same color (on elements)
preserves alternation: sorted insertion into a red run, and the
merged red pair, are both instances. -/
theorem alt_replace_run {A B : List (List X)} {S T : List X}
    (hT : ∀ x ∈ T, ∀ y ∈ S, color x = color y)
    (hSne : S ≠ []) (hTne : T ≠ []) :
    AltRuns color (A ++ S :: B) → AltRuns color (A ++ T :: B) := by
  induction A with
  | nil =>
      intro h
      cases B with
      | nil => exact AltRuns.single T
      | cons T' B' =>
          cases h with
          | cons hseam htail =>
              refine AltRuns.cons ?_ htail
              obtain ⟨t₀, ht₀⟩ : ∃ t₀, t₀ ∈ T := by
                cases T with
                | nil => simp at hTne
                | cons x xs => exact ⟨x, by simp⟩
              obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
                cases S with
                | nil => simp at hSne
                | cons x xs => exact ⟨x, by simp⟩
              intro x hx y hy
              rw [hT x hx s₀ hs₀]
              exact hseam s₀ hs₀ y hy
  | cons R A ih =>
      cases A with
      | nil =>
          intro h
          cases h with
          | cons hseam htail =>
              refine AltRuns.cons ?_ (ih htail)
              obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
                cases S with
                | nil => simp at hSne
                | cons x xs => exact ⟨x, by simp⟩
              intro x hx y hy
              rw [hT y hy s₀ hs₀]
              exact hseam x hx s₀ hs₀
      | cons T' A' =>
          intro h
          cases h with
          | cons hseam htail => exact AltRuns.cons hseam (ih htail)

/-- Splitting a blue run into two blue sub-runs around the red
singleton `[r]` preserves alternation. -/
theorem alt_split_run {A B : List (List X)} {C below above : List X}
    {r : X}
    (hsub_b : ∀ x ∈ below, x ∈ C) (hsub_a : ∀ x ∈ above, x ∈ C)
    (hblue : ∀ x ∈ C, color x = Color.blue) (hred : color r = Color.red)
    (hbne : below ≠ []) (hane : above ≠ []) :
    AltRuns color (A ++ C :: B) →
      AltRuns color (A ++ below :: [r] :: above :: B) := by
  induction A with
  | nil =>
      intro h
      have hseam1 : ∀ x ∈ below, ∀ y ∈ [r], color x ≠ color y := by
        intro x hx y hy
        simp at hy
        rw [hy, hblue x (hsub_b x hx), hred]
        exact Color.noConfusion
      have hseam2 : ∀ x ∈ [r], ∀ y ∈ above, color x ≠ color y := by
        intro x hx y hy
        simp at hx
        rw [hx, hblue y (hsub_a y hy), hred]
        exact fun hh => Color.noConfusion hh.symm
      cases B with
      | nil =>
          exact AltRuns.cons hseam1 (AltRuns.cons hseam2 (AltRuns.single above))
      | cons T B' =>
          cases h with
          | cons hseam htail =>
              refine AltRuns.cons hseam1 (AltRuns.cons hseam2
                (AltRuns.cons ?_ htail))
              intro x hx y hy
              exact hseam x (hsub_a x hx) y hy
  | cons R A ih =>
      cases A with
      | nil =>
          intro h
          cases h with
          | cons hseam htail =>
              refine AltRuns.cons (fun x hx y hy => hseam x hx y (hsub_b y hy))
                (ih htail)
      | cons T A' =>
          intro h
          cases h with
          | cons hseam htail => exact AltRuns.cons hseam (ih htail)

/-- A fresh red singleton before a blue first run preserves
alternation. -/
theorem alt_fresh_left {B : List (List X)} {C : List X} {r : X}
    (hblue : ∀ x ∈ C, color x = Color.blue) (hred : color r = Color.red) :
    AltRuns color (C :: B) → AltRuns color ([r] :: C :: B) := by
  intro h
  refine AltRuns.cons ?_ h
  intro x hx y hy
  simp at hx
  rw [hx, hblue y hy, hred]
  exact Color.noConfusion

/-- An appended red singleton after a blue last run preserves
alternation. -/
theorem alt_append_right {A : List (List X)} {C : List X} {r : X}
    (hblue : ∀ x ∈ C, color x = Color.blue) (hred : color r = Color.red) :
    AltRuns color (A ++ [C]) → AltRuns color ((A ++ [C]) ++ [[r]]) := by
  induction A with
  | nil =>
      intro _
      exact AltRuns.cons (by
        intro x hx y hy
        simp only [List.mem_singleton] at hy
        rw [hblue x hx, hy, hred]
        exact Color.noConfusion) (AltRuns.single [r])
  | cons R A ih =>
      cases A with
      | nil =>
          intro h
          cases h with
          | cons hseam _ =>
              refine AltRuns.cons hseam ?_
              exact AltRuns.cons (by
                intro x hx y hy
                simp only [List.mem_singleton] at hy
                rw [hblue x hx, hy, hred]
                exact Color.noConfusion) (AltRuns.single [r])
      | cons T A' =>
          intro h
          cases h with
          | cons hseam htail => exact AltRuns.cons hseam (ih htail)


/-- Founder records at an activation configuration: in any of
the three activation forms, the founder `r₀` is a record for
every blue element of every scanned run. Separation at the
activation state itself: earlier red elements lie in runs on
the far side of the scanned run or of `r₀`'s singleton run, so
none lies strictly between `r₀` and `b`. This is the paper's
founder property, proved at the moment of activation rather
than traced back to the founder's creation. -/
theorem activationAt_record {σ : List (List X)} {r r₀ : X}
    {scans : List (List X)}
    (hact : ActivationAt color σ r r₀ scans)
    (hord : RunsOrdered σ) (hred₀ : color r₀ = Color.red)
    (τ : X → ℕ) (hinj : Function.Injective τ)
    (hpresent : ∀ r' : X, color r' = Color.red → τ r' < τ r₀ →
      r' ∈ σ.flatten) :
    ∀ C ∈ scans, ∀ b ∈ C, IsRecord color τ b r₀ := by
  rcases hact with ⟨A, B, L, S, U, hσ, hS, -, hLb, hUb, hbL, haU, hscans⟩
    | ⟨B, S, C, hσ, hS, -, hblue, haC, hlt, hscans⟩
    | ⟨A, C, S, hσ, hS, -, hblue, hbC, hlt, hscans⟩
  · -- interior: scanned runs are `L` (below `r₀`) and `U` (above)
    have hord2 : RunsOrdered (A ++ L :: S :: U :: B) := hσ ▸ hord
    intro C' hC' b hb
    rw [hscans] at hC'
    have hcases : C' = L ∨ C' = U := by simpa using hC'
    have hbS : ∀ y ∈ S, ∀ z ∈ U, y < z := by
      have e : A ++ L :: S :: U :: B = (A ++ [L, S]) ++ U :: B := by
        simp [List.append_assoc]
      have hord3 : RunsOrdered ((A ++ [L, S]) ++ U :: B) := e ▸ hord2
      exact (List.pairwise_append.mp hord3).2.2 S (by simp) U (by simp)
    have hb0S : ∀ x ∈ L, ∀ y ∈ S, x < y := by
      have e : A ++ L :: S :: U :: B = (A ++ [L]) ++ S :: U :: B := by
        simp [List.append_assoc]
      have hord3 : RunsOrdered ((A ++ [L]) ++ S :: U :: B) := e ▸ hord2
      exact (List.pairwise_append.mp hord3).2.2 L (by simp) S (by simp)
    rcases hcases with rfl | rfl
    · -- `b ∈ L`, `b < r₀`: successor record
      have hb0 : b < r₀ := by
        have h1 := hb0S b hb r₀ (by rw [hS]; simp)
        exact h1
      have hne : r₀ ≠ b := by
        intro hcon
        have h1 : color r₀ = Color.blue := by rw [hcon]; exact hLb b hb
        rw [hred₀] at h1
        exact Color.noConfusion h1
      apply record_key color hred₀ hne τ hinj
      apply record_key_of_separation color τ hinj
        (fun r' hr' hlt => by
          have hmem := hpresent r' hr' hlt
          rw [hσ] at hmem
          exact hmem)
      intro r' hr' hmem hinter
      rw [List.mem_flatten] at hmem
      obtain ⟨R, hRruns, hRr⟩ := hmem
      simp only [List.mem_append, List.mem_cons] at hRruns
      rcases hRruns with hA | rfl | rfl | rfl | hB
      · have hlt1 : r' < b :=
          (List.pairwise_append.mp hord2).2.2 R hA C' (by simp) r' hRr b hb
        have hlt2 : r' < r₀ := lt_trans hlt1 hb0
        cases hinter with
        | inl hh => exact absurd hh.1 (not_lt.mpr (le_of_lt hlt2))
        | inr hh => exact absurd hh.1 (not_lt.mpr (le_of_lt hlt1))
      · have hcb : color r' = Color.blue := hLb r' hRr
        rw [hr'] at hcb
        exact Color.noConfusion hcb
      · rw [hS] at hRr
        simp at hRr
        rw [hRr] at hinter
        cases hinter with
        | inl hh => exact absurd hh.1 (lt_irrefl r₀)
        | inr hh => exact absurd hh.2 (lt_irrefl r₀)
      · have hlt1 : r₀ < r' := hbS r₀ (by rw [hS]; simp) r' hRr
        cases hinter with
        | inl hh => exact absurd hh.2 (not_lt.mpr (le_of_lt (lt_trans hb0 hlt1)))
        | inr hh => exact absurd hh.2 (not_lt.mpr (le_of_lt hlt1))
      · have hlt1 : r₀ < r' := by
          have e : A ++ C' :: S :: U :: B = (A ++ [C', S, U]) ++ B := by
            simp [List.append_assoc]
          have hord3 : RunsOrdered ((A ++ [C', S, U]) ++ B) := e ▸ hord2
          exact (List.pairwise_append.mp hord3).2.2 S (by simp) R hB
            r₀ (by rw [hS]; simp) r' hRr
        cases hinter with
        | inl hh => exact absurd hh.2 (not_lt.mpr (le_of_lt (lt_trans hb0 hlt1)))
        | inr hh => exact absurd hh.2 (not_lt.mpr (le_of_lt hlt1))
    · -- `b ∈ U`, `r₀ < b`: predecessor record
      have hb0 : r₀ < b := hbS r₀ (by rw [hS]; simp) b hb
      have hne : r₀ ≠ b := by
        intro hcon
        have h1 : color r₀ = Color.blue := by rw [hcon]; exact hUb b hb
        rw [hred₀] at h1
        exact Color.noConfusion h1
      apply record_key color hred₀ hne τ hinj
      apply record_key_of_separation color τ hinj
        (fun r' hr' hlt => by
          have hmem := hpresent r' hr' hlt
          rw [hσ] at hmem
          exact hmem)
      intro r' hr' hmem hinter
      rw [List.mem_flatten] at hmem
      obtain ⟨R, hRruns, hRr⟩ := hmem
      simp only [List.mem_append, List.mem_cons] at hRruns
      rcases hRruns with hA | rfl | rfl | rfl | hB
      · have hlt1 : r' < r₀ := by
          have e : A ++ L :: S :: C' :: B = (A ++ [L]) ++ S :: C' :: B := by
            simp [List.append_assoc]
          have hord3 : RunsOrdered ((A ++ [L]) ++ S :: C' :: B) := e ▸ hord2
          exact (List.pairwise_append.mp hord3).2.2 R
            (by simp [hA]) S (by simp) r' hRr r₀
            (by rw [hS]; simp)
        cases hinter with
        | inl hh => exact absurd hh.1 (not_lt.mpr (le_of_lt hlt1))
        | inr hh => exact absurd hh.1 (not_lt.mpr (le_of_lt (lt_trans hlt1 hb0)))
      · have hlt1 : r' < r₀ := hb0S r' hRr r₀ (by rw [hS]; simp)
        cases hinter with
        | inl hh => exact absurd hh.1 (not_lt.mpr (le_of_lt hlt1))
        | inr hh => exact absurd hh.1 (not_lt.mpr (le_of_lt (lt_trans hlt1 hb0)))
      · rw [hS] at hRr
        simp at hRr
        rw [hRr] at hinter
        cases hinter with
        | inl hh => exact absurd hh.1 (lt_irrefl r₀)
        | inr hh => exact absurd hh.2 (lt_irrefl r₀)
      · have hcb : color r' = Color.blue := hUb r' hRr
        rw [hr'] at hcb
        exact Color.noConfusion hcb
      · have hlt1 : b < r' := by
          have e : A ++ L :: S :: C' :: B = (A ++ [L, S, C']) ++ B := by
            simp [List.append_assoc]
          have hord3 : RunsOrdered ((A ++ [L, S, C']) ++ B) := e ▸ hord2
          exact (List.pairwise_append.mp hord3).2.2 C' (by simp) R hB
            b hb r' hRr
        cases hinter with
        | inl hh => exact absurd hh.2 (not_lt.mpr (le_of_lt hlt1))
        | inr hh => exact absurd hh.2 (not_lt.mpr (le_of_lt (lt_trans hb0 hlt1)))
  · -- left end: scanned run `C` above `r₀`
    have hord2 : RunsOrdered (S :: C :: B) := hσ ▸ hord
    intro C' hC' b hb
    rw [hscans] at hC'
    simp at hC'
    subst hC'
    have hb0 : r₀ < b := by
      have hcross := (List.pairwise_cons.mp hord2).1 C' (by simp)
      exact hcross r₀ (by rw [hS]; simp) b hb
    have hne : r₀ ≠ b := by
      intro hcon
      have h1 : color r₀ = Color.blue := by rw [hcon]; exact hblue b hb
      rw [hred₀] at h1
      exact Color.noConfusion h1
    apply record_key color hred₀ hne τ hinj
    apply record_key_of_separation color τ hinj
      (fun r' hr' hlt => by
        have hmem := hpresent r' hr' hlt
        rw [hσ] at hmem
        exact hmem)
    intro r' hr' hmem hinter
    rw [List.mem_flatten] at hmem
    obtain ⟨R, hRruns, hRr⟩ := hmem
    simp only [List.mem_cons] at hRruns
    rcases hRruns with rfl | rfl | hB
    · rw [hS] at hRr
      simp at hRr
      rw [hRr] at hinter
      cases hinter with
      | inl hh => exact absurd hh.1 (lt_irrefl r₀)
      | inr hh => exact absurd hh.2 (lt_irrefl r₀)
    · have hcb : color r' = Color.blue := hblue r' hRr
      rw [hr'] at hcb
      exact Color.noConfusion hcb
    · have hlt1 : b < r' := by
        have e : S :: C' :: B = [S, C'] ++ B := rfl
        have hord3 : RunsOrdered ([S, C'] ++ B) := e ▸ hord2
        exact (List.pairwise_append.mp hord3).2.2 C' (by simp) R hB
          b hb r' hRr
      cases hinter with
      | inl hh => exact absurd hh.2 (not_lt.mpr (le_of_lt hlt1))
      | inr hh => exact absurd hh.2 (not_lt.mpr (le_of_lt (lt_trans hb0 hlt1)))
  · -- right end: scanned run `C` below `r₀`
    have hord2 : RunsOrdered (A ++ [C, S]) := hσ ▸ hord
    intro C' hC' b hb
    rw [hscans] at hC'
    simp at hC'
    subst hC'
    have hb0 : b < r₀ := by
      have hcross := (List.pairwise_cons.mp
        (List.pairwise_append.mp hord2).2.1).1 S (by simp)
      exact hcross b hb r₀ (by rw [hS]; simp)
    have hne : r₀ ≠ b := by
      intro hcon
      have h1 : color r₀ = Color.blue := by rw [hcon]; exact hblue b hb
      rw [hred₀] at h1
      exact Color.noConfusion h1
    apply record_key color hred₀ hne τ hinj
    apply record_key_of_separation color τ hinj
      (fun r' hr' hlt => by
        have hmem := hpresent r' hr' hlt
        rw [hσ] at hmem
        exact hmem)
    intro r' hr' hmem hinter
    rw [List.mem_flatten] at hmem
    obtain ⟨R, hRruns, hRr⟩ := hmem
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hRruns
    rcases hRruns with hA | rfl | rfl
    · have hlt1 : r' < b :=
        (List.pairwise_append.mp hord2).2.2 R hA C' (by simp) r' hRr b hb
      cases hinter with
      | inl hh => exact absurd hh.1 (not_lt.mpr (le_of_lt (lt_trans hlt1 hb0)))
      | inr hh => exact absurd hh.1 (not_lt.mpr (le_of_lt hlt1))
    · have hcb : color r' = Color.blue := hblue r' hRr
      rw [hr'] at hcb
      exact Color.noConfusion hcb
    · rw [hS] at hRr
      simp at hRr
      rw [hRr] at hinter
      cases hinter with
      | inl hh => exact absurd hh.1 (lt_irrefl r₀)
      | inr hh => exact absurd hh.2 (lt_irrefl r₀)

/-- Arrival at an interior located gap: the state decomposes as
`A ++ L :: S :: U :: B` with `L`, `U` blue, `S` red, and location
certificates `l₀ < r < u₀` for some `l₀ ∈ L`, `u₀ ∈ U` (the
paper's `lem:location`, from minimality of the locate index).
Then some step exists, and its scans are charged — except in the
Case-B activation subcase, which is flagged separately. Case
dispatch follows the paper: a mixed neighbour splits; otherwise
the one-sided neighbours force `L` below and `U` above, and the
candidate `S` decides: singleton merges (activation), a
one-sided `S` attaches at its near end (activated merger), and a
straddling `S` absorbs `r` with no scan. -/
theorem exists_step_for_arrival_interior {A B : List (List X)}
    {L S U : List X} {r : X}
    (hinv : Invariant color (A ++ L :: S :: U :: B))
    (hred : color r = Color.red)
    (hLblue : ∀ x ∈ L, color x = Color.blue)
    (hUblue : ∀ x ∈ U, color x = Color.blue)
    (hSred : ∀ x ∈ S, color x = Color.red)
    (hl₀ : ∃ l₀ ∈ L, l₀ < r) (hu₀ : ∃ u₀ ∈ U, r < u₀) :
    ∃ σ' scans, Step color (A ++ L :: S :: U :: B) r σ' ∧
      (∀ C ∈ scans, C ∈ A ++ L :: S :: U :: B) ∧
      (StepCharged color (A ++ L :: S :: U :: B) r scans ∨
       StepActivation color (A ++ L :: S :: U :: B) r scans) := by
  classical
  obtain ⟨l₀, hl₀L, hl₀r⟩ := hl₀
  obtain ⟨u₀, hu₀U, hu₀r⟩ := hu₀
  have hord : RunsOrdered (A ++ L :: S :: U :: B) := hinv.2.1
  have hLne : L ≠ [] := hinv.1 L (by simp)
  have hUne : U ≠ [] := hinv.1 U (by simp)
  have hSne : S ≠ [] := hinv.1 S (by simp)
  by_cases hbL : ∀ x ∈ L, x < r
  · by_cases haU : ∀ x ∈ U, r < x
    · -- both neighbours one-sided: dispatch on the candidate `S`
      by_cases hSsing : ∃ r₀, S = [r₀]
      · obtain ⟨r₀, hr₀⟩ := hSsing
        exact ⟨applyOp (A ++ [L]) (U :: B) S r (.mergePair r₀), [L, U],
          scan_activation_step (color := color) hord hr₀
            (hSred r₀ (by rw [hr₀]; simp))
            hLne hUne hbL haU,
          by intro C hC; simp at hC; rcases hC with rfl | rfl <;> simp,
          Or.inr ⟨r₀, Or.inl ⟨A, B, L, S, U, rfl, hr₀, hSred, hLblue, hUblue, hbL, haU, rfl⟩⟩⟩
      · by_cases hbS : ∀ x ∈ S, r < x
        · obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
            cases S with
            | nil => simp at hSne
            | cons x xs => exact ⟨x, by simp⟩
          exact ⟨applyOp (A ++ [L]) (U :: B) S r .insertInto, [L],
            scan_attach_below (color := color) hord hSred hLne hbL hs₀ (hbS s₀ hs₀),
            by intro C hC; simp at hC; rw [hC]; simp,
            Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨A, U :: B, L, S, rfl, hLblue, hbL, hbS, hSne, rfl⟩)))))⟩
        · by_cases haS : ∀ x ∈ S, x < r
          · have e : A ++ L :: S :: U :: B = (A ++ [L]) ++ S :: U :: B := by
              simp [List.append_assoc]
            obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
              cases S with
              | nil => simp at hSne
              | cons x xs => exact ⟨x, by simp⟩
            exact ⟨applyOp (A ++ [L]) (U :: B) S r .insertInto, [U],
              e ▸ scan_attach_above (color := color) (e ▸ hord) hSred hUne
                haU hs₀ (haS s₀ hs₀),
              by intro C hC; simp at hC; rw [hC]; simp,
              Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                ⟨A ++ [L], B, U, S, e, hUblue, haU, haS, hSne, rfl⟩)))))⟩
          · -- `r` straddles `S`: sorted insertion, no scan
            have e : (A ++ [L]) ++ S :: U :: B = A ++ L :: S :: U :: B := by
              simp [List.append_assoc]
            have hstep : Step color ((A ++ [L]) ++ S :: (U :: B)) r
                (applyOp (A ++ [L]) (U :: B) S r .insertInto) := by
              apply Step.insertInto
              · exact hSred
              · intro R hR x hx
                simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
                  or_false] at hR
                rcases hR with h | rfl
                · have hcross := (List.pairwise_append.mp hord).2.2
                  exact lt_trans (hcross R h L (by simp) x hx l₀ hl₀L) hl₀r
                · exact hbL x hx
              · intro T hT y hy
                simp only [List.mem_cons] at hT
                rcases hT with rfl | h
                · exact haU y hy
                · have e2 : A ++ L :: S :: U :: B
                      = (A ++ [L, S, U]) ++ B := by simp [List.append_assoc]
                  have hcross := (List.pairwise_append.mp (e2 ▸ hord)).2.2
                  exact lt_trans hu₀r (hcross U (by simp) T h u₀ hu₀U y hy)
            exact ⟨applyOp (A ++ [L]) (U :: B) S r .insertInto, [],
              e ▸ hstep, by intro C hC; simp at hC, Or.inl (Or.inl rfl)⟩
    · by_cases hbU : ∀ x ∈ U, x < r
      · exact absurd (hbU u₀ hu₀U) (not_lt.mpr (le_of_lt hu₀r))
      · -- `U` mixed: split it
        have hmixed : scanVerdict U r = ScanVerdict.mixed :=
          scanVerdict_mixed hbU haU
        have e : A ++ L :: S :: U :: B = (A ++ [L, S]) ++ U :: B := by
          simp [List.append_assoc]
        exact ⟨applyOp (A ++ [L, S]) B U r
            (.splitRun (belowPiece U r) (abovePiece U r)), [U],
          e ▸ scan_split_step (color := color) (e ▸ hord) hUblue hred hmixed,
          by intro C hC; simp at hC; rw [hC]; simp,
          Or.inl (Or.inr (Or.inl ⟨A ++ [L, S], B, U, e, hUblue, hmixed, rfl⟩))⟩
  · by_cases haL : ∀ x ∈ L, r < x
    · exact absurd (haL l₀ hl₀L) (not_lt.mpr (le_of_lt hl₀r))
    · -- `L` mixed: split it
      have hmixed : scanVerdict L r = ScanVerdict.mixed :=
        scanVerdict_mixed hbL haL
      exact ⟨applyOp A (S :: U :: B) L r
          (.splitRun (belowPiece L r) (abovePiece L r)), [L],
        scan_split_step (color := color) hord hLblue hred hmixed,
        by intro C hC; simp at hC; rw [hC]; simp,
        Or.inl (Or.inr (Or.inl ⟨A, S :: U :: B, L, rfl, hLblue, hmixed, rfl⟩))⟩

/-- Arrival at the left end: `C` is the first run, blue, and the
location certificate `r < c₀` for some `c₀ ∈ C` (the locate index
is `0`) excludes a one-sided-below verdict. A mixed verdict
splits `C`; a one-sided-above verdict is a creator scan, fresh
singleton before `C`. Every outcome is charged. -/
theorem exists_step_for_arrival_left {B : List (List X)}
    {C : List X} {r : X}
    (hinv : Invariant color (C :: B))
    (hred : color r = Color.red)
    (hblue : ∀ x ∈ C, color x = Color.blue)
    (hc₀ : ∃ c₀ ∈ C, r < c₀) :
    ∃ σ' scans, Step color (C :: B) r σ' ∧
      (∀ D ∈ scans, D ∈ C :: B) ∧
      StepCharged color (C :: B) r scans := by
  classical
  obtain ⟨c₀, hc₀C, hc₀r⟩ := hc₀
  have hord : RunsOrdered (C :: B) := hinv.2.1
  have hCne : C ≠ [] := hinv.1 C (by simp)
  by_cases hbC : ∀ x ∈ C, x < r
  · exact absurd (hbC c₀ hc₀C) (not_lt.mpr (le_of_lt hc₀r))
  · by_cases haC : ∀ x ∈ C, r < x
    · exact ⟨applyOp [] B C r .freshSingleton, [C],
        scan_fresh_step (color := color) hord hCne haC,
        by intro D hD; simp at hD; rw [hD]; simp,
        Or.inr (Or.inr (Or.inl ⟨B, C, rfl, hblue, haC, rfl⟩))⟩
    · have hmixed : scanVerdict C r = ScanVerdict.mixed :=
        scanVerdict_mixed hbC haC
      exact ⟨applyOp [] B C r (.splitRun (belowPiece C r) (abovePiece C r)),
        [C],
        scan_split_step (color := color) (A := []) (B := B) hord hblue hred hmixed,
        by intro D hD; simp at hD; rw [hD]; simp,
        Or.inr (Or.inl ⟨[], B, C, rfl, hblue, hmixed, rfl⟩)⟩

/-- Arrival at the right end: `C` is the last run, blue, and the
location certificate `c₀ < r` for some `c₀ ∈ C` (the locate index
is `q`, past the end) excludes a one-sided-above verdict. A mixed
verdict splits `C`; a one-sided-below verdict is a creator scan,
appended singleton after `C`. Every outcome is charged. -/
theorem exists_step_for_arrival_right {A : List (List X)}
    {C : List X} {r : X}
    (hinv : Invariant color (A ++ [C]))
    (hred : color r = Color.red)
    (hblue : ∀ x ∈ C, color x = Color.blue)
    (hc₀ : ∃ c₀ ∈ C, c₀ < r) :
    ∃ σ' scans, Step color (A ++ [C]) r σ' ∧
      (∀ D ∈ scans, D ∈ A ++ [C]) ∧
      StepCharged color (A ++ [C]) r scans := by
  classical
  obtain ⟨c₀, hc₀C, hc₀r⟩ := hc₀
  have hCne : C ≠ [] := hinv.1 C (by simp)
  by_cases haC : ∀ x ∈ C, r < x
  · exact absurd (haC c₀ hc₀C) (not_lt.mpr (le_of_lt hc₀r))
  · by_cases hbC : ∀ x ∈ C, x < r
    · have hA : ∀ R ∈ A, ∀ x ∈ R, x < r := by
        intro R hR x hx
        have hcross := (List.pairwise_append.mp hinv.2.1).2.2
        exact lt_trans (hcross R hR C (by simp) x hx c₀ hc₀C) hc₀r
      exact ⟨applyOp A [] C r .appendSingleton, [C],
        scan_append_step (color := color) hA hbC,
        by intro D hD; simp at hD; rw [hD]; simp,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨A, C, rfl, hblue, hbC, rfl⟩)))⟩
    · have hmixed : scanVerdict C r = ScanVerdict.mixed :=
        scanVerdict_mixed hbC haC
      have e : A ++ [C] = A ++ C :: [] := by simp
      exact ⟨applyOp A [] C r (.splitRun (belowPiece C r) (abovePiece C r)),
        [C],
        e ▸ scan_split_step (color := color) (e ▸ hinv.2.1) hblue hred hmixed,
        by intro D hD; simp at hD; rw [hD]; simp,
        Or.inr (Or.inl ⟨A, [], C, e, hblue, hmixed, rfl⟩)⟩

/-- Arrival at the left end with a candidate: the state is
`S :: C :: B` with `S` red, `C` blue, and the location
certificate `r < c₀` for some `c₀ ∈ C` excludes a
one-sided-below verdict on `C`. A mixed verdict splits `C`.
A one-sided-above verdict dispatches on `S`: a singleton
`[r₀]` with `r < r₀` merges (activation; with `r₀ < r`, `r`
attaches above and is itself a record); a one-sided `S`
attaches `r` at its near end; `r` below all of `S` starts a
fresh singleton with no scan; a straddling `S` absorbs `r`
with no scan. -/
theorem exists_step_for_arrival_left_candidate {B : List (List X)}
    {S C : List X} {r : X}
    (hinv : Invariant color (S :: C :: B))
    (hred : color r = Color.red) (hfresh : r ∉ (S :: C :: B).flatten)
    (hSred : ∀ x ∈ S, color x = Color.red)
    (hblue : ∀ x ∈ C, color x = Color.blue)
    (hc₀ : ∃ c₀ ∈ C, r < c₀) :
    ∃ σ' scans, Step color (S :: C :: B) r σ' ∧
      (∀ D ∈ scans, D ∈ S :: C :: B) ∧
      (StepCharged color (S :: C :: B) r scans ∨
       StepActivation color (S :: C :: B) r scans) := by
  classical
  obtain ⟨c₀, hc₀C, hc₀r⟩ := hc₀
  have hord : RunsOrdered (S :: C :: B) := hinv.2.1
  have hCne : C ≠ [] := hinv.1 C (by simp)
  have hSne : S ≠ [] := hinv.1 S (by simp)
  have hSC : ∀ x ∈ S, ∀ y ∈ C, x < y := (List.pairwise_cons.mp hord).1 C (by simp)
  have hcrossB : ∀ R ∈ [S, C], ∀ T' ∈ B, ∀ x ∈ R, ∀ y ∈ T', x < y := by
    have e : S :: C :: B = [S, C] ++ B := rfl
    exact (List.pairwise_append.mp (e ▸ hord)).2.2
  have hBr : ∀ T ∈ B, ∀ y ∈ T, r < y := by
    intro T hT y hy
    exact lt_trans hc₀r (hcrossB C (by simp) T hT c₀ hc₀C y hy)
  by_cases hbC : ∀ x ∈ C, x < r
  · exact absurd (hbC c₀ hc₀C) (not_lt.mpr (le_of_lt hc₀r))
  · by_cases haC : ∀ x ∈ C, r < x
    · by_cases hsing : ∃ r₀, S = [r₀]
      · obtain ⟨r₀, hr₀⟩ := hsing
        have hr₀C : ∀ y ∈ C, r₀ < y := fun y hy =>
          hSC r₀ (by rw [hr₀]; simp) y hy
        by_cases hlt : r < r₀
        · -- activation: merge with the founder, scan `C`
          have hstep : Step color ([] ++ S :: (C :: B)) r
              (applyOp [] (C :: B) S r (.mergePair r₀)) := by
            apply Step.mergePair
            · exact hr₀
            · exact hSred
            · intro R hR; simp at hR
            · intro T hT y hy
              simp only [List.mem_cons] at hT
              rcases hT with rfl | h
              · exact ⟨haC y hy, hr₀C y hy⟩
              · exact ⟨hBr T h y hy, lt_trans (hr₀C c₀ hc₀C)
                  (hcrossB C (by simp) T h c₀ hc₀C y hy)⟩
          refine ⟨applyOp [] (C :: B) S r (.mergePair r₀), [C], hstep,
            by intro D hD; simp at hD; rw [hD]; simp,
            Or.inr ⟨r₀, Or.inr (Or.inl ⟨B, S, C, rfl, hr₀, hSred, hblue, haC, hlt, rfl⟩)⟩⟩
        · have hr₀r : r₀ < r := by
            have hne : r ≠ r₀ := by
              intro hcon
              apply hfresh
              rw [hcon]
              exact List.mem_flatten.mpr ⟨S, by simp, by rw [hr₀]; simp⟩
            exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
          exact ⟨applyOp [] (C :: B) S r .insertInto, [C],
            scan_attach_above (color := color) (A := []) hord hSred hCne haC
              (s₀ := r₀) (by rw [hr₀]; simp) hr₀r,
            by intro D hD; simp at hD; rw [hD]; simp,
            Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨[], B, C, S, rfl, hblue, haC,
                fun x hx => by rw [hr₀] at hx; simp at hx; rw [hx]; exact hr₀r,
                hSne, rfl⟩)))))⟩
      · by_cases hbS : ∀ x ∈ S, r < x
        · -- below all of `S`: attach at the bottom of `S`, no scan
          obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
            cases S with
            | nil => simp at hSne
            | cons x xs => exact ⟨x, by simp⟩
          have hstep : Step color ([] ++ S :: (C :: B)) r
              (applyOp [] (C :: B) S r .insertInto) := by
            apply Step.insertInto
            · exact hSred
            · intro R hR; simp at hR
            · intro T hT y hy
              simp only [List.mem_cons] at hT
              rcases hT with rfl | h
              · exact lt_trans (hbS s₀ hs₀) (hSC s₀ hs₀ y hy)
              · exact hBr T h y hy
          exact ⟨applyOp [] (C :: B) S r .insertInto, [], hstep,
            by intro D hD; simp at hD, Or.inl (Or.inl rfl)⟩
        · by_cases haS : ∀ x ∈ S, x < r
          · obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
              cases S with
              | nil => simp at hSne
              | cons x xs => exact ⟨x, by simp⟩
            exact ⟨applyOp [] (C :: B) S r .insertInto, [C],
              scan_attach_above (color := color) (A := []) hord hSred hCne
                haC hs₀ (haS s₀ hs₀),
              by intro D hD; simp at hD; rw [hD]; simp,
              Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                ⟨[], B, C, S, rfl, hblue, haC, haS, hSne, rfl⟩)))))⟩
          · -- straddling `S`: sorted insertion, no scan
            have hstep : Step color ([] ++ S :: (C :: B)) r
                (applyOp [] (C :: B) S r .insertInto) := by
              apply Step.insertInto
              · exact hSred
              · intro R hR; simp at hR
              · intro T hT y hy
                simp only [List.mem_cons] at hT
                rcases hT with rfl | h
                · exact haC y hy
                · exact hBr T h y hy
            exact ⟨applyOp [] (C :: B) S r .insertInto, [], hstep,
              by intro D hD; simp at hD, Or.inl (Or.inl rfl)⟩
    · have hmixed : scanVerdict C r = ScanVerdict.mixed :=
        scanVerdict_mixed hbC haC
      exact ⟨applyOp [S] B C r (.splitRun (belowPiece C r) (abovePiece C r)),
        [C],
        scan_split_step (color := color) (A := [S]) (B := B) hord hblue hred
          hmixed,
        by intro D hD; simp at hD; rw [hD]; simp,
        Or.inl (Or.inr (Or.inl ⟨[S], B, C, rfl, hblue, hmixed, rfl⟩))⟩

/-- Arrival at the right end with a candidate: the state is
`A ++ [C, S]` with `C` blue, `S` red, and the location
certificate `c₀ < r` for some `c₀ ∈ C` excludes a
one-sided-above verdict on `C`. Mirror of the left candidate:
a mixed verdict splits `C`; a one-sided-below verdict dispatches
on `S` (singleton activation when `r₀ < r`, merger when
`r < r₀`, attach at the near end, append past everything, or
absorb with no scan). -/
theorem exists_step_for_arrival_right_candidate {A : List (List X)}
    {C S : List X} {r : X}
    (hinv : Invariant color (A ++ [C, S]))
    (hred : color r = Color.red) (hfresh : r ∉ (A ++ [C, S]).flatten)
    (hSred : ∀ x ∈ S, color x = Color.red)
    (hblue : ∀ x ∈ C, color x = Color.blue)
    (hc₀ : ∃ c₀ ∈ C, c₀ < r) :
    ∃ σ' scans, Step color (A ++ [C, S]) r σ' ∧
      (∀ D ∈ scans, D ∈ A ++ [C, S]) ∧
      (StepCharged color (A ++ [C, S]) r scans ∨
       StepActivation color (A ++ [C, S]) r scans) := by
  classical
  obtain ⟨c₀, hc₀C, hc₀r⟩ := hc₀
  have hord : RunsOrdered (A ++ [C, S]) := hinv.2.1
  have hCne : C ≠ [] := hinv.1 C (by simp)
  have hSne : S ≠ [] := hinv.1 S (by simp)
  have heq : A ++ [C, S] = A ++ C :: S :: [] := by simp
  by_cases haC : ∀ x ∈ C, r < x
  · exact absurd (haC c₀ hc₀C) (not_lt.mpr (le_of_lt hc₀r))
  · by_cases hbC : ∀ x ∈ C, x < r
    · by_cases hsing : ∃ r₀, S = [r₀]
      · obtain ⟨r₀, hr₀⟩ := hsing
        by_cases hlt : r₀ < r
        · -- activation: merge with the founder, scan `C`
          have hcross2 : ∀ R ∈ A ++ [C], ∀ T ∈ S :: [], ∀ x ∈ R, ∀ y ∈ T,
              x < y :=
            (List.pairwise_append.mp (show RunsOrdered ((A ++ [C]) ++ S :: [])
              from by simpa using hord)).2.2
          have hc₀r₀ : c₀ < r₀ := hcross2 C (by simp) S (by simp) c₀ hc₀C r₀
            (by rw [hr₀]; simp)
          have hstep : Step color ((A ++ [C]) ++ S :: []) r
              (applyOp (A ++ [C]) [] S r (.mergePair r₀)) := by
            apply Step.mergePair
            · exact hr₀
            · exact hSred
            · intro R hR x hx
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
                or_false] at hR
              rcases hR with h | rfl
              · have hcross := (List.pairwise_append.mp hord).2.2
                exact ⟨lt_trans (hcross R h C (by simp) x hx c₀ hc₀C) hc₀r,
                  lt_trans (hcross R h C (by simp) x hx c₀ hc₀C) hc₀r₀⟩
              · exact ⟨hbC x hx, hcross2 R (by simp) S (by simp) x hx r₀
                  (by rw [hr₀]; simp)⟩
            · intro T hT; simp at hT
          refine ⟨applyOp (A ++ [C]) [] S r (.mergePair r₀), [C], ?_,
            by intro D hD; simp at hD; rw [hD]; simp,
            Or.inr ⟨r₀, Or.inr (Or.inr ⟨A, C, S, rfl, hr₀, hSred, hblue, hbC, hlt,
              rfl⟩)⟩⟩
          rwa [show (A ++ [C]) ++ S :: [] = A ++ [C, S] by simp] at hstep
        · have hrr₀ : r < r₀ := by
            have hne : r ≠ r₀ := by
              intro hcon
              apply hfresh
              rw [hcon]
              exact List.mem_flatten.mpr ⟨S, by simp, by rw [hr₀]; simp⟩
            exact lt_of_le_of_ne (le_of_not_gt hlt) hne
          exact ⟨applyOp (A ++ [C]) [] S r .insertInto, [C],
            scan_attach_below (color := color) (A := A) (B := []) hord
              hSred hCne hbC (s₀ := r₀) (by rw [hr₀]; simp) hrr₀,
            by intro D hD; simp at hD; rw [hD]; simp,
            Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              ⟨A, [], C, S, heq, hblue, hbC,
                fun x hx => by rw [hr₀] at hx; simp at hx; rw [hx]; exact hrr₀,
                hSne, rfl⟩)))))⟩
      · by_cases haS : ∀ x ∈ S, x < r
        · -- above all of `S`: attach at the top of `S`, no scan
          have hAr : ∀ R ∈ A, ∀ x ∈ R, x < r := by
            intro R hR x hx
            have hcross := (List.pairwise_append.mp hord).2.2
            exact lt_trans (hcross R hR C (by simp) x hx c₀ hc₀C) hc₀r
          have hstep : Step color ((A ++ [C]) ++ S :: []) r
              (applyOp (A ++ [C]) [] S r .insertInto) := by
            apply Step.insertInto
            · exact hSred
            · intro R hR x hx
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
                or_false] at hR
              rcases hR with h | rfl
              · exact hAr R h x hx
              · exact hbC x hx
            · intro T hT; simp at hT
          refine ⟨applyOp (A ++ [C]) [] S r .insertInto, [], ?_,
            by intro D hD; simp at hD, Or.inl (Or.inl rfl)⟩
          rwa [show (A ++ [C]) ++ S :: [] = A ++ [C, S] by simp] at hstep
        · by_cases hbS : ∀ x ∈ S, r < x
          · obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
              cases S with
              | nil => simp at hSne
              | cons x xs => exact ⟨x, by simp⟩
            exact ⟨applyOp (A ++ [C]) [] S r .insertInto, [C],
              scan_attach_below (color := color) (A := A) (B := []) hord
                hSred hCne hbC hs₀ (hbS s₀ hs₀),
              by intro D hD; simp at hD; rw [hD]; simp,
              Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨A, [], C, S, heq, hblue, hbC, hbS, hSne, rfl⟩)))))⟩
          · -- straddling `S`: sorted insertion, no scan
            have hAr : ∀ R ∈ A, ∀ x ∈ R, x < r := by
              intro R hR x hx
              have hcross := (List.pairwise_append.mp hord).2.2
              exact lt_trans (hcross R hR C (by simp) x hx c₀ hc₀C) hc₀r
            have hstep : Step color ((A ++ [C]) ++ S :: []) r
                (applyOp (A ++ [C]) [] S r .insertInto) := by
              apply Step.insertInto
              · exact hSred
              · intro R hR x hx
                simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
                  or_false] at hR
                rcases hR with h | rfl
                · exact hAr R h x hx
                · exact hbC x hx
              · intro T hT; simp at hT
            refine ⟨applyOp (A ++ [C]) [] S r .insertInto, [], ?_,
              by intro D hD; simp at hD, Or.inl (Or.inl rfl)⟩
            rwa [show (A ++ [C]) ++ S :: [] = A ++ [C, S] by simp] at hstep
    · have hmixed : scanVerdict C r = ScanVerdict.mixed :=
        scanVerdict_mixed hbC haC
      exact ⟨applyOp A [S] C r (.splitRun (belowPiece C r) (abovePiece C r)),
        [C],
        scan_split_step (color := color) (A := A) (B := [S]) hord
          hblue hred hmixed,
        by intro D hD; simp at hD; rw [hD]; simp,
        Or.inl (Or.inr (Or.inl ⟨A, [S], C, rfl, hblue, hmixed, rfl⟩))⟩

/-- Decomposition of a state around a fresh red arrival `r`:
either there is no blue run at all, or the state has one of the
five located forms the arrival lemmas consume. The located blue
run is found by scanning from the left: the first blue run with
an element above `r` is the upper neighbour; the blue run before
it (if any) has an element below `r`. Proved by induction on the
run list, lifting each configuration through the head run;
alternation excludes the two impossible adjacencies (blue next
to blue, red next to red where a candidate already sits). -/
theorem decompose_state {r : X} (hred : color r = Color.red) :
    ∀ {σ : List (List X)}, Invariant color σ → MonoRuns color σ →
      AltRuns color σ →
      (∀ R ∈ σ, ∀ x ∈ R, color x = Color.red) ∨
      (∃ B C, σ = C :: B ∧ (∀ x ∈ C, color x = Color.blue) ∧
        ∃ c₀ ∈ C, r < c₀) ∨
      (∃ B S C, σ = S :: C :: B ∧ (∀ x ∈ S, color x = Color.red) ∧
        (∀ x ∈ C, color x = Color.blue) ∧ ∃ c₀ ∈ C, r < c₀) ∨
      (∃ A C, σ = A ++ [C] ∧ (∀ x ∈ C, color x = Color.blue) ∧
        ∃ c₀ ∈ C, c₀ < r) ∨
      (∃ A C S, σ = A ++ [C, S] ∧ (∀ x ∈ C, color x = Color.blue) ∧
        (∀ x ∈ S, color x = Color.red) ∧ ∃ c₀ ∈ C, c₀ < r) ∨
      (∃ A B L S U, σ = A ++ L :: S :: U :: B ∧
        (∀ x ∈ L, color x = Color.blue) ∧
        (∀ x ∈ S, color x = Color.red) ∧
        (∀ x ∈ U, color x = Color.blue) ∧
        (∃ l₀ ∈ L, l₀ < r) ∧ ∃ u₀ ∈ U, r < u₀) := by
  intro σ
  induction σ with
  | nil =>
      intro _ _ _
      exact Or.inl (by intro R hR; simp at hR)
  | cons R rest ih =>
      intro hinv hmono halt
      have hinv' : Invariant color rest :=
        ⟨fun T hT => hinv.1 T (List.mem_cons_of_mem R hT),
         (List.pairwise_cons.mp hinv.2.1).2,
         fun T hT => hinv.2.2 T (List.mem_cons_of_mem R hT)⟩
      have hmono' : MonoRuns color rest :=
        fun T hT => hmono T (List.mem_cons_of_mem R hT)
      have halt' : AltRuns color rest := by
        cases rest with
        | nil => exact AltRuns.nil
        | cons T rest' =>
            cases halt with
            | cons _ ht => exact ht
      have hRne : R ≠ [] := hinv.1 R (by simp)
      obtain ⟨d₀, hd₀⟩ : ∃ d₀, d₀ ∈ R := by
        cases R with
        | nil => simp at hRne
        | cons x xs => exact ⟨x, by simp⟩
      rcases ih hinv' hmono' halt' with h | h | h | h | h | h
      · -- rest has no blue run
        rcases hmono R (by simp) with hRred | hRblue
        · exact Or.inl (by
            intro T hT x hx
            simp only [List.mem_cons] at hT
            rcases hT with rfl | hT
            · exact hRred x hx
            · exact h T hT x hx)
        · have hne : d₀ ≠ r := by
            intro hcon
            have h1 : color d₀ = Color.red := by rw [hcon]; exact hred
            rw [hRblue d₀ hd₀] at h1
            exact Color.noConfusion h1
          cases lt_or_gt_of_ne hne with
          | inl hd =>
              -- `d₀ < r`: `R` is the last blue run; what follows is red
              cases rest with
              | nil =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl
                    ⟨[], R, by simp, hRblue, ⟨d₀, hd₀, hd⟩⟩)))
              | cons S rest' =>
                  have hSred : ∀ x ∈ S, color x = Color.red :=
                    h S (by simp)
                  cases rest' with
                  | nil =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                        ⟨[], R, S, by simp, hRblue, hSred, ⟨d₀, hd₀, hd⟩⟩))))
                  | cons S2 rest'' =>
                      have hSne : S ≠ [] := hinv.1 S (by simp)
                      obtain ⟨s₁, hs₁⟩ : ∃ s₁, s₁ ∈ S := by
                        cases S with
                        | nil => simp at hSne
                        | cons x xs => exact ⟨x, by simp⟩
                      have hS2ne : S2 ≠ [] := hinv.1 S2 (by simp)
                      obtain ⟨s₂, hs₂⟩ : ∃ s₂, s₂ ∈ S2 := by
                        cases S2 with
                        | nil => simp at hS2ne
                        | cons x xs => exact ⟨x, by simp⟩
                      have hseam := alt_seam (color := color) (A := [R]) halt
                        s₁ hs₁ s₂ hs₂
                      rw [h S (by simp) s₁ hs₁,
                        h S2 (by simp) s₂ hs₂] at hseam
                      exact (hseam rfl).elim
          | inr hd =>
              exact Or.inr (Or.inl ⟨rest, R, rfl, hRblue, ⟨d₀, hd₀, hd⟩⟩)
      · -- rest starts with the located blue run
        obtain ⟨B, C, hrest, hblue, c₀, hc₀, hc₀r⟩ := h
        rcases hmono R (by simp) with hRred | hRblue
        · exact Or.inr (Or.inr (Or.inl
            ⟨B, R, C, (congrArg (fun l => R :: l) hrest), hRred, hblue, ⟨c₀, hc₀, hc₀r⟩⟩))
        · have hne : d₀ ≠ r := by
            intro hcon
            have h1 : color d₀ = Color.red := by rw [hcon]; exact hred
            rw [hRblue d₀ hd₀] at h1
            exact Color.noConfusion h1
          cases lt_or_gt_of_ne hne with
          | inl hd =>
              have halt2 : AltRuns color (R :: C :: B) := hrest ▸ halt
              have hseam := alt_seam (color := color) (A := []) halt2 d₀ hd₀
                c₀ hc₀
              rw [hRblue d₀ hd₀, hblue c₀ hc₀] at hseam
              exact (hseam rfl).elim
          | inr hd =>
              exact Or.inr (Or.inl
                ⟨C :: B, R, (congrArg (fun l => R :: l) hrest), hRblue, ⟨d₀, hd₀, hd⟩⟩)
      · -- rest starts with a candidate then the located blue run
        obtain ⟨B, S, C, hrest, hSred, hblue, c₀, hc₀, hc₀r⟩ := h
        rcases hmono R (by simp) with hRred | hRblue
        · have halt2 : AltRuns color (R :: S :: C :: B) := hrest ▸ halt
          have hSne : S ≠ [] := hinv.1 S (by rw [hrest]; simp)
          obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
            cases S with
            | nil => simp at hSne
            | cons x xs => exact ⟨x, by simp⟩
          have hseam := alt_seam (color := color) (A := []) halt2 d₀ hd₀
            s₀ hs₀
          rw [hRred d₀ hd₀, hSred s₀ hs₀] at hseam
          exact (hseam rfl).elim
        · have hne : d₀ ≠ r := by
            intro hcon
            have h1 : color d₀ = Color.red := by rw [hcon]; exact hred
            rw [hRblue d₀ hd₀] at h1
            exact Color.noConfusion h1
          cases lt_or_gt_of_ne hne with
          | inl hd =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                ⟨[], B, R, S, C, (congrArg (fun l => R :: l) hrest), hRblue, hSred, hblue,
                  ⟨d₀, hd₀, hd⟩, ⟨c₀, hc₀, hc₀r⟩⟩))))
          | inr hd =>
              exact Or.inr (Or.inl
                ⟨S :: C :: B, R, (congrArg (fun l => R :: l) hrest), hRblue, ⟨d₀, hd₀, hd⟩⟩)
      · -- rest ends with the located blue run
        obtain ⟨A, C, hrest, hblue, c₀, hc₀, hc₀r⟩ := h
        exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨R :: A, C, (congrArg (fun l => R :: l) hrest), hblue, ⟨c₀, hc₀, hc₀r⟩⟩)))
      · -- rest ends with the located blue run and a candidate
        obtain ⟨A, C, S, hrest, hblue, hSred, c₀, hc₀, hc₀r⟩ := h
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨R :: A, C, S, (congrArg (fun l => R :: l) hrest), hblue, hSred, ⟨c₀, hc₀, hc₀r⟩⟩))))
      · -- rest has an interior located gap
        obtain ⟨A, B, L, S, U, hrest, hLblue, hSred, hUblue, hl, hu⟩ := h
        obtain ⟨l₀, hl₀, hl₀r⟩ := hl
        obtain ⟨u₀, hu₀, hu₀r⟩ := hu
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨R :: A, B, L, S, U, (congrArg (fun l => R :: l) hrest), hLblue, hSred, hUblue,
            ⟨l₀, hl₀, hl₀r⟩, ⟨u₀, hu₀, hu₀r⟩⟩))))

/-- Every run is internally sorted (in increasing order). This
holds initially for the single blue run and is preserved by the
produced steps: split pieces are filters of a sorted run, merged
pairs are ordered by construction, and sorted insertion preserves
sortedness. It is the internal half of the final output lemma. -/
def RunsInternallySorted (color : X → Color) (σ : List (List X)) : Prop :=
  ∀ R ∈ σ, R.Pairwise (· ≤ ·)

/-- A produced operation at a decomposition preserves internal
sortedness, provided split pieces are sublists of the split run
(the produced splits are the two filters `belowPiece` and
`abovePiece`). -/
theorem runsInternallySorted_applyOp {A B : List (List X)}
    {S : List X} {r : X} (op : InsertOp X)
    (hsrt : RunsInternallySorted color (A ++ S :: B))
    (hsub : ∀ below above : List X, op = InsertOp.splitRun below above →
      below.Sublist S ∧ above.Sublist S) :
    RunsInternallySorted color (applyOp A B S r op) := by
  have hA : RunsInternallySorted color A := fun R hR =>
    hsrt R (List.mem_append.mpr (Or.inl hR))
  have hS : S.Pairwise (· ≤ ·) :=
    hsrt S (by simp)
  have hB : RunsInternallySorted color B := fun R hR =>
    hsrt R (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem S hR)))
  intro R hR
  cases op with
  | freshSingleton =>
      simp only [applyOp, List.mem_append, List.mem_cons] at hR
      rcases hR with h | rfl | rfl | h
      · exact hA R h
      · simp
      · exact hS
      · exact hB R h
  | appendSingleton =>
      simp only [applyOp, List.mem_append, List.mem_cons] at hR
      rcases hR with (h1 | rfl | h2) | h
      · exact hA R h1
      · exact hS
      · exact hB R h2
      · have hRr : R = [r] := by simpa using h
        rw [hRr]; simp
  | mergePair r₀ =>
      simp only [applyOp, List.mem_append, List.mem_cons] at hR
      rcases hR with h | rfl | h
      · exact hA R h
      · split_ifs with hh
        · exact List.Pairwise.cons
            (fun y hy => by
              simp only [List.mem_singleton] at hy
              rw [hy]; exact le_of_lt hh) (by simp)
        · exact List.Pairwise.cons
            (fun y hy => by
              simp only [List.mem_singleton] at hy
              rw [hy]; exact le_of_not_gt hh) (by simp)
      · exact hB R h
  | insertInto =>
      simp only [applyOp, List.mem_append, List.mem_cons] at hR
      rcases hR with h | rfl | h
      · exact hA R h
      · exact insertSorted_pairwise hS
      · exact hB R h
  | splitRun below above =>
      obtain ⟨hbl, hab⟩ := hsub below above rfl
      simp only [applyOp, List.mem_append, List.mem_cons] at hR
      rcases hR with h | rfl | rfl | rfl | h
      · exact hA R h
      · exact List.Pairwise.sublist hbl hS
      · simp
      · exact List.Pairwise.sublist hab hS
      · exact hB R h

/-- Full arrival dispatch: in a state with invariant, mono runs,
alternation, and at least one blue run, a fresh red arrival `r`
has a step whose scans are charged or an activation, and the new
state still alternates. This is `decompose_state` followed by
the case analysis of the arrival lemmas, with `alt_*`
preservation at each produced form. -/

theorem exists_step_for_arrival_full {σ : List (List X)} {r : X}
    (hinv : Invariant color σ) (hmono : MonoRuns color σ)
    (halt : AltRuns color σ)
    (hred : color r = Color.red) (hfresh : r ∉ σ.flatten)
    (hblue0 : ∃ C ∈ σ, ∀ x ∈ C, color x = Color.blue)
    (hsrt : RunsInternallySorted color σ) :
    ∃ σ' scans, RunsInternallySorted color σ' ∧ Step color σ r σ' ∧
      (∀ C ∈ scans, C ∈ σ) ∧
      StepStrong color σ r σ' scans ∧
      AltRuns color σ' := by
  classical
  rcases decompose_state (color := color) hred hinv hmono halt with
    h | h | h | h | h | h
  · -- no blue run: contradicts the blue-run hypothesis
    obtain ⟨C, hC, hblue⟩ := hblue0
    obtain ⟨x, hx⟩ : ∃ x, x ∈ C := by
      have hne : C ≠ [] := hinv.1 C hC
      cases C with
      | nil => simp at hne
      | cons y ys => exact ⟨y, by simp⟩
    have hbx := hblue x hx
    rw [h C hC x hx] at hbx
    have hfalse : False := Color.noConfusion hbx
    exact hfalse.elim
  · -- left end: `σ = C :: B`
    obtain ⟨B, C, hσ, hblue, c₀, hc₀, hc₀r⟩ := h
    have hinv2 : Invariant color (C :: B) := hσ ▸ hinv
    have halt2 : AltRuns color (C :: B) := hσ ▸ halt
    have hf2 : r ∉ (C :: B).flatten := hσ ▸ hfresh
    have hord : RunsOrdered (C :: B) := hinv2.2.1
    have hCne : C ≠ [] := hinv2.1 C (by simp)
    by_cases hbC : ∀ x ∈ C, x < r
    · exact absurd (hbC c₀ hc₀) (not_lt.mpr (le_of_lt hc₀r))
    · by_cases haC : ∀ x ∈ C, r < x
      · refine ⟨applyOp [] B C r .freshSingleton, [C], ?_, ?_, ?_, ?_, ?_⟩
        · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
          · have hsrt2 := hsrt
            rw [hσ] at hsrt2
            simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
          · intro below above hop
            cases hop
        · rw [hσ]
          exact scan_fresh_step (color := color) hord hCne haC
        · intro D hD
          simp at hD
          rw [hD, hσ]
          simp
        · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨B, C, hσ, hblue, haC, rfl⟩)))
        · exact alt_fresh_left (color := color) hblue hred halt2
      · have hmixed : scanVerdict C r = ScanVerdict.mixed :=
          scanVerdict_mixed hbC haC
        have hne : ∀ x ∈ C, x ≠ r := by
          intro x hx hcon
          have h1 : color r = Color.blue := by rw [← hcon]; exact hblue x hx
          rw [hred] at h1
          exact Color.noConfusion h1
        obtain ⟨⟨c₂, hc₂C, hc₂r⟩, ⟨c₁, hc₁C, hc₁r⟩⟩ := exists_of_mixed hne hmixed
        refine ⟨applyOp [] B C r (.splitRun (belowPiece C r) (abovePiece C r)),
          [C], ?_, ?_, ?_, ?_, ?_⟩
        · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
          · have hsrt2 := hsrt
            rw [hσ] at hsrt2
            simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
          · intro below above hop
            injection hop with h1 h2
            subst h1
            subst h2
            exact ⟨List.filter_sublist, List.filter_sublist⟩
        · rw [hσ]
          exact scan_split_step (color := color) (A := []) (B := B) hord
            hblue hred hmixed
        · intro D hD
          simp at hD
          rw [hD, hσ]
          simp
        · exact Or.inl (Or.inr (Or.inl ⟨[], B, C, hσ, hblue, hmixed, rfl⟩))
        · exact alt_split_run (color := color)
            (fun x hx => (belowPiece_mem hx).1)
            (fun x hx => (abovePiece_mem hx).1) hblue hred
            (List.ne_nil_of_mem (show c₁ ∈ belowPiece C r by
              simp [belowPiece, List.mem_filter, hc₁C, hc₁r]))
            (List.ne_nil_of_mem (show c₂ ∈ abovePiece C r by
              simp [abovePiece, List.mem_filter, hc₂C, hc₂r])) halt2
  · -- left candidate: `σ = S :: C :: B`
    obtain ⟨B, S, C, hσ, hSred, hblue, c₀, hc₀, hc₀r⟩ := h
    have hinv2 : Invariant color (S :: C :: B) := hσ ▸ hinv
    have hmono2 : MonoRuns color (S :: C :: B) := hσ ▸ hmono
    have halt2 : AltRuns color (S :: C :: B) := hσ ▸ halt
    have hf2 : r ∉ (S :: C :: B).flatten := hσ ▸ hfresh
    have hord : RunsOrdered (S :: C :: B) := hinv2.2.1
    have hCne : C ≠ [] := hinv2.1 C (by simp)
    have hSne : S ≠ [] := hinv2.1 S (by simp)
    have hSC : ∀ x ∈ S, ∀ y ∈ C, x < y := (List.pairwise_cons.mp hord).1 C (by simp)
    have hcrossB : ∀ R ∈ [S, C], ∀ T' ∈ B, ∀ x ∈ R, ∀ y ∈ T', x < y := by
      have e : S :: C :: B = [S, C] ++ B := rfl
      exact (List.pairwise_append.mp (e ▸ hord)).2.2
    have hBr : ∀ T ∈ B, ∀ y ∈ T, r < y := by
      intro T hT y hy
      exact lt_trans hc₀r (hcrossB C (by simp) T hT c₀ hc₀ y hy)
    by_cases hbC : ∀ x ∈ C, x < r
    · exact absurd (hbC c₀ hc₀) (not_lt.mpr (le_of_lt hc₀r))
    · by_cases haC : ∀ x ∈ C, r < x
      · by_cases hsing : ∃ r₀, S = [r₀]
        · obtain ⟨r₀, hr₀⟩ := hsing
          have hr₀C : ∀ y ∈ C, r₀ < y := fun y hy =>
            hSC r₀ (by rw [hr₀]; simp) y hy
          by_cases hlt : r < r₀
          · -- activation at the left end
            have hstep : Step color (S :: C :: B) r
                (applyOp [] (C :: B) S r (.mergePair r₀)) := by
              show Step color ([] ++ S :: (C :: B)) r
                (applyOp [] (C :: B) S r (.mergePair r₀))
              apply Step.mergePair
              · exact hr₀
              · exact hSred
              · intro R hR; simp at hR
              · intro T hT y hy
                simp only [List.mem_cons] at hT
                rcases hT with rfl | h
                · exact ⟨haC y hy, hr₀C y hy⟩
                · exact ⟨hBr T h y hy, lt_trans (hr₀C c₀ hc₀)
                    (hcrossB C (by simp) T h c₀ hc₀ y hy)⟩
            refine ⟨applyOp [] (C :: B) S r (.mergePair r₀), [C], ?_, ?_, ?_,
              ?_, ?_⟩
            · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
              · have hsrt2 := hsrt
                rw [hσ] at hsrt2
                simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
              · intro below above hop
                cases hop
            · rw [hσ]; exact hstep
            · intro D hD
              simp at hD
              rw [hD, hσ]
              simp
            · exact Or.inr ⟨r₀, Or.inr (Or.inl
                ⟨B, S, C, hσ, hr₀, hSred, hblue, haC, hlt, rfl⟩),
                ⟨if r < r₀ then [r, r₀] else [r₀, r], by simp [applyOp],
                  by split_ifs <;> simp, by split_ifs <;> simp⟩⟩
            · have hr₀red : color r₀ = Color.red :=
                hSred r₀ (by rw [hr₀]; simp)
              have hT : ∀ x ∈ (if r < r₀ then [r, r₀] else [r₀, r]),
                  ∀ y ∈ S, color x = color y := by
                intro x hx y hy
                rw [hr₀] at hy
                simp only [List.mem_singleton] at hy
                rw [hy, hr₀red]
                split_ifs at hx <;>
                  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                    or_false] at hx <;>
                  rcases hx with rfl | rfl <;>
                  first | exact hred | exact hr₀red
              exact alt_replace_run (color := color) hT hSne
                (by split_ifs with hh <;> intro h <;> cases h) halt2
          · have hr₀r : r₀ < r := by
              have hne : r ≠ r₀ := by
                intro hcon
                apply hf2
                rw [hcon]
                exact List.mem_flatten.mpr ⟨S, by simp, by rw [hr₀]; simp⟩
              exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
            refine ⟨applyOp [] (C :: B) S r .insertInto, [C], ?_, ?_, ?_, ?_, ?_⟩
            · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
              · have hsrt2 := hsrt
                rw [hσ] at hsrt2
                simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
              · intro below above hop
                cases hop
            · rw [hσ]
              exact scan_attach_above (color := color) (A := []) hord hSred
                hCne haC (s₀ := r₀) (by rw [hr₀]; simp) hr₀r
            · intro D hD
              simp at hD
              rw [hD, hσ]
              simp
            · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                ⟨[], B, C, S, hσ, hblue, haC,
                  fun x hx => by
                    rw [hr₀] at hx
                    simp at hx
                    rw [hx]
                    exact hr₀r,
                  hSne, rfl⟩)))))
            · have hT : ∀ x ∈ insertSorted r S, ∀ y ∈ S,
                  color x = color y := by
                intro x hx y hy
                rw [insertSorted_mem] at hx
                rcases hx with rfl | hx
                · rw [hred, hSred y hy]
                · rw [hSred x hx, hSred y hy]
              exact alt_replace_run (color := color) hT hSne
                insertSorted_ne_nil halt2
        · by_cases hbS : ∀ x ∈ S, r < x
          · obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
              cases S with
              | nil => simp at hSne
              | cons x xs => exact ⟨x, by simp⟩
            have hstep : Step color (S :: C :: B) r
                (applyOp [] (C :: B) S r .insertInto) := by
              show Step color ([] ++ S :: (C :: B)) r
                (applyOp [] (C :: B) S r .insertInto)
              apply Step.insertInto
              · exact hSred
              · intro R hR; simp at hR
              · intro T hT y hy
                simp only [List.mem_cons] at hT
                rcases hT with rfl | h
                · exact lt_trans (hbS s₀ hs₀) (hSC s₀ hs₀ y hy)
                · exact hBr T h y hy
            refine ⟨applyOp [] (C :: B) S r .insertInto, [], ?_, ?_, ?_, ?_, ?_⟩
            · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
              · have hsrt2 := hsrt
                rw [hσ] at hsrt2
                simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
              · intro below above hop
                cases hop
            · rw [hσ]; exact hstep
            · intro D hD; simp at hD
            · exact Or.inl (Or.inl rfl)
            · have hT : ∀ x ∈ insertSorted r S, ∀ y ∈ S,
                  color x = color y := by
                intro x hx y hy
                rw [insertSorted_mem] at hx
                rcases hx with rfl | hx
                · rw [hred, hSred y hy]
                · rw [hSred x hx, hSred y hy]
              exact alt_replace_run (color := color) hT hSne
                insertSorted_ne_nil halt2
          · by_cases haS : ∀ x ∈ S, x < r
            · obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
                cases S with
                | nil => simp at hSne
                | cons x xs => exact ⟨x, by simp⟩
              refine ⟨applyOp [] (C :: B) S r .insertInto, [C], ?_, ?_, ?_,
                ?_, ?_⟩
              · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
                · have hsrt2 := hsrt
                  rw [hσ] at hsrt2
                  simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
                · intro below above hop
                  cases hop
              · rw [hσ]
                exact scan_attach_above (color := color) (A := []) hord hSred
                  hCne haC hs₀ (haS s₀ hs₀)
              · intro D hD
                simp at hD
                rw [hD, hσ]
                simp
              · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨[], B, C, S, hσ, hblue, haC, haS, hSne, rfl⟩)))))
              · have hT : ∀ x ∈ insertSorted r S, ∀ y ∈ S,
                    color x = color y := by
                  intro x hx y hy
                  rw [insertSorted_mem] at hx
                  rcases hx with rfl | hx
                  · rw [hred, hSred y hy]
                  · rw [hSred x hx, hSred y hy]
                exact alt_replace_run (color := color) hT hSne
                  insertSorted_ne_nil halt2
            · have hstep : Step color (S :: C :: B) r
                  (applyOp [] (C :: B) S r .insertInto) := by
                show Step color ([] ++ S :: (C :: B)) r
                  (applyOp [] (C :: B) S r .insertInto)
                apply Step.insertInto
                · exact hSred
                · intro R hR; simp at hR
                · intro T hT y hy
                  simp only [List.mem_cons] at hT
                  rcases hT with rfl | h
                  · exact haC y hy
                  · exact hBr T h y hy
              refine ⟨applyOp [] (C :: B) S r .insertInto, [], ?_, ?_, ?_, ?_, ?_⟩
              · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
                · have hsrt2 := hsrt
                  rw [hσ] at hsrt2
                  simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
                · intro below above hop
                  cases hop
              · rw [hσ]; exact hstep
              · intro D hD; simp at hD
              · exact Or.inl (Or.inl rfl)
              · have hT : ∀ x ∈ insertSorted r S, ∀ y ∈ S,
                    color x = color y := by
                  intro x hx y hy
                  rw [insertSorted_mem] at hx
                  rcases hx with rfl | hx
                  · rw [hred, hSred y hy]
                  · rw [hSred x hx, hSred y hy]
                exact alt_replace_run (color := color) hT hSne
                  insertSorted_ne_nil halt2
      · have hmixed : scanVerdict C r = ScanVerdict.mixed :=
          scanVerdict_mixed hbC haC
        have hne : ∀ x ∈ C, x ≠ r := by
          intro x hx hcon
          have h1 : color r = Color.blue := by rw [← hcon]; exact hblue x hx
          rw [hred] at h1
          exact Color.noConfusion h1
        obtain ⟨⟨c₂, hc₂C, hc₂r⟩, ⟨c₁, hc₁C, hc₁r⟩⟩ := exists_of_mixed hne hmixed
        refine ⟨applyOp [S] B C r (.splitRun (belowPiece C r) (abovePiece C r)),
          [C], ?_, ?_, ?_, ?_, ?_⟩
        · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
          · have hsrt2 := hsrt
            rw [hσ] at hsrt2
            simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
          · intro below above hop
            injection hop with h1 h2
            subst h1
            subst h2
            exact ⟨List.filter_sublist, List.filter_sublist⟩
        · rw [hσ]
          exact scan_split_step (color := color) (A := [S]) (B := B) hord
            hblue hred hmixed
        · intro D hD
          simp at hD
          rw [hD, hσ]
          simp
        · exact Or.inl (Or.inr (Or.inl ⟨[S], B, C, hσ, hblue, hmixed, rfl⟩))
        · have halt3 : AltRuns color ([S] ++ C :: B) := halt2
          exact alt_split_run (color := color) (A := [S])
            (fun x hx => (belowPiece_mem hx).1)
            (fun x hx => (abovePiece_mem hx).1) hblue hred
            (List.ne_nil_of_mem (show c₁ ∈ belowPiece C r by
              simp [belowPiece, List.mem_filter, hc₁C, hc₁r]))
            (List.ne_nil_of_mem (show c₂ ∈ abovePiece C r by
              simp [abovePiece, List.mem_filter, hc₂C, hc₂r])) halt3

  · -- right end: `σ = A ++ [C]`
    obtain ⟨A, C, hσ, hblue, c₀, hc₀, hc₀r⟩ := h
    have hinv2 : Invariant color (A ++ [C]) := hσ ▸ hinv
    have halt2 : AltRuns color (A ++ [C]) := hσ ▸ halt
    have hord : RunsOrdered (A ++ [C]) := hinv2.2.1
    have hCne : C ≠ [] := hinv2.1 C (by simp)
    by_cases haC : ∀ x ∈ C, r < x
    · exact absurd (haC c₀ hc₀) (not_lt.mpr (le_of_lt hc₀r))
    · by_cases hbC : ∀ x ∈ C, x < r
      · refine ⟨applyOp A [] C r .appendSingleton, [C], ?_, ?_, ?_, ?_, ?_⟩
        · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
          · have hsrt2 := hsrt
            rw [hσ] at hsrt2
            simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
          · intro below above hop
            cases hop
        · rw [hσ]
          exact scan_append_step (color := color)
            (fun R hR x hx =>
              lt_trans ((List.pairwise_append.mp hord).2.2 R hR C (by simp)
                x hx c₀ hc₀) hc₀r) hbC
        · intro D hD
          simp at hD
          rw [hD, hσ]
          simp
        · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨A, C, hσ, hblue, hbC, rfl⟩))))
        · exact alt_append_right (color := color) hblue hred halt2
      · have hmixed : scanVerdict C r = ScanVerdict.mixed :=
          scanVerdict_mixed hbC haC
        have hne : ∀ x ∈ C, x ≠ r := by
          intro x hx hcon
          have h1 : color r = Color.blue := by rw [← hcon]; exact hblue x hx
          rw [hred] at h1
          exact Color.noConfusion h1
        obtain ⟨⟨c₂, hc₂C, hc₂r⟩, ⟨c₁, hc₁C, hc₁r⟩⟩ := exists_of_mixed hne hmixed
        refine ⟨applyOp A [] C r (.splitRun (belowPiece C r) (abovePiece C r)),
          [C], ?_, ?_, ?_, ?_, ?_⟩
        · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
          · have hsrt2 := hsrt
            rw [hσ] at hsrt2
            simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
          · intro below above hop
            injection hop with h1 h2
            subst h1
            subst h2
            exact ⟨List.filter_sublist, List.filter_sublist⟩
        · rw [hσ]
          exact scan_split_step (color := color) (A := A) (B := []) hord
            hblue hred hmixed
        · intro D hD
          simp at hD
          rw [hD, hσ]
          simp
        · exact Or.inl (Or.inr (Or.inl ⟨A, [], C, hσ, hblue, hmixed, rfl⟩))
        · exact alt_split_run (color := color)
            (fun x hx => (belowPiece_mem hx).1)
            (fun x hx => (abovePiece_mem hx).1) hblue hred
            (List.ne_nil_of_mem (show c₁ ∈ belowPiece C r by
              simp [belowPiece, List.mem_filter, hc₁C, hc₁r]))
            (List.ne_nil_of_mem (show c₂ ∈ abovePiece C r by
              simp [abovePiece, List.mem_filter, hc₂C, hc₂r])) halt2
  · -- right candidate: `σ = A ++ [C, S]`
    obtain ⟨A, C, S, hσ, hblue, hSred, c₀, hc₀, hc₀r⟩ := h
    have hinv2 : Invariant color (A ++ [C, S]) := hσ ▸ hinv
    have halt2 : AltRuns color (A ++ [C, S]) := hσ ▸ halt
    have hf2 : r ∉ (A ++ [C, S]).flatten := hσ ▸ hfresh
    have hord : RunsOrdered (A ++ [C, S]) := hinv2.2.1
    have hCne : C ≠ [] := hinv2.1 C (by simp)
    have hSne : S ≠ [] := hinv2.1 S (by simp)
    have haltS : AltRuns color ((A ++ [C]) ++ S :: []) := by
      rwa [show (A ++ [C]) ++ S :: [] = A ++ [C, S] by simp]
    by_cases haC : ∀ x ∈ C, r < x
    · exact absurd (haC c₀ hc₀) (not_lt.mpr (le_of_lt hc₀r))
    · by_cases hbC : ∀ x ∈ C, x < r
      · by_cases hsing : ∃ r₀, S = [r₀]
        · obtain ⟨r₀, hr₀⟩ := hsing
          have hr₀red : color r₀ = Color.red := hSred r₀ (by rw [hr₀]; simp)
          by_cases hlt : r₀ < r
          · -- activation at the right end
            have hcross2 : ∀ R ∈ A ++ [C], ∀ T ∈ S :: [], ∀ x ∈ R, ∀ y ∈ T,
                x < y :=
              (List.pairwise_append.mp (show RunsOrdered ((A ++ [C]) ++ S :: [])
                from by simpa using hord)).2.2
            have hc₀r₀ : c₀ < r₀ := hcross2 C (by simp) S (by simp) c₀ hc₀ r₀
              (by rw [hr₀]; simp)
            have hstep : Step color ((A ++ [C]) ++ S :: []) r
                (applyOp (A ++ [C]) [] S r (.mergePair r₀)) := by
              apply Step.mergePair
              · exact hr₀
              · exact hSred
              · intro R hR x hx
                simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
                  or_false] at hR
                rcases hR with h | rfl
                · have hcross := (List.pairwise_append.mp hord).2.2
                  exact ⟨lt_trans (hcross R h C (by simp) x hx c₀ hc₀) hc₀r,
                    lt_trans (hcross R h C (by simp) x hx c₀ hc₀) hc₀r₀⟩
                · exact ⟨hbC x hx, hcross2 R (by simp) S (by simp) x hx r₀
                    (by rw [hr₀]; simp)⟩
              · intro T hT; simp at hT
            have e : (A ++ [C]) ++ S :: [] = A ++ [C, S] := by simp
            refine ⟨applyOp (A ++ [C]) [] S r (.mergePair r₀), [C], ?_, ?_,
              ?_, ?_, ?_⟩
            · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
              · have hsrt2 := hsrt
                rw [hσ] at hsrt2
                simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
              · intro below above hop
                cases hop
            · rw [hσ]; exact e ▸ hstep
            · intro D hD
              simp at hD
              rw [hD, hσ]
              simp
            · exact Or.inr ⟨r₀, Or.inr (Or.inr
                ⟨A, C, S, hσ, hr₀, hSred, hblue, hbC, hlt, rfl⟩),
                ⟨if r < r₀ then [r, r₀] else [r₀, r], by simp [applyOp],
                  by split_ifs <;> simp, by split_ifs <;> simp⟩⟩
            · have hT : ∀ x ∈ (if r < r₀ then [r, r₀] else [r₀, r]),
                  ∀ y ∈ S, color x = color y := by
                intro x hx y hy
                rw [hr₀] at hy
                simp only [List.mem_singleton] at hy
                rw [hy, hr₀red]
                split_ifs at hx <;>
                  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil,
                    or_false] at hx <;>
                  rcases hx with rfl | rfl <;>
                  first | exact hred | exact hr₀red
              exact alt_replace_run (color := color) (A := A ++ [C]) (B := [])
                hT hSne
                (List.ne_nil_of_mem (show r ∈ (if r < r₀ then [r, r₀]
                  else [r₀, r]) by
                  split_ifs with hh
                  · exact List.mem_cons_self
                  · exact List.mem_cons_of_mem r₀ List.mem_cons_self)) haltS
          · have hrr₀ : r < r₀ := by
              have hne : r ≠ r₀ := by
                intro hcon
                apply hf2
                rw [hcon]
                exact List.mem_flatten.mpr ⟨S, by simp, by rw [hr₀]; simp⟩
              exact lt_of_le_of_ne (le_of_not_gt hlt) hne
            refine ⟨applyOp (A ++ [C]) [] S r .insertInto, [C], ?_, ?_, ?_,
              ?_, ?_⟩
            · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
              · have hsrt2 := hsrt
                rw [hσ] at hsrt2
                simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
              · intro below above hop
                cases hop
            · rw [hσ]
              exact scan_attach_below (color := color) (A := A) (B := []) hord
                hSred hCne hbC (s₀ := r₀) (by rw [hr₀]; simp) hrr₀
            · intro D hD
              simp at hD
              rw [hD, hσ]
              simp
            · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨A, [], C, S, hσ, hblue, hbC,
                  fun x hx => by
                    rw [hr₀] at hx
                    simp at hx
                    rw [hx]
                    exact hrr₀,
                  hSne, rfl⟩)))))
            · have hT : ∀ x ∈ insertSorted r S, ∀ y ∈ S,
                  color x = color y := by
                intro x hx y hy
                rw [insertSorted_mem] at hx
                rcases hx with rfl | hx
                · rw [hred, hSred y hy]
                · rw [hSred x hx, hSred y hy]
              exact alt_replace_run (color := color) (A := A ++ [C]) (B := [])
                hT hSne insertSorted_ne_nil haltS
        · by_cases haS : ∀ x ∈ S, x < r
          · -- attach at the top of `S`, no scan
            have hAr : ∀ R ∈ A, ∀ x ∈ R, x < r := by
              intro R hR x hx
              have hcross := (List.pairwise_append.mp hord).2.2
              exact lt_trans (hcross R hR C (by simp) x hx c₀ hc₀) hc₀r
            have hstep : Step color ((A ++ [C]) ++ S :: []) r
                (applyOp (A ++ [C]) [] S r .insertInto) := by
              apply Step.insertInto
              · exact hSred
              · intro R hR x hx
                simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
                  or_false] at hR
                rcases hR with h | rfl
                · exact hAr R h x hx
                · exact hbC x hx
              · intro T hT; simp at hT
            have e : (A ++ [C]) ++ S :: [] = A ++ [C, S] := by simp
            refine ⟨applyOp (A ++ [C]) [] S r .insertInto, [], ?_, ?_, ?_, ?_, ?_⟩
            · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
              · have hsrt2 := hsrt
                rw [hσ] at hsrt2
                simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
              · intro below above hop
                cases hop
            · rw [hσ]; exact e ▸ hstep
            · intro D hD; simp at hD
            · exact Or.inl (Or.inl rfl)
            · have hT : ∀ x ∈ insertSorted r S, ∀ y ∈ S,
                  color x = color y := by
                intro x hx y hy
                rw [insertSorted_mem] at hx
                rcases hx with rfl | hx
                · rw [hred, hSred y hy]
                · rw [hSred x hx, hSred y hy]
              exact alt_replace_run (color := color) (A := A ++ [C]) (B := [])
                hT hSne insertSorted_ne_nil haltS
          · by_cases hbS : ∀ x ∈ S, r < x
            · obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
                cases S with
                | nil => simp at hSne
                | cons x xs => exact ⟨x, by simp⟩
              refine ⟨applyOp (A ++ [C]) [] S r .insertInto, [C], ?_, ?_, ?_,
                ?_, ?_⟩
              · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
                · have hsrt2 := hsrt
                  rw [hσ] at hsrt2
                  simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
                · intro below above hop
                  cases hop
              · rw [hσ]
                exact scan_attach_below (color := color) (A := A) (B := [])
                  hord hSred hCne hbC hs₀ (hbS s₀ hs₀)
              · intro D hD
                simp at hD
                rw [hD, hσ]
                simp
              · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨A, [], C, S, hσ, hblue, hbC, hbS, hSne, rfl⟩)))))
              · have hT : ∀ x ∈ insertSorted r S, ∀ y ∈ S,
                    color x = color y := by
                  intro x hx y hy
                  rw [insertSorted_mem] at hx
                  rcases hx with rfl | hx
                  · rw [hred, hSred y hy]
                  · rw [hSred x hx, hSred y hy]
                exact alt_replace_run (color := color) (A := A ++ [C])
                  (B := []) hT hSne insertSorted_ne_nil haltS
            · -- straddling `S`: sorted insertion, no scan
              have hAr : ∀ R ∈ A, ∀ x ∈ R, x < r := by
                intro R hR x hx
                have hcross := (List.pairwise_append.mp hord).2.2
                exact lt_trans (hcross R hR C (by simp) x hx c₀ hc₀) hc₀r
              have hstep : Step color ((A ++ [C]) ++ S :: []) r
                  (applyOp (A ++ [C]) [] S r .insertInto) := by
                apply Step.insertInto
                · exact hSred
                · intro R hR x hx
                  simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
                    or_false] at hR
                  rcases hR with h | rfl
                  · exact hAr R h x hx
                  · exact hbC x hx
                · intro T hT; simp at hT
              have e : (A ++ [C]) ++ S :: [] = A ++ [C, S] := by simp
              refine ⟨applyOp (A ++ [C]) [] S r .insertInto, [], ?_, ?_, ?_,
                ?_, ?_⟩
              · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
                · have hsrt2 := hsrt
                  rw [hσ] at hsrt2
                  simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
                · intro below above hop
                  cases hop
              · rw [hσ]; exact e ▸ hstep
              · intro D hD; simp at hD
              · exact Or.inl (Or.inl rfl)
              · have hT : ∀ x ∈ insertSorted r S, ∀ y ∈ S,
                    color x = color y := by
                  intro x hx y hy
                  rw [insertSorted_mem] at hx
                  rcases hx with rfl | hx
                  · rw [hred, hSred y hy]
                  · rw [hSred x hx, hSred y hy]
                exact alt_replace_run (color := color) (A := A ++ [C])
                  (B := []) hT hSne insertSorted_ne_nil haltS
      · have hmixed : scanVerdict C r = ScanVerdict.mixed :=
          scanVerdict_mixed hbC haC
        have hne : ∀ x ∈ C, x ≠ r := by
          intro x hx hcon
          have h1 : color r = Color.blue := by rw [← hcon]; exact hblue x hx
          rw [hred] at h1
          exact Color.noConfusion h1
        obtain ⟨⟨c₂, hc₂C, hc₂r⟩, ⟨c₁, hc₁C, hc₁r⟩⟩ := exists_of_mixed hne hmixed
        refine ⟨applyOp A [S] C r (.splitRun (belowPiece C r) (abovePiece C r)),
          [C], ?_, ?_, ?_, ?_, ?_⟩
        · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
          · have hsrt2 := hsrt
            rw [hσ] at hsrt2
            simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
          · intro below above hop
            injection hop with h1 h2
            subst h1
            subst h2
            exact ⟨List.filter_sublist, List.filter_sublist⟩
        · rw [hσ]
          exact scan_split_step (color := color) (A := A) (B := [S]) hord
            hblue hred hmixed
        · intro D hD
          simp at hD
          rw [hD, hσ]
          simp
        · exact Or.inl (Or.inr (Or.inl ⟨A, [S], C, hσ, hblue, hmixed, rfl⟩))
        · exact alt_split_run (color := color) (A := A) (B := [S])
            (fun x hx => (belowPiece_mem hx).1)
            (fun x hx => (abovePiece_mem hx).1) hblue hred
            (List.ne_nil_of_mem (show c₁ ∈ belowPiece C r by
              simp [belowPiece, List.mem_filter, hc₁C, hc₁r]))
            (List.ne_nil_of_mem (show c₂ ∈ abovePiece C r by
              simp [abovePiece, List.mem_filter, hc₂C, hc₂r])) halt2

  · -- interior gap: `σ = A ++ L :: S :: U :: B`
    obtain ⟨A, B, L, S, U, hσ, hLblue, hSred, hUblue, hl, hu⟩ := h
    obtain ⟨l₀, hl₀, hl₀r⟩ := hl
    obtain ⟨u₀, hu₀, hu₀r⟩ := hu
    have hinv2 : Invariant color (A ++ L :: S :: U :: B) := hσ ▸ hinv
    have halt2 : AltRuns color (A ++ L :: S :: U :: B) := hσ ▸ halt
    have hord : RunsOrdered (A ++ L :: S :: U :: B) := hinv2.2.1
    have hLne : L ≠ [] := hinv2.1 L (by simp)
    have hUne : U ≠ [] := hinv2.1 U (by simp)
    have hSne : S ≠ [] := hinv2.1 S (by simp)
    have hTins : ∀ (T : List X), (∀ x ∈ T, ∀ y ∈ S, color x = color y) →
        T ≠ [] → AltRuns color ((A ++ [L]) ++ T :: (U :: B)) := by
      intro T hT hTne
      have haltS : AltRuns color ((A ++ [L]) ++ S :: (U :: B)) := by
        rwa [show (A ++ [L]) ++ S :: (U :: B) = A ++ L :: S :: U :: B by
          simp [List.append_assoc]]
      exact alt_replace_run (color := color) hT hSne hTne haltS
    have hTS : ∀ x ∈ insertSorted r S, ∀ y ∈ S, color x = color y := by
      intro x hx y hy
      rw [insertSorted_mem] at hx
      rcases hx with rfl | hx
      · rw [hred, hSred y hy]
      · rw [hSred x hx, hSred y hy]
    by_cases hbL : ∀ x ∈ L, x < r
    · by_cases haU : ∀ x ∈ U, r < x
      · by_cases hsing : ∃ r₀, S = [r₀]
        · obtain ⟨r₀, hr₀⟩ := hsing
          have hr₀red : color r₀ = Color.red := hSred r₀ (by rw [hr₀]; simp)
          refine ⟨applyOp (A ++ [L]) (U :: B) S r (.mergePair r₀), [L, U],
            ?_, ?_, ?_, ?_, ?_⟩
          · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
            · have hsrt2 := hsrt
              rw [hσ] at hsrt2
              simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
            · intro below above hop
              cases hop
          · rw [hσ]
            exact scan_activation_step (color := color) hord hr₀ hr₀red
              hLne hUne hbL haU
          · intro D hD
            simp at hD
            rcases hD with rfl | rfl
            · rw [hσ]; simp
            · rw [hσ]; simp
          · exact Or.inr ⟨r₀, Or.inl
              ⟨A, B, L, S, U, hσ, hr₀, hSred, hLblue, hUblue, hbL, haU, rfl⟩,
              ⟨if r < r₀ then [r, r₀] else [r₀, r], by simp [applyOp],
                by split_ifs <;> simp, by split_ifs <;> simp⟩⟩
          · have hT : ∀ x ∈ (if r < r₀ then [r, r₀] else [r₀, r]),
                ∀ y ∈ S, color x = color y := by
              intro x hx y hy
              rw [hr₀] at hy
              simp only [List.mem_singleton] at hy
              rw [hy, hr₀red]
              split_ifs at hx <;>
                simp only [List.mem_cons, List.mem_singleton,
                  List.not_mem_nil, or_false] at hx <;>
                rcases hx with rfl | rfl <;>
                first | exact hred | exact hr₀red
            exact hTins _ hT
              (List.ne_nil_of_mem (show r ∈ (if r < r₀ then [r, r₀]
                else [r₀, r]) by
                split_ifs with hh
                · exact List.mem_cons_self
                · exact List.mem_cons_of_mem r₀ List.mem_cons_self))
        · by_cases hbS : ∀ x ∈ S, r < x
          · obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
              cases S with
              | nil => simp at hSne
              | cons x xs => exact ⟨x, by simp⟩
            refine ⟨applyOp (A ++ [L]) (U :: B) S r .insertInto, [L], ?_, ?_,
              ?_, ?_, ?_⟩
            · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
              · have hsrt2 := hsrt
                rw [hσ] at hsrt2
                simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
              · intro below above hop
                cases hop
            · rw [hσ]
              exact scan_attach_below (color := color) hord hSred hLne hbL
                hs₀ (hbS s₀ hs₀)
            · intro D hD
              simp at hD
              rw [hD, hσ]
              simp
            · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨A, U :: B, L, S, hσ, hLblue, hbL, hbS, hSne, rfl⟩)))))
            · exact hTins _ hTS insertSorted_ne_nil
          · by_cases haS : ∀ x ∈ S, x < r
            · obtain ⟨s₀, hs₀⟩ : ∃ s₀, s₀ ∈ S := by
                cases S with
                | nil => simp at hSne
                | cons x xs => exact ⟨x, by simp⟩
              have e : A ++ L :: S :: U :: B = (A ++ [L]) ++ S :: U :: B := by
                simp [List.append_assoc]
              refine ⟨applyOp (A ++ [L]) (U :: B) S r .insertInto, [U], ?_,
                ?_, ?_, ?_, ?_⟩
              · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
                · have hsrt2 := hsrt
                  rw [hσ] at hsrt2
                  simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
                · intro below above hop
                  cases hop
              · rw [hσ]
                exact e ▸ scan_attach_above (color := color) (e ▸ hord) hSred
                  hUne haU hs₀ (haS s₀ hs₀)
              · intro D hD
                simp at hD
                rw [hD, hσ]
                simp
              · have hσe : σ = (A ++ [L]) ++ S :: U :: B := by
                  rw [hσ]; simp [List.append_assoc]
                exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨A ++ [L], B, U, S, hσe, hUblue, haU, haS, hSne, rfl⟩)))))
              · exact hTins _ hTS insertSorted_ne_nil
            · -- straddling `S`: sorted insertion, no scan
              have e : (A ++ [L]) ++ S :: (U :: B) = A ++ L :: S :: U :: B := by
                simp [List.append_assoc]
              have hstep : Step color ((A ++ [L]) ++ S :: (U :: B)) r
                  (applyOp (A ++ [L]) (U :: B) S r .insertInto) := by
                apply Step.insertInto
                · exact hSred
                · intro R hR x hx
                  simp only [List.mem_append, List.mem_cons, List.not_mem_nil,
                    or_false] at hR
                  rcases hR with h | rfl
                  · have hcross := (List.pairwise_append.mp hord).2.2
                    exact lt_trans (hcross R h L (by simp) x hx l₀ hl₀) hl₀r
                  · exact hbL x hx
                · intro T hT y hy
                  simp only [List.mem_cons] at hT
                  rcases hT with rfl | h
                  · exact haU y hy
                  · have e2 : A ++ L :: S :: U :: B
                        = (A ++ [L, S, U]) ++ B := by simp [List.append_assoc]
                    have hcross := (List.pairwise_append.mp (e2 ▸ hord)).2.2
                    exact lt_trans hu₀r (hcross U (by simp) T h u₀ hu₀ y hy)
              refine ⟨applyOp (A ++ [L]) (U :: B) S r .insertInto, [], ?_, ?_,
                ?_, ?_, ?_⟩
              · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
                · have hsrt2 := hsrt
                  rw [hσ] at hsrt2
                  simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
                · intro below above hop
                  cases hop
              · rw [hσ]; exact e ▸ hstep
              · intro D hD; simp at hD
              · exact Or.inl (Or.inl rfl)
              · exact hTins _ hTS insertSorted_ne_nil
      · by_cases hbU : ∀ x ∈ U, x < r
        · exact absurd (hbU u₀ hu₀) (not_lt.mpr (le_of_lt hu₀r))
        · have hmixed : scanVerdict U r = ScanVerdict.mixed :=
            scanVerdict_mixed hbU haU
          have hne : ∀ x ∈ U, x ≠ r := by
            intro x hx hcon
            have h1 : color r = Color.blue := by
              rw [← hcon]; exact hUblue x hx
            rw [hred] at h1
            exact Color.noConfusion h1
          obtain ⟨⟨c₂, hc₂U, hc₂r⟩, ⟨c₁, hc₁U, hc₁r⟩⟩ :=
            exists_of_mixed hne hmixed
          have e : (A ++ [L, S]) ++ U :: B = A ++ L :: S :: U :: B := by
            simp [List.append_assoc]
          have hσe : σ = (A ++ [L, S]) ++ U :: B := by
            rw [hσ]; simp [List.append_assoc]
          have hord2 : RunsOrdered ((A ++ [L, S]) ++ U :: B) := e ▸ hord
          refine ⟨applyOp (A ++ [L, S]) B U r
              (.splitRun (belowPiece U r) (abovePiece U r)), [U], ?_, ?_, ?_,
            ?_, ?_⟩
          · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
            · have hsrt2 := hsrt
              rw [hσ] at hsrt2
              simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
            · intro below above hop
              injection hop with h1 h2
              subst h1
              subst h2
              exact ⟨List.filter_sublist, List.filter_sublist⟩
          · rw [hσ]
            exact e ▸ scan_split_step (color := color) hord2 hUblue hred
              hmixed
          · intro D hD
            simp at hD
            rw [hD, hσ]
            simp
          · exact Or.inl (Or.inr (Or.inl
              ⟨A ++ [L, S], B, U, hσe, hUblue, hmixed, rfl⟩))
          · have halt3 : AltRuns color ((A ++ [L, S]) ++ U :: B) := e ▸ halt2
            exact alt_split_run (color := color)
              (fun x hx => (belowPiece_mem hx).1)
              (fun x hx => (abovePiece_mem hx).1) hUblue hred
              (List.ne_nil_of_mem (show c₁ ∈ belowPiece U r by
                simp [belowPiece, List.mem_filter, hc₁U, hc₁r]))
              (List.ne_nil_of_mem (show c₂ ∈ abovePiece U r by
                simp [abovePiece, List.mem_filter, hc₂U, hc₂r])) halt3
    · by_cases haL : ∀ x ∈ L, r < x
      · exact absurd (haL l₀ hl₀) (not_lt.mpr (le_of_lt hl₀r))
      · have hmixed : scanVerdict L r = ScanVerdict.mixed :=
          scanVerdict_mixed hbL haL
        have hne : ∀ x ∈ L, x ≠ r := by
          intro x hx hcon
          have h1 : color r = Color.blue := by rw [← hcon]; exact hLblue x hx
          rw [hred] at h1
          exact Color.noConfusion h1
        obtain ⟨⟨c₂, hc₂L, hc₂r⟩, ⟨c₁, hc₁L, hc₁r⟩⟩ := exists_of_mixed hne hmixed
        refine ⟨applyOp A (S :: U :: B) L r
            (.splitRun (belowPiece L r) (abovePiece L r)), [L], ?_, ?_, ?_,
          ?_, ?_⟩
        · refine runsInternallySorted_applyOp (color := color) _ ?_ ?_
          · have hsrt2 := hsrt
            rw [hσ] at hsrt2
            simpa only [List.append_assoc, List.nil_append, List.cons_append] using hsrt2
          · intro below above hop
            injection hop with h1 h2
            subst h1
            subst h2
            exact ⟨List.filter_sublist, List.filter_sublist⟩
        · rw [hσ]
          exact scan_split_step (color := color) hord hLblue hred hmixed
        · intro D hD
          simp at hD
          rw [hD, hσ]
          simp
        · exact Or.inl (Or.inr (Or.inl
            ⟨A, S :: U :: B, L, hσ, hLblue, hmixed, rfl⟩))
        · exact alt_split_run (color := color)
            (fun x hx => (belowPiece_mem hx).1)
            (fun x hx => (abovePiece_mem hx).1) hLblue hred
            (List.ne_nil_of_mem (show c₁ ∈ belowPiece L r by
              simp [belowPiece, List.mem_filter, hc₁L, hc₁r]))
            (List.ne_nil_of_mem (show c₂ ∈ abovePiece L r by
              simp [abovePiece, List.mem_filter, hc₂L, hc₂r])) halt2

/-- A charged step is never an activation step (in a state
satisfying the invariant). The shapes are incompatible: scan
lists differ in length, verdicts on the scanned run contradict
the one-sided verdicts an activation needs on any element of
the nonempty run, the candidate cannot sit where an activation
needs it (position uniqueness for nonempty ordered runs), and
at an end the candidate would have to be both a blue element
and the red founder. -/
theorem stepCharged_not_activation {σ : List (List X)} {r : X}
    {scans : List (List X)}
    (hinv : Invariant color σ) (hrred : color r = Color.red)
    (hch : StepCharged color σ r scans) :
    ¬ StepActivation color σ r scans := by
  intro hact
  obtain ⟨q, hAt⟩ := hact
  have hord : RunsOrdered σ := hinv.2.1
  rcases hAt with ⟨A₂, B₂, L, S₂, U, hσa, hS, -, -, -, -, -, hsea⟩
    | ⟨B₂, S₂, D, hσa, hS, hSredA, -, haD, hlt, hsea⟩
    | ⟨A₂, D, S₂, hσa, hS, hSredA, -, hbD, hlt, hsea⟩
  · -- interior activation: the scan list has length two
    have hlen : scans.length = 2 := by rw [hsea]; rfl
    rcases hch with hse | ⟨A, B, C, -, -, -, hse⟩ | ⟨B, C, -, -, -, hse⟩
      | ⟨A, C, -, -, -, hse⟩ | ⟨A, B, C, S, -, -, -, -, -, hse⟩
      | ⟨A, B, C, S, -, -, -, -, -, hse⟩ <;>
      rw [hse] at hlen <;> simp at hlen
  · -- left-end activation: one scanned run, all above `r`
    have hlen : scans.length = 1 := by rw [hsea]; rfl
    rcases hch with hse | ⟨A, B, C, hσ, hblue, hmixed, hse⟩
      | ⟨B, C, hσ, hblue, habove, hse⟩
      | ⟨A, C, hσ, hblue, hbelow, hse⟩
      | ⟨A, B, C, S, hσ, hblue, hbC, hrS, -, hse⟩
      | ⟨A, B, C, S, hσ, hblue, hbC, hrS, -, hse⟩
    · rw [hse] at hlen
      simp at hlen
    · -- split: a mixed run has an element below `r`
      have hCD : C = D := by
        have e : [C] = [D] := hse.symm.trans hsea
        simpa using e
      have hne : ∀ x ∈ C, x ≠ r := by
        intro x hx hcon
        have h1 : color r = Color.blue := by rw [← hcon]; exact hblue x hx
        rw [hrred] at h1
        exact Color.noConfusion h1
      obtain ⟨⟨c₂, -, -⟩, ⟨c₁, hc₁, hc₁r⟩⟩ := exists_of_mixed hne hmixed
      exact absurd (haD c₁ (hCD ▸ hc₁)) (not_lt.mpr (le_of_lt hc₁r))
    · -- fresh singleton at the left end: its run would be the founder's
      have hCeq : C = S₂ := by
        have e : C :: B = S₂ :: D :: B₂ := hσ.symm.trans hσa
        simp only [List.cons.injEq] at e
        exact e.1
      have hqC : q ∈ C := by
        rw [hCeq, hS]
        simp
      have hblueq : color q = Color.blue := hblue q hqC
      have hredq : color q = Color.red := hSredA q (by rw [hS]; simp)
      rw [hblueq] at hredq
      exact Color.noConfusion hredq
    · -- creator at the right end: verdicts on the nonempty run clash
      have hCD : C = D := by
        have e : [C] = [D] := hse.symm.trans hsea
        simpa using e
      obtain ⟨c, hc⟩ : ∃ c, c ∈ C := by
        have hCne : C ≠ [] := hinv.1 C (by rw [hσ]; simp)
        cases C with
        | nil => simp at hCne
        | cons x xs => exact ⟨x, by simp⟩
      exact absurd (haD c (hCD ▸ hc)) (not_lt.mpr (le_of_lt (hbelow c hc)))
    · -- merger below: verdicts on the nonempty run clash
      have hCD : C = D := by
        have e : [C] = [D] := hse.symm.trans hsea
        simpa using e
      obtain ⟨c, hc⟩ : ∃ c, c ∈ C := by
        have hCne : C ≠ [] := hinv.1 C (by rw [hσ]; simp)
        cases C with
        | nil => simp at hCne
        | cons x xs => exact ⟨x, by simp⟩
      exact absurd (haD c (hCD ▸ hc)) (not_lt.mpr (le_of_lt (hbC c hc)))
    · -- merger above: position uniqueness puts the candidate on `S`
      have hCD : C = D := by
        have e : [C] = [D] := hse.symm.trans hsea
        simpa using e
      have hCne : C ≠ [] := hinv.1 C (by rw [hσ]; simp)
      have e1 : (A ++ [S]) ++ C :: B = A ++ S :: C :: B := by
        simp [List.append_assoc]
      have hord3 : RunsOrdered ((A ++ [S]) ++ C :: B) :=
        (hσ.trans e1.symm) ▸ hord
      have heq : (A ++ [S]) ++ C :: B = [S₂] ++ C :: B₂ :=
        e1.trans (hσ.symm.trans (hσa.trans
          (congrArg (fun D => S₂ :: D :: B₂) hCD.symm)))
      have happ := runsOrdered_append_inj hCne hord3 heq
      have hAeq : A ++ [S] = [S₂] := happ.1
      have hSlen : (A ++ [S]).length = 1 := by rw [hAeq]; rfl
      simp only [List.length_append, List.length_singleton] at hSlen
      have hA : A = [] := by
        cases A with
        | nil => rfl
        | cons x xs => simp at hSlen
      have hSeq : S = S₂ := by
        rw [hA] at hAeq
        simpa using hAeq
      have hqS : q ∈ S := by
        rw [hSeq, hS]
        simp
      exact absurd (hlt) (not_lt.mpr (le_of_lt (hrS q hqS)))
  · -- right-end activation: one scanned run, all below `r`
    have hlen : scans.length = 1 := by rw [hsea]; rfl
    rcases hch with hse | ⟨A, B, C, hσ, hblue, hmixed, hse⟩
      | ⟨B, C, hσ, hblue, habove, hse⟩
      | ⟨A, C, hσ, hblue, hbelow, hse⟩
      | ⟨A, B, C, S, hσ, hblue, hbC, hrS, -, hse⟩
      | ⟨A, B, C, S, hσ, hblue, hbC, hrS, -, hse⟩
    · rw [hse] at hlen
      simp at hlen
    · -- split: a mixed run has an element above `r`
      have hCD : C = D := by
        have e : [C] = [D] := hse.symm.trans hsea
        simpa using e
      have hne : ∀ x ∈ C, x ≠ r := by
        intro x hx hcon
        have h1 : color r = Color.blue := by rw [← hcon]; exact hblue x hx
        rw [hrred] at h1
        exact Color.noConfusion h1
      obtain ⟨⟨c₂, hc₂, hc₂r⟩, ⟨-, -, -⟩⟩ := exists_of_mixed hne hmixed
      exact absurd (hbD c₂ (hCD ▸ hc₂)) (not_lt.mpr (le_of_lt hc₂r))
    · -- fresh singleton at the left end: verdicts clash
      have hCD : C = D := by
        have e : [C] = [D] := hse.symm.trans hsea
        simpa using e
      obtain ⟨c, hc⟩ : ∃ c, c ∈ C := by
        have hCne : C ≠ [] := hinv.1 C (by rw [hσ]; simp)
        cases C with
        | nil => simp at hCne
        | cons x xs => exact ⟨x, by simp⟩
      exact absurd (hbD c (hCD ▸ hc)) (not_lt.mpr (le_of_lt (habove c hc)))
    · -- creator at the right end: position forces a tail of one run
      have hCD : C = D := by
        have e : [C] = [D] := hse.symm.trans hsea
        simpa using e
      have hCne : C ≠ [] := hinv.1 C (by rw [hσ]; simp)
      have hord1 : RunsOrdered (A ++ C :: ([] : List (List X))) :=
        hσ ▸ hord
      have heq : A ++ C :: ([] : List (List X)) = A₂ ++ C :: [S₂] := by
        rw [← hσ, hσa, ← hCD]
      have happ := runsOrdered_append_inj hCne hord1 heq
      simp at happ
    · -- merger below: position uniqueness puts the candidate on `S`
      have hCD : C = D := by
        have e : [C] = [D] := hse.symm.trans hsea
        simpa using e
      have hCne : C ≠ [] := hinv.1 C (by rw [hσ]; simp)
      have hord1 : RunsOrdered (A ++ C :: (S :: B)) := hσ ▸ hord
      have heq : A ++ C :: (S :: B) = A₂ ++ C :: [S₂] := by
        rw [← hσ, hσa, ← hCD]
      have happ := runsOrdered_append_inj hCne hord1 heq
      have hSeq : S = S₂ := by
        have e : S :: B = [S₂] := happ.2
        have e2 : S = S₂ ∧ B = [] := by simpa using e
        exact e2.1
      have hqS : q ∈ S := by
        rw [hSeq, hS]
        simp
      exact absurd (hlt) (not_lt.mpr (le_of_lt (hrS q hqS)))
    · -- merger above: verdicts on the nonempty run clash
      have hCD : C = D := by
        have e : [C] = [D] := hse.symm.trans hsea
        simpa using e
      obtain ⟨c, hc⟩ : ∃ c, c ∈ C := by
        have hCne : C ≠ [] := hinv.1 C (by rw [hσ]; simp)
        cases C with
        | nil => simp at hCne
        | cons x xs => exact ⟨x, by simp⟩
      exact absurd (hbD c (hCD ▸ hc)) (not_lt.mpr (le_of_lt (hbC c hc)))

/-- Every step of an execution is charged or an activation. -/
def ExecStepsClassified {σ : List (List X)} {L : List X}
    {σf : List (List X)} : ExecFrom color σ L σf → Prop
  | .nil _ => True
  | .cons r _ scans _ tail =>
      (StepCharged color σ r scans ∨ StepActivation color σ r scans) ∧
        ExecStepsClassified tail

/-- Every activation step of an execution grows its founder's
run: after the step, the founder lies in a run of length at least
two. Produced executions have this property (`exists_execution`);
it is the dynamic half of founder charging. -/
def ExecActivationGrows {σ : List (List X)} {L : List X}
    {σf : List (List X)} : ExecFrom color σ L σf → Prop
  | .nil _ => True
  | @ExecFrom.cons _ _ _ σ σ' σf r rest step scans hscans tail =>
      (∀ q, ActivationAt color σ r q scans →
        ∃ R ∈ σ', q ∈ R ∧ 2 ≤ R.length) ∧ ExecActivationGrows tail

/-- Assembling an execution from an arrival list: processing
distinct fresh red arrivals in order from a state with the
invariant package (including alternation and a blue run) yields
an execution whose every step is charged or an activation, and
the final state keeps the invariant package and the expected
flattening. The assembly maintains alternation through the
dispatch, freshness of later arrivals through provenance, and
the blue-run existence through persistence of blue elements. -/
theorem exists_execution :
    ∀ (L : List X) (σ : List (List X)), Invariant color σ →
      MonoRuns color σ → AltRuns color σ →
      RunsInternallySorted color σ →
      (∃ C ∈ σ, ∀ x ∈ C, color x = Color.blue) →
      (∀ r ∈ L, color r = Color.red) → L.Nodup →
      (∀ r ∈ L, r ∉ σ.flatten) →
      ∃ σf, ∃ e : ExecFrom color σ L σf, ExecStepsClassified (color := color) e ∧
        Invariant color σf ∧ MonoRuns color σf ∧ AltRuns color σf ∧
        ExecActivationGrows (color := color) e ∧
        RunsInternallySorted color σf ∧
        σf.flatten.Perm (L ++ σ.flatten) := by
  intro L
  induction L with
  | nil =>
      intro σ hinv hmono halt hsrt hblue0 _ _ _
      exact ⟨σ, ExecFrom.nil σ, trivial, hinv, hmono, halt, trivial, hsrt,
        by simp⟩
  | cons r rest ih =>
      intro σ hinv hmono halt hsrt hblue0 hredL hnd hfresh
      have hrred : color r = Color.red := hredL r (by simp)
      have hrfresh : r ∉ σ.flatten := hfresh r (by simp)
      obtain ⟨σ', scans, hsrt', hstep, hscansmem, hclass, halt'⟩ :=
        exists_step_for_arrival_full (color := color) hinv hmono halt hrred
          hrfresh hblue0 hsrt
      obtain ⟨hinv', hmono'⟩ := step_invariant color hstep hinv hmono hrred
      have hblue' : ∃ C ∈ σ', ∀ x ∈ C, color x = Color.blue := by
        obtain ⟨C, hC, hblue⟩ := hblue0
        obtain ⟨b, hb⟩ : ∃ b, b ∈ C := by
          have hne : C ≠ [] := hinv.1 C hC
          cases C with
          | nil => simp at hne
          | cons y ys => exact ⟨y, by simp⟩
        have hbσ : b ∈ σ.flatten := List.mem_flatten.mpr ⟨C, hC, hb⟩
        have hperm : σ'.flatten.Perm (r :: σ.flatten) := step_flatten color hstep
        have hbσ' : b ∈ σ'.flatten := hperm.mem_iff.mpr (List.mem_cons_of_mem r hbσ)
        obtain ⟨R', hR', hbR'⟩ := List.mem_flatten.mp hbσ'
        rcases hmono' R' hR' with hredR' | hblueR'
        · have hbb := hblue b hb
          rw [hredR' b hbR'] at hbb
          have hfalse : False := Color.noConfusion hbb
          exact hfalse.elim
        · exact ⟨R', hR', hblueR'⟩
      have hnd' : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hrfresh' : ∀ r' ∈ rest, r' ∉ σ'.flatten := by
        intro r' hr' hcon
        have hperm : σ'.flatten.Perm (r :: σ.flatten) := step_flatten color hstep
        have hmem : r' ∈ r :: σ.flatten := hperm.mem_iff.mp hcon
        cases List.mem_cons.mp hmem with
        | inl he =>
            rw [he] at hr'
            exact (List.nodup_cons.mp hnd).1 hr'
        | inr hmem =>
            exact hfresh r' (List.mem_cons_of_mem r hr') hmem
      obtain ⟨σf, e', hclass', hinvf, hmonof, haltf, hgrows', hsrtf,
          hpermf⟩ :=
        ih σ' hinv' hmono' halt' hsrt' hblue'
          (fun r' hr' => hredL r' (List.mem_cons_of_mem r hr')) hnd' hrfresh'
      have hclass1 : StepCharged color σ r scans ∨
          StepActivation color σ r scans := by
        rcases hclass with hch | ⟨q, hAt, -⟩
        · exact Or.inl hch
        · exact Or.inr ⟨q, hAt⟩
      have hgrows1 : ∀ q, ActivationAt color σ r q scans →
          ∃ R ∈ σ', q ∈ R ∧ 2 ≤ R.length := by
        intro q hAt
        rcases hclass with hch | ⟨q₀, hAt₀, hg⟩
        · exact absurd ⟨q, hAt⟩ (stepCharged_not_activation (color := color) hinv hrred hch)
        · have hqq : q = q₀ :=
            activationAt_founder_unique (color := color) hinv.2.1 hinv.1 hAt hAt₀
          rw [hqq]
          exact hg
      refine ⟨σf, ExecFrom.cons r hstep scans hscansmem e',
        ⟨hclass1, hclass'⟩, hinvf, hmonof, haltf, ⟨hgrows1, hgrows'⟩, hsrtf,
        ?_⟩
      have hperm : σ'.flatten.Perm (r :: σ.flatten) := step_flatten color hstep
      exact hpermf.trans
        ((List.Perm.append_left rest hperm).trans List.perm_middle)

/-- The founder of an activation configuration is red. -/
theorem activationAt_founder_red {σ : List (List X)} {r q : X}
    {scans : List (List X)} (h : ActivationAt color σ r q scans) :
    color q = Color.red := by
  rcases h with ⟨A, B, L, S, U, -, hS, hSred, -⟩
    | ⟨B, S, C, -, hS, hSred, -⟩
    | ⟨A, C, S, -, hS, hSred, -⟩ <;>
    exact hSred q (by rw [hS]; simp)

/-- The founder of an activation configuration is present in
the state. -/
theorem activationAt_founder_mem {σ : List (List X)} {r q : X}
    {scans : List (List X)} (h : ActivationAt color σ r q scans) :
    q ∈ σ.flatten := by
  rcases h with ⟨A, B, L, S, U, hσ, hS, -⟩
    | ⟨B, S, C, hσ, hS, -⟩
    | ⟨A, C, S, hσ, hS, -⟩ <;>
    · exact List.mem_flatten.mpr ⟨S, by simp [hσ], by rw [hS]; simp⟩

/-- Records at a single charged step: the five ordinary shapes,
discharged by the record lemmas. -/
theorem stepCharged_events_record
    (τF : X → Fin (Fintype.card X)) (hinjF : Function.Injective τF)
    {σ : List (List X)} {r : X} {scans : List (List X)}
    (hch : StepCharged color σ r scans) (hinv : Invariant color σ)
    (hrred : color r = Color.red)
    (hpresent : ∀ r' : X, color r' = Color.red →
      (fun x => (τF x).val) r' < (fun x => (τF x).val) r →
      r' ∈ σ.flatten) :
    ∀ C ∈ scans, ∀ b ∈ C,
      IsRecord color (fun x => (τF x).val) b r := by
  have hinj : Function.Injective (fun x => (τF x).val) := by
    intro x y h
    exact hinjF (Fin.ext h)
  intro C hC b hb
  rcases hch with hquiet
    | ⟨A, B, C', hσ, hblue, hmixed, hscansEq⟩
    | ⟨B, C', hσ, hblue, habove, hscansEq⟩
    | ⟨A, C', hσ, hblue, hbelow, hscansEq⟩
    | ⟨A, B, C', S, hσ, hblue, hbC, hrS, hSne, hscansEq⟩
    | ⟨A, B, C', S, hσ, hblue, hbC, hrS, hSne, hscansEq⟩
  · rw [hquiet] at hC
    simp at hC
  · rw [hscansEq] at hC
    have hCeq : C = C' := List.mem_singleton.mp hC
    subst hCeq
    exact (split_scan_charged color (hσ ▸ hinv).2.1 hblue hrred hmixed
      (fun x => (τF x).val) hinj (fun r' hr' hlt => hσ ▸ hpresent r' hr' hlt)).2
      b hb
  · rw [hscansEq] at hC
    have hCeq : C = C' := List.mem_singleton.mp hC
    subst hCeq
    exact creator_record_left color (hσ ▸ hinv).2.1 habove hb hblue hrred
      (fun x => (τF x).val) hinj (fun r' hr' hlt => hσ ▸ hpresent r' hr' hlt)
  · rw [hscansEq] at hC
    have hCeq : C = C' := List.mem_singleton.mp hC
    subst hCeq
    exact creator_record color (hσ ▸ hinv).2.1 hbelow hb hblue hrred
      (fun x => (τF x).val) hinj (fun r' hr' hlt => hσ ▸ hpresent r' hr' hlt)
  · rw [hscansEq] at hC
    have hCeq : C = C' := List.mem_singleton.mp hC
    subst hCeq
    exact merger_record color (hσ ▸ hinv).2.1 hbC hrS hSne hb hblue hrred
      (fun x => (τF x).val) hinj (fun r' hr' hlt => hσ ▸ hpresent r' hr' hlt)
  · rw [hscansEq] at hC
    have hCeq : C = C' := List.mem_singleton.mp hC
    subst hCeq
    exact merger_record_succ color (hσ ▸ hinv).2.1 hbC hrS hSne hb hblue
      hrred (fun x => (τF x).val) hinj
      (fun r' hr' hlt => hσ ▸ hpresent r' hr' hlt)

/-- Records for the ordinary events of a classified execution:
at a charged step, the arrival is a record for every blue
element scanned (`stepCharged_events_record`); activation steps
contribute no ordinary events. -/
theorem ordinary_events_records
    (τF : X → Fin (Fintype.card X)) (hinjF : Function.Injective τF)
    (Λ : List X) (σ0 : List (List X))
    (hΛred : ∀ r ∈ Λ, color r = Color.red)
    (horder : ∀ (L₁ : List X) (r : X) (L₂ : List X),
      Λ = L₁ ++ r :: L₂ → ∀ r' : X, color r' = Color.red →
      (τF r').val < (τF r).val → r' ∈ L₁ ∨ r' ∈ σ0.flatten) :
    ∀ {σ : List (List X)} {L : List X} {σf : List (List X)}
      (e : ExecFrom color σ L σf), ExecStepsClassified (color := color) e →
      ∀ (past : List X), Λ = past ++ L → Invariant color σ →
      MonoRuns color σ → σ.flatten.Perm (past ++ σ0.flatten) →
      ∀ ev ∈ e.ordinaryEvents, ∀ b ∈ ev.2,
        IsRecord color (fun x => (τF x).val) b ev.1 := by
  intro σ L σf e
  induction e with
  | nil σ =>
      intro _ _ _ _ _ _ ev hev
      simp [ExecFrom.ordinaryEvents] at hev
  | @cons σ σ' σf r rest step scans hsc tail ih =>
      intro hc past hΛ hinv hmono hprov ev hev
      obtain ⟨hch, htailch⟩ := hc
      have hrred : color r = Color.red := hΛred r (by rw [hΛ]; simp)
      obtain ⟨hinv', hmono'⟩ := step_invariant color step hinv hmono hrred
      have hprov' : σ'.flatten.Perm ((past ++ [r]) ++ σ0.flatten) := by
        have hp1 : σ'.flatten.Perm (r :: σ.flatten) := step_flatten color step
        have happ : ((past ++ [r]) ++ σ0.flatten).Perm
            (r :: (past ++ σ0.flatten)) := by
          rw [List.append_assoc]
          exact List.perm_middle
        exact (hp1.trans (List.Perm.cons r hprov)).trans happ.symm
      have hΛ' : Λ = (past ++ [r]) ++ rest := by
        rw [List.append_assoc]; exact hΛ
      by_cases hact : StepActivation color σ r scans
      · have hord : (ExecFrom.cons r step scans hsc tail).ordinaryEvents
            = tail.ordinaryEvents := by
          simp [ExecFrom.ordinaryEvents,
            stepIsActivation_of_activation (color := color) hact]
        rw [hord] at hev
        exact ih htailch (past ++ [r]) hΛ' hinv' hmono' hprov' ev hev
      · have hord : (ExecFrom.cons r step scans hsc tail).ordinaryEvents
            = (scans.map fun C => (r, C)) ++ tail.ordinaryEvents := by
          simp [ExecFrom.ordinaryEvents,
            stepIsActivation_of_not_activation (color := color) hact]
        rw [hord] at hev
        simp only [List.mem_append, List.mem_map] at hev
        rcases hev with ⟨C, hC, rfl⟩ | hev
        · intro b hb
          have hpresent : ∀ r' : X, color r' = Color.red →
              (fun x => (τF x).val) r' < (fun x => (τF x).val) r →
              r' ∈ σ.flatten := by
            intro r' hr' hlt
            rcases horder past r rest hΛ r' hr' hlt with h | h
            · exact hprov.mem_iff.mpr (List.mem_append.mpr (Or.inl h))
            · exact hprov.mem_iff.mpr (List.mem_append.mpr (Or.inr h))
          rcases hch with hcharged | hact2
          · exact stepCharged_events_record (color := color) τF hinjF
              hcharged hinv hrred hpresent C hC b hb
          · exact absurd hact2 hact
        · exact ih htailch (past ++ [r]) hΛ' hinv' hmono' hprov' ev hev

/-- Records for the activation events of a classified execution:
at an activation step, the founder is a record for every blue
element scanned (`activationAt_record`). The founder's record
uses only that earlier red elements are present in the current
state, which the initial state being all-blue gives from the
founder's presence there. -/
theorem activation_events_records
    (τF : X → Fin (Fintype.card X)) (hinjF : Function.Injective τF)
    (Λ : List X) (σ0 : List (List X))
    (hΛred : ∀ r ∈ Λ, color r = Color.red)
    (horder : ∀ (L₁ : List X) (r : X) (L₂ : List X),
      Λ = L₁ ++ r :: L₂ → ∀ r' : X, color r' = Color.red →
      (τF r').val < (τF r).val → r' ∈ L₁ ∨ r' ∈ σ0.flatten)
    (hσ0blue : ∀ x ∈ σ0.flatten, color x = Color.blue) :
    ∀ {σ : List (List X)} {L : List X} {σf : List (List X)}
      (e : ExecFrom color σ L σf), ExecStepsClassified (color := color) e →
      ∀ (past : List X), Λ = past ++ L → Invariant color σ →
      MonoRuns color σ → σ.flatten.Perm (past ++ σ0.flatten) →
      ∀ ev ∈ e.activationEvents, ∀ b ∈ ev.2,
        IsRecord color (fun x => (τF x).val) b ev.1 := by
  intro σ L σf e
  induction e with
  | nil σ =>
      intro _ _ _ _ _ _ ev hev
      simp [ExecFrom.activationEvents] at hev
  | @cons σ σ' σf r rest step scans hsc tail ih =>
      intro hc past hΛ hinv hmono hprov ev hev
      obtain ⟨hch, htailch⟩ := hc
      have hrred : color r = Color.red := hΛred r (by rw [hΛ]; simp)
      obtain ⟨hinv', hmono'⟩ := step_invariant color step hinv hmono hrred
      have hprov' : σ'.flatten.Perm ((past ++ [r]) ++ σ0.flatten) := by
        have hp1 : σ'.flatten.Perm (r :: σ.flatten) := step_flatten color step
        have happ : ((past ++ [r]) ++ σ0.flatten).Perm
            (r :: (past ++ σ0.flatten)) := by
          rw [List.append_assoc]
          exact List.perm_middle
        exact (hp1.trans (List.Perm.cons r hprov)).trans happ.symm
      have hΛ' : Λ = (past ++ [r]) ++ rest := by
        rw [List.append_assoc]; exact hΛ
      by_cases hact : StepActivation color σ r scans
      · obtain ⟨q, hAt, hEq⟩ :=
          activationEvents_cons_of_activation (color := color) step scans
            hsc tail hact
        rw [hEq] at hev
        simp only [List.mem_append, List.mem_map] at hev
        rcases hev with ⟨C, hC, rfl⟩ | hev
        · intro b hb
          have hqred : color q = Color.red :=
            activationAt_founder_red (color := color) hAt
          have hqmem : q ∈ σ.flatten :=
            activationAt_founder_mem (color := color) hAt
          have hqpast : q ∈ past := by
            have hmem : q ∈ past ++ σ0.flatten := hprov.mem_iff.mp hqmem
            rcases List.mem_append.mp hmem with h | h
            · exact h
            · have hblue : color q = Color.blue := hσ0blue q h
              rw [hqred] at hblue
              have hfalse : False := Color.noConfusion hblue
              exact hfalse.elim
          obtain ⟨L₁, L₂, hpast⟩ := List.append_of_mem hqpast
          have hΛq : Λ = L₁ ++ q :: (L₂ ++ r :: rest) := by
            rw [hΛ, hpast]
            simp [List.append_assoc]
          have hpresent : ∀ r' : X, color r' = Color.red →
              (fun x => (τF x).val) r' < (fun x => (τF x).val) q →
              r' ∈ σ.flatten := by
            intro r' hr' hlt
            rcases horder L₁ q (L₂ ++ r :: rest) hΛq r' hr' hlt with h | h
            · apply hprov.mem_iff.mpr
              rw [hpast]
              exact List.mem_append.mpr
                (Or.inl (List.mem_append.mpr (Or.inl h)))
            · exact hprov.mem_iff.mpr (List.mem_append.mpr (Or.inr h))
          have hinj : Function.Injective (fun x => (τF x).val) := by
            intro x y h
            exact hinjF (Fin.ext h)
          exact activationAt_record (color := color) hAt hinv.2.1 hqred
            (fun x => (τF x).val) hinj hpresent C hC b hb
        · exact ih htailch (past ++ [r]) hΛ' hinv' hmono' hprov' ev hev
      · have hEq :=
          activationEvents_cons_of_not_activation (color := color) step
            scans hsc tail hact
        rw [hEq] at hev
        exact ih htailch (past ++ [r]) hΛ' hinv' hmono' hprov' ev hev

/-- An activation step's scanned runs meet a fixed element `b`
at most once: the two neighbours of the candidate are separated
by the candidate's run in the flattened order, so `b` cannot
lie in both. -/
theorem activation_scans_filter_length_le {σ : List (List X)}
    (hnd : σ.flatten.Nodup)
    {r q : X} {scans : List (List X)}
    (hAt : ActivationAt color σ r q scans) (b : X) :
    (scans.filter (fun C => b ∈ C)).length ≤ 1 := by
  rcases hAt with ⟨A, B, L, S, U, hσ, -, -, -, -, -, -, hscans⟩
    | ⟨B, S, C, -, -, -, -, -, -, hscans⟩
    | ⟨A, C, S, -, -, -, -, -, -, hscans⟩
  · rw [hscans]
    by_cases hbL : b ∈ L
    · by_cases hbU : b ∈ U
      · have hflat : σ.flatten = (A.flatten ++ L ++ S) ++ (U ++ B.flatten) := by
          rw [hσ]
          simp [List.flatten_append, List.flatten_cons, List.append_assoc]
        have hnd2 : ((A.flatten ++ L ++ S) ++ (U ++ B.flatten)).Nodup :=
          hflat ▸ hnd
        have hdisj := (List.nodup_append.mp hnd2).2.2
        have hbleft : b ∈ A.flatten ++ L ++ S :=
          List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hbL)))
        have hbright : b ∈ U ++ B.flatten :=
          List.mem_append.mpr (Or.inl hbU)
        exact False.elim ((hdisj b hbleft b hbright) rfl)
      · simp [hbL, hbU]
    · by_cases hbU : b ∈ U
      · simp [hbL, hbU]
      · simp [hbL, hbU]
  · rw [hscans]
    exact (List.filter_sublist (p := fun C => decide (b ∈ C))).length_le
  · rw [hscans]
    exact (List.filter_sublist (p := fun C => decide (b ∈ C))).length_le

/-- A run of a state with duplicate-free flattening is itself
duplicate-free. -/
theorem nodup_run_of_flatten_nodup {σ : List (List X)}
    (hnd : σ.flatten.Nodup) {R : List X} (hR : R ∈ σ) : R.Nodup := by
  induction σ with
  | nil => simp at hR
  | cons S σ ih =>
      rw [List.flatten_cons] at hnd
      obtain ⟨hS, hσnd, -⟩ := List.nodup_append.mp hnd
      cases List.mem_cons.mp hR with
      | inl he => rw [he]; exact hS
      | inr he => exact ih hσnd he

/-- A duplicate-free run of length at least two containing `q`
contains another element. -/
theorem exists_ne_of_nodup_length {R : List X} (hndR : R.Nodup)
    {q : X} (hq : q ∈ R) (hlen : 2 ≤ R.length) :
    ∃ y ∈ R, y ≠ q := by
  have hpos : 0 < (R.erase q).length := by
    have h1 : (R.erase q).length = R.length - 1 :=
      List.length_erase_of_mem hq
    omega
  obtain ⟨y, hy⟩ : ∃ y, y ∈ R.erase q := by
    cases h : R.erase q with
    | nil => simp [h] at hpos
    | cons y t => exact ⟨y, List.mem_cons_self⟩
  refine ⟨y, List.mem_of_mem_erase hy, ?_⟩
  intro hyq
  rw [hyq] at hy
  exact hndR.not_mem_erase hy

/-- Mapping a constant over a list of length at most one is
duplicate-free. -/
theorem nodup_map_const_of_length_le_one {F : List (List X)} {q : X}
    (hF : F.length ≤ 1) : (F.map (fun _ => q)).Nodup := by
  cases F with
  | nil => simp
  | cons C t =>
      cases t with
      | nil => simp
      | cons C₂ t₂ => simp at hF

/-- The founder's singleton run is a run of the activation
state. -/
theorem activationAt_founder_run {σ : List (List X)} {r q : X}
    {scans : List (List X)} (h : ActivationAt color σ r q scans) :
    [q] ∈ σ := by
  rcases h with ⟨A, B, L, S, U, hσ, hS, -⟩
    | ⟨B, S, C, hσ, hS, -⟩
    | ⟨A, C, S, hσ, hS, -⟩ <;>
    · rw [hσ]; simp [hS]

/-- Distinctness and blocking for activation events: for every
blue element `b`, the founders charged with scanning `b` are
distinct across the whole execution; and a red element already
sitting in a run with another element is never charged as a
founder. The second claim is proved simultaneously: after an
activation the founder's run has grown (`ExecActivationGrows`),
forward persistence keeps the founder in a multi-element run,
and blocking is preserved by every step. -/
theorem activationEvents_fst_nodup_and_blocked
    (Λ : List X) (σ0 : List (List X))
    (hΛred : ∀ r ∈ Λ, color r = Color.red)
    (hΛnd : Λ.Nodup) (hΛfresh : ∀ r ∈ Λ, r ∉ σ0.flatten) :
    ∀ {σ : List (List X)} {L : List X} {σf : List (List X)}
      (e : ExecFrom color σ L σf), ExecStepsClassified (color := color) e →
      ExecActivationGrows (color := color) e →
      ∀ (past : List X), Λ = past ++ L → Invariant color σ →
      MonoRuns color σ → σ.flatten.Nodup →
      σ.flatten.Perm (past ++ σ0.flatten) →
      (∀ b, ((e.activationEvents.filter (fun ev => b ∈ ev.2)).map
          Prod.fst).Nodup) ∧
      (∀ q, color q = Color.red →
        (∃ R ∈ σ, q ∈ R ∧ ∃ y ∈ R, y ≠ q) →
        ∀ b, q ∉ ((e.activationEvents.filter (fun ev => b ∈ ev.2)).map
          Prod.fst)) := by
  intro σ L σf e
  induction e with
  | nil σ =>
      intro _ _ _ _ _ _ _ _
      refine ⟨fun b => by simp [ExecFrom.activationEvents], ?_⟩
      intro q _ _ b
      simp [ExecFrom.activationEvents]
  | @cons σ σ' σf r rest step scans hsc tail ih =>
      intro hc hg past hΛ hinv hmono hndσ hprov
      obtain ⟨hch, htailch⟩ := hc
      obtain ⟨hg1, hg2⟩ := hg
      have hrred : color r = Color.red := hΛred r (by rw [hΛ]; simp)
      obtain ⟨hinv', hmono'⟩ := step_invariant color step hinv hmono hrred
      have hprov' : σ'.flatten.Perm ((past ++ [r]) ++ σ0.flatten) := by
        have hp1 : σ'.flatten.Perm (r :: σ.flatten) := step_flatten color step
        have happ : ((past ++ [r]) ++ σ0.flatten).Perm
            (r :: (past ++ σ0.flatten)) := by
          rw [List.append_assoc]
          exact List.perm_middle
        exact (hp1.trans (List.Perm.cons r hprov)).trans happ.symm
      have hΛ' : Λ = (past ++ [r]) ++ rest := by
        rw [List.append_assoc]; exact hΛ
      have hrpast : r ∉ past := by
        have hnd : (past ++ r :: rest).Nodup := hΛ ▸ hΛnd
        intro hrp
        exact (List.nodup_append.mp hnd).2.2 r hrp r List.mem_cons_self rfl
      have hrσ : r ∉ σ.flatten := by
        intro hcon
        have hmem : r ∈ past ++ σ0.flatten := hprov.mem_iff.mp hcon
        rcases List.mem_append.mp hmem with h | h
        · exact hrpast h
        · exact hΛfresh r (by rw [hΛ]; simp) h
      have hndσ' : σ'.flatten.Nodup :=
        (step_flatten color step).nodup_iff.mpr
          (List.nodup_cons.mpr ⟨hrσ, hndσ⟩)
      obtain ⟨ih1, ih2⟩ := ih htailch hg2 (past ++ [r]) hΛ' hinv' hmono'
        hndσ' hprov'
      have hblocked' : ∀ q, color q = Color.red →
          (∃ R ∈ σ, q ∈ R ∧ ∃ y ∈ R, y ≠ q) →
          ∃ R ∈ σ', q ∈ R ∧ ∃ y ∈ R, y ≠ q := by
        intro q hqred ⟨R, hR, hqR, y, hyR, hyq⟩
        obtain ⟨R', hR', hqR', hyR'⟩ :=
          step_same_run_forward (color := color) step hqred hR hqR hyR
        exact ⟨R', hR', hqR', y, hyR', hyq⟩
      constructor
      · intro b
        by_cases hact : StepActivation color σ r scans
        · obtain ⟨q, hAt, hEq⟩ :=
            activationEvents_cons_of_activation (color := color) step scans
              hsc tail hact
          rw [hEq, List.filter_append, List.map_append]
          have hhead : ((scans.map fun C => (q, C)).filter
                (fun ev => b ∈ ev.2)).map Prod.fst
              = (scans.filter (fun C => b ∈ C)).map (fun _ => q) := by
            simp only [List.filter_map, List.map_map]
            rfl
          rw [hhead]
          apply List.nodup_append.mpr
          refine ⟨nodup_map_const_of_length_le_one (q := q) ?_,
            ih1 b, ?_⟩
          · exact activation_scans_filter_length_le (color := color)
              hndσ hAt b
          · intro x hx1 y hx2 hxy
            have hxq : x = q := by
              obtain ⟨C, -, hCeq⟩ := List.mem_map.mp hx1
              rw [← hCeq]
            have hqx : q ∉ ((tail.activationEvents.filter
                (fun ev => b ∈ ev.2)).map Prod.fst) := by
              apply ih2 q (activationAt_founder_red (color := color) hAt) _ b
              obtain ⟨R, hR, hqR, hlenR⟩ := hg1 q hAt
              exact ⟨R, hR, hqR,
                exists_ne_of_nodup_length
                  (nodup_run_of_flatten_nodup hndσ' hR) hqR hlenR⟩
            exact hqx ((hxq.symm.trans hxy) ▸ hx2)
        · have hEq :=
            activationEvents_cons_of_not_activation (color := color) step
              scans hsc tail hact
          rw [hEq]
          exact ih1 b
      · intro q hqred hblocked b
        obtain ⟨R, hR, hqR, y, hyR, hyq⟩ := hblocked
        by_cases hact : StepActivation color σ r scans
        · obtain ⟨q₀, hAt, hEq⟩ :=
            activationEvents_cons_of_activation (color := color) step scans
              hsc tail hact
          rw [hEq, List.filter_append, List.map_append, List.mem_append]
          intro hmem
          rcases hmem with hhead | htail
          · have hqq₀ : q = q₀ := by
              have hhead2 : ((scans.map fun C => (q₀, C)).filter
                    (fun ev => b ∈ ev.2)).map Prod.fst
                  = (scans.filter (fun C => b ∈ C)).map (fun _ => q₀) := by
                simp only [List.filter_map, List.map_map]
                rfl
              rw [hhead2] at hhead
              obtain ⟨C, -, hCeq⟩ := List.mem_map.mp hhead
              rw [← hCeq]
            have hReq : R = [q] := by
              have hReq0 : R = [q₀] :=
                run_unique (R₂ := [q₀]) hndσ hR
                  (activationAt_founder_run (color := color) (q := q₀) hAt)
                  hqR (by rw [hqq₀]; simp)
              rwa [← hqq₀] at hReq0
            exact hyq (by rw [hReq] at hyR; simpa using hyR)
          · exact ih2 q hqred (hblocked' q hqred ⟨R, hR, hqR, y, hyR, hyq⟩)
              b htail
        · have hEq :=
            activationEvents_cons_of_not_activation (color := color) step
              scans hsc tail hact
          rw [hEq]
          exact ih2 q hqred (hblocked' q hqred ⟨R, hR, hqR, y, hyR, hyq⟩) b

/-- Distinctness for activation events. -/
theorem activationEvents_fst_nodup
    (Λ : List X) (σ0 : List (List X))
    (hΛred : ∀ r ∈ Λ, color r = Color.red)
    (hΛnd : Λ.Nodup) (hΛfresh : ∀ r ∈ Λ, r ∉ σ0.flatten) :
    ∀ {σ : List (List X)} {L : List X} {σf : List (List X)}
      (e : ExecFrom color σ L σf), ExecStepsClassified (color := color) e →
      ExecActivationGrows (color := color) e →
      ∀ (past : List X), Λ = past ++ L → Invariant color σ →
      MonoRuns color σ → σ.flatten.Nodup →
      σ.flatten.Perm (past ++ σ0.flatten) →
      ∀ b, ((e.activationEvents.filter (fun ev => b ∈ ev.2)).map
        Prod.fst).Nodup :=
  fun e hc hg past hΛ hinv hmono hnd hprov =>
    (activationEvents_fst_nodup_and_blocked (color := color) Λ σ0 hΛred
      hΛnd hΛfresh e hc hg past hΛ hinv hmono hnd hprov).1

/-- Every ordinary event's first component is an arrival of the
execution. -/
theorem ordinaryEvents_fst_mem {σ : List (List X)} {L : List X}
    {σf : List (List X)} (e : ExecFrom color σ L σf) :
    ∀ ev ∈ e.ordinaryEvents, ev.1 ∈ L := by
  induction e with
  | nil σ =>
      intro ev hev
      simp [ExecFrom.ordinaryEvents] at hev
  | @cons σ σ' σf r rest step scans hsc tail ih =>
      intro ev hev
      by_cases hact : StepActivation color σ r scans
      · have hord : (ExecFrom.cons r step scans hsc tail).ordinaryEvents
            = tail.ordinaryEvents := by
          simp [ExecFrom.ordinaryEvents,
            stepIsActivation_of_activation (color := color) hact]
        rw [hord] at hev
        exact List.mem_cons_of_mem r (ih ev hev)
      · have hord : (ExecFrom.cons r step scans hsc tail).ordinaryEvents
            = (scans.map fun C => (r, C)) ++ tail.ordinaryEvents := by
          simp [ExecFrom.ordinaryEvents,
            stepIsActivation_of_not_activation (color := color) hact]
        rw [hord] at hev
        simp only [List.mem_append, List.mem_map] at hev
        rcases hev with ⟨C, -, rfl⟩ | hev
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem r (ih ev hev)

/-- Distinctness for ordinary events: an arrival scans at most
one run in a charged step, and distinct arrivals are distinct,
so the arrivals charged with scanning a fixed `b` are distinct
across the execution. -/
theorem ordinaryEvents_fst_nodup
    (Λ : List X) (σ0 : List (List X))
    (hΛred : ∀ r ∈ Λ, color r = Color.red)
    (hΛnd : Λ.Nodup) (hΛfresh : ∀ r ∈ Λ, r ∉ σ0.flatten) :
    ∀ {σ : List (List X)} {L : List X} {σf : List (List X)}
      (e : ExecFrom color σ L σf), ExecStepsClassified (color := color) e →
      ∀ (past : List X), Λ = past ++ L → Invariant color σ →
      MonoRuns color σ → σ.flatten.Nodup →
      σ.flatten.Perm (past ++ σ0.flatten) →
      ∀ b, ((e.ordinaryEvents.filter (fun ev => b ∈ ev.2)).map
        Prod.fst).Nodup := by
  intro σ L σf e
  induction e with
  | nil σ =>
      intro _ _ _ _ _ _ _ b
      simp [ExecFrom.ordinaryEvents]
  | @cons σ σ' σf r rest step scans hsc tail ih =>
      intro hc past hΛ hinv hmono hndσ hprov b
      obtain ⟨hch, htailch⟩ := hc
      have hrred : color r = Color.red := hΛred r (by rw [hΛ]; simp)
      obtain ⟨hinv', hmono'⟩ := step_invariant color step hinv hmono hrred
      have hprov' : σ'.flatten.Perm ((past ++ [r]) ++ σ0.flatten) := by
        have hp1 : σ'.flatten.Perm (r :: σ.flatten) := step_flatten color step
        have happ : ((past ++ [r]) ++ σ0.flatten).Perm
            (r :: (past ++ σ0.flatten)) := by
          rw [List.append_assoc]
          exact List.perm_middle
        exact (hp1.trans (List.Perm.cons r hprov)).trans happ.symm
      have hΛ' : Λ = (past ++ [r]) ++ rest := by
        rw [List.append_assoc]; exact hΛ
      have hrpast : r ∉ past := by
        have hnd : (past ++ r :: rest).Nodup := hΛ ▸ hΛnd
        intro hrp
        exact (List.nodup_append.mp hnd).2.2 r hrp r List.mem_cons_self rfl
      have hrσ : r ∉ σ.flatten := by
        intro hcon
        have hmem : r ∈ past ++ σ0.flatten := hprov.mem_iff.mp hcon
        rcases List.mem_append.mp hmem with h | h
        · exact hrpast h
        · exact hΛfresh r (by rw [hΛ]; simp) h
      have hndσ' : σ'.flatten.Nodup :=
        (step_flatten color step).nodup_iff.mpr
          (List.nodup_cons.mpr ⟨hrσ, hndσ⟩)
      have htail := ih htailch (past ++ [r]) hΛ' hinv' hmono' hndσ' hprov' b
      by_cases hact : StepActivation color σ r scans
      · have hord : (ExecFrom.cons r step scans hsc tail).ordinaryEvents
            = tail.ordinaryEvents := by
          simp [ExecFrom.ordinaryEvents,
            stepIsActivation_of_activation (color := color) hact]
        rw [hord]
        exact htail
      · have hord : (ExecFrom.cons r step scans hsc tail).ordinaryEvents
            = (scans.map fun C => (r, C)) ++ tail.ordinaryEvents := by
          simp [ExecFrom.ordinaryEvents,
            stepIsActivation_of_not_activation (color := color) hact]
        rw [hord, List.filter_append, List.map_append]
        have hhead : ((scans.map fun C => (r, C)).filter
              (fun ev => b ∈ ev.2)).map Prod.fst
            = (scans.filter (fun C => b ∈ C)).map (fun _ => r) := by
          simp only [List.filter_map, List.map_map]
          rfl
        rw [hhead]
        have hcharged : StepCharged color σ r scans := by
          rcases hch with h | h
          · exact h
          · exact absurd h hact
        have hlen : (scans.filter (fun C => b ∈ C)).length ≤ 1 := by
          rcases hcharged with hq | ⟨A, B, C, -, -, -, hse⟩
            | ⟨B, C, -, -, -, hse⟩ | ⟨A, C, -, -, -, hse⟩
            | ⟨A, B, C, S, -, -, -, -, -, hse⟩
            | ⟨A, B, C, S, -, -, -, -, -, hse⟩
          · rw [hq]; simp
          · rw [hse]
            exact (List.filter_sublist (p := fun C => decide (b ∈ C))).length_le
          · rw [hse]
            exact (List.filter_sublist (p := fun C => decide (b ∈ C))).length_le
          · rw [hse]
            exact (List.filter_sublist (p := fun C => decide (b ∈ C))).length_le
          · rw [hse]
            exact (List.filter_sublist (p := fun C => decide (b ∈ C))).length_le
          · rw [hse]
            exact (List.filter_sublist (p := fun C => decide (b ∈ C))).length_le
        apply List.nodup_append.mpr
        refine ⟨nodup_map_const_of_length_le_one (q := r) ?_, htail, ?_⟩
        · exact hlen
        · intro x hx1 y hx2 hxy
          have hxr : x = r := by
            obtain ⟨C, -, hCeq⟩ := List.mem_map.mp hx1
            rw [← hCeq]
          have hxrest : y ∈ rest := by
            obtain ⟨ev, hev, rfl⟩ := List.mem_map.mp hx2
            rw [List.mem_filter] at hev
            exact ordinaryEvents_fst_mem (color := color) tail ev hev.1
          have hrnd : r ∉ rest := by
            have hnd : (past ++ r :: rest).Nodup := hΛ ▸ hΛnd
            have h2 : (r :: rest).Nodup := (List.nodup_append.mp hnd).2.1
            exact (List.nodup_cons.mp h2).1
          exact hrnd ((hxr.symm.trans hxy) ▸ hxrest)

/-- Every event's scanned run is duplicate-free: scanned runs are
runs of states whose flattening is duplicate-free. -/
theorem events_snd_nodup
    (Λ : List X) (σ0 : List (List X))
    (hΛnd : Λ.Nodup) (hΛfresh : ∀ r ∈ Λ, r ∉ σ0.flatten) :
    ∀ {σ : List (List X)} {L : List X} {σf : List (List X)}
      (e : ExecFrom color σ L σf) (past : List X),
      Λ = past ++ L → σ.flatten.Nodup →
      σ.flatten.Perm (past ++ σ0.flatten) →
      (∀ ev ∈ e.events, ev.2.Nodup) ∧
      (∀ ev ∈ e.ordinaryEvents, ev.2.Nodup) ∧
      (∀ ev ∈ e.activationEvents, ev.2.Nodup) := by
  intro σ L σf e
  induction e with
  | nil σ =>
      intro _ _ _ _
      refine ⟨fun ev hev => by simp [ExecFrom.events] at hev,
        fun ev hev => by simp [ExecFrom.ordinaryEvents] at hev,
        fun ev hev => by simp [ExecFrom.activationEvents] at hev⟩
  | @cons σ σ' σf r rest step scans hsc tail ih =>
      intro past hΛ hndσ hprov
      have hrpast : r ∉ past := by
        have hnd : (past ++ r :: rest).Nodup := hΛ ▸ hΛnd
        intro hrp
        exact (List.nodup_append.mp hnd).2.2 r hrp r List.mem_cons_self rfl
      have hrσ : r ∉ σ.flatten := by
        intro hcon
        have hmem : r ∈ past ++ σ0.flatten := hprov.mem_iff.mp hcon
        rcases List.mem_append.mp hmem with h | h
        · exact hrpast h
        · exact hΛfresh r (by rw [hΛ]; simp) h
      have hndσ' : σ'.flatten.Nodup :=
        (step_flatten color step).nodup_iff.mpr
          (List.nodup_cons.mpr ⟨hrσ, hndσ⟩)
      have hprov' : σ'.flatten.Perm ((past ++ [r]) ++ σ0.flatten) := by
        have hp1 : σ'.flatten.Perm (r :: σ.flatten) := step_flatten color step
        have happ : ((past ++ [r]) ++ σ0.flatten).Perm
            (r :: (past ++ σ0.flatten)) := by
          rw [List.append_assoc]
          exact List.perm_middle
        exact (hp1.trans (List.Perm.cons r hprov)).trans happ.symm
      have hΛ' : Λ = (past ++ [r]) ++ rest := by
        rw [List.append_assoc]; exact hΛ
      obtain ⟨ih1, ih2, ih3⟩ := ih (past ++ [r]) hΛ' hndσ' hprov'
      have hscnd : ∀ C ∈ scans, C.Nodup :=
        fun C hC => nodup_run_of_flatten_nodup hndσ (hsc C hC)
      refine ⟨?_, ?_, ?_⟩
      · intro ev hev
        simp only [ExecFrom.events, List.mem_append, List.mem_map] at hev
        rcases hev with ⟨C, hC, rfl⟩ | hev
        · exact hscnd C hC
        · exact ih1 ev hev
      · intro ev hev
        by_cases hact : StepActivation color σ r scans
        · have hord : (ExecFrom.cons r step scans hsc tail).ordinaryEvents
              = tail.ordinaryEvents := by
            simp [ExecFrom.ordinaryEvents,
              stepIsActivation_of_activation (color := color) hact]
          rw [hord] at hev
          exact ih2 ev hev
        · have hord : (ExecFrom.cons r step scans hsc tail).ordinaryEvents
              = (scans.map fun C => (r, C)) ++ tail.ordinaryEvents := by
            simp [ExecFrom.ordinaryEvents,
              stepIsActivation_of_not_activation (color := color) hact]
          rw [hord] at hev
          simp only [List.mem_append, List.mem_map] at hev
          rcases hev with ⟨C, hC, rfl⟩ | hev
          · exact hscnd C hC
          · exact ih2 ev hev
      · intro ev hev
        by_cases hact : StepActivation color σ r scans
        · obtain ⟨q, -, hEq⟩ :=
            activationEvents_cons_of_activation (color := color) step scans
              hsc tail hact
          rw [hEq] at hev
          simp only [List.mem_append, List.mem_map] at hev
          rcases hev with ⟨C, hC, rfl⟩ | hev
          · exact hscnd C hC
          · exact ih3 ev hev
        · have hEq :=
            activationEvents_cons_of_not_activation (color := color) step
              scans hsc tail hact
          rw [hEq] at hev
          exact ih3 ev hev

/-- The flattening of an ordered, internally sorted run list is
sorted: elements within a run are sorted by internal sortedness,
and elements across runs are separated by run order. This is the
output half of the final-runs lemma. -/
theorem flatten_pairwise_le {σ : List (List X)}
    (hord : RunsOrdered σ) (hsrt : RunsInternallySorted color σ) :
    σ.flatten.Pairwise (· ≤ ·) := by
  induction σ with
  | nil => simp
  | cons R σ ih =>
      rw [List.flatten_cons]
      obtain ⟨hRrel, hordσ⟩ := List.pairwise_cons.mp hord
      have ih' := ih hordσ (fun S hS => hsrt S (List.mem_cons_of_mem R hS))
      apply List.pairwise_append.mpr
      refine ⟨hsrt R List.mem_cons_self, ih', ?_⟩
      intro x hx y hy
      obtain ⟨S, hS, hyS⟩ := List.mem_flatten.mp hy
      exact le_of_lt (hRrel S hS x hx y hyS)

end Bichromatic.Randomized
