import RandomizedLog.TotalCost

/-!
# The benchmark is the cheapest proof (`prop:Hlower`)

The paper's Proposition (`prop:Hlower`): every comparison algorithm
pays at least `H` on every input, and `H` is exactly the cost of the
cheapest proof of the sorted order. Following the paper's own proof,
we lower-bound every *determining* set of comparisons: a set of
compared pairs (a simple graph `G` on the elements) whose outcomes
leave exactly one order standing. A candidate order is a list `L`
(a permutation of the sorted list); it is *consistent* with `G` if
no compared pair is inverted in `L`, and `G` is *determining* if
the sorted list is the only consistent candidate.

The lower bound has the paper's three parts: inside each colour run
of size `s`, the compared pairs must connect the run, contributing
at least `s - 1` monochromatic comparisons at the run's price; and
the runs must be stitched together by at least `K - 1` cross-run
comparisons at cost at least `1` each. Tightness: the adjacent
pairs of the sorted order are determining and cost exactly `H`.
-/

namespace Bichromatic.Randomized

open Bichromatic

variable {X : Type*} [LinearOrder X] [Fintype X]

theorem pairCost_symm (α β : ℝ) (color : X → Color) (x y : X) :
    pairCost α β color x y = pairCost α β color y x := by
  unfold pairCost
  by_cases h : color x = color y
  · rw [if_pos h, if_pos h.symm, h]
  · rw [if_neg h, if_neg (fun hh => h hh.symm)]

/-- The cost of one compared pair, as a function on unordered pairs. -/
def edgeCost (α β : ℝ) (color : X → Color) : Sym2 X → ℝ :=
  Sym2.lift ⟨fun x y => pairCost α β color x y,
    fun x y => pairCost_symm α β color x y⟩

open Classical in
/-- The total cost of a set of comparisons. -/
noncomputable def graphCost (α β : ℝ) (color : X → Color)
    (G : SimpleGraph X) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => e ∈ G.edgeSet),
    edgeCost α β color e

theorem edgeCost_mk (α β : ℝ) (color : X → Color) (x y : X) :
    edgeCost α β color s(x, y) = pairCost α β color x y := rfl

theorem edgeCost_ge_one (α β : ℝ) (color : X → Color)
    (hα : 1 ≤ α) (hβ : 1 ≤ β) (e : Sym2 X) :
    1 ≤ edgeCost α β color e := by
  refine Sym2.ind (fun x y => ?_) e
  rw [edgeCost_mk]
  exact pairCost_ge_one α β color hα hβ x y

/-- `x` comes strictly before `y` in the list `L`. -/
def Before (L : List X) (x y : X) : Prop :=
  ∃ a b c, L = a ++ x :: b ++ y :: c

theorem before_mem {L : List X} {x y : X} (h : Before L x y) :
    x ∈ L ∧ y ∈ L := by
  obtain ⟨a, b, c, rfl⟩ := h
  constructor <;> simp

theorem before_cons {z : X} {t : List X} {x y : X} :
    Before (z :: t) x y ↔ (x = z ∧ y ∈ t) ∨ Before t x y := by
  constructor
  · intro h
    obtain ⟨a, b, c, ha⟩ := h
    cases a with
    | nil =>
      have h2 : z = x ∧ t = b ++ y :: c :=
        List.cons.inj (by simpa using ha)
      exact Or.inl ⟨h2.1.symm, by rw [h2.2]; simp⟩
    | cons w a' =>
      have h2 : z = w ∧ t = a' ++ x :: b ++ y :: c :=
        List.cons.inj (by simpa using ha)
      exact Or.inr ⟨a', b, c, h2.2⟩
  · rintro (⟨rfl, hy⟩ | ⟨a, b, c, rfl⟩)
    · obtain ⟨u, v, hv⟩ := List.append_of_mem hy
      exact ⟨[], u, v, by simp [hv]⟩
    · exact ⟨z :: a, b, c, by simp⟩

theorem before_trans {L : List X} (hnd : L.Nodup) {x y z : X}
    (h1 : Before L x y) (h2 : Before L y z) : Before L x z := by
  induction L with
  | nil => obtain ⟨a, b, c, ha⟩ := h1; simp at ha
  | cons w t ih =>
    rw [List.nodup_cons] at hnd
    rw [before_cons] at h1 h2 ⊢
    rcases h1 with ⟨rfl, hy⟩ | h1
    · rcases h2 with ⟨hyz, -⟩ | h2
      · exact absurd hyz (by
          intro hh
          rw [hh] at hy
          exact hnd.1 hy)
      · exact Or.inl ⟨rfl, (before_mem h2).2⟩
    · rcases h2 with ⟨hyw, -⟩ | h2
      · exfalso
        have hw : w ∈ t := by
          have hmem : y ∈ t := (before_mem h1).2
          rwa [hyw] at hmem
        exact hnd.1 hw
      · exact Or.inr (ih hnd.2 h1 h2)

theorem before_dichotomy {L : List X} (hnd : L.Nodup) {x y : X}
    (hx : x ∈ L) (hy : y ∈ L) (hxy : x ≠ y) :
    Before L x y ∨ Before L y x := by
  induction L with
  | nil => simp at hx
  | cons z t ih =>
    rw [List.nodup_cons] at hnd
    cases hx with
    | head =>
      refine Or.inl ?_
      rw [before_cons]
      refine Or.inl ⟨rfl, ?_⟩
      cases hy with
      | head => simp at hxy
      | tail _ hy => exact hy
    | tail _ hx =>
      cases hy with
      | head =>
        refine Or.inr ?_
        rw [before_cons]
        exact Or.inl ⟨rfl, hx⟩
      | tail _ hy =>
        rcases ih hnd.2 hx hy with h | h
        · refine Or.inl ?_
          rw [before_cons]
          exact Or.inr h
        · refine Or.inr ?_
          rw [before_cons]
          exact Or.inr h

theorem before_irrefl {L : List X} (hnd : L.Nodup) {x : X} :
    ¬ Before L x x := by
  intro h
  induction L with
  | nil => obtain ⟨a, b, c, ha⟩ := h; simp at ha
  | cons z t ih =>
    rw [List.nodup_cons] at hnd
    rw [before_cons] at h
    rcases h with ⟨rfl, hx⟩ | h
    · exact hnd.1 hx
    · exact ih hnd.2 h

theorem before_antisymm {L : List X} (hnd : L.Nodup) {x y : X}
    (h1 : Before L x y) (h2 : Before L y x) : False := by
  induction L with
  | nil => obtain ⟨a, b, c, ha⟩ := h1; simp at ha
  | cons z t ih =>
    rw [List.nodup_cons] at hnd
    rw [before_cons] at h1 h2
    rcases h1 with ⟨rfl, hy⟩ | h1
    · rcases h2 with ⟨hyz, -⟩ | h2
      · rw [hyz] at hy; exact hnd.1 hy
      · exact hnd.1 (before_mem h2).2
    · rcases h2 with ⟨rfl, hx⟩ | h2
      · exact hnd.1 (before_mem h1).2
      · exact ih hnd.2 h1 h2

theorem pairwise_of_before {R : X → X → Prop} {L : List X}
    (h : L.Pairwise R) {x y : X} (hxy : Before L x y) : R x y := by
  cases h with
  | nil => obtain ⟨a, b, c, ha⟩ := hxy; simp at ha
  | cons hz ht =>
    rw [before_cons] at hxy
    rcases hxy with ⟨rfl, hy⟩ | hxy
    · exact hz y hy
    · exact pairwise_of_before ht hxy

theorem before_of_mem_append {l₁ l₂ : List X} {x y : X}
    (hx : x ∈ l₁) (hy : y ∈ l₂) : Before (l₁ ++ l₂) x y := by
  obtain ⟨a, b, ha⟩ := List.append_of_mem hx
  obtain ⟨c, d, hc⟩ := List.append_of_mem hy
  exact ⟨a, b ++ c, d, by rw [ha, hc]; simp [List.append_assoc]⟩

theorem before_append_or {l₁ l₂ : List X} {x y : X}
    (h : Before (l₁ ++ l₂) x y) :
    Before l₁ x y ∨ (x ∈ l₁ ∧ y ∈ l₂) ∨ Before l₂ x y := by
  induction l₁ with
  | nil => exact Or.inr (Or.inr h)
  | cons z t ih =>
    rw [List.cons_append, before_cons] at h
    rcases h with ⟨rfl, hy⟩ | h
    · simp only [List.mem_append] at hy
      rcases hy with hy | hy
      · refine Or.inl ?_
        rw [before_cons]
        exact Or.inl ⟨rfl, hy⟩
      · exact Or.inr (Or.inl ⟨by simp, hy⟩)
    · rcases ih h with h | h | h
      · refine Or.inl ?_
        rw [before_cons]
        exact Or.inr h
      · exact Or.inr (Or.inl ⟨List.mem_cons_of_mem z h.1, h.2⟩)
      · exact Or.inr (Or.inr h)

theorem eq_of_before_eq {L₁ L₂ : List X}
    (hnd₁ : L₁.Nodup) (hnd₂ : L₂.Nodup)
    (hmem : ∀ x, x ∈ L₁ ↔ x ∈ L₂)
    (hbef : ∀ x y, Before L₁ x y ↔ Before L₂ x y) : L₁ = L₂ := by
  induction L₁ generalizing L₂ with
  | nil =>
    cases L₂ with
    | nil => rfl
    | cons z t =>
      exact absurd ((hmem z).mpr (by simp)) (by simp)
  | cons z t ih =>
    rw [List.nodup_cons] at hnd₁
    obtain ⟨s, u, hs⟩ := List.append_of_mem ((hmem z).mp (by simp))
    cases s with
    | nil =>
      simp only [List.nil_append] at hs
      subst hs
      rw [List.nodup_cons] at hnd₂
      have hmem' : ∀ x, x ∈ t ↔ x ∈ u := by
        intro x
        by_cases hxz : x = z
        · subst hxz
          exact ⟨fun hx => absurd hx hnd₁.1, fun hx => absurd hx hnd₂.1⟩
        · constructor
          · intro hx
            have hxL : x ∈ z :: u := (hmem x).mp (List.mem_cons_of_mem z hx)
            rcases List.mem_cons.mp hxL with h1 | h1
            · exact absurd h1 hxz
            · exact h1
          · intro hx
            have hxL : x ∈ z :: t := (hmem x).mpr (List.mem_cons_of_mem z hx)
            rcases List.mem_cons.mp hxL with h1 | h1
            · exact absurd h1 hxz
            · exact h1
      have hbef' : ∀ x y, Before t x y ↔ Before u x y := by
        intro x y
        have h := hbef x y
        rw [before_cons, before_cons] at h
        constructor
        · intro ht
          rcases h.mp (Or.inr ht) with ⟨hxz, -⟩ | hu
          · exfalso
            have hmemt : x ∈ t := (before_mem ht).1
            rw [hxz] at hmemt
            exact hnd₁.1 hmemt
          · exact hu
        · intro hu
          rcases h.mpr (Or.inr hu) with ⟨hxz, -⟩ | ht
          · exfalso
            have hmemu : x ∈ u := (before_mem hu).1
            rw [hxz] at hmemu
            exact hnd₂.1 hmemu
          · exact ht
      rw [ih hnd₁.2 hnd₂.2 hmem' hbef']
    | cons w s =>
      exfalso
      have hw2 : Before ((w :: s) ++ z :: u) w z :=
        ⟨[], s, u, by simp⟩
      have hw2' : Before L₂ w z := by
        rw [hs]
        exact hw2
      have hw3 : Before (z :: t) w z := (hbef w z).mpr hw2'
      rw [before_cons] at hw3
      rcases hw3 with ⟨hwz, -⟩ | hw3
      · rw [hs] at hnd₂
        obtain ⟨-, -, hdis⟩ := List.nodup_append.mp hnd₂
        exact (hdis z (by simp [hwz]) z (by simp)) rfl
      · exact hnd₁.1 (before_mem hw3).2

theorem before_append_extend {l₁ l₂ : List X} {x y : X}
    (h : Before l₁ x y) : Before (l₁ ++ l₂) x y := by
  obtain ⟨a, b, c, rfl⟩ := h
  exact ⟨a, b, c ++ l₂, by simp [List.append_assoc]⟩

/-- A candidate order consistent with `G`: a permutation of the
sorted list in which no compared pair is inverted. -/
def Consistent (G : SimpleGraph X) (L : List X) : Prop :=
  L.Perm (sortedList X) ∧
    L.Pairwise (fun x y => ¬ (y < x ∧ G.Adj x y))

/-- `G` is determining: the sorted list is the only consistent
candidate order. -/
def Determining (G : SimpleGraph X) : Prop :=
  ∀ L, Consistent G L → L = sortedList X

theorem pairwise_noinvert_of_le (G : SimpleGraph X) {L : List X}
    (h : L.Pairwise (· ≤ ·)) :
    L.Pairwise (fun x y => ¬ (y < x ∧ G.Adj x y)) := by
  refine List.Pairwise.imp (fun {x y} hxy => ?_) h
  intro hcon
  exact lt_irrefl y (lt_of_lt_of_le hcon.1 hxy)

theorem sortedList_pairwise_le : (sortedList X).Pairwise (· ≤ ·) :=
  Finset.pairwise_sort Finset.univ (· ≤ ·)

theorem sortedList_nodup : (sortedList X).Nodup := by
  unfold sortedList
  exact Finset.sort_nodup _ _

theorem mem_sortedList (x : X) : x ∈ sortedList X := by
  simp [sortedList, Finset.mem_sort]

variable (color : X → Color)

/-- A run of the sorted order occupies a contiguous segment. -/
theorem exists_run_segment {R : List X}
    (hR : R ∈ runsOf color (sortedList X)) :
    ∃ pre post, sortedList X = pre ++ R ++ post := by
  obtain ⟨σ1, σ2, hσ⟩ := List.append_of_mem hR
  refine ⟨σ1.flatten, σ2.flatten, ?_⟩
  have h := runsOf_flatten (color := color) (sortedList X)
  rw [← h, hσ]
  simp [List.flatten_append, List.append_assoc]

theorem disjoint_of_flatten_nodup {σ : List (List X)}
    (h : σ.flatten.Nodup)
    {R S : List X} (hR : R ∈ σ) (hS : S ∈ σ) {x : X}
    (hxR : x ∈ R) (hxS : x ∈ S) : R = S := by
  induction σ with
  | nil => simp at hR
  | cons T σ ih =>
    rw [List.flatten_cons] at h
    obtain ⟨hTnd, hσnd, hdis⟩ := List.nodup_append.mp h
    cases hR with
    | head =>
      cases hS with
      | head => rfl
      | tail _ hS =>
        exfalso
        have hxσ : x ∈ σ.flatten :=
          List.mem_flatten.mpr ⟨S, hS, hxS⟩
        exact (hdis x hxR x hxσ) rfl
    | tail _ hR =>
      cases hS with
      | head =>
        exfalso
        have hxσ : x ∈ σ.flatten :=
          List.mem_flatten.mpr ⟨R, hR, hxR⟩
        exact (hdis x hxS x hxσ) rfl
      | tail _ hS => exact ih hσnd hR hS

/-- Two runs of the sorted order sharing an element are equal. -/
theorem runsOf_disjoint {R S : List X}
    (hR : R ∈ runsOf color (sortedList X))
    (hS : S ∈ runsOf color (sortedList X)) {x : X}
    (hxR : x ∈ R) (hxS : x ∈ S) : R = S :=
  disjoint_of_flatten_nodup (by
    rw [runsOf_flatten]
    exact sortedList_nodup) hR hS hxR hxS

theorem nodup_of_flatten_nodup {σ : List (List X)}
    (h : σ.flatten.Nodup) (hne : ∀ R ∈ σ, R ≠ []) : σ.Nodup := by
  induction σ with
  | nil => exact List.nodup_nil
  | cons T σ ih =>
    rw [List.flatten_cons] at h
    obtain ⟨hTnd, hσnd, hdis⟩ := List.nodup_append.mp h
    rw [List.nodup_cons]
    refine ⟨?_, ih hσnd (fun R hR => hne R (List.mem_cons_of_mem T hR))⟩
    intro hTσ
    obtain ⟨z, t, hT⟩ := List.exists_cons_of_ne_nil (hne T (by simp))
    have hzσ : z ∈ σ.flatten :=
      List.mem_flatten.mpr ⟨T, hTσ, by rw [hT]; simp⟩
    exact (hdis z (by rw [hT]; simp) z hzσ) rfl

theorem runsOf_nodup : (runsOf color (sortedList X)).Nodup :=
  nodup_of_flatten_nodup (by
    rw [runsOf_flatten]
    exact sortedList_nodup)
    (fun R hR => runsOf_nonempty (color := color) (sortedList X) R hR)

theorem run_sublist {R : List X}
    (hR : R ∈ runsOf color (sortedList X)) :
    R.Sublist (sortedList X) := by
  obtain ⟨pre, post, hseg⟩ := exists_run_segment (color := color) hR
  rw [hseg]
  have h1 : R.Sublist (pre ++ (R ++ post)) :=
    (List.sublist_append_left R post).trans
      (List.sublist_append_right pre (R ++ post))
  rwa [← List.append_assoc] at h1

theorem run_nodup {R : List X}
    (hR : R ∈ runsOf color (sortedList X)) : R.Nodup :=
  (run_sublist (color := color) hR).nodup sortedList_nodup

theorem filter_perm_append {Y : Type*} (l : List Y) (p : Y → Prop)
    [DecidablePred p] :
    ((l.filter p) ++ (l.filter fun x => ¬ p x)).Perm l := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases h : p a
    · have e1 : (a :: t).filter p = a :: t.filter p := by simp [h]
      have e2 : (a :: t).filter (fun x => ¬ p x)
          = t.filter (fun x => ¬ p x) := by simp [h]
      rw [e1, e2]
      exact List.Perm.cons a ih
    · have e1 : (a :: t).filter p = t.filter p := by simp [h]
      have e2 : (a :: t).filter (fun x => ¬ p x)
          = a :: t.filter (fun x => ¬ p x) := by simp [h]
      rw [e1, e2]
      have step1 : ((t.filter p) ++ (a :: (t.filter fun x => ¬ p x)))
          = ((t.filter p) ++ [a])
            ++ (t.filter fun x => ¬ p x) := by
        simp [List.append_assoc]
      have step2 : (((t.filter p) ++ [a])
            ++ (t.filter fun x => ¬ p x)).Perm
          (([a] ++ (t.filter p))
            ++ (t.filter fun x => ¬ p x)) :=
        List.Perm.append List.perm_append_comm
          (List.Perm.refl _)
      have step3 : (([a] ++ (t.filter p))
            ++ (t.filter fun x => ¬ p x))
          = a :: ((t.filter p) ++ (t.filter fun x => ¬ p x)) := by
        simp
      rw [step1]
      exact step2.trans (step3.symm ▸ List.Perm.cons a ih)

/-- Swapping two consecutive blocks inside one run's segment of the
sorted order (with no compared pair between the blocks in the
displayed order) produces a consistent candidate; if it also moves
an element `u` of the first block before an element `v` of the
second that did not already precede it, the graph is not
determining. -/
theorem not_determining_of_swap (G : SimpleGraph X)
    (hG : Determining G)
    {R : List X} (hR : R ∈ runsOf color (sortedList X))
    (F S : List X)
    (hFle : F.Pairwise (· ≤ ·)) (hSle : S.Pairwise (· ≤ ·))
    (hperm : (F ++ S).Perm R)
    (hnoedge : ∀ a ∈ F, ∀ b ∈ S, ¬ (b < a ∧ G.Adj a b))
    {u v : X} (hu : u ∈ F) (hv : v ∈ S)
    (huv : ¬ Before (sortedList X) u v) : False := by
  obtain ⟨pre, post, hseg⟩ := exists_run_segment (color := color) hR
  have hseg2 : sortedList X = (pre ++ R) ++ post := by
    rw [hseg, List.append_assoc]
  have hle : ∀ (l : List X), l.Sublist (sortedList X) →
      l.Pairwise (fun x y => ¬ (y < x ∧ G.Adj x y)) := by
    intro l hl
    exact pairwise_noinvert_of_le G
      (List.Pairwise.sublist hl sortedList_pairwise_le)
  have hcross : ∀ (l₁ l₂ : List X),
      (∀ a ∈ l₁, ∀ b ∈ l₂, a ≤ b) →
      ∀ a ∈ l₁, ∀ b ∈ l₂, ¬ (b < a ∧ G.Adj a b) := by
    intro l₁ l₂ hle2 a ha b hb hcon
    exact lt_irrefl b (lt_of_lt_of_le hcon.1 (hle2 a ha b hb))
  have hpreR : ∀ a ∈ pre, ∀ b ∈ R, a ≤ b := by
    intro a ha b hb
    refine pairwise_of_before sortedList_pairwise_le ?_
    rw [hseg]
    exact before_append_extend (before_of_mem_append ha hb)
  have hprePost : ∀ a ∈ pre, ∀ b ∈ post, a ≤ b := by
    intro a ha b hb
    refine pairwise_of_before sortedList_pairwise_le ?_
    rw [hseg]
    exact before_of_mem_append (List.mem_append_left R ha) hb
  have hRpost : ∀ a ∈ R, ∀ b ∈ post, a ≤ b := by
    intro a ha b hb
    refine pairwise_of_before sortedList_pairwise_le ?_
    rw [hseg2]
    exact before_of_mem_append
      (List.mem_append_right pre ha) hb
  have hFsubR : ∀ x ∈ F, x ∈ R := by
    intro x hx
    have hxFS : x ∈ F ++ S := List.mem_append_left S hx
    exact hperm.subset hxFS
  have hSsubR : ∀ x ∈ S, x ∈ R := by
    intro x hx
    have hxFS : x ∈ F ++ S := List.mem_append_right F hx
    exact hperm.subset hxFS
  have hleF : F.Pairwise (fun x y => ¬ (y < x ∧ G.Adj x y)) :=
    pairwise_noinvert_of_le G hFle
  have hleS : S.Pairwise (fun x y => ¬ (y < x ∧ G.Adj x y)) :=
    pairwise_noinvert_of_le G hSle
  have hlePre : pre.Pairwise (fun x y => ¬ (y < x ∧ G.Adj x y)) :=
    hle pre (by
      rw [hseg]
      exact (List.sublist_append_left pre R).trans
        (List.sublist_append_left (pre ++ R) post))
  have hlePost : post.Pairwise (fun x y => ¬ (y < x ∧ G.Adj x y)) :=
    hle post (by
      rw [hseg2]
      exact List.sublist_append_right (pre ++ R) post)
  have hcons : Consistent G (pre ++ F ++ S ++ post) := by
    refine ⟨?_, ?_⟩
    · have e : (pre ++ F ++ S ++ post)
          = (pre ++ (F ++ S)) ++ post := by
        simp [List.append_assoc]
      rw [e]
      have e2 : sortedList X = (pre ++ R) ++ post := hseg
      rw [e2]
      exact List.Perm.append
        (List.Perm.append (List.Perm.refl pre) hperm)
        (List.Perm.refl post)
    · have e1 : (pre ++ F ++ S ++ post)
          = pre ++ (F ++ (S ++ post)) := by
        simp [List.append_assoc]
      rw [e1, List.pairwise_append]
      refine ⟨hlePre, ?_, hcross pre (F ++ (S ++ post)) ?_⟩
      · rw [List.pairwise_append]
        refine ⟨hleF, ?_, ?_⟩
        · rw [List.pairwise_append]
          exact ⟨hleS, hlePost, hcross S post
            (fun a ha b hb => hRpost a (hSsubR a ha) b hb)⟩
        · intro a ha b hb
          simp only [List.mem_append] at hb
          rcases hb with hb | hb
          · exact hnoedge a ha b hb
          · intro hcon
            exact lt_irrefl b (lt_of_lt_of_le hcon.1
              (hRpost a (hFsubR a ha) b hb))
      · intro a ha b hb
        simp only [List.mem_append] at hb
        rcases hb with hb | hb | hb
        · exact hpreR a ha b (hFsubR b hb)
        · exact hpreR a ha b (hSsubR b hb)
        · exact hprePost a ha b hb
  have hEq := hG (pre ++ F ++ S ++ post) hcons
  have hbef : Before (pre ++ F ++ S ++ post) u v := by
    have e1 : (pre ++ F ++ S ++ post)
        = (pre ++ F) ++ (S ++ post) := by
      simp [List.append_assoc]
    rw [e1]
    exact before_of_mem_append
      (List.mem_append_right pre hu) (List.mem_append_left post hv)
  rw [hEq] at hbef
  exact huv hbef

/-- If a set `A` splits a run `R` into two nonempty parts with no
compared pair between them, the graph is not determining: swapping
the two parts inside the run's segment is a consistent candidate
different from the sorted order. -/
theorem determining_partition_false (G : SimpleGraph X)
    (hG : Determining G)
    {R : List X} (hR : R ∈ runsOf color (sortedList X))
    (A : Finset X) {a0 b0 : X}
    (ha0R : a0 ∈ R) (ha0A : a0 ∈ A)
    (hb0R : b0 ∈ R) (hb0A : b0 ∉ A)
    (hnoedge : ∀ u ∈ A, ∀ w ∈ R, w ∉ A → ¬ G.Adj u w) : False := by
  classical
  obtain ⟨pre, post, hseg⟩ := exists_run_segment (color := color) hR
  obtain ⟨z, t, hRz⟩ := List.exists_cons_of_ne_nil
    (runsOf_nonempty (color := color) (sortedList X) R hR)
  have hRnd : R.Nodup := run_nodup (color := color) hR
  have hzt : z ∉ t := by
    rw [hRz] at hRnd
    exact (List.nodup_cons.mp hRnd).1
  have hndA : ((pre ++ R) ++ post).Nodup := by
    rw [← hseg]
    exact sortedList_nodup
  have hndB : (pre ++ (R ++ post)).Nodup := by
    have h := hndA
    rwa [List.append_assoc] at h
  obtain ⟨hndpre, -, hdis1⟩ := List.nodup_append.mp hndB
  obtain ⟨-, -, hdis2⟩ := List.nodup_append.mp hndA
  have hzR : z ∈ R := by rw [hRz]; simp
  have hzpost : z ∉ post :=
    fun hz => (hdis2 z (List.mem_append_right pre hzR) z hz) rfl
  have hsegz : sortedList X = pre ++ z :: (t ++ post) := by
    calc sortedList X = (pre ++ R) ++ post := hseg
      _ = (pre ++ (z :: t)) ++ post := by rw [hRz]
      _ = pre ++ z :: (t ++ post) := by simp [List.append_assoc]
  have hnotbefore : ∀ (u : X), u ∈ R → u ≠ z → u ∉ pre →
      ¬ Before (sortedList X) u z := by
    intro u huR huz hupre hb
    rw [hsegz] at hb
    rcases before_append_or hb with h1 | h1 | h1
    · exact hupre (before_mem h1).1
    · exact hupre h1.1
    · rw [before_cons] at h1
      rcases h1 with ⟨h1, -⟩ | h1
      · exact huz h1
      · have hzmem : z ∈ t ++ post := (before_mem h1).2
        rcases List.mem_append.mp hzmem with hzt2 | hzpost2
        · exact hzt hzt2
        · exact hzpost hzpost2
  have hupre : ∀ (u : X), u ∈ R → u ∉ pre := by
    intro u huR hupre
    exact (hdis1 u hupre u (List.mem_append_left post huR)) rfl
  have hAle : (R.filter (fun x => x ∈ A)).Pairwise (· ≤ ·) :=
    List.Pairwise.sublist
      (List.filter_sublist.trans (run_sublist (color := color) hR))
      sortedList_pairwise_le
  have hBle : (R.filter (fun x => x ∉ A)).Pairwise (· ≤ ·) :=
    List.Pairwise.sublist
      (List.filter_sublist.trans (run_sublist (color := color) hR))
      sortedList_pairwise_le
  by_cases hzA : z ∈ A
  · -- Blocks: non-`A` part first, then `A` part; `b0` moves before `z`.
    have hperm : ((R.filter (fun x => x ∉ A))
        ++ (R.filter (fun x => x ∈ A))).Perm R :=
      List.perm_append_comm.trans
        (filter_perm_append R (fun x => x ∈ A))
    have hnoe : ∀ a ∈ (R.filter (fun x => x ∉ A)),
        ∀ b ∈ (R.filter (fun x => x ∈ A)),
        ¬ (b < a ∧ G.Adj a b) := by
      intro a ha b hb hcon
      rw [List.mem_filter] at ha hb
      exact hnoedge b (of_decide_eq_true hb.2) a ha.1
        (of_decide_eq_true ha.2) hcon.2.symm
    exact not_determining_of_swap (color := color) G hG hR
      (R.filter (fun x => x ∉ A)) (R.filter (fun x => x ∈ A))
      hBle hAle hperm hnoe
      (List.mem_filter.mpr ⟨hb0R, by simpa using hb0A⟩)
      (List.mem_filter.mpr ⟨hzR, by simpa using hzA⟩)
      (hnotbefore b0 hb0R
        (fun hbz => hb0A (hbz.symm ▸ hzA)) (hupre b0 hb0R))
  · -- Blocks: `A` part first, then non-`A` part; `a0` moves before `z`.
    have hperm : ((R.filter (fun x => x ∈ A))
        ++ (R.filter (fun x => x ∉ A))).Perm R :=
      filter_perm_append R (fun x => x ∈ A)
    have hnoe : ∀ a ∈ (R.filter (fun x => x ∈ A)),
        ∀ b ∈ (R.filter (fun x => x ∉ A)),
        ¬ (b < a ∧ G.Adj a b) := by
      intro a ha b hb hcon
      rw [List.mem_filter] at ha hb
      exact hnoedge a (of_decide_eq_true ha.2) b hb.1
        (of_decide_eq_true hb.2) hcon.2
    exact not_determining_of_swap (color := color) G hG hR
      (R.filter (fun x => x ∈ A)) (R.filter (fun x => x ∉ A))
      hAle hBle hperm hnoe
      (List.mem_filter.mpr ⟨ha0R, by simpa using ha0A⟩)
      (List.mem_filter.mpr ⟨hzR, by simpa using hzA⟩)
      (hnotbefore a0 ha0R
        (fun haz => hzA (haz ▸ ha0A)) (hupre a0 ha0R))

/-- In a determining graph, the compared pairs inside each colour
run connect the run. -/
theorem determining_internal_preconnected (G : SimpleGraph X)
    (hG : Determining G)
    {R : List X} (hR : R ∈ runsOf color (sortedList X))
    (a b : {x // x ∈ (↑(R.toFinset) : Set X)}) :
    (G.induce (↑(R.toFinset) : Set X)).Reachable a b := by
  classical
  by_contra hcon
  set A : Finset X := (Finset.univ.filter
    (fun y : {x // x ∈ (↑(R.toFinset) : Set X)} =>
      Relation.ReflTransGen (G.induce (↑(R.toFinset) : Set X)).Adj a y)
    ).image Subtype.val with hAdef
  have haR : a.val ∈ R := by
    have h1 : a.val ∈ (↑(R.toFinset) : Set X) := a.property
    have h2 : a.val ∈ R.toFinset := h1
    exact List.mem_toFinset.mp h2
  have hbR : b.val ∈ R := by
    have h1 : b.val ∈ (↑(R.toFinset) : Set X) := b.property
    have h2 : b.val ∈ R.toFinset := h1
    exact List.mem_toFinset.mp h2
  have haA : a.val ∈ A := by
    rw [hAdef]
    exact Finset.mem_image.mpr ⟨a,
      Finset.mem_filter.mpr ⟨Finset.mem_univ a,
        Relation.ReflTransGen.refl⟩, rfl⟩
  have hbA : b.val ∉ A := by
    intro hm
    rw [hAdef] at hm
    obtain ⟨y, hy, hval⟩ := Finset.mem_image.mp hm
    have hyb : y = b := Subtype.ext hval
    rw [Finset.mem_filter] at hy
    apply hcon
    rw [hyb] at hy
    exact (SimpleGraph.reachable_iff_reflTransGen a b).mpr hy.2
  have hnoedge : ∀ u ∈ A, ∀ w ∈ R, w ∉ A → ¬ G.Adj u w := by
    intro u hu w hwR hwA hadj
    rw [hAdef] at hu
    obtain ⟨y, hy, hval⟩ := Finset.mem_image.mp hu
    rw [Finset.mem_filter] at hy
    have hwsub : w ∈ (↑(R.toFinset) : Set X) :=
      List.mem_toFinset.mpr hwR
    have hadjI : (G.induce (↑(R.toFinset) : Set X)).Adj
        y ⟨w, hwsub⟩ :=
      SimpleGraph.induce_adj.mpr (by rw [hval]; exact hadj)
    have hreach : Relation.ReflTransGen
        (G.induce (↑(R.toFinset) : Set X)).Adj a ⟨w, hwsub⟩ :=
      hy.2.tail hadjI
    exact hwA (by
      rw [hAdef]
      exact Finset.mem_image.mpr ⟨⟨w, hwsub⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreach⟩, rfl⟩)
  exact determining_partition_false (color := color) G hG hR A
    haR haA hbR hbA hnoedge

/-- The graph on the colour runs of the sorted order, two runs
joined when some compared pair joins them. -/
def quotientGraph (G : SimpleGraph X) :
    SimpleGraph {R // R ∈ (runsOf color (sortedList X)).toFinset} where
  Adj R S := R ≠ S ∧ ∃ x ∈ R.val, ∃ y ∈ S.val, G.Adj x y
  symm := by
    refine ⟨?_⟩
    rintro R S ⟨hne, x, hx, y, hy, hadj⟩
    exact ⟨hne.symm, y, hy, x, hx, hadj.symm⟩
  loopless := by
    refine ⟨?_⟩
    rintro R ⟨hne, -⟩
    exact hne rfl

/-- Listing first the runs in `F`, then the runs in `S` (a
complementary split of all runs with no compared pair between the
blocks) is a consistent candidate order. -/
theorem consistent_runs_blocks (G : SimpleGraph X)
    (F S : Finset (List X))
    (hcov : ∀ R ∈ runsOf color (sortedList X), R ∈ F ∨ R ∈ S)
    (hexcl : ∀ R ∈ runsOf color (sortedList X), R ∈ F → R ∉ S)
    (hnoedge : ∀ Rf ∈ F, ∀ Rs ∈ S, ∀ a ∈ Rf, ∀ b ∈ Rs,
      ¬ G.Adj a b) :
    Consistent G
      (((runsOf color (sortedList X)).filter (· ∈ F)).flatten
        ++ ((runsOf color (sortedList X)).filter (· ∈ S)).flatten) := by
  classical
  have hsub : ∀ (T : Finset (List X)),
      ((runsOf color (sortedList X)).filter (· ∈ T)).flatten.Sublist
        (sortedList X) := by
    intro T
    have h := List.Sublist.flatten
      (List.filter_sublist (l := runsOf color (sortedList X))
        (p := fun R => R ∈ T))
    rwa [runsOf_flatten] at h
  have hfilterS : (runsOf color (sortedList X)).filter (· ∈ S)
      = (runsOf color (sortedList X)).filter (fun R => R ∉ F) := by
    apply List.filter_congr
    intro R hR
    by_cases hF : R ∈ F
    · have hS : R ∉ S := hexcl R hR hF
      simp [hF, hS]
    · have hS : R ∈ S := (hcov R hR).resolve_left hF
      simp [hF, hS]
  have hperm : (((runsOf color (sortedList X)).filter (· ∈ F)).flatten
      ++ ((runsOf color (sortedList X)).filter (· ∈ S)).flatten).Perm
        (sortedList X) := by
    rw [← List.flatten_append, hfilterS]
    have h := List.Perm.flatten
      (filter_perm_append (runsOf color (sortedList X))
        (fun R => R ∈ F))
    rwa [runsOf_flatten] at h
  refine ⟨hperm, ?_⟩
  rw [List.pairwise_append]
  refine ⟨pairwise_noinvert_of_le G
      (List.Pairwise.sublist (hsub F) sortedList_pairwise_le),
    pairwise_noinvert_of_le G
      (List.Pairwise.sublist (hsub S) sortedList_pairwise_le), ?_⟩
  intro a ha b hb hcon
  obtain ⟨Rf, hRf, haRf⟩ := List.mem_flatten.mp ha
  obtain ⟨Rs, hRs, hbRs⟩ := List.mem_flatten.mp hb
  rw [List.mem_filter] at hRf hRs
  exact hnoedge Rf (of_decide_eq_true hRf.2) Rs
    (of_decide_eq_true hRs.2) a haRf b hbRs hcon.2

/-- In a determining graph, the quotient graph on colour runs is
connected: otherwise listing one clump of runs before the other is
a consistent candidate different from the sorted order. -/
theorem determining_quotient_preconnected (G : SimpleGraph X)
    (hG : Determining G)
    (R S : {R // R ∈ (runsOf color (sortedList X)).toFinset}) :
    (quotientGraph (color := color) G).Reachable R S := by
  classical
  by_contra hcon
  have hSnot : ¬ Relation.ReflTransGen
      (quotientGraph (color := color) G).Adj R S :=
    fun h => hcon ((SimpleGraph.reachable_iff_reflTransGen R S).mpr h)
  set Cfin : Finset (List X) := (Finset.univ.filter
    (fun y => Relation.ReflTransGen
      (quotientGraph (color := color) G).Adj R y)).image Subtype.val
    with hCdef
  set Dfin : Finset (List X) := (Finset.univ.filter
    (fun y => ¬ Relation.ReflTransGen
      (quotientGraph (color := color) G).Adj R y)).image Subtype.val
    with hDdef
  have hcov : ∀ R' ∈ runsOf color (sortedList X),
      R' ∈ Cfin ∨ R' ∈ Dfin := by
    intro R' hR'
    set y : {R // R ∈ (runsOf color (sortedList X)).toFinset} :=
      ⟨R', List.mem_toFinset.mpr hR'⟩ with hy
    by_cases hreach : Relation.ReflTransGen
        (quotientGraph (color := color) G).Adj R y
    · refine Or.inl ?_
      rw [hCdef]
      exact Finset.mem_image.mpr ⟨y,
        Finset.mem_filter.mpr ⟨Finset.mem_univ y, hreach⟩, rfl⟩
    · refine Or.inr ?_
      rw [hDdef]
      exact Finset.mem_image.mpr ⟨y,
        Finset.mem_filter.mpr ⟨Finset.mem_univ y, hreach⟩, rfl⟩
  have hexcl : ∀ R' ∈ runsOf color (sortedList X),
      R' ∈ Cfin → R' ∉ Dfin := by
    intro R' hR' hC hD
    rw [hCdef] at hC
    rw [hDdef] at hD
    obtain ⟨y1, hy1, hval1⟩ := Finset.mem_image.mp hC
    obtain ⟨y2, hy2, hval2⟩ := Finset.mem_image.mp hD
    rw [Finset.mem_filter] at hy1 hy2
    have hyy : y1 = y2 := Subtype.ext (by rw [hval1, hval2])
    rw [hyy] at hy1
    exact hy2.2 hy1.2
  have hnoedgeDC : ∀ Rd ∈ Dfin, ∀ Rc ∈ Cfin,
      ∀ a ∈ Rd, ∀ b ∈ Rc, ¬ G.Adj a b ∧ ¬ G.Adj b a := by
    intro Rd hRd Rc hRc a ha b hb
    rw [hCdef] at hRc
    rw [hDdef] at hRd
    obtain ⟨yc, hyc, hvalc⟩ := Finset.mem_image.mp hRc
    obtain ⟨yd, hyd, hvald⟩ := Finset.mem_image.mp hRd
    rw [Finset.mem_filter] at hyc hyd
    have hne : (yc : {R // R ∈ (runsOf color
        (sortedList X)).toFinset}) ≠ yd := by
      intro hEq
      have : Rc = Rd := by rw [← hvalc, ← hvald, hEq]
      subst this
      rw [hEq] at hyc
      exact hyd.2 hyc.2
    constructor
    · intro hadj
      have hreach : Relation.ReflTransGen
          (quotientGraph (color := color) G).Adj R yd :=
        hyc.2.tail ⟨hne, b, by rwa [← hvalc] at hb, a, by
          rwa [← hvald] at ha, hadj.symm⟩
      exact hyd.2 hreach
    · intro hadj
      have hreach : Relation.ReflTransGen
          (quotientGraph (color := color) G).Adj R yd :=
        hyc.2.tail ⟨hne, b, by rwa [← hvalc] at hb, a, by
          rwa [← hvald] at ha, hadj⟩
      exact hyd.2 hreach
  cases hσ : runsOf color (sortedList X) with
  | nil =>
    exfalso
    obtain ⟨Rv, hRv, -⟩ : ∃ Rv : List X,
        Rv ∈ runsOf color (sortedList X) ∧ Rv = R.val :=
      ⟨R.val, List.mem_toFinset.mp R.property, rfl⟩
    rw [hσ] at hRv
    simp at hRv
  | cons R1 σ' =>
    have hR1σ : R1 ∈ runsOf color (sortedList X) := by
      rw [hσ]
      simp
    have hseg1 : sortedList X = R1 ++ σ'.flatten := by
      have h := runsOf_flatten (color := color) (sortedList X)
      rw [hσ, List.flatten_cons] at h
      exact h.symm
    obtain ⟨cz, t1, hR1z⟩ := List.exists_cons_of_ne_nil
      (runsOf_nonempty (color := color) (sortedList X) R1 hR1σ)
    have hR1nd : R1.Nodup := run_nodup (color := color) hR1σ
    have hczt : cz ∉ t1 := by
      rw [hR1z] at hR1nd
      exact (List.nodup_cons.mp hR1nd).1
    have hσnd : (runsOf color (sortedList X)).Nodup :=
      runsOf_nodup (color := color)
    have hR1notσ' : R1 ∉ σ' := by
      rw [hσ] at hσnd
      exact (List.nodup_cons.mp hσnd).1
    have hnotbefore : ∀ (u : X) (Ru : List X),
        Ru ∈ runsOf color (sortedList X) → u ∈ Ru → Ru ≠ R1 →
        ¬ Before (sortedList X) u cz := by
      intro u Ru hRu hu hRu1 hb
      rw [hseg1, hR1z] at hb
      rcases before_append_or hb with h1 | h1 | h1
      · rw [before_cons] at h1
        rcases h1 with ⟨h1, -⟩ | h1
        · have hczR1 : cz ∈ R1 := by rw [hR1z]; simp
          rw [← h1] at hczR1
          exact hRu1 (runsOf_disjoint (color := color) hRu hR1σ
            hu hczR1)
        · exact hczt (before_mem h1).2
      · exact hRu1 (runsOf_disjoint (color := color) hRu hR1σ hu
          (by rw [hR1z]; exact h1.1))
      · have hczmem : cz ∈ σ'.flatten := (before_mem h1).2
        obtain ⟨Rs, hRs, hczRs⟩ := List.mem_flatten.mp hczmem
        have hRsσ : Rs ∈ runsOf color (sortedList X) := by
          rw [hσ]
          exact List.mem_cons_of_mem R1 hRs
        have heq : R1 = Rs :=
          runsOf_disjoint (color := color) hR1σ hRsσ
            (by rw [hR1z]; simp) hczRs
        rw [← heq] at hRs
        exact hR1notσ' hRs
    rcases hcov R1 hR1σ with hR1C | hR1D
    · -- First run is in `R`'s clump; list the other clump first.
      have hSvalD : S.val ∈ Dfin := by
        rw [hDdef]
        exact Finset.mem_image.mpr ⟨S,
          Finset.mem_filter.mpr ⟨Finset.mem_univ S, hSnot⟩, rfl⟩
      have hSvalσ : S.val ∈ runsOf color (sortedList X) :=
        List.mem_toFinset.mp S.property
      obtain ⟨d, td, hSd⟩ := List.exists_cons_of_ne_nil
        (runsOf_nonempty (color := color) (sortedList X) S.val hSvalσ)
      have hdS : d ∈ S.val := by rw [hSd]; simp
      have hcons := consistent_runs_blocks (color := color) G
        Dfin Cfin
        (fun R' hR' => (hcov R' hR').symm)
        (fun R' hR' hD => fun hC => hexcl R' hR' hC hD)
        (fun Rf hRf Rs hRs a ha b hb =>
          (hnoedgeDC Rf hRf Rs hRs a ha b hb).1)
      have hEq := hG _ hcons
      have hbef : Before
          (((runsOf color (sortedList X)).filter (· ∈ Dfin)).flatten
            ++ ((runsOf color (sortedList X)).filter
              (· ∈ Cfin)).flatten) d cz := by
        apply before_of_mem_append
        · exact List.mem_flatten.mpr ⟨S.val,
            List.mem_filter.mpr ⟨hSvalσ, by simpa using hSvalD⟩, hdS⟩
        · refine List.mem_flatten.mpr ⟨R1,
            List.mem_filter.mpr ⟨hR1σ, by simpa using hR1C⟩, ?_⟩
          rw [hR1z]
          simp
      rw [hEq] at hbef
      exact hnotbefore d S.val hSvalσ hdS
        (fun heq => hexcl S.val hSvalσ (by
          have h2 := hR1C
          rwa [← heq] at h2) hSvalD) hbef
    · -- First run is outside `R`'s clump; list `R`'s clump first.
      have hRvalC : R.val ∈ Cfin := by
        rw [hCdef]
        exact Finset.mem_image.mpr ⟨R,
          Finset.mem_filter.mpr ⟨Finset.mem_univ R,
            Relation.ReflTransGen.refl⟩, rfl⟩
      have hRvalσ : R.val ∈ runsOf color (sortedList X) :=
        List.mem_toFinset.mp R.property
      obtain ⟨c, tc, hRc⟩ := List.exists_cons_of_ne_nil
        (runsOf_nonempty (color := color) (sortedList X) R.val hRvalσ)
      have hcR : c ∈ R.val := by rw [hRc]; simp
      have hcons := consistent_runs_blocks (color := color) G
        Cfin Dfin hcov hexcl
        (fun Rf hRf Rs hRs a ha b hb =>
          (hnoedgeDC Rs hRs Rf hRf b hb a ha).2)
      have hEq := hG _ hcons
      have hbef : Before
          (((runsOf color (sortedList X)).filter (· ∈ Cfin)).flatten
            ++ ((runsOf color (sortedList X)).filter
              (· ∈ Dfin)).flatten) c cz := by
        apply before_of_mem_append
        · exact List.mem_flatten.mpr ⟨R.val,
            List.mem_filter.mpr ⟨hRvalσ, by simpa using hRvalC⟩, hcR⟩
        · refine List.mem_flatten.mpr ⟨R1,
            List.mem_filter.mpr ⟨hR1σ, by simpa using hR1D⟩, ?_⟩
          rw [hR1z]
          simp
      rw [hEq] at hbef
      exact hnotbefore c R.val hRvalσ hcR
        (fun heq => hexcl R.val hRvalσ hRvalC (by
          have h2 := hR1D
          rwa [← heq] at h2)) hbef

open Classical in
/-- The compared pairs with both endpoints in `S`. -/
noncomputable def internalEdges (G : SimpleGraph X) (S : Finset X) :
    Finset (Sym2 X) :=
  Finset.univ.filter (fun e => ∃ x y, e = s(x, y) ∧ G.Adj x y
    ∧ x ∈ S ∧ y ∈ S)

theorem mem_internalEdges {G : SimpleGraph X} {S : Finset X}
    {e : Sym2 X} :
    e ∈ internalEdges G S ↔ ∃ x y, e = s(x, y) ∧ G.Adj x y
      ∧ x ∈ S ∧ y ∈ S := by
  simp [internalEdges]

/-- A connected graph on `n` vertices has at least `n - 1` edges. -/
theorem card_le_of_preconnected {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V)
    (hne : Nonempty V) (hconn : ∀ a b, G.Reachable a b) :
    Fintype.card V ≤ Nat.card ↥G.edgeSet + 1 := by
  classical
  haveI := hne
  have hC : G.Connected := ⟨hconn⟩
  have h := hC.card_vert_le_card_edgeSet_add_one
  rwa [Nat.card_eq_fintype_card] at h

theorem sym2_map_subtype_val_injective (S : Finset X) :
    Function.Injective (Sym2.map (Subtype.val :
      {x // x ∈ (↑S : Set X)} → X)) :=
  Sym2.map.injective Subtype.val_injective

theorem card_internalEdges (G : SimpleGraph X) (S : Finset X) :
    (internalEdges G S).card
      = Nat.card ↥(G.induce (↑S : Set X)).edgeSet := by
  classical
  have hbij : (Finset.univ.filter
        (fun e => e ∈ (G.induce (↑S : Set X)).edgeSet)).card
      = (internalEdges G S).card := by
    refine Finset.card_bij
      (fun e _ => Sym2.map Subtype.val e) ?_ ?_ ?_
    · intro e he
      rw [Finset.mem_filter] at he
      have heAdj : e ∈ (G.induce (↑S : Set X)).edgeSet := he.2
      induction e using Sym2.ind with
      | _ x y =>
        rw [Sym2.map_mk, mem_internalEdges]
        refine ⟨x.val, y.val, rfl, ?_, x.property, y.property⟩
        have hAdj : (G.induce (↑S : Set X)).Adj x y :=
          (SimpleGraph.mem_edgeSet _).mp heAdj
        exact SimpleGraph.induce_adj.mp hAdj
    · intro e1 _ e2 _ h
      exact (sym2_map_subtype_val_injective S) h
    · intro e he
      rw [mem_internalEdges] at he
      obtain ⟨x, y, rfl, hadj, hxS, hyS⟩ := he
      refine ⟨s(⟨x, hxS⟩, ⟨y, hyS⟩), ?_, by rw [Sym2.map_mk]⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [SimpleGraph.mem_edgeSet]
      exact SimpleGraph.induce_adj.mpr hadj
  rw [← hbij, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]

/-- A determining graph compares at least `|R| - 1` pairs inside
each colour run `R`. -/
theorem internalEdges_card_ge (G : SimpleGraph X)
    (hG : Determining G)
    {R : List X} (hR : R ∈ runsOf color (sortedList X)) :
    R.length - 1 ≤ (internalEdges G (R.toFinset)).card := by
  classical
  have hconn : ∀ a b, (G.induce (↑R.toFinset : Set X)).Reachable
      a b :=
    fun a b => determining_internal_preconnected
      (color := color) G hG hR a b
  have hne : Nonempty {x // x ∈ (↑R.toFinset : Set X)} := by
    obtain ⟨z, t, hz⟩ := List.exists_cons_of_ne_nil
      (runsOf_nonempty (color := color) (sortedList X) R hR)
    exact ⟨⟨z, List.mem_toFinset.mpr (by rw [hz]; simp)⟩⟩
  have h := card_le_of_preconnected
    (G.induce (↑R.toFinset : Set X)) hne hconn
  have h2 : (internalEdges G (R.toFinset)).card
      = Nat.card ↥(G.induce (↑R.toFinset : Set X)).edgeSet :=
    card_internalEdges G (R.toFinset)
  rw [← h2] at h
  have hcard : Fintype.card {x // x ∈ (↑R.toFinset : Set X)}
      = R.length := by
    rw [Fintype.card_subtype]
    have hfil : (Finset.univ.filter
        (fun x => x ∈ (↑R.toFinset : Set X))) = R.toFinset := by
      ext x
      simp [List.mem_toFinset]
    rw [hfil,
      List.toFinset_card_of_nodup (run_nodup (color := color) hR)]
  rw [hcard] at h
  omega

theorem adjCostWith_add (w₁ w₂ : X → X → ℝ) (l : List X) :
    adjCostWith (fun x y => w₁ x y + w₂ x y) l
      = adjCostWith w₁ l + adjCostWith w₂ l := by
  induction l with
  | nil => simp [adjCostWith]
  | cons a t ih =>
    cases t with
    | nil => simp [adjCostWith]
    | cons b t =>
      have e : ∀ w : X → X → ℝ, adjCostWith w (a :: b :: t)
          = w a b + adjCostWith w (b :: t) := fun w => rfl
      rw [e, e, e, ih]
      ring

/-- Pointwise, the pair cost is the red weight plus the blue
weight plus the cross weight. -/
theorem pairCost_add_split (α β : ℝ) (x y : X) :
    pairCost α β color x y
      = (if color x = Color.red ∧ color y = Color.red then α else 0)
        + (if color x = Color.blue ∧ color y = Color.blue then β else 0)
        + (if color x ≠ color y then (1 : ℝ) else 0) := by
  cases hcx : color x <;> cases hcy : color y <;>
    simp [pairCost, hcx, hcy]

theorem adjCostWith_pairCost_split (α β : ℝ) (l : List X) :
    adjCostWith (pairCost α β color) l
      = adjCostWith (fun x y => if color x = Color.red
          ∧ color y = Color.red then α else 0) l
        + adjCostWith (fun x y => if color x = Color.blue
          ∧ color y = Color.blue then β else 0) l
        + adjCostWith (fun x y => if color x ≠ color y
          then (1 : ℝ) else 0) l := by
  rw [← adjCostWith_add, ← adjCostWith_add]
  congr 1
  funext x y
  exact pairCost_add_split (color := color) α β x y

/-- The cross weight over the runs of a list counts the seams:
one per run boundary. -/
theorem adjCostWith_crossW_of_runs {σ : List (List X)}
    (hmono : MonoRuns color σ) (halt : AltRuns color σ)
    (hne : ∀ R ∈ σ, R ≠ []) :
    adjCostWith (fun x y => if color x ≠ color y then (1 : ℝ)
      else 0) σ.flatten = ((σ.length - 1 : ℕ) : ℝ) := by
  induction σ with
  | nil => simp [adjCostWith]
  | cons R σ ih =>
    have hR0 : adjCostWith (fun x y => if color x ≠ color y
        then (1 : ℝ) else 0) R = 0 := by
      obtain (hc | hc) := hmono R (by simp)
      · have h := adjCostWith_of_mono (color := color)
          (fun x y => if color x ≠ color y then (1 : ℝ) else 0)
          0 Color.red R hc (by
            intro x y hx hy
            have hxy : color x = color y := by rw [hx, hy]
            rw [hxy]
            simp)
        simpa using h
      · have h := adjCostWith_of_mono (color := color)
          (fun x y => if color x ≠ color y then (1 : ℝ) else 0)
          0 Color.blue R hc (by
            intro x y hx hy
            have hxy : color x = color y := by rw [hx, hy]
            rw [hxy]
            simp)
        simpa using h
    cases σ with
    | nil =>
      rw [List.flatten_cons, List.flatten_nil, List.append_nil, hR0]
      simp
    | cons T σ' =>
      have hmono' : MonoRuns color (T :: σ') :=
        fun S hS => hmono S (List.mem_cons_of_mem R hS)
      have halt' : AltRuns color (T :: σ') := by
        cases halt with
        | cons _ htail => exact htail
      have hne' : ∀ S ∈ (T :: σ'), S ≠ [] :=
        fun S hS => hne S (List.mem_cons_of_mem R hS)
      have ih' := ih hmono' halt' hne'
      have hTne : T ≠ [] := hne T
        (List.mem_cons_of_mem R List.mem_cons_self)
      obtain ⟨b, t', hT⟩ := List.exists_cons_of_ne_nil hTne
      have hseam : seam (fun x y => if color x ≠ color y
          then (1 : ℝ) else 0) R ((T :: σ').flatten) = 1 := by
        have hhead : ((T :: σ').flatten).head? = some b := by
          rw [hT]
          simp [List.flatten_cons]
        have hRne : R ≠ [] := hne R (by simp)
        have hne2 : color (R.getLast hRne) ≠ color b := by
          cases halt with
          | cons hs _ =>
            exact hs _ (List.getLast_mem hRne) b
              (by rw [hT]; exact List.mem_cons_self)
        have ha : R.getLast? = some (R.getLast hRne) :=
          List.getLast?_eq_getLast hRne
        have hfin : seam (fun x y => if color x ≠ color y
            then (1 : ℝ) else 0) R ((T :: σ').flatten)
            = (if color (R.getLast hRne) ≠ color b
              then (1 : ℝ) else 0) := by
          simp [seam, ha, hT]
        rw [hfin, if_pos hne2]
      have hflat : (R :: T :: σ').flatten
          = R ++ (T :: σ').flatten := List.flatten_cons
      rw [hflat, adjCostWith_append, ih', hR0, hseam]
      have hlen : ((R :: T :: σ').length - 1 : ℕ)
          = ((T :: σ').length - 1 : ℕ) + 1 := by
        simp only [List.length_cons]
        omega
      rw [hlen, Nat.cast_add, Nat.cast_one]
      ring

/-- The benchmark in run form: `H = α Σᵢ(sᵢ-1) + β Σⱼ(tⱼ-1) + (K-1)`. -/
theorem benchmarkH_eq_runs (α β : ℝ) :
    benchmarkH α β color
      = redAdjWeight α color + blueAdjWeight β color
        + (((runsOf color (sortedList X)).length - 1 : ℕ) : ℝ) := by
  have hcross : adjCostWith (fun x y => if color x ≠ color y
        then (1 : ℝ) else 0) (sortedList X)
      = (((runsOf color (sortedList X)).length - 1 : ℕ) : ℝ) := by
    have hmono : MonoRuns color (runsOf color (sortedList X)) := by
      intro R hR
      obtain ⟨c, hc⟩ := runsOf_mono (color := color) (sortedList X) R hR
      cases c with
      | red => exact Or.inl hc
      | blue => exact Or.inr hc
    have h := adjCostWith_crossW_of_runs (color := color)
      hmono (runsOf_alt (color := color) (sortedList X))
      (fun R hR => runsOf_nonempty (color := color) (sortedList X) R hR)
    rwa [runsOf_flatten] at h
  unfold benchmarkH redAdjWeight blueAdjWeight
  rw [adjCost_eq_adjCostWith, adjCostWith_pairCost_split, hcross]

theorem run_exists (x : X) :
    ∃ R, R ∈ runsOf color (sortedList X) ∧ x ∈ R := by
  have h : x ∈ (runsOf color (sortedList X)).flatten := by
    rw [runsOf_flatten]
    exact mem_sortedList x
  exact List.mem_flatten.mp h

/-- The run containing `x`. -/
noncomputable def runVert (x : X) :
    {R // R ∈ (runsOf color (sortedList X)).toFinset} :=
  ⟨Classical.choose (run_exists (color := color) x), by
    have h := Classical.choose_spec (run_exists (color := color) x)
    exact List.mem_toFinset.mpr h.1⟩

theorem runVert_spec (x : X) :
    (runVert (color := color) x).val ∈ runsOf color (sortedList X)
      ∧ x ∈ (runVert (color := color) x).val :=
  Classical.choose_spec (run_exists (color := color) x)

theorem runVert_eq_of_mem {R : List X}
    (hR : R ∈ runsOf color (sortedList X)) {x : X}
    (hx : x ∈ R) : (runVert (color := color) x).val = R :=
  runsOf_disjoint (color := color)
    (runVert_spec (color := color) x).1 hR
    (runVert_spec (color := color) x).2 hx

open Classical in
/-- The compared pairs that are not inside a single run. -/
noncomputable def crossEdges (G : SimpleGraph X) : Finset (Sym2 X) :=
  (Finset.univ.filter (fun e => e ∈ G.edgeSet)).filter
    (fun e => ¬ ∃ R ∈ runsOf color (sortedList X),
      e ∈ internalEdges G (R.toFinset))

/-- A determining graph compares at least `K - 1` pairs across
different runs, where `K` is the number of runs. -/
theorem quotient_card_le_cross (G : SimpleGraph X)
    (hG : Determining G)
    (hσ : runsOf color (sortedList X) ≠ []) :
    (runsOf color (sortedList X)).length - 1
      ≤ (crossEdges (color := color) G).card := by
  classical
  have hne : Nonempty
      {R // R ∈ (runsOf color (sortedList X)).toFinset} := by
    obtain ⟨R1, σ', hσ'⟩ := List.exists_cons_of_ne_nil hσ
    exact ⟨⟨R1, List.mem_toFinset.mpr (by rw [hσ']; simp)⟩⟩
  have hconn : ∀ a b, (quotientGraph (color := color) G).Reachable
      a b :=
    fun a b => determining_quotient_preconnected
      (color := color) G hG a b
  have hq := card_le_of_preconnected
    (quotientGraph (color := color) G) hne hconn
  have hcard : Fintype.card
      {R // R ∈ (runsOf color (sortedList X)).toFinset}
      = (runsOf color (sortedList X)).length := by
    rw [Fintype.card_coe,
      List.toFinset_card_of_nodup (runsOf_nodup (color := color))]
  rw [hcard] at hq
  have hfil : (Finset.univ.filter
        (fun e => e ∈ (quotientGraph (color := color) G).edgeSet)).card
      = Nat.card ↥(quotientGraph (color := color) G).edgeSet := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have hle : (Finset.univ.filter
        (fun e => e ∈ (quotientGraph (color := color) G).edgeSet)).card
      ≤ (crossEdges (color := color) G).card := by
    apply Finset.card_le_card_of_surjOn (Sym2.map (runVert color))
    intro eQ heQ
    rw [Finset.mem_coe] at heQ
    induction eQ using Sym2.ind with
    | _ Rv Sv =>
      rw [Finset.mem_filter] at heQ
      have hAdj : (quotientGraph (color := color) G).Adj Rv Sv :=
        (SimpleGraph.mem_edgeSet _).mp heQ.2
      obtain ⟨hneQ, x, hx, y, hy, hadjQ⟩ := hAdj
      refine ⟨s(x, y), ?_, ?_⟩
      · rw [Finset.mem_coe, crossEdges]
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (SimpleGraph.mem_edgeSet _).mpr hadjQ⟩, ?_⟩
        rintro ⟨R0, hR0, hmem⟩
        rw [mem_internalEdges] at hmem
        obtain ⟨u, v, huv, -, hu, hv⟩ := hmem
        have hxR0 : x ∈ R0 := by
          rw [Sym2.eq_iff] at huv
          rcases huv with ⟨rfl, -⟩ | ⟨h1, -⟩
          · exact List.mem_toFinset.mp hu
          · rw [h1]
            exact List.mem_toFinset.mp hv
        have hyR0 : y ∈ R0 := by
          rw [Sym2.eq_iff] at huv
          rcases huv with ⟨-, rfl⟩ | ⟨-, h2⟩
          · exact List.mem_toFinset.mp hv
          · rw [h2]
            exact List.mem_toFinset.mp hu
        have heq1 : R0 = Rv.val :=
          runsOf_disjoint (color := color) hR0
            (List.mem_toFinset.mp Rv.property) hxR0 hx
        have heq2 : R0 = Sv.val :=
          runsOf_disjoint (color := color) hR0
            (List.mem_toFinset.mp Sv.property) hyR0 hy
        have heq3 : Rv.val = Sv.val := by rw [← heq1, heq2]
        exact hneQ (Subtype.ext heq3)
      · rw [Sym2.map_mk]
        have hRx : runVert (color := color) x = Rv :=
          Subtype.ext (runVert_eq_of_mem (color := color)
            (List.mem_toFinset.mp Rv.property) hx)
        have hSy : runVert (color := color) y = Sv :=
          Subtype.ext (runVert_eq_of_mem (color := color)
            (List.mem_toFinset.mp Sv.property) hy)
        rw [hRx, hSy]
  omega

/-- **`prop:Hlower`.** Every determining set of comparisons costs
at least `H`: no comparison algorithm can pay less than the cost
of the cheapest proof of the sorted order. -/
theorem determining_cost_ge (α β : ℝ) (hα : 1 < α) (hβ : 1 < β)
    (G : SimpleGraph X) (hG : Determining G) :
    benchmarkH α β color ≤ graphCost α β color G := by
  classical
  by_cases hσ : runsOf color (sortedList X) = []
  · have hsorted : sortedList X = [] := by
      have h := runsOf_flatten (color := color) (sortedList X)
      rw [hσ] at h
      simpa using h.symm
    have hH : benchmarkH α β color = 0 := by
      unfold benchmarkH
      rw [hsorted]
      rfl
    rw [hH, graphCost]
    apply Finset.sum_nonneg
    intro e _
    exact le_trans (by norm_num)
      (edgeCost_ge_one α β color (le_of_lt hα) (le_of_lt hβ) e)
  · have hId := benchmarkH_eq_runs (color := color) α β
    have hsplit : graphCost α β color G
        = (∑ e ∈ Finset.univ.filter (fun e =>
            ∃ R ∈ runsOf color (sortedList X),
            e ∈ internalEdges G (R.toFinset)),
            edgeCost α β color e)
          + (∑ e ∈ crossEdges (color := color) G,
            edgeCost α β color e) := by
      have hset : (Finset.univ.filter (fun e => e ∈ G.edgeSet)).filter
            (fun e => ∃ R ∈ runsOf color (sortedList X),
              e ∈ internalEdges G (R.toFinset))
          = Finset.univ.filter (fun e =>
              ∃ R ∈ runsOf color (sortedList X),
              e ∈ internalEdges G (R.toFinset)) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          exact h.2
        · intro h
          obtain ⟨R, hR, hmem⟩ := h
          refine ⟨?_, R, hR, hmem⟩
          rw [mem_internalEdges] at hmem
          obtain ⟨x, y, rfl, hadj, -, -⟩ := hmem
          exact (SimpleGraph.mem_edgeSet _).mpr hadj
      rw [graphCost, crossEdges,
        ← Finset.sum_filter_add_sum_filter_not
          (Finset.univ.filter (fun e => e ∈ G.edgeSet))
          (fun e => ∃ R ∈ runsOf color (sortedList X),
            e ∈ internalEdges G (R.toFinset))
          (edgeCost α β color), hset]
    have hIF : (Finset.univ.filter (fun e =>
          ∃ R ∈ runsOf color (sortedList X),
          e ∈ internalEdges G (R.toFinset)))
        = (runsOf color (sortedList X)).toFinset.biUnion
            (fun R => internalEdges G (R.toFinset)) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_biUnion, List.mem_toFinset]
    have hpairdisj : ((runsOf color (sortedList X)).toFinset :
        Set (List X)).PairwiseDisjoint
          (fun R => internalEdges G (R.toFinset)) := by
      intro R hR S hS hneRS
      show Disjoint (internalEdges G (R.toFinset))
        (internalEdges G (S.toFinset))
      rw [Finset.disjoint_left]
      intro e heR heS
      rw [mem_internalEdges] at heR heS
      obtain ⟨x, y, heR_eq, -, hxR, -⟩ := heR
      obtain ⟨u, v, heS_eq, -, huS, hvS⟩ := heS
      have huv : s(x, y) = s(u, v) := heR_eq.symm.trans heS_eq
      have hxS : x ∈ S := by
        rw [Sym2.eq_iff] at huv
        rcases huv with ⟨rfl, -⟩ | ⟨h1, -⟩
        · exact List.mem_toFinset.mp huS
        · rw [h1]
          exact List.mem_toFinset.mp hvS
      exact hneRS (runsOf_disjoint (color := color)
        (List.mem_toFinset.mp (Finset.mem_coe.mp hR))
        (List.mem_toFinset.mp (Finset.mem_coe.mp hS))
        (List.mem_toFinset.mp hxR) hxS)
    have hper : ∀ R ∈ (runsOf color (sortedList X)).toFinset,
        (if (∀ x ∈ R, color x = Color.red)
          then α * ((R.length - 1 : ℕ) : ℝ)
          else β * ((R.length - 1 : ℕ) : ℝ))
          ≤ ∑ e ∈ internalEdges G (R.toFinset),
            edgeCost α β color e := by
      intro R hR
      have hRσ : R ∈ runsOf color (sortedList X) :=
        List.mem_toFinset.mp hR
      have hcard := internalEdges_card_ge (color := color) G hG hRσ
      have hcardR : ((R.length - 1 : ℕ) : ℝ)
          ≤ ((internalEdges G (R.toFinset)).card : ℝ) := by
        exact_mod_cast hcard
      by_cases hred : ∀ x ∈ R, color x = Color.red
      · rw [if_pos hred]
        have hsum : (∑ e ∈ internalEdges G (R.toFinset),
              edgeCost α β color e)
            = ((internalEdges G (R.toFinset)).card : ℝ) * α := by
          rw [Finset.sum_congr rfl
            (show ∀ e ∈ internalEdges G (R.toFinset),
              edgeCost α β color e = α from by
              intro e he
              rw [mem_internalEdges] at he
              obtain ⟨x, y, rfl, -, hx, hy⟩ := he
              rw [edgeCost_mk]
              have hxy : color x = color y := by
                rw [hred x (List.mem_toFinset.mp hx),
                  hred y (List.mem_toFinset.mp hy)]
              unfold pairCost
              rw [if_pos hxy, hred x (List.mem_toFinset.mp hx)]),
            Finset.sum_const, nsmul_eq_mul]
        rw [hsum]
        have hα0 : (0 : ℝ) ≤ α := le_trans (by norm_num) (le_of_lt hα)
        calc α * ((R.length - 1 : ℕ) : ℝ)
            = ((R.length - 1 : ℕ) : ℝ) * α := mul_comm _ _
          _ ≤ ((internalEdges G (R.toFinset)).card : ℝ) * α :=
              mul_le_mul_of_nonneg_right hcardR hα0
      · rw [if_neg hred]
        obtain ⟨c, hc⟩ := runsOf_mono (color := color)
          (sortedList X) R hRσ
        have hblue : ∀ x ∈ R, color x = Color.blue := by
          cases hcc : c with
          | red =>
            rw [hcc] at hc
            exact absurd hc hred
          | blue =>
            rw [hcc] at hc
            exact hc
        have hsum : (∑ e ∈ internalEdges G (R.toFinset),
              edgeCost α β color e)
            = ((internalEdges G (R.toFinset)).card : ℝ) * β := by
          rw [Finset.sum_congr rfl
            (show ∀ e ∈ internalEdges G (R.toFinset),
              edgeCost α β color e = β from by
              intro e he
              rw [mem_internalEdges] at he
              obtain ⟨x, y, rfl, -, hx, hy⟩ := he
              rw [edgeCost_mk]
              have hxy : color x = color y := by
                rw [hblue x (List.mem_toFinset.mp hx),
                  hblue y (List.mem_toFinset.mp hy)]
              unfold pairCost
              rw [if_pos hxy, hblue x (List.mem_toFinset.mp hx)]),
            Finset.sum_const, nsmul_eq_mul]
        rw [hsum]
        have hβ0 : (0 : ℝ) ≤ β := le_trans (by norm_num) (le_of_lt hβ)
        calc β * ((R.length - 1 : ℕ) : ℝ)
            = ((R.length - 1 : ℕ) : ℝ) * β := mul_comm _ _
          _ ≤ ((internalEdges G (R.toFinset)).card : ℝ) * β :=
              mul_le_mul_of_nonneg_right hcardR hβ0
    have hcontrib : (∑ R ∈ (runsOf color (sortedList X)).toFinset,
          (if (∀ x ∈ R, color x = Color.red)
            then α * ((R.length - 1 : ℕ) : ℝ)
            else β * ((R.length - 1 : ℕ) : ℝ)))
        = redAdjWeight α color + blueAdjWeight β color := by
      have hpt : ∀ R ∈ (runsOf color (sortedList X)).toFinset,
          (if (∀ x ∈ R, color x = Color.red)
              then α * ((R.length - 1 : ℕ) : ℝ)
              else β * ((R.length - 1 : ℕ) : ℝ))
            = α * (((if (∀ x ∈ R, color x = Color.red)
                then R.length - 1 else 0 : ℕ)) : ℝ)
              + β * (((if (∀ x ∈ R, color x = Color.blue)
                then R.length - 1 else 0 : ℕ)) : ℝ) := by
        intro R hR
        have hRσ : R ∈ runsOf color (sortedList X) :=
          List.mem_toFinset.mp hR
        by_cases hred : ∀ x ∈ R, color x = Color.red
        · have hnb : ¬ (∀ x ∈ R, color x = Color.blue) := by
            intro hb
            obtain ⟨z, t, hz⟩ := List.exists_cons_of_ne_nil
              (runsOf_nonempty (color := color) (sortedList X) R hRσ)
            have hz1 : color z = Color.red :=
              hred z (by rw [hz]; simp)
            have hz2 : color z = Color.blue :=
              hb z (by rw [hz]; simp)
            rw [hz1] at hz2
            exact Color.noConfusion hz2
          rw [if_pos hred, if_pos hred, if_neg hnb]
          simp
        · obtain ⟨c, hc⟩ := runsOf_mono (color := color)
            (sortedList X) R hRσ
          have hblue : ∀ x ∈ R, color x = Color.blue := by
            cases hcc : c with
            | red =>
              rw [hcc] at hc
              exact absurd hc hred
            | blue =>
              rw [hcc] at hc
              exact hc
          rw [if_neg hred, if_neg hred, if_pos hblue]
          simp
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, redAdjWeight_eq,
        blueAdjWeight_eq]
      congr 1
      · congr 1
        have hnd := runsOf_nodup (color := color)
        rw [redRunSum, ← List.sum_toFinset _ hnd]
        simp [Nat.cast_sum, List.map_map]
      · congr 1
        have hnd := runsOf_nodup (color := color)
        rw [blueRunSum, ← List.sum_toFinset _ hnd]
        simp [Nat.cast_sum, List.map_map]
    have hcrosscard : (((runsOf color (sortedList X)).length
          - 1 : ℕ) : ℝ)
        ≤ ∑ e ∈ crossEdges (color := color) G,
          edgeCost α β color e := by
      refine le_trans ?_
        (Finset.sum_le_sum (fun e _ =>
          edgeCost_ge_one α β color (le_of_lt hα) (le_of_lt hβ) e))
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast quotient_card_le_cross (color := color) G hG hσ
    rw [hId, hsplit, hIF, Finset.sum_biUnion hpairdisj]
    have hsumge : redAdjWeight α color + blueAdjWeight β color
        ≤ ∑ R ∈ (runsOf color (sortedList X)).toFinset,
            (∑ e ∈ internalEdges G (R.toFinset),
              edgeCost α β color e) := by
      rw [← hcontrib]
      exact Finset.sum_le_sum hper
    linarith [hsumge, hcrosscard]

/-! ### Tightness: the adjacent pairs

The adjacent pairs of the sorted order pin the order by
transitivity, and their total cost is exactly `H`. So `H` is not
only a lower bound on every determining set of comparisons; it is
attained, and is therefore exactly the cheapest-proof cost. -/

/-- Adjacent pairs of a list, as unordered pairs. -/
def adjPairs : List X → List (Sym2 X)
  | [] => []
  | [_] => []
  | a :: b :: t => s(a, b) :: adjPairs (b :: t)

theorem mem_adjPairs_cons {x y a : X} :
    ∀ l : List X, s(x, y) ∈ adjPairs (a :: l) ↔
      ∃ pre post, (a :: l) = pre ++ x :: y :: post ∨
        (a :: l) = pre ++ y :: x :: post := by
  intro l
  induction l generalizing a x y with
  | nil =>
    constructor
    · intro h
      simp [adjPairs] at h
    · rintro ⟨pre, post, h | h⟩ <;> cases pre <;> simp at h
  | cons b t ih =>
    constructor
    · intro h
      have h' : s(x, y) = s(a, b) ∨ s(x, y) ∈ adjPairs (b :: t) := by
        have e : adjPairs (a :: b :: t) = s(a, b) :: adjPairs (b :: t) :=
          rfl
        rw [e] at h
        exact List.mem_cons.mp h
      rcases h' with heq | hmem
      · rw [Sym2.eq_iff] at heq
        rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨[], t, Or.inl rfl⟩
        · exact ⟨[], t, Or.inr rfl⟩
      · obtain ⟨pre, post, h | h⟩ := ih.mp hmem
        · refine ⟨a :: pre, post, Or.inl ?_⟩
          rw [List.cons_append, h]
        · refine ⟨a :: pre, post, Or.inr ?_⟩
          rw [List.cons_append, h]
    · rintro ⟨pre, post, h | h⟩
      · cases pre with
        | nil =>
          obtain ⟨h1, h2⟩ := List.cons.inj h
          obtain ⟨h3, h4⟩ := List.cons.inj h2
          have e : adjPairs (a :: b :: t) = s(a, b) :: adjPairs (b :: t) :=
            rfl
          rw [e]
          exact List.mem_cons.mpr (Or.inl (by rw [← h1, ← h3]))
        | cons w pre =>
          obtain ⟨-, h2⟩ := List.cons.inj h
          have e : adjPairs (a :: b :: t) = s(a, b) :: adjPairs (b :: t) :=
            rfl
          rw [e]
          exact List.mem_cons.mpr
            (Or.inr (ih.mpr ⟨pre, post, Or.inl h2⟩))
      · cases pre with
        | nil =>
          obtain ⟨h1, h2⟩ := List.cons.inj h
          obtain ⟨h3, h4⟩ := List.cons.inj h2
          have e : adjPairs (a :: b :: t) = s(a, b) :: adjPairs (b :: t) :=
            rfl
          rw [e]
          apply List.mem_cons.mpr
          left
          rw [← h1, ← h3]
          exact Sym2.eq_swap
        | cons w pre =>
          obtain ⟨-, h2⟩ := List.cons.inj h
          have e : adjPairs (a :: b :: t) = s(a, b) :: adjPairs (b :: t) :=
            rfl
          rw [e]
          exact List.mem_cons.mpr
            (Or.inr (ih.mpr ⟨pre, post, Or.inr h2⟩))

theorem mem_adjPairs {x y : X} {l : List X} :
    s(x, y) ∈ adjPairs l ↔
      ∃ pre post, l = pre ++ x :: y :: post ∨
        l = pre ++ y :: x :: post := by
  cases l with
  | nil =>
    constructor
    · intro h
      simp [adjPairs] at h
    · rintro ⟨pre, post, h | h⟩ <;> cases pre <;> simp at h
  | cons a l => exact mem_adjPairs_cons l

theorem adjPairs_nodup_cons {a : X} :
    ∀ l : List X, (a :: l).Nodup → (adjPairs (a :: l)).Nodup := by
  intro l
  induction l generalizing a with
  | nil => simp [adjPairs]
  | cons b t ih =>
    intro hnd
    have ha_not : a ∉ b :: t := (List.nodup_cons.mp hnd).1
    have hnd_bt : (b :: t).Nodup := (List.nodup_cons.mp hnd).2
    have e : adjPairs (a :: b :: t) = s(a, b) :: adjPairs (b :: t) := rfl
    rw [e, List.nodup_cons]
    refine ⟨?_, ih hnd_bt⟩
    intro hmem
    obtain ⟨pre, post, h | h⟩ := mem_adjPairs.mp hmem
    · exact ha_not (by
        rw [h]
        exact List.mem_append_right pre (List.mem_cons_self))
    · exact ha_not (by
        rw [h]
        exact List.mem_append_right pre
          (List.mem_cons_of_mem b (List.mem_cons_self)))

theorem adjPairs_nodup {l : List X} (h : l.Nodup) :
    (adjPairs l).Nodup := by
  cases l with
  | nil => simp [adjPairs]
  | cons a l => exact adjPairs_nodup_cons l h

theorem adjPairs_cons_sum (α β : ℝ) (color : X → Color) (a : X) :
    ∀ l : List X, ((adjPairs (a :: l)).map (edgeCost α β color)).sum
      = adjCost α β color (a :: l) := by
  intro l
  induction l generalizing a with
  | nil => rfl
  | cons b t ih =>
    have e : adjPairs (a :: b :: t) = s(a, b) :: adjPairs (b :: t) := rfl
    rw [e]
    simp only [List.map_cons, List.sum_cons, edgeCost_mk]
    rw [ih]
    rfl

theorem adjPairs_sum (α β : ℝ) (color : X → Color) (l : List X) :
    ((adjPairs l).map (edgeCost α β color)).sum
      = adjCost α β color l := by
  cases l with
  | nil => rfl
  | cons a l => exact adjPairs_cons_sum α β color a l

/-- The graph whose edges are the adjacent pairs of the sorted
order. -/
def adjGraph : SimpleGraph X where
  Adj x y := s(x, y) ∈ adjPairs (sortedList X)
  symm := by
    refine ⟨?_⟩
    intro x y h
    show s(y, x) ∈ adjPairs (sortedList X)
    rw [Sym2.eq_swap]
    exact h
  loopless := by
    refine ⟨?_⟩
    intro x h
    obtain ⟨pre, post, h | h⟩ := mem_adjPairs.mp h
    · have hnd := sortedList_nodup (X := X)
      rw [h] at hnd
      obtain ⟨-, h2, -⟩ := List.nodup_append.mp hnd
      exact (List.nodup_cons.mp h2).1 (List.mem_cons_self)
    · have hnd := sortedList_nodup (X := X)
      rw [h] at hnd
      obtain ⟨-, h2, -⟩ := List.nodup_append.mp hnd
      exact (List.nodup_cons.mp h2).1 (List.mem_cons_self)

theorem sorted_before_iff_lt {x y : X} :
    Before (sortedList X) x y ↔ x < y := by
  constructor
  · intro h
    have hle : x ≤ y := pairwise_of_before sortedList_pairwise_le h
    have hne : x ≠ y := by
      intro he
      subst he
      exact before_irrefl sortedList_nodup h
    exact lt_of_le_of_ne hle hne
  · intro hlt
    rcases before_dichotomy sortedList_nodup (mem_sortedList x)
        (mem_sortedList y) (ne_of_lt hlt) with h | h
    · exact h
    · exfalso
      have hle : y ≤ x := pairwise_of_before sortedList_pairwise_le h
      exact lt_irrefl x (lt_of_lt_of_le hlt hle)

/-- If every adjacent pair of the sorted order appears in that
order in `L`, then every pair that is in sorted order appears in
that order in `L`: transitivity along the chain of adjacent pairs
between them. -/
theorem before_of_chain {L : List X} (hndL : L.Nodup)
    (hstep : ∀ p q pre post, sortedList X = pre ++ p :: q :: post →
      Before L p q) :
    ∀ (a b c : List X) (x y : X),
      sortedList X = a ++ x :: b ++ y :: c → Before L x y := by
  intro a b
  induction b generalizing a with
  | nil =>
    intro c x y h
    exact hstep x y a c (by simpa using h)
  | cons z b ih =>
    intro c x y h
    have hxz : Before L x z :=
      hstep x z a (b ++ y :: c) (by simpa using h)
    have hzy : Before L z y :=
      ih (a ++ [x]) c z y (by
        rw [h]
        simp [List.append_assoc])
    exact before_trans hndL hxz hzy

/-- The adjacent pairs of the sorted order are determining: a
candidate order consistent with them must put every adjacent pair
in its sorted order, hence (by transitivity along the chain) every
pair in its sorted order, hence must be the sorted order itself. -/
theorem adjGraph_determining :
    Determining (adjGraph : SimpleGraph X) := by
  intro L hL
  obtain ⟨hperm, hpair⟩ := hL
  have hndL : L.Nodup :=
    hperm.nodup_iff.mpr (sortedList_nodup (X := X))
  have hmemL : ∀ z, z ∈ L :=
    fun z => hperm.symm.subset (mem_sortedList z)
  have hstep : ∀ p q pre post, sortedList X = pre ++ p :: q :: post →
      Before L p q := by
    intro p q pre post hconsec
    have hpq : p < q :=
      sorted_before_iff_lt.mp ⟨pre, [], post, by simpa using hconsec⟩
    rcases before_dichotomy hndL (hmemL p) (hmemL q) (ne_of_lt hpq)
        with h | h
    · exact h
    · exfalso
      have hno := pairwise_of_before hpair h
      refine hno ⟨hpq, ?_⟩
      show s(q, p) ∈ adjPairs (sortedList X)
      exact mem_adjPairs.mpr ⟨pre, post, Or.inr hconsec⟩
  have hLlt : ∀ x y, Before L x y ↔ x < y := by
    intro x y
    constructor
    · intro h
      by_contra hnot
      have hyx : y ≤ x := le_of_not_gt hnot
      rcases eq_or_lt_of_le hyx with heq | hlt
      · subst heq
        exact before_irrefl hndL h
      · obtain ⟨a, b, c, habc⟩ := sorted_before_iff_lt.mpr hlt
        exact before_antisymm hndL h
          (before_of_chain hndL hstep a b c y x habc)
    · intro hlt
      obtain ⟨a, b, c, habc⟩ := sorted_before_iff_lt.mpr hlt
      exact before_of_chain hndL hstep a b c x y habc
  apply eq_of_before_eq hndL sortedList_nodup
  · intro z
    exact ⟨fun _ => mem_sortedList z, fun _ => hmemL z⟩
  · intro x y
    rw [hLlt x y, sorted_before_iff_lt]

/-- The adjacent-pairs graph costs exactly `H`: its edges are
exactly the adjacent pairs of the sorted order, and `H` is the sum
of their costs. -/
theorem graphCost_adjGraph (α β : ℝ) :
    graphCost α β color adjGraph = benchmarkH α β color := by
  classical
  have hset : Finset.univ.filter (fun e => e ∈ adjGraph.edgeSet)
      = (adjPairs (sortedList X)).toFinset := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        List.mem_toFinset]
      constructor
      · intro h
        exact (SimpleGraph.mem_edgeSet adjGraph).mp h
      · intro h
        exact (SimpleGraph.mem_edgeSet adjGraph).mpr h
  rw [graphCost, hset,
    List.sum_toFinset _ (adjPairs_nodup sortedList_nodup),
    adjPairs_sum]
  rfl

/-- **`prop:Hlower`.** `H` is exactly the cost of the cheapest
proof of the sorted order: every determining set of comparisons
costs at least `H`, and the adjacent pairs are a determining set
costing exactly `H`. -/
theorem benchmarkH_is_cheapest_proof (α β : ℝ)
    (hα : 1 < α) (hβ : 1 < β) :
    (∀ G, Determining G → benchmarkH α β color ≤ graphCost α β color G)
      ∧ (∃ G, Determining G ∧ graphCost α β color G
          = benchmarkH α β color) :=
  ⟨fun G hG => determining_cost_ge (color := color) α β hα hβ G hG,
    adjGraph, adjGraph_determining,
    graphCost_adjGraph (color := color) α β⟩

end Bichromatic.Randomized
