import RandomizedLog.Statements
import RandomizedLog.HLower

/-!
# From injective ranks to the red permutation

The paper's random experiment is a uniform random permutation of
the red elements: the blues start in place, and the reds arrive in
a uniform random order. The counting formalization instead averages
over all injective ranks `τF : X → Fin N` of all elements
(`InjRanks`). This file proves the two experiments give the same
expected total cost:

* every quantity in `totalExecCost` depends on `τF` only through
  the induced red arrival order `arrivalsOf color τF` (the record
  predicates compare ranks of red elements only);
* each red permutation is induced by exactly the same number of
  injective ranks (relabeling the elements by an equivalence that
  carries one arrival order to the other is a bijection between
  the fibres).

Hence `spliceSorter.expectedCost`, the average over injective
ranks, equals the average over the uniform red permutation of the
cost of that arrival order (`redArrivalCost`).
-/

namespace Bichromatic.Randomized

open Bichromatic

variable {X : Type*} [LinearOrder X] [Fintype X] (color : X → Color)

/-- Any two orderings of the same elements are carried to each
other by an equivalence of `X` that fixes everything outside the
list. Proved by induction on the permutation. -/
theorem exists_equiv_map_of_perm {L L' : List X}
    (hperm : L.Perm L') (hnd : L.Nodup) :
    ∃ e : X ≃ X, List.map e L = L' ∧ ∀ x, x ∉ L → e x = x := by
  classical
  induction hperm with
  | nil => exact ⟨Equiv.refl X, rfl, fun x _ => rfl⟩
  | cons a hperm ih =>
    obtain ⟨e, hmap, hfix⟩ := ih (List.nodup_cons.mp hnd).2
    have hea : e a = a := hfix a (List.nodup_cons.mp hnd).1
    refine ⟨e, ?_, fun x hx =>
      hfix x (fun hxL => hx (List.mem_cons_of_mem a hxL))⟩
    rw [List.map_cons, hea, hmap]
  | swap a b l =>
    refine ⟨Equiv.swap a b, ?_, ?_⟩
    · have hb_not : b ∉ a :: l := (List.nodup_cons.mp hnd).1
      have ha_not : a ∉ l :=
        (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
      have hmap_l : List.map (Equiv.swap a b) l = l := by
        have h : List.map (Equiv.swap a b) l = List.map id l :=
          List.map_congr_left (fun z hz =>
            Equiv.swap_apply_of_ne_of_ne
              (fun hh => ha_not (hh ▸ hz))
              (fun hh => hb_not (List.mem_cons_of_mem a (hh ▸ hz))))
        rw [h, List.map_id]
      rw [List.map_cons, List.map_cons, Equiv.swap_apply_right,
        Equiv.swap_apply_left, hmap_l]
    · intro x hx
      have hxb : x ≠ b := fun h => hx (h ▸ List.mem_cons_self)
      have hxa : x ≠ a :=
        fun h => hx (List.mem_cons_of_mem b (h ▸ List.mem_cons_self))
      exact Equiv.swap_apply_of_ne_of_ne hxa hxb
  | trans hperm₁ hperm₂ ih₁ ih₂ =>
    obtain ⟨e₁, hmap₁, hfix₁⟩ := ih₁ hnd
    obtain ⟨e₂, hmap₂, hfix₂⟩ :=
      ih₂ (hperm₁.nodup_iff.mp hnd)
    refine ⟨e₁.trans e₂, ?_, ?_⟩
    · rw [Equiv.coe_trans, ← List.map_map, hmap₁, hmap₂]
    · intro x hx
      rw [Equiv.trans_apply, hfix₁ x hx,
        hfix₂ x (fun h => hx (hperm₁.mem_iff.mpr h))]

/-- In a list sorted by an injective key, `x` comes before `y`
exactly when its key is smaller. -/
theorem before_iff_key_lt {M : List X} {k : X → Fin (Fintype.card X)}
    (hk : Function.Injective k) (hnd : M.Nodup)
    (hpw : M.Pairwise (fun a b => (k a).val ≤ (k b).val))
    {x y : X} (hx : x ∈ M) (hy : y ∈ M) :
    Before M x y ↔ (k x).val < (k y).val := by
  constructor
  · intro h
    have hle := pairwise_of_before hpw h
    have hne : x ≠ y := by
      intro he
      subst he
      exact before_irrefl hnd h
    have hne2 : (k x).val ≠ (k y).val :=
      fun he => hne (hk (Fin.ext he))
    exact lt_of_le_of_ne hle hne2
  · intro hlt
    rcases before_dichotomy hnd hx hy (fun he => by
        subst he
        exact lt_irrefl _ hlt) with h | h
    · exact h
    · exfalso
      have hle := pairwise_of_before hpw h
      exact lt_irrefl _ (lt_of_lt_of_le hlt hle)

/-- Relabeling the elements by an equivalence carries the arrival
order along: if `e` carries the arrival order of `τ` to `L'`, then
the arrival order of `τ ∘ e.symm` is `L'`. -/
theorem arrivalsOf_comp_equiv {τ : X → Fin (Fintype.card X)}
    (hinj : Function.Injective τ) {L L' : List X} {e : X ≃ X}
    (harr : arrivalsOf color τ = L) (hemap : List.map e L = L')
    (hefix : ∀ x, x ∉ L → e x = x) :
    arrivalsOf color (τ ∘ e.symm) = L' := by
  have hinj' : Function.Injective (τ ∘ e.symm) :=
    hinj.comp e.symm.injective
  have hndL : L.Nodup := harr ▸ arrivalsOf_nodup color τ
  have hndL' : L'.Nodup := by
    rw [← hemap]
    exact hndL.map e.injective
  have hmem : ∀ z, z ∈ arrivalsOf color (τ ∘ e.symm) ↔ z ∈ L' := by
    intro z
    constructor
    · intro hz
      have hzred : color z = Color.red := arrivalsOf_mem_red color hz
      have h1 : e.symm z ∈ L := by
        by_contra hnot
        by_cases hc : color (e.symm z) = Color.red
        · exact hnot (harr ▸ arrivalsOf_mem color hc)
        · have hcblue : color (e.symm z) = Color.blue := by
            cases h : color (e.symm z) with
            | red => exact absurd h hc
            | blue => rfl
          have hfix : e (e.symm z) = e.symm z := hefix _ hnot
          rw [Equiv.apply_symm_apply] at hfix
          rw [← hfix] at hcblue
          rw [hzred] at hcblue
          exact Color.noConfusion hcblue
      have hzmap : z ∈ List.map e L :=
        List.mem_map.mpr ⟨e.symm z, h1, Equiv.apply_symm_apply e z⟩
      rwa [hemap] at hzmap
    · intro hz
      rw [← hemap] at hz
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
      have hyred : color y = Color.red :=
        arrivalsOf_mem_red color (harr.symm ▸ hy)
      have hred : color (e y) = Color.red := by
        by_contra hnot
        have hcblue : color (e y) = Color.blue := by
          cases h : color (e y) with
          | red => exact absurd h hnot
          | blue => rfl
        have hnotL : e y ∉ L := fun hm => by
          have hm2 : e y ∈ arrivalsOf color τ := harr ▸ hm
          have hm3 := arrivalsOf_mem_red color hm2
          rw [hcblue] at hm3
          exact Color.noConfusion hm3
        have hfix := hefix _ hnotL
        have hyey : y = e y := e.injective hfix.symm
        rw [hyey] at hyred
        rw [hcblue] at hyred
        exact Color.noConfusion hyred
      exact arrivalsOf_mem color hred
  have hpw' : L'.Pairwise
      (fun a b => ((τ ∘ e.symm) a).val ≤ ((τ ∘ e.symm) b).val) := by
    have hpw : (arrivalsOf color τ).Pairwise
        (fun a b => (τ a).val ≤ (τ b).val) :=
      List.pairwise_mergeSort' _ _
    rw [harr] at hpw
    rw [← hemap]
    exact hpw.map e (fun a b hab => by
      show (τ (e.symm (e a))).val ≤ (τ (e.symm (e b))).val
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      exact hab)
  have hpwA : (arrivalsOf color (τ ∘ e.symm)).Pairwise
      (fun a b => ((τ ∘ e.symm) a).val ≤ ((τ ∘ e.symm) b).val) :=
    List.pairwise_mergeSort' _ _
  apply eq_of_before_eq (arrivalsOf_nodup color (τ ∘ e.symm)) hndL' hmem
  intro x y
  constructor
  · intro h
    have hx := (before_mem h).1
    have hy := (before_mem h).2
    have hlt : ((τ ∘ e.symm) x).val < ((τ ∘ e.symm) y).val :=
      (before_iff_key_lt hinj' (arrivalsOf_nodup color (τ ∘ e.symm))
        hpwA hx hy).mp h
    exact (before_iff_key_lt hinj' hndL' hpw'
      ((hmem x).mp hx) ((hmem y).mp hy)).mpr hlt
  · intro h
    have hx : x ∈ L' := (before_mem h).1
    have hy : y ∈ L' := (before_mem h).2
    have hlt : ((τ ∘ e.symm) x).val < ((τ ∘ e.symm) y).val :=
      (before_iff_key_lt hinj' hndL' hpw' hx hy).mp h
    exact (before_iff_key_lt hinj'
      (arrivalsOf_nodup color (τ ∘ e.symm)) hpwA
      ((hmem x).mpr hx) ((hmem y).mpr hy)).mpr hlt

theorem injective_of_mem_InjRanks {τ : X → Fin (Fintype.card X)}
    (hτ : τ ∈ InjRanks X) : Function.Injective τ := by
  have h2 : τ ∈ Finset.univ.filter
      (fun τ : X → Fin (Fintype.card X) => Function.Injective τ) := hτ
  exact (Finset.mem_filter.mp h2).2

/-- For red elements, comparing ranks is the same as comparing
positions in the arrival order. -/
theorem red_lt_iff {τ : X → Fin (Fintype.card X)}
    (hinj : Function.Injective τ)
    {r s : X} (hr : color r = Color.red) (hs : color s = Color.red) :
    (τ r).val < (τ s).val ↔ Before (arrivalsOf color τ) r s := by
  have hpw : (arrivalsOf color τ).Pairwise
      (fun a b => (τ a).val ≤ (τ b).val) :=
    List.pairwise_mergeSort' _ _
  constructor
  · intro hlt
    have hrs : r ≠ s := fun he => by
      subst he
      exact lt_irrefl _ hlt
    rcases before_dichotomy (arrivalsOf_nodup color τ)
        (arrivalsOf_mem color hr) (arrivalsOf_mem color hs) hrs
        with h | h
    · exact h
    · exfalso
      have hle := pairwise_of_before hpw h
      exact lt_irrefl _ (lt_of_lt_of_le hlt hle)
  · intro h
    have hle := pairwise_of_before hpw h
    have hrs : r ≠ s := by
      intro he
      subst he
      exact before_irrefl (arrivalsOf_nodup color τ) h
    have hne : (τ r).val ≠ (τ s).val :=
      fun he => hrs (hinj (Fin.ext he))
    exact lt_of_le_of_ne hle hne

theorem rank_lt_iff_rank_lt_of_arrivals
    {τ₁ τ₂ : X → Fin (Fintype.card X)}
    (h1 : Function.Injective τ₁) (h2 : Function.Injective τ₂)
    (h : arrivalsOf color τ₁ = arrivalsOf color τ₂)
    {r r' : X} (hr : color r = Color.red)
    (hr' : color r' = Color.red) :
    (τ₁ r).val < (τ₁ r').val ↔ (τ₂ r).val < (τ₂ r').val := by
  rw [red_lt_iff (color := color) h1 hr hr',
    red_lt_iff (color := color) h2 hr hr', h]

theorem predRecords_eq_of_arrivalsOf_eq
    {τ₁ τ₂ : X → Fin (Fintype.card X)}
    (h1 : Function.Injective τ₁) (h2 : Function.Injective τ₂)
    (h : arrivalsOf color τ₁ = arrivalsOf color τ₂) (b : X) :
    predRecords color τ₁ b = predRecords color τ₂ b := by
  classical
  apply Finset.ext
  intro r
  simp only [predRecords, Finset.mem_filter]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro hh
    refine ⟨hh.1, hh.2.1, fun r' hr' hrr' hrb => ?_⟩
    exact (rank_lt_iff_rank_lt_of_arrivals (color := color) h1 h2 h
      hh.1 hr').mp (hh.2.2 r' hr' hrr' hrb)
  · intro hh
    refine ⟨hh.1, hh.2.1, fun r' hr' hrr' hrb => ?_⟩
    exact (rank_lt_iff_rank_lt_of_arrivals (color := color) h1 h2 h
      hh.1 hr').mpr (hh.2.2 r' hr' hrr' hrb)

theorem succRecords_eq_of_arrivalsOf_eq
    {τ₁ τ₂ : X → Fin (Fintype.card X)}
    (h1 : Function.Injective τ₁) (h2 : Function.Injective τ₂)
    (h : arrivalsOf color τ₁ = arrivalsOf color τ₂) (b : X) :
    succRecords color τ₁ b = succRecords color τ₂ b := by
  classical
  apply Finset.ext
  intro r
  simp only [succRecords, Finset.mem_filter]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro hh
    refine ⟨hh.1, hh.2.1, fun r' hr' hrb hrr' => ?_⟩
    exact (rank_lt_iff_rank_lt_of_arrivals (color := color) h1 h2 h
      hh.1 hr').mp (hh.2.2 r' hr' hrb hrr')
  · intro hh
    refine ⟨hh.1, hh.2.1, fun r' hr' hrb hrr' => ?_⟩
    exact (rank_lt_iff_rank_lt_of_arrivals (color := color) h1 h2 h
      hh.1 hr').mpr (hh.2.2 r' hr' hrb hrr')

theorem recordsAt_eq_of_arrivalsOf_eq
    {τ₁ τ₂ : X → Fin (Fintype.card X)}
    (h1 : Function.Injective τ₁) (h2 : Function.Injective τ₂)
    (h : arrivalsOf color τ₁ = arrivalsOf color τ₂) (a : X) :
    recordsAt color τ₁ a = recordsAt color τ₂ a := by
  unfold recordsAt
  rw [predRecords_eq_of_arrivalsOf_eq (color := color) h1 h2 h,
    succRecords_eq_of_arrivalsOf_eq (color := color) h1 h2 h]

theorem foreignAt_eq_of_arrivalsOf_eq
    {τ₁ τ₂ : X → Fin (Fintype.card X)}
    (h1 : Function.Injective τ₁) (h2 : Function.Injective τ₂)
    (h : arrivalsOf color τ₁ = arrivalsOf color τ₂) (R : List X) :
    foreignAt color τ₁ R = foreignAt color τ₂ R := by
  cases R with
  | nil => rfl
  | cons a t =>
    show (if (∀ x ∈ a :: t, color x = Color.red) ∧ 2 ≤ (a :: t).length
        then 2 * (recordsAt color τ₁ a
          + recordsAt color τ₁ ((a :: t).getLast (by simp)))
        else 0)
      = (if (∀ x ∈ a :: t, color x = Color.red) ∧ 2 ≤ (a :: t).length
        then 2 * (recordsAt color τ₂ a
          + recordsAt color τ₂ ((a :: t).getLast (by simp)))
        else 0)
    rw [recordsAt_eq_of_arrivalsOf_eq (color := color) h1 h2 h a,
      recordsAt_eq_of_arrivalsOf_eq (color := color) h1 h2 h
        ((a :: t).getLast (by simp))]

theorem foreignCharge_eq_of_arrivalsOf_eq
    {τ₁ τ₂ : X → Fin (Fintype.card X)}
    (h1 : Function.Injective τ₁) (h2 : Function.Injective τ₂)
    (h : arrivalsOf color τ₁ = arrivalsOf color τ₂) :
    foreignCharge color τ₁ = foreignCharge color τ₂ := by
  have hm : ((runsOf color (sortedList X)).map (foreignAt color τ₁)).sum
      = ((runsOf color (sortedList X)).map (foreignAt color τ₂)).sum := by
    congr 1
    exact List.map_congr_left
      (fun R _ => foreignAt_eq_of_arrivalsOf_eq (color := color) h1 h2 h R)
  exact hm

/-- The total cost of an execution depends on the ranking only
through the red arrival order it induces. -/
theorem totalExecCost_eq_of_arrivalsOf_eq (α β : ℝ)
    {τ₁ τ₂ : X → Fin (Fintype.card X)}
    (h1 : Function.Injective τ₁) (h2 : Function.Injective τ₂)
    (h : arrivalsOf color τ₁ = arrivalsOf color τ₂) :
    totalExecCost α β color τ₁ = totalExecCost α β color τ₂ := by
  classical
  by_cases hb : blueList color = []
  · unfold totalExecCost
    rw [dif_pos hb, dif_pos hb]
  · have hev : execEvents color hb (arrivalsOf color τ₁)
        (arrivalsOf_perm color τ₁)
        = execEvents color hb (arrivalsOf color τ₂)
          (arrivalsOf_perm color τ₂) := by
      have key : ∀ (L₁ L₂ : List X)
          (hp₁ : L₁.Perm (redList color))
          (hp₂ : L₂.Perm (redList color)), L₁ = L₂ →
          execEvents color hb L₁ hp₁ = execEvents color hb L₂ hp₂ := by
        intro L₁ L₂ hp₁ hp₂ hL
        cases hL
        rfl
      exact key _ _ _ _ h
    have hfc : foreignCharge color τ₁ = foreignCharge color τ₂ :=
      foreignCharge_eq_of_arrivalsOf_eq (color := color) h1 h2 h
    unfold totalExecCost
    rw [dif_neg hb, dif_neg hb, hev, hfc]

open Classical in
/-- The red arrival orders: permutations of the red elements. The
paper's random experiment is the uniform distribution on these. -/
noncomputable def redPerms (color : X → Color) : Finset (List X) :=
  (redList color).permutations.toFinset

theorem mem_redPerms {L : List X} :
    L ∈ redPerms color ↔ L.Perm (redList color) := by
  simp [redPerms, List.mem_permutations]

/-- Every red arrival order is induced by some injective rank. -/
theorem exists_rank_of_mem_redPerms {L : List X}
    (hL : L ∈ redPerms color) :
    ∃ τ, τ ∈ InjRanks X ∧ arrivalsOf color τ = L := by
  classical
  have hLp : L.Perm (redList color) :=
    (mem_redPerms (color := color)).mp hL
  set τ0 : X → Fin (Fintype.card X) := ⇑(Fintype.equivFin X)
  have hinj0 : Function.Injective τ0 := (Fintype.equivFin X).injective
  have hL0perm : (arrivalsOf color τ0).Perm (redList color) :=
    arrivalsOf_perm color τ0
  have hperm : (arrivalsOf color τ0).Perm L := hL0perm.trans hLp.symm
  obtain ⟨e, hemap, hefix⟩ := exists_equiv_map_of_perm hperm
    (arrivalsOf_nodup color τ0)
  exact ⟨τ0 ∘ e.symm,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hinj0.comp e.symm.injective⟩,
    arrivalsOf_comp_equiv (color := color) hinj0 rfl hemap hefix⟩

/-- The cost of one red arrival order: the total cost of any (hence
every) injective rank inducing it. -/
noncomputable def redArrivalCost (α β : ℝ) (color : X → Color)
    (L : List X) : ℝ :=
  if h : ∃ τ, τ ∈ InjRanks X ∧ arrivalsOf color τ = L
  then totalExecCost α β color (Classical.choose h) else 0

theorem redArrivalCost_eq (α β : ℝ) {L : List X}
    {τ : X → Fin (Fintype.card X)} (hτ : τ ∈ InjRanks X)
    (harr : arrivalsOf color τ = L) :
    redArrivalCost α β color L = totalExecCost α β color τ := by
  classical
  unfold redArrivalCost
  rw [dif_pos ⟨τ, hτ, harr⟩]
  have hex : ∃ τ, τ ∈ InjRanks X ∧ arrivalsOf color τ = L :=
    ⟨τ, hτ, harr⟩
  have hs := Classical.choose_spec hex
  exact totalExecCost_eq_of_arrivalsOf_eq (color := color) α β
    (injective_of_mem_InjRanks hs.1) (injective_of_mem_InjRanks hτ)
    (hs.2.trans harr.symm)

open Classical in
/-- Injective ranks inducing a given red arrival order. -/
noncomputable def arrivalFiber (color : X → Color) (L : List X) :
    Finset (X → Fin (Fintype.card X)) :=
  (InjRanks X).filter (fun τ => arrivalsOf color τ = L)

theorem equiv_symm_fix_of {L L' : List X} {e : X ≃ X}
    (hemap : List.map e L = L') (hefix : ∀ x, x ∉ L → e x = x) :
    (∀ x, x ∉ L' → e.symm x = x) ∧ List.map e.symm L' = L := by
  constructor
  · intro x hx
    by_contra hne
    by_cases hy : e.symm x ∈ L
    · have hm : e (e.symm x) ∈ L' :=
        hemap ▸ List.mem_map.mpr ⟨e.symm x, hy, rfl⟩
      rw [Equiv.apply_symm_apply] at hm
      exact hx hm
    · have hfix := hefix _ hy
      rw [Equiv.apply_symm_apply] at hfix
      exact hne hfix.symm
  · rw [← hemap, List.map_map]
    apply List.map_id''
    intro x
    exact Equiv.symm_apply_apply e x

/-- Every red arrival order is induced by the same number of
injective ranks: relabeling by an equivalence carrying one order
to the other is a bijection between the fibres. -/
theorem arrivalFiber_card_eq {L L' : List X}
    (hL : L ∈ redPerms color) (hL' : L' ∈ redPerms color) :
    (arrivalFiber color L).card = (arrivalFiber color L').card := by
  classical
  have hLp : L.Perm (redList color) :=
    (mem_redPerms (color := color)).mp hL
  have hL'p : L'.Perm (redList color) :=
    (mem_redPerms (color := color)).mp hL'
  have hperm : L.Perm L' := hLp.trans hL'p.symm
  have hnd : L.Nodup := hLp.nodup_iff.mpr (redList_nodup (color := color))
  obtain ⟨e, hemap, hefix⟩ := exists_equiv_map_of_perm hperm hnd
  obtain ⟨hefix', hemap'⟩ := equiv_symm_fix_of hemap hefix
  apply Finset.card_bij (fun τ _ => τ ∘ e.symm)
  · intro τ hτ
    simp only [arrivalFiber, Finset.mem_filter] at hτ ⊢
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (injective_of_mem_InjRanks hτ.1).comp e.symm.injective⟩, ?_⟩
    exact arrivalsOf_comp_equiv (color := color)
      (injective_of_mem_InjRanks hτ.1) hτ.2 hemap hefix
  · intro τ₁ _ τ₂ _ hh
    funext x
    have hcc := congrFun hh (e x)
    simpa [Function.comp_apply, Equiv.symm_apply_apply] using hcc
  · intro σ hσ
    simp only [arrivalFiber, Finset.mem_filter] at hσ
    refine ⟨σ ∘ e, ?_, ?_⟩
    · simp only [arrivalFiber, Finset.mem_filter]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (injective_of_mem_InjRanks hσ.1).comp e.injective⟩, ?_⟩
      have harr := arrivalsOf_comp_equiv (color := color)
        (injective_of_mem_InjRanks hσ.1) hσ.2 hemap' hefix'
      rwa [Equiv.symm_symm] at harr
    · funext x
      simp [Function.comp_apply, Equiv.apply_symm_apply]

/-- **The paper's random experiment.** The expected total cost of
SpliceSort, defined as the average over injective ranks of all
elements, equals the average over the uniform red permutation of
the cost of the arrival order — the paper's expectation. -/
theorem spliceSorter_expectedCost_eq_redPerm (α β : ℝ) :
    (spliceSorter (X := X)).expectedCost α β color
      = (∑ L ∈ redPerms color, redArrivalCost α β color L)
        / (redPerms color).card := by
  classical
  have hmaps : ∀ τ ∈ InjRanks X, arrivalsOf color τ ∈ redPerms color :=
    fun τ _ => (mem_redPerms (color := color)).mpr
      (arrivalsOf_perm color τ)
  have hsumfib : (∑ L ∈ redPerms color,
        ∑ τ ∈ arrivalFiber color L, totalExecCost α β color τ)
      = ∑ τ ∈ InjRanks X, totalExecCost α β color τ :=
    Finset.sum_fiberwise_of_maps_to hmaps _
  have hcardfib : (InjRanks X).card
      = ∑ L ∈ redPerms color, (arrivalFiber color L).card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := InjRanks X) (t := redPerms color) (f := arrivalsOf color)
      (fun τ hτ => Finset.mem_coe.mpr
        (hmaps τ (Finset.mem_coe.mp hτ)))
    exact h
  have hredmem : redList color ∈ redPerms color :=
    (mem_redPerms (color := color)).mpr (List.Perm.refl _)
  have hcpos : 0 < (arrivalFiber color (redList color)).card := by
    apply Finset.card_pos.mpr
    obtain ⟨τ, hτ, harr⟩ :=
      exists_rank_of_mem_redPerms (color := color) hredmem
    exact ⟨τ, by
      simp only [arrivalFiber, Finset.mem_filter]
      exact ⟨hτ, harr⟩⟩
  have hconst : ∀ L ∈ redPerms color,
      (arrivalFiber color L).card
        = (arrivalFiber color (redList color)).card :=
    fun L hL => arrivalFiber_card_eq (color := color) hL hredmem
  have hsum : (∑ τ ∈ InjRanks X, totalExecCost α β color τ)
      = ((arrivalFiber color (redList color)).card : ℝ)
        * ∑ L ∈ redPerms color, redArrivalCost α β color L := by
    rw [← hsumfib]
    have h1 : ∀ L ∈ redPerms color,
        (∑ τ ∈ arrivalFiber color L, totalExecCost α β color τ)
          = ((arrivalFiber color (redList color)).card : ℝ)
            * redArrivalCost α β color L := by
      intro L hL
      rw [← hconst L hL]
      have h2 : (∑ τ ∈ arrivalFiber color L, totalExecCost α β color τ)
          = ∑ τ ∈ arrivalFiber color L, redArrivalCost α β color L := by
        apply Finset.sum_congr rfl
        intro τ hτ
        have hτ' : τ ∈ (InjRanks X).filter
            (fun τ => arrivalsOf color τ = L) := hτ
        exact (redArrivalCost_eq (color := color) α β
          (Finset.mem_filter.mp hτ').1
          (Finset.mem_filter.mp hτ').2).symm
      rw [h2, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
  have hcard : ((InjRanks X).card : ℝ)
      = (redPerms color).card
        * ((arrivalFiber color (redList color)).card : ℝ) := by
    have hN : (InjRanks X).card
        = (redPerms color).card
          * (arrivalFiber color (redList color)).card := by
      rw [hcardfib]
      rw [Finset.sum_congr rfl (fun L hL => hconst L hL)]
      simp [Finset.sum_const, smul_eq_mul]
    rw [hN]
    push_cast
    ring
  show ((∑ τF ∈ InjRanks X, totalExecCost α β color τF)
      / (InjRanks X).card) = _
  rw [hsum, hcard, mul_comm ((arrivalFiber color (redList color)).card : ℝ),
    mul_div_mul_right _ _ (by exact_mod_cast hcpos.ne')]

end Bichromatic.Randomized
