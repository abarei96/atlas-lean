import RandomizedLog.Cost

/-!
# Records: the symmetry lemma behind `lem:records`

The paper's record bound rests on one symmetry: for red elements
`r, r'` in an interval, the uniform arrival permutation makes each of
them equally likely to arrive first. Formalized here over injective
arrival ranks `τ : X → Fin n` (the counting form of the uniform
permutation): for a finite set `S` of elements and `r ∈ S`, the number
of injective `τ` whose minimum on `S` is attained at `r`, times `|S|`,
equals the total number of injective `τ`. Hence the probability that
`r` is the minimum on `S` is exactly `1 / |S|`.

The proof: the sets `A s₀` (minimum attained at `s₀`) partition all
injective `τ` (values on `S` are distinct, so the minimum is attained
exactly once), and swapping the values at `r` and `s₀` — precomposition
with `Equiv.swap r s₀` — is a bijection `A r ≃ A s₀`.
-/

namespace Bichromatic.Randomized

open Bichromatic

variable {X : Type*} [LinearOrder X] [Fintype X] (color : X → Color)

/-- All injective arrival ranks. -/
def InjRanks (X : Type*) [Fintype X] [DecidableEq X] :
    Finset (X → Fin (Fintype.card X)) :=
  Finset.univ.filter (fun τ : X → Fin (Fintype.card X) => Function.Injective τ)

/-- Injective ranks whose minimum on `S` is attained at `s₀`. -/
def MinAt (S : Finset X) (s₀ : X) : Finset (X → Fin (Fintype.card X)) :=
  (InjRanks X).filter (fun τ => ∀ s ∈ S, s ≠ s₀ → τ s₀ < τ s)

theorem mem_minAt {S : Finset X} {s₀ : X} {τ : X → Fin (Fintype.card X)} :
    τ ∈ MinAt S s₀ ↔ Function.Injective τ ∧ ∀ s ∈ S, s ≠ s₀ → τ s₀ < τ s := by
  constructor
  · intro h
    rw [MinAt, Finset.mem_filter] at h
    exact ⟨(Finset.mem_filter.mp h.1).2, h.2⟩
  · intro h
    rw [MinAt, Finset.mem_filter]
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1⟩, h.2⟩

/-- Value-swapping at `r, s₀` sends minimum-at-`r` ranks to
minimum-at-`s₀` ranks, and is its own inverse. -/
theorem card_minAt_eq (S : Finset X) (r s₀ : X) (hr : r ∈ S) (hs₀ : s₀ ∈ S) :
    (MinAt S r).card = (MinAt S s₀).card := by
  apply Finset.card_bij (fun τ _ => τ ∘ Equiv.swap r s₀)
  · intro τ hτ
    rw [mem_minAt] at hτ ⊢
    obtain ⟨hinj, hmin⟩ := hτ
    constructor
    · exact hinj.comp (Equiv.swap r s₀).injective
    · intro s hs hne
      have hswap_s : Equiv.swap r s₀ s ≠ r := by
        intro hcon
        apply hne
        have := congrArg (Equiv.swap r s₀) hcon
        simpa using this
      have hval : (τ ∘ Equiv.swap r s₀) s₀ = τ r := by
        simp [Function.comp_apply, Equiv.swap_apply_right]
      have hvals : (τ ∘ Equiv.swap r s₀) s = τ (Equiv.swap r s₀ s) := rfl
      rw [hval, hvals]
      apply hmin (Equiv.swap r s₀ s) _ hswap_s
      by_cases h1 : s = r
      · subst h1; rw [Equiv.swap_apply_left]; exact hs₀
      · by_cases h2 : s = s₀
        · exact absurd h2 hne
        · have hsw : Equiv.swap r s₀ s = s := Equiv.swap_apply_of_ne_of_ne h1 h2
          rw [hsw]; exact hs
  · intro a _ b _ h
    have : (a ∘ Equiv.swap r s₀) ∘ Equiv.swap r s₀ = (b ∘ Equiv.swap r s₀) ∘ Equiv.swap r s₀ :=
      congrArg (· ∘ Equiv.swap r s₀) h
    have hcomp : ∀ f : X → Fin (Fintype.card X),
        (f ∘ Equiv.swap r s₀) ∘ Equiv.swap r s₀ = f := by
      intro f
      funext x
      simp [Function.comp_apply, Equiv.swap_apply_self]
    rw [hcomp a, hcomp b] at this
    exact this
  · intro τ hτ
    rw [mem_minAt] at hτ
    refine ⟨τ ∘ Equiv.swap r s₀, ?_, ?_⟩
    · rw [mem_minAt]
      obtain ⟨hinj, hmin⟩ := hτ
      constructor
      · exact hinj.comp (Equiv.swap r s₀).injective
      · intro s hs hne
        have hswap_s : Equiv.swap r s₀ s ≠ s₀ := by
          intro hcon
          apply hne
          have := congrArg (Equiv.swap r s₀) hcon
          simpa using this
        have hval : (τ ∘ Equiv.swap r s₀) r = τ s₀ := by
          simp [Function.comp_apply, Equiv.swap_apply_left]
        have hvals : (τ ∘ Equiv.swap r s₀) s = τ (Equiv.swap r s₀ s) := rfl
        rw [hval, hvals]
        apply hmin (Equiv.swap r s₀ s) _ hswap_s
        by_cases h1 : s = s₀
        · subst h1; rw [Equiv.swap_apply_right]; exact hr
        · by_cases h2 : s = r
          · exact absurd h2 hne
          · have hsw : Equiv.swap r s₀ s = s := Equiv.swap_apply_of_ne_of_ne h2 h1
            rw [hsw]; exact hs
    · funext x
      simp [Function.comp_apply, Equiv.swap_apply_self]

/-- The minimum on a nonempty `S` is attained somewhere: every
injective rank lies in some `MinAt S s₀`. -/
theorem exists_minAt (S : Finset X) (hS : S.Nonempty)
    {τ : X → Fin (Fintype.card X)} (hτ : Function.Injective τ) :
    ∃ s₀ ∈ S, τ ∈ MinAt S s₀ := by
  classical
  have hne : (S.image (fun s => (τ s).val)).Nonempty := Finset.Nonempty.image hS (fun s => (τ s).val)
  obtain ⟨s₀, hs₀, hs₀eq⟩ :
      ∃ s₀ ∈ S, (τ s₀).val = (S.image (fun s => (τ s).val)).min' hne := by
    have hm := Finset.min'_mem _ hne
    rw [Finset.mem_image] at hm
    obtain ⟨s₀, hs₀, he⟩ := hm
    exact ⟨s₀, hs₀, he⟩
  refine ⟨s₀, hs₀, ?_⟩
  rw [mem_minAt]
  refine ⟨hτ, fun s hs hne_s => ?_⟩
  have hle : (τ s₀).val ≤ (τ s).val := by
    rw [hs₀eq]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  have hne' : τ s₀ ≠ τ s := fun hcon => hne_s (hτ hcon).symm
  exact lt_of_le_of_ne (Fin.le_def.mpr hle) hne'

/-- Counting form of the symmetry: `|S|` times the number of injective
ranks minimized at `r` is the total number of injective ranks. -/
theorem card_minAt_mul (S : Finset X) (hS : S.Nonempty) (r : X) (hr : r ∈ S) :
    (MinAt S r).card * S.card = (InjRanks X).card := by
  have hpart : InjRanks X = S.biUnion (fun s₀ => MinAt S s₀) := by
    apply Finset.Subset.antisymm
    · intro τ hτ
      have hinj : Function.Injective τ := by
        have h2 : τ ∈ Finset.filter
            (fun τ : X → Fin (Fintype.card X) => Function.Injective τ) Finset.univ := hτ
        exact (Finset.mem_filter.mp h2).2
      obtain ⟨s₀, hs₀, hmin⟩ := exists_minAt (τ := τ) S hS hinj
      exact Finset.mem_biUnion.mpr ⟨s₀, hs₀, hmin⟩
    · intro τ hτ
      simp only [Finset.mem_biUnion] at hτ
      obtain ⟨s₀, _, hmin⟩ := hτ
      rw [mem_minAt] at hmin
      simp [InjRanks, hmin.1]
  have hdisj : (S : Set X).PairwiseDisjoint (fun s₀ => MinAt S s₀) := by
    intro a ha b hb hab
    rw [Function.onFun, Finset.disjoint_left]
    intro τ hτa hτb
    rw [mem_minAt] at hτa hτb
    have h1 := hτa.2 b hb (Ne.symm hab)
    have h2 := hτb.2 a ha hab
    exact absurd (lt_trans h1 h2) (lt_irrefl _)
  rw [hpart, Finset.card_biUnion hdisj]
  rw [Finset.sum_congr rfl (g := fun _ => (MinAt S r).card) (fun s₀ hs₀ => (card_minAt_eq S r s₀ hr hs₀).symm)]
  simp [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]

/-- The red elements below `b`. -/
def redsBelow (b : X) : Finset X :=
  Finset.univ.filter (fun r => color r = Color.red ∧ r < b)

/-- The interval set of a predecessor record candidate: red elements
in `[r, b)`. Its cardinality is the `i` of the paper's `1/i`. -/
def intervalSet (b r : X) : Finset X :=
  Finset.univ.filter (fun r' => color r' = Color.red ∧ r ≤ r' ∧ r' < b)

theorem mem_intervalSet {b r r' : X} :
    r' ∈ intervalSet color b r ↔ color r' = Color.red ∧ r ≤ r' ∧ r' < b := by
  simp [intervalSet]

theorem mem_redsBelow {b r : X} :
    r ∈ redsBelow color b ↔ color r = Color.red ∧ r < b := by
  simp [redsBelow]

/-- A red `r` below `b` is a predecessor record for arrival ranks `τ`
exactly when `τ` is minimized on the interval set at `r`. -/
theorem isPredRecord_iff_minAt {τ : X → Fin (Fintype.card X)} {b r : X}
    (hinj : Function.Injective τ) (hr : r ∈ redsBelow color b) :
    IsPredRecord color (fun x => (τ x).val) b r ↔ τ ∈ MinAt (intervalSet color b r) r := by
  rw [mem_redsBelow] at hr
  constructor
  · intro h
    rw [mem_minAt]
    refine ⟨hinj, fun s hs hne => ?_⟩
    rw [mem_intervalSet] at hs
    have hrs : r < s := lt_of_le_of_ne hs.2.1 (fun hcon => hne hcon.symm)
    have := h.2.2 s hs.1 hrs hs.2.2
    exact Fin.lt_def.mpr this
  · intro h
    rw [mem_minAt] at h
    refine ⟨hr.1, hr.2, fun r' hr'red hrr' hr'b => ?_⟩
    have hmem : r' ∈ intervalSet color b r := by
      rw [mem_intervalSet]; exact ⟨hr'red, le_of_lt hrr', hr'b⟩
    have := h.2 r' hmem (fun hcon => by rw [hcon] at hrr'; exact lt_irrefl _ hrr')
    exact Fin.lt_def.mp this

/-- The record predicates are decidable: bounded quantification over
a finite type with decidable comparisons. Stated as an instance so
the record finsets below have one consistent decidability instance. -/
instance (τ : X → Fin (Fintype.card X)) (b : X) :
    DecidablePred (fun r => IsPredRecord color (fun x => (τ x).val) b r) :=
  fun r => by unfold IsPredRecord; infer_instance

/-- The predecessor records for `b` under `τ`, as a finset. -/
noncomputable def predRecords (τ : X → Fin (Fintype.card X)) (b : X) : Finset X :=
  (redsBelow color b).filter (fun r => IsPredRecord color (fun x => (τ x).val) b r)

/-- Counting identity: total predecessor records over all injective
ranks equals the sum over red `r < b` of the ranks minimized at `r`.
(Linearity of expectation, in counting form.) -/
theorem sum_card_predRecords (b : X) :
    (∑ τ ∈ InjRanks X, (predRecords color τ b).card)
      = ∑ r ∈ redsBelow color b, (MinAt (intervalSet color b r) r).card := by
  classical
  have hinjOf : ∀ τ ∈ InjRanks X, Function.Injective τ := by
    intro τ hτ
    have h2 : τ ∈ Finset.filter
        (fun τ : X → Fin (Fintype.card X) => Function.Injective τ) Finset.univ := hτ
    exact (Finset.mem_filter.mp h2).2
  have h1 : ∀ τ ∈ InjRanks X, (predRecords color τ b).card
      = ∑ r ∈ redsBelow color b, (if τ ∈ MinAt (intervalSet color b r) r then 1 else 0) := by
    intro τ hτ
    unfold predRecords
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro r hr
    have hiff := isPredRecord_iff_minAt color (hinjOf τ hτ) hr
    by_cases hm : τ ∈ MinAt (intervalSet color b r) r <;> simp [hm, hiff]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hsub : MinAt (intervalSet color b r) r ⊆ InjRanks X := by
    intro τ hτ
    rw [mem_minAt] at hτ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ.1⟩
  rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hsub]

/-- Generic expected bound for a record system: if membership of `r`
in the record set of `τ` is exactly minimality of `τ` on an interval
set `I r`, with `I` self-containing, `R`-contained, and with distinct
cardinalities on `R`, then the expected number of records (average
over injective ranks) is at most `1 + log |R|`. This is the paper's
`lem:records` argument: counting identity, the `1/i` symmetry, and
the harmonic bound (Mathlib's `harmonic_le_one_add_log`). -/
theorem expected_le_one_add_log_of_system
    (R : Finset X) (I : X → Finset X)
    (recs : (X → Fin (Fintype.card X)) → Finset X)
    (hrecs : ∀ τ ∈ InjRanks X, recs τ = R.filter (fun r => τ ∈ MinAt (I r) r))
    (hIself : ∀ r ∈ R, r ∈ I r) (hIsub : ∀ r ∈ R, I r ⊆ R)
    (hIinj : Set.InjOn (fun r => (I r).card) R) :
    ((∑ τ ∈ InjRanks X, ((recs τ).card : ℝ)) / (InjRanks X).card)
      ≤ 1 + Real.log R.card := by
  classical
  have htotal_pos : 0 < (InjRanks X).card := by
    apply Finset.card_pos.mpr
    refine ⟨Fintype.equivFin X, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Fintype.equivFin X).injective⟩
  have hinjOf : ∀ τ ∈ InjRanks X, Function.Injective τ := by
    intro τ hτ
    have h2 : τ ∈ Finset.filter
        (fun τ : X → Fin (Fintype.card X) => Function.Injective τ) Finset.univ := hτ
    exact (Finset.mem_filter.mp h2).2
  -- counting identity
  have hcount : (∑ τ ∈ InjRanks X, ((recs τ).card : ℝ))
      = ∑ r ∈ R, ((MinAt (I r) r).card : ℝ) := by
    have h1 : ∀ τ ∈ InjRanks X, ((recs τ).card : ℝ)
        = ∑ r ∈ R, (if τ ∈ MinAt (I r) r then (1 : ℝ) else 0) := by
      intro τ hτ
      rw [hrecs τ hτ, Finset.card_filter]
      push_cast
      rfl
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    have hsub : MinAt (I r) r ⊆ InjRanks X := by
      intro τ hτ
      rw [mem_minAt] at hτ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ.1⟩
    have hNr : (∑ τ ∈ InjRanks X, (if τ ∈ MinAt (I r) r then (1 : ℝ) else 0))
        = ((MinAt (I r) r).card : ℝ) := by
      rw [show ((MinAt (I r) r).card : ℝ)
          = (((InjRanks X).filter (fun τ => τ ∈ MinAt (I r) r)).card : ℝ) by
          rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub]]
      rw [Finset.card_filter]
      push_cast
      rfl
    exact hNr
  rw [hcount, Finset.sum_div]
  -- each term is 1 / |I r|
  have hterm : ∀ r ∈ R, ((MinAt (I r) r).card : ℝ) / (InjRanks X).card
      = ((I r).card : ℝ)⁻¹ := by
    intro r hr
    have hne : (I r).Nonempty := ⟨r, hIself r hr⟩
    have hmul := card_minAt_mul (I r) hne r (hIself r hr)
    have hcast : ((MinAt (I r) r).card : ℝ) * ((I r).card : ℝ) = (InjRanks X).card := by
      exact_mod_cast hmul
    have hS : (0 : ℝ) < ((I r).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hne
    have hSne : ((I r).card : ℝ) ≠ 0 := ne_of_gt hS
    have hTne : ((InjRanks X).card : ℝ) ≠ 0 := by exact_mod_cast htotal_pos.ne'
    rw [div_eq_iff hTne, inv_mul_eq_div, eq_div_iff hSne]
    exact hcast
  rw [Finset.sum_congr rfl hterm]
  -- bound the sum of reciprocals by the harmonic sum over 1..|R|
  have himage : ∀ r ∈ R, (I r).card ∈ Finset.Icc 1 R.card := by
    intro r hr
    simp only [Finset.mem_Icc]
    exact ⟨Finset.card_pos.mpr ⟨r, hIself r hr⟩, Finset.card_le_card (hIsub r hr)⟩
  calc (∑ r ∈ R, ((I r).card : ℝ)⁻¹)
      = ∑ i ∈ R.image (fun r => (I r).card), (i : ℝ)⁻¹ := by
        rw [Finset.sum_image]
        intro x hx y hy hxy
        exact hIinj hx hy hxy
    _ ≤ ∑ i ∈ Finset.Icc 1 R.card, (i : ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          rw [Finset.mem_image] at hi
          obtain ⟨r, hr, rfl⟩ := hi
          exact himage r hr
        · intro i _ _; positivity
    _ = ((harmonic R.card : ℚ) : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        rfl
    _ ≤ 1 + Real.log R.card := harmonic_le_one_add_log R.card

/-- The red elements above `b`. -/
def redsAbove (b : X) : Finset X :=
  Finset.univ.filter (fun r => color r = Color.red ∧ b < r)

/-- The interval set of a successor record candidate: red elements
in `(b, r]`. -/
def intervalSetSucc (b r : X) : Finset X :=
  Finset.univ.filter (fun r' => color r' = Color.red ∧ b < r' ∧ r' ≤ r)

theorem mem_intervalSetSucc {b r r' : X} :
    r' ∈ intervalSetSucc color b r ↔ color r' = Color.red ∧ b < r' ∧ r' ≤ r := by
  simp [intervalSetSucc]

theorem mem_redsAbove {b r : X} :
    r ∈ redsAbove color b ↔ color r = Color.red ∧ b < r := by
  simp [redsAbove]

/-- Successor records are minima on their interval sets, as
predecessor records are. -/
theorem isSuccRecord_iff_minAt {τ : X → Fin (Fintype.card X)} {b r : X}
    (hinj : Function.Injective τ) (hr : r ∈ redsAbove color b) :
    IsSuccRecord color (fun x => (τ x).val) b r ↔ τ ∈ MinAt (intervalSetSucc color b r) r := by
  rw [mem_redsAbove] at hr
  constructor
  · intro h
    rw [mem_minAt]
    refine ⟨hinj, fun s hs hne => ?_⟩
    rw [mem_intervalSetSucc] at hs
    have hrs : s < r := lt_of_le_of_ne hs.2.2 (fun hcon => hne hcon)
    have := h.2.2 s hs.1 hs.2.1 hrs
    exact Fin.lt_def.mpr this
  · intro h
    rw [mem_minAt] at h
    refine ⟨hr.1, hr.2, fun r' hr'red hbr' hr'r => ?_⟩
    have hmem : r' ∈ intervalSetSucc color b r := by
      rw [mem_intervalSetSucc]; exact ⟨hr'red, hbr', le_of_lt hr'r⟩
    have := h.2 r' hmem (fun hcon => by rw [hcon] at hr'r; exact lt_irrefl _ hr'r)
    exact Fin.lt_def.mp this

instance (τ : X → Fin (Fintype.card X)) (b : X) :
    DecidablePred (fun r => IsSuccRecord color (fun x => (τ x).val) b r) :=
  fun r => by unfold IsSuccRecord; infer_instance

/-- The successor records for `b` under `τ`, as a finset. -/
noncomputable def succRecords (τ : X → Fin (Fintype.card X)) (b : X) : Finset X :=
  (redsAbove color b).filter (fun r => IsSuccRecord color (fun x => (τ x).val) b r)

/-- Expected predecessor records are `O(log N)`: the generic bound
instantiated on reds below `b` with their interval sets. The interval
cardinalities are distinct on `redsBelow b`: a nearer red has a
strictly larger interval. -/
theorem expected_pred_le (b : X) :
    ((∑ τ ∈ InjRanks X, ((predRecords color τ b).card : ℝ)) / (InjRanks X).card)
      ≤ 1 + Real.log (redsBelow color b).card := by
  apply expected_le_one_add_log_of_system (redsBelow color b) (intervalSet color b)
    (predRecords color · b)
  · intro τ hτ
    have hinj : Function.Injective τ := by
      have h2 : τ ∈ Finset.filter
          (fun τ : X → Fin (Fintype.card X) => Function.Injective τ) Finset.univ := hτ
      exact (Finset.mem_filter.mp h2).2
    unfold predRecords
    apply Finset.ext
    intro r
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro h; exact ⟨h.1, (isPredRecord_iff_minAt color hinj h.1).mp h.2⟩
    · intro h; exact ⟨h.1, (isPredRecord_iff_minAt color hinj h.1).mpr h.2⟩
  · intro r hr
    rw [mem_intervalSet]
    rw [mem_redsBelow] at hr
    exact ⟨hr.1, le_refl r, hr.2⟩
  · intro r hr r' hr'
    rw [mem_intervalSet] at hr'
    rw [mem_redsBelow]
    exact ⟨hr'.1, hr'.2.2⟩
  · intro r1 hr1 r2 hr2 hEq
    by_contra hne
    dsimp only at hEq
    have hr1' : r1 ∈ redsBelow color b := Finset.mem_coe.mp hr1
    have hr2' : r2 ∈ redsBelow color b := Finset.mem_coe.mp hr2
    rw [mem_redsBelow] at hr1' hr2'
    obtain ⟨hr1c, hr1lt⟩ := hr1'; obtain ⟨hr2c, hr2lt⟩ := hr2'
    rcases lt_trichotomy r1 r2 with h | h | h
    · have hss : intervalSet color b r2 ⊂ intervalSet color b r1 := by
        constructor
        · intro x hx
          rw [mem_intervalSet] at hx ⊢
          exact ⟨hx.1, le_trans (le_of_lt h) hx.2.1, hx.2.2⟩
        · intro hsub
          have : r1 ∈ intervalSet color b r2 := hsub (by
            rw [mem_intervalSet]; exact ⟨hr1c, le_refl r1, hr1lt⟩)
          rw [mem_intervalSet] at this
          exact absurd this.2.1 (not_le.mpr h)
      have := Finset.card_lt_card hss
      omega
    · exact absurd h hne
    · have hss : intervalSet color b r1 ⊂ intervalSet color b r2 := by
        constructor
        · intro x hx
          rw [mem_intervalSet] at hx ⊢
          exact ⟨hx.1, le_trans (le_of_lt h) hx.2.1, hx.2.2⟩
        · intro hsub
          have : r2 ∈ intervalSet color b r1 := hsub (by
            rw [mem_intervalSet]; exact ⟨hr2c, le_refl r2, hr2lt⟩)
          rw [mem_intervalSet] at this
          exact absurd this.2.1 (not_le.mpr h)
      have := Finset.card_lt_card hss
      omega

/-- Expected successor records are `O(log N)`, by the mirror argument. -/
theorem expected_succ_le (b : X) :
    ((∑ τ ∈ InjRanks X, ((succRecords color τ b).card : ℝ)) / (InjRanks X).card)
      ≤ 1 + Real.log (redsAbove color b).card := by
  apply expected_le_one_add_log_of_system (redsAbove color b) (intervalSetSucc color b)
    (succRecords color · b)
  · intro τ hτ
    have hinj : Function.Injective τ := by
      have h2 : τ ∈ Finset.filter
          (fun τ : X → Fin (Fintype.card X) => Function.Injective τ) Finset.univ := hτ
      exact (Finset.mem_filter.mp h2).2
    unfold succRecords
    apply Finset.ext
    intro r
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro h; exact ⟨h.1, (isSuccRecord_iff_minAt color hinj h.1).mp h.2⟩
    · intro h; exact ⟨h.1, (isSuccRecord_iff_minAt color hinj h.1).mpr h.2⟩
  · intro r hr
    rw [mem_intervalSetSucc]
    rw [mem_redsAbove] at hr
    exact ⟨hr.1, hr.2, le_refl r⟩
  · intro r hr r' hr'
    rw [mem_intervalSetSucc] at hr'
    rw [mem_redsAbove]
    exact ⟨hr'.1, hr'.2.1⟩
  · intro r1 hr1 r2 hr2 hEq
    by_contra hne
    dsimp only at hEq
    have hr1' : r1 ∈ redsAbove color b := Finset.mem_coe.mp hr1
    have hr2' : r2 ∈ redsAbove color b := Finset.mem_coe.mp hr2
    rw [mem_redsAbove] at hr1' hr2'
    obtain ⟨hr1c, hr1lt⟩ := hr1'; obtain ⟨hr2c, hr2lt⟩ := hr2'
    rcases lt_trichotomy r1 r2 with h | h | h
    · have hss : intervalSetSucc color b r1 ⊂ intervalSetSucc color b r2 := by
        constructor
        · intro x hx
          rw [mem_intervalSetSucc] at hx ⊢
          exact ⟨hx.1, hx.2.1, le_trans hx.2.2 (le_of_lt h)⟩
        · intro hsub
          have : r2 ∈ intervalSetSucc color b r1 := hsub (by
            rw [mem_intervalSetSucc]; exact ⟨hr2c, hr2lt, le_refl r2⟩)
          rw [mem_intervalSetSucc] at this
          exact absurd this.2.2 (not_le.mpr h)
      have := Finset.card_lt_card hss
      omega
    · exact absurd h hne
    · have hss : intervalSetSucc color b r2 ⊂ intervalSetSucc color b r1 := by
        constructor
        · intro x hx
          rw [mem_intervalSetSucc] at hx ⊢
          exact ⟨hx.1, hx.2.1, le_trans hx.2.2 (le_of_lt h)⟩
        · intro hsub
          have : r1 ∈ intervalSetSucc color b r2 := hsub (by
            rw [mem_intervalSetSucc]; exact ⟨hr1c, hr1lt, le_refl r1⟩)
          rw [mem_intervalSetSucc] at this
          exact absurd this.2.2 (not_le.mpr h)
      have := Finset.card_lt_card hss
      omega

/-- Records (predecessor or successor) are decidable, as above. -/
instance (τ : X → Fin (Fintype.card X)) (b : X) :
    DecidablePred (fun r => IsRecord color (fun x => (τ x).val) b r) :=
  fun r => by unfold IsRecord IsPredRecord IsSuccRecord; infer_instance

/-- **Records bound (paper `lem:records`), as a statement.**
The expected number of records for a fixed blue `b`, averaged over
injective arrival ranks, is bounded by a constant times `log` of the
instance size. (Averaging over injective ranks `X → Fin (card X)` is
the counting form of averaging over uniform permutations.) -/
def RecordsExpectedBound : Prop :=
  ∃ C₀ : ℝ, ∀ b : X,
    (∑ τ ∈ InjRanks X,
      ((Finset.univ.filter (fun r => IsRecord color (fun x => (τ x).val) b r)).card : ℝ))
      / (InjRanks X).card
      ≤ C₀ * Real.logb 2 (instSize X)

/-- The records finset of the paper's bound splits into predecessor
and successor records. -/
theorem records_card_split (τ : X → Fin (Fintype.card X)) (b : X) :
    (Finset.univ.filter (fun r => IsRecord color (fun x => (τ x).val) b r)).card
      = (predRecords color τ b).card + (succRecords color τ b).card := by
  classical
  have hset : Finset.univ.filter (fun r => IsRecord color (fun x => (τ x).val) b r)
      = predRecords color τ b ∪ succRecords color τ b := by
    ext r
    constructor
    · intro h
      have h' := Finset.mem_filter.mp h
      cases h'.2 with
      | inl hp =>
          apply Finset.mem_union_left
          exact Finset.mem_filter.mpr ⟨by rw [mem_redsBelow]; exact ⟨hp.1, hp.2.1⟩, hp⟩
      | inr hs =>
          apply Finset.mem_union_right
          exact Finset.mem_filter.mpr ⟨by rw [mem_redsAbove]; exact ⟨hs.1, hs.2.1⟩, hs⟩
    · intro h
      cases Finset.mem_union.mp h with
      | inl hp =>
          have h1 := Finset.mem_filter.mp hp
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, Or.inl h1.2⟩
      | inr hs =>
          have h1 := Finset.mem_filter.mp hs
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ r, Or.inr h1.2⟩
  have hdisj : Disjoint (predRecords color τ b) (succRecords color τ b) := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    have h1 : r ∈ redsBelow color b ∧ IsPredRecord color (fun x => (τ x).val) b r :=
      Finset.mem_filter.mp hr1
    have h2 : r ∈ redsAbove color b ∧ IsSuccRecord color (fun x => (τ x).val) b r :=
      Finset.mem_filter.mp hr2
    rw [mem_redsBelow] at h1
    rw [mem_redsAbove] at h2
    exact absurd h2.1.2 (not_lt.mpr (le_of_lt h1.1.2))
  rw [hset, Finset.card_union_of_disjoint hdisj]

/-- **The records bound (`lem:records`) holds**: the expected number of
records for any blue element, averaged over injective arrival ranks,
is `O(log N)` with the explicit constant `2 + 2 / log 2`. Assembled
from the two expected bounds by linearity, the harmonic estimate,
and `log |reds| ≤ log N`. -/
theorem recordsExpectedBound_holds : RecordsExpectedBound color := by
  classical
  refine ⟨2 + 2 / Real.log 2, fun b => ?_⟩
  have hsplit : ∀ τ ∈ InjRanks X,
      ((Finset.univ.filter (fun r => IsRecord color (fun x => (τ x).val) b r)).card : ℝ)
        = ((predRecords color τ b).card : ℝ) + ((succRecords color τ b).card : ℝ) := by
    intro τ _
    rw [records_card_split]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, add_div]
  have h1 : (1 : ℝ) ≤ (instSize X) := by
    have hpos : 1 ≤ Fintype.card X := Fintype.card_pos_iff.mpr ⟨b⟩
    exact_mod_cast hpos
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hempty : redsBelow color b = ∅ ∧ redsAbove color b = ∅
  · -- No red elements on either side: every record set is empty.
    have e1 : (∑ τ ∈ InjRanks X, ((predRecords color τ b).card : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro τ _
      have hem : predRecords color τ b = ∅ :=
        Finset.eq_empty_of_forall_notMem (fun r hr => by
          have h2 : r ∈ redsBelow color b ∧ IsPredRecord color (fun x => (τ x).val) b r :=
            Finset.mem_filter.mp hr
          rw [hempty.1] at h2
          exact Finset.notMem_empty r h2.1)
      simp [hem]
    have e2 : (∑ τ ∈ InjRanks X, ((succRecords color τ b).card : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro τ _
      have hem : succRecords color τ b = ∅ :=
        Finset.eq_empty_of_forall_notMem (fun r hr => by
          have h2 : r ∈ redsAbove color b ∧ IsSuccRecord color (fun x => (τ x).val) b r :=
            Finset.mem_filter.mp hr
          rw [hempty.2] at h2
          exact Finset.notMem_empty r h2.1)
      simp [hem]
    rw [e1, e2]
    simp only [zero_div, add_zero]
    apply mul_nonneg
    · positivity
    · rw [Real.logb]
      exact div_nonneg (Real.log_nonneg h1) (le_of_lt hc)
  · -- Some red element on a side: the instance has at least 2 elements.
    push_neg at hempty
    obtain ⟨r, hr⟩ : ∃ r, r ∈ redsBelow color b ∨ r ∈ redsAbove color b := by
      cases Finset.eq_empty_or_nonempty (redsBelow color b) with
      | inl hb =>
          have hne : (redsAbove color b).Nonempty := hempty hb
          obtain ⟨r, hr⟩ := hne
          exact ⟨r, Or.inr hr⟩
      | inr hb =>
          obtain ⟨r, hr⟩ := hb
          exact ⟨r, Or.inl hr⟩
    have hne : r ≠ b := by
      cases hr with
      | inl h => rw [mem_redsBelow] at h; exact fun hcon => by rw [hcon] at h; exact lt_irrefl _ h.2
      | inr h => rw [mem_redsAbove] at h; exact fun hcon => by rw [hcon] at h; exact lt_irrefl _ h.2
    have hN2 : (2 : ℝ) ≤ (instSize X) := by
      have h2 : 2 ≤ Fintype.card X :=
        Finset.one_lt_card.mpr ⟨r, Finset.mem_univ r, b, Finset.mem_univ b, hne⟩
      exact_mod_cast h2
    have hlog : ∀ S : Finset X, Real.log S.card ≤ Real.log (instSize X) := by
      intro S
      cases eq_or_ne S.card 0 with
      | inl h0 => simp [h0, Real.log_nonneg h1]
      | inr h0 =>
          apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero h0)
          have hcard : S.card ≤ Fintype.card X :=
            le_trans (Finset.card_le_card (Finset.subset_univ S)) (by simp)
          exact_mod_cast hcard
    have hc1 : Real.log 2 ≤ 1 := by
      have hh : Real.log 2 ≤ Real.log (Real.exp 1) :=
        Real.log_le_log (by norm_num) (by
          have hexp := Real.exp_one_gt_d9
          linarith)
      rwa [Real.log_exp] at hh
    have hL : Real.log 2 ≤ Real.log (instSize X) := Real.log_le_log (by norm_num) hN2
    have hL0 : 0 < Real.log (instSize X) := lt_of_lt_of_le hc hL
    have key : (2 + 2 / Real.log 2) * Real.logb 2 (instSize X)
        = 2 * Real.log (instSize X) / Real.log 2
          + 2 * Real.log (instSize X) / (Real.log 2) ^ 2 := by
      rw [Real.logb]; field_simp <;> ring
    have g1 : 2 * Real.log (instSize X) / Real.log 2 ≥ 2 * Real.log (instSize X) := by
      rw [ge_iff_le, le_div_iff₀ hc]
      nlinarith [hL0, hc1]
    have g2 : 2 * Real.log (instSize X) / (Real.log 2) ^ 2 ≥ 2 := by
      rw [ge_iff_le, le_div_iff₀ (pow_pos hc 2)]
      nlinarith [hc, hc1, hL]
    have hfin : (2 : ℝ) + Real.log (redsBelow color b).card + Real.log (redsAbove color b).card
        ≤ (2 + 2 / Real.log 2) * Real.logb 2 (instSize X) := by
      rw [key]; linarith [hlog (redsBelow color b), hlog (redsAbove color b)]
    have e1 := expected_pred_le color b
    have e2 := expected_succ_le color b
    linarith

end Bichromatic.Randomized
