/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Martingale.Centering
public import Mathlib.Probability.Martingale.OptionalSampling
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Conditional optional stopping for uniformly integrable submartingales

For a uniformly integrable submartingale `f` and stopping times `L ≤ M`
(possibly infinite),
`f_L ≤ᵐ μ[f_M | ℱ_L]`, where `f_τ` is the stopped value at `τ`, with the
a.e. limit `f_∞` used on `{τ = ∞}`. Taking integrals gives the expectation
form `∫ f_L ≤ ∫ f_M`.

## Source

This is target "Theorem (General form of optional stopping)" (Lecture 29)
of `v1/Atlas/TheoryOfProbability/targets.yaml`: "If `L ≤ M` are stopping
times and `Y_{M ∧ n}` is a uniformly integrable submartingale, then
`EY_L ≤ EY_M` and `Y_L ≤ E(Y_M | ℱ_L)`." The v1 file
`GeneralOptionalStopping.lean` only proves the bounded-stopping-time
form and leaves the unbounded form unproved; the bounded form was
ported in an earlier batch, the expectation form for unbounded stopping
times in another, and the conditional form for martingales in a third.
The conditional form for submartingales, proved here, is in none of
them.

## Proof outline

Write `f = M + A` for the Doob decomposition (`martingalePart`,
`predictablePart`). Since `f` is uniformly integrable, so is `A` (it is
dominated by its integrable limit `A_∞`), hence so is the martingale
part `M = f - A`. The martingale part satisfies the conditional
optional-stopping equality by optional sampling at `τ ∧ n` for each
stopping time `τ`, plus Lévy's upward theorem for the stopped filtration
`n ↦ ℱ_{τ ∧ n}` and the tower property. The predictable part satisfies
`A_L ≤ μ[A_M | ℱ_L]` because `A` is monotone and each
`A_{L ∧ n}` is `ℱ_L`-measurable, so conditioning on `ℱ_L` fixes it
while monotonicity bounds the other side. Adding the two parts gives
the result.

## Notes on scope and names

* The stopped value at a possibly infinite stopping time is
  `MeasureTheory.stoppedValueAtInf`, defined below. Earlier batches
  define the same function under the names `stoppedValueAtTop` (two
  batches, identically) and `stoppedValueAtInfinity` (one batch); this
  file uses a distinct name so that rebase does not create a duplicate
  definition. A future unification should keep one of these definitions
  and delete the others.
* The bounded conditional optional stopping theorem, the stopped
  filtration and its exhaustion of `ℱ_τ`, and the martingale
  conditional optional stopping equality are reproduced below as
  `private` lemmas (adapted from the earlier batches that ported them
  publicly, with distinct names where needed). They are private so
  that, on rebase, the public versions from those batches are used and
  the private copies are deleted — only the submartingale theorem and
  its corollary are new public content here.
* The hypothesis here is that the whole process `f` is uniformly
  integrable; the book's weaker hypothesis (only `Y_{M ∧ n}` uniformly
  integrable) is not claimed.

## Main results

* `MeasureTheory.stoppedValueAtInf`: the stopped value at a possibly
  infinite stopping time.
* `MeasureTheory.Submartingale.stoppedValueAtInf_le_condExp_stoppedValueAtInf`:
  `f_L ≤ᵐ μ[f_M | ℱ_L]` for a uniformly integrable submartingale `f`
  and stopping times `L ≤ M`.
* `MeasureTheory.Submartingale.integral_stoppedValueAtInf_mono_of_uniformIntegrable`:
  `∫ f_L ≤ ∫ f_M` under the same hypotheses.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}

/-- The value of a process `f` at a possibly infinite stopping time `τ`:
`f (τ ω) ω` when `τ ω < ∞`, and the limit `limUnder atTop (f · ω)` when
`τ ω = ∞`. This extends `stoppedValue` (which returns `f 0` at `τ = ⊤`)
to allow infinite stopping times. -/
noncomputable def stoppedValueAtInf (f : ℕ → Ω → ℝ) (τ : Ω → WithTop ℕ) : Ω → ℝ :=
  fun ω => if τ ω = ⊤ then limUnder atTop (fun n => f n ω) else stoppedValue f τ ω

/-- Helper lemma: for any extended natural `a : ℕ∞` that is not `⊤`, coercing
`a.untopA : ℕ` back into `ℕ∞` recovers `a`. -/
private lemma coe_untopA_eq (a : ℕ∞) (ha : a ≠ ⊤) : (↑(a.untopA) : ℕ∞) = a := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp ha
  rw [← hn]
  simp only [WithTop.untopA, WithTop.untopD, WithTop.recTopCoe]
  rfl

omit [IsProbabilityMeasure μ] in
/-- If `f n ω → g ω` almost everywhere, then the stopped process
`n ↦ f_{τ ∧ n} ω` converges almost everywhere to the stopped value at
`τ` (with the limit `g ω` used on `{τ = ∞}`). -/
private theorem tendsto_stoppedProcess_to_stoppedValueAtInf {g : Ω → ℝ}
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)))
    {τ : Ω → WithTop ℕ} :
    ∀ᵐ ω ∂μ, Tendsto (fun n => stoppedProcess f τ n ω) atTop
      (𝓝 (stoppedValueAtInf f τ ω)) := by
  filter_upwards [hconv] with ω hω
  by_cases hτtop : τ ω = ⊤
  · have hlim : limUnder atTop (fun n => f n ω) = g ω := hω.limUnder_eq
    have hfun : (fun n => stoppedProcess f τ n ω) = fun n => f n ω := by
      funext n
      show f (min ((n : WithTop ℕ)) (τ ω)).untopA ω = f n ω
      rw [hτtop, min_top_right]
      rfl
    rw [hfun]
    have hval : stoppedValueAtInf f τ ω = g ω := by
      show (if τ ω = ⊤ then limUnder atTop (fun n => f n ω)
        else stoppedValue f τ ω) = g ω
      rw [ite_eq_left hτtop, hlim]
    rw [hval]
    exact hω
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hτtop
    have hval : stoppedValueAtInf f τ ω = f k ω := by
      show (if τ ω = ⊤ then limUnder atTop (fun n => f n ω)
        else stoppedValue f τ ω) = f k ω
      rw [ite_eq_right hτtop]
      show f (τ ω).untopA ω = f k ω
      rw [← hk]
      rfl
    rw [hval]
    refine tendsto_atTop_of_eventually_const (i₀ := k) (fun n hn => ?_)
    have hle : τ ω ≤ ((n : WithTop ℕ)) := by
      rw [← hk]
      exact WithTop.coe_le_coe.mpr hn
    have hsp := stoppedProcess_eq_of_ge (u := f) (τ := τ) (i := n) hle
    rw [hsp, ← hk]
    rfl

/-- **Bounded conditional optional stopping for submartingales**
(private copy). If `f` is a submartingale and `L ≤ M` are stopping
times with `M` bounded above by a finite `N`, then the stopped value
at `L` is almost surely at most the conditional expectation of the
stopped value at `M` given `ℱ_L`. -/
private theorem submartingale_stoppedValue_le_condExp_stoppedValue_bounded
    (hsub : Submartingale f ℱ μ)
    {L M : Ω → ℕ∞}
    (hL : IsStoppingTime ℱ L)
    (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M)
    {N : ℕ} (hbdd : ∀ ω, M ω ≤ N) :
    stoppedValue f L ≤ᵐ[μ] μ[stoppedValue f M | hL.measurableSpace] := by
  have h_sp_sub : Submartingale (stoppedProcess f M) ℱ μ := hsub.stoppedProcess hM
  have hL_bdd : ∀ ω, L ω ≤ N := fun ω => (hLM ω).trans (hbdd ω)
  have hL_ne_top : ∀ ω, L ω ≠ ⊤ := fun ω =>
    ne_top_of_le_ne_top (ne_top_of_le_ne_top (by simp) (hbdd ω)) (hLM ω)
  have h_sp_N : stoppedProcess f M N = stoppedValue f M := by
    funext ω
    exact stoppedProcess_eq_of_ge (hbdd ω)
  have h_key : ∀ᵐ ω ∂μ, ∀ k : ℕ, L ω = ↑k →
      stoppedProcess f M k ω ≤
        (μ[stoppedValue f M | hL.measurableSpace]) ω := by
    rw [ae_all_iff]
    intro k
    by_cases hkN : k ≤ N
    · have h_ineq_k : stoppedProcess f M k ≤ᵐ[μ] μ[stoppedValue f M | ℱ k] := by
        have := h_sp_sub.ae_le_condExp hkN
        rwa [h_sp_N] at this
      have h_ce_restrict :
          μ[stoppedValue f M | hL.measurableSpace]
            =ᵐ[μ.restrict {ω | L ω = ↑k}]
            μ[stoppedValue f M | ℱ k] :=
        condExp_ae_eq_restrict_of_measurableSpace_eq_on
          hL.measurableSpace_le (ℱ.le k) (hL.measurableSet_eq' k)
          (fun t => by rw [Set.inter_comm]; exact hL.measurableSet_inter_eq_iff t k)
      have h_restrict := (ae_restrict_iff'
        (ℱ.le _ _ (hL.measurableSet_eq k))).mp h_ce_restrict
      filter_upwards [h_restrict, h_ineq_k] with ω hω_ce hω_ineq hLk
      calc stoppedProcess f M k ω
          ≤ (μ[stoppedValue f M | ℱ k]) ω := hω_ineq
        _ = (μ[stoppedValue f M | hL.measurableSpace]) ω := (hω_ce hLk).symm
    · have hNk : N < k := Nat.lt_of_not_le hkN
      filter_upwards with ω hLk
      exfalso
      have : L ω ≤ ↑N := hL_bdd ω
      rw [hLk] at this
      exact Nat.not_lt.mpr (mod_cast this) hNk
  filter_upwards [h_key] with ω hω
  have h_sv_eq : stoppedValue f L ω = stoppedProcess f M (L ω).untopA ω := by
    simp only [stoppedValue]
    rw [stoppedProcess_eq_of_le ((coe_untopA_eq _ (hL_ne_top ω)).le.trans (hLM ω))]
  rw [h_sv_eq]
  exact hω _ (coe_untopA_eq _ (hL_ne_top ω)).symm

/-- The filtration `n ↦ ℱ_{τ ∧ n}` obtained by stopping the filtration
at the stopping time `τ` and then at the deterministic time `n`
(private copy; an earlier batch defines the same filtration publicly). -/
private noncomputable def IsStoppingTime.stoppedFiltrationSub (ℱ : Filtration ℕ m0)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) : Filtration ℕ m0 where
  seq n := (hτ.min_const n).measurableSpace
  mono' := by
    intro i j hij
    exact IsStoppingTime.measurableSpace_mono (hτ.min_const i) (hτ.min_const j)
      (fun ω => min_le_min le_rfl (WithTop.coe_le_coe.mpr hij))
  le' n := (hτ.min_const n).measurableSpace_le

/-- The `n`-th level of the stopped filtration is `ℱ_{τ ∧ n}`. -/
private theorem IsStoppingTime.stoppedFiltrationSub_apply (ℱ : Filtration ℕ m0)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) (n : ℕ) :
    (hτ.stoppedFiltrationSub ℱ) n = (hτ.min_const n).measurableSpace :=
  rfl

/-- The set `{τ = ⊤}` is measurable with respect to `⨆ n, ℱ_{τ ∧ n}`. -/
private theorem IsStoppingTime.measurableSet_eq_top_iSup_stoppedFiltrationSub
    (ℱ : Filtration ℕ m0) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) :
    MeasurableSet[⨆ n, (hτ.stoppedFiltrationSub ℱ) n] {ω | τ ω = ⊤} := by
  have hset : {ω : Ω | τ ω = ⊤} = ⋂ (n : ℕ), {ω | ((n : WithTop ℕ)) < τ ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h n
      rw [h]
      exact WithTop.coe_lt_top n
    · intro h
      by_contra hne
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hne
      have := h n
      rw [← hn] at this
      exact absurd this (by simp)
  rw [hset]
  apply MeasurableSet.iInter
  intro n
  have h1 : MeasurableSet[(hτ.min_const n).measurableSpace]
      {ω | ((n : WithTop ℕ)) < τ ω} := by
    have hinf : MeasurableSet[hτ.measurableSpace ⊓ ℱ n]
        {ω | ((n : WithTop ℕ)) < τ ω} :=
      MeasurableSpace.measurableSet_inf.mpr ⟨hτ.measurableSet_gt' n, hτ.measurableSet_gt n⟩
    exact (IsStoppingTime.measurableSpace_min_const hτ).symm ▸ hinf
  exact (le_iSup (fun k => (hτ.stoppedFiltrationSub ℱ) k) n) _ h1

/-- If `t` is measurable with respect to `⨆ n, ℱ n`, then `t ∩ {τ = ⊤}`
is measurable with respect to `⨆ n, ℱ_{τ ∧ n}`. -/
private theorem IsStoppingTime.measurableSet_inter_eq_top_iSup_stoppedFiltrationSub
    (ℱ : Filtration ℕ m0) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ)
    {s : Set Ω} (hs : MeasurableSet[⨆ n, ℱ n] s) :
    MeasurableSet[⨆ n, (hτ.stoppedFiltrationSub ℱ) n] (s ∩ {ω | τ ω = ⊤}) := by
  have htop := hτ.measurableSet_eq_top_iSup_stoppedFiltrationSub ℱ
  have hpi : IsPiSystem {t : Set Ω | ∃ n, MeasurableSet[ℱ n] t} := by
    rw [Set.ofPred_exists]
    exact isPiSystem_iUnion_of_monotone _ (fun n => (ℱ n).isPiSystem_measurableSet)
      (fun _ _ => ℱ.mono)
  induction s, hs using MeasurableSpace.induction_on_inter
    (MeasurableSpace.measurableSpace_iSup_eq ℱ) hpi with
  | empty =>
    simp
  | basic t ht =>
    obtain ⟨n, hn⟩ := ht
    have hBℱ : ∀ m, n ≤ m →
        MeasurableSet[ℱ m]
          ((t ∩ {ω | (m : WithTop ℕ) < τ ω}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)}) := by
      intro m hmn
      exact ((ℱ.mono hmn _ hn).inter (hτ.measurableSet_gt m)).union (hτ.measurableSet_le m)
    have hBτ : ∀ m, n ≤ m →
        MeasurableSet[hτ.measurableSpace]
          ((t ∩ {ω | (m : WithTop ℕ) < τ ω}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)}) := by
      intro m hmn
      rw [hτ.measurableSet]
      refine ⟨(le_iSup (fun k => ℱ k) m) _ (hBℱ m hmn), fun k => ?_⟩
      by_cases hk : k ≤ m
      · have heq : ((t ∩ {ω | (m : WithTop ℕ) < τ ω}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)}) ∩
              {ω | τ ω ≤ (k : WithTop ℕ)} = {ω | τ ω ≤ (k : WithTop ℕ)} := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
          constructor
          · intro h
            obtain ⟨hunion, hle⟩ := h
            rcases hunion with ⟨-, hlt⟩ | hle_m
            · exact absurd (hlt.trans_le hle) (not_lt.mpr (WithTop.coe_le_coe.mpr hk))
            · exact hle
          · intro hle
            exact ⟨Or.inr (hle.trans (WithTop.coe_le_coe.mpr hk)), hle⟩
        exact (congrArg (fun s => MeasurableSet[ℱ k] s) heq).mpr (hτ.measurableSet_le k)
      · have hk' : m < k := Nat.lt_of_not_le hk
        have heq : ((t ∩ {ω | (m : WithTop ℕ) < τ ω}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)}) ∩
                {ω | τ ω ≤ (k : WithTop ℕ)}
            = (t ∩ {ω | (m : WithTop ℕ) < τ ω ∧ τ ω ≤ (k : WithTop ℕ)}) ∪
              {ω | τ ω ≤ (m : WithTop ℕ)} := by
          ext ω
          simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_ofPred_eq]
          constructor
          · intro h
            obtain ⟨hunion, hle⟩ := h
            rcases hunion with ⟨htω, hlt⟩ | hle_m
            · exact Or.inl ⟨htω, hlt, hle⟩
            · exact Or.inr hle_m
          · intro h
            rcases h with ⟨htω, hlt, hle⟩ | hle_m
            · exact ⟨Or.inl ⟨htω, hlt⟩, hle⟩
            · exact ⟨Or.inr hle_m, hle_m.trans (WithTop.coe_le_coe.mpr (Nat.le_of_lt hk'))⟩
        refine (congrArg (fun s => MeasurableSet[ℱ k] s) heq).mpr ?_
        apply MeasurableSet.union
        · apply MeasurableSet.inter
          · exact ℱ.mono (hmn.trans (Nat.le_of_lt hk')) _ hn
          · exact ((ℱ.mono (Nat.le_of_lt hk') _ (hτ.measurableSet_gt m)).inter
              (hτ.measurableSet_le k))
        · exact ℱ.mono (Nat.le_of_lt hk') _ (hτ.measurableSet_le m)
    have hBmem : ∀ m, n ≤ m →
        MeasurableSet[⨆ k, (hτ.stoppedFiltrationSub ℱ) k]
          ((t ∩ {ω | (m : WithTop ℕ) < τ ω}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)}) := by
      intro m hmn
      have h1 : MeasurableSet[(hτ.min_const m).measurableSpace]
          ((t ∩ {ω | (m : WithTop ℕ) < τ ω}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)}) := by
        have hinf : MeasurableSet[hτ.measurableSpace ⊓ ℱ m]
            ((t ∩ {ω | (m : WithTop ℕ) < τ ω}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)}) :=
          MeasurableSpace.measurableSet_inf.mpr ⟨hBτ m hmn, hBℱ m hmn⟩
        exact (IsStoppingTime.measurableSpace_min_const hτ).symm ▸ hinf
      exact (le_iSup (fun k => (hτ.stoppedFiltrationSub ℱ) k) m) _ h1
    have hInter : (⋂ m ∈ Set.Ici n,
            ((t ∩ {ω | (m : WithTop ℕ) < τ ω}) ∪ {ω | τ ω ≤ (m : WithTop ℕ)})) ∩
          {ω | τ ω = ⊤}
        = t ∩ {ω | τ ω = ⊤} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_Ici, Set.mem_union,
        Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hω, htopω⟩
        have hmem := hω n le_rfl
        rcases hmem with ⟨htω, -⟩ | hle
        · exact ⟨htω, htopω⟩
        · rw [htopω] at hle
          exact absurd hle (by simp)
      · rintro ⟨htω, htopω⟩
        refine ⟨fun m _ => Or.inl ⟨htω, ?_⟩, htopω⟩
        rw [htopω]
        exact WithTop.coe_lt_top m
    rw [← hInter]
    exact MeasurableSet.inter
      (MeasurableSet.iInter fun m => MeasurableSet.iInter fun (_ : n ≤ m) => hBmem m ‹n ≤ m›)
      htop
  | compl t _ iht =>
    have : tᶜ ∩ {ω | τ ω = ⊤} = {ω | τ ω = ⊤} \ (t ∩ {ω | τ ω = ⊤}) := by
      ext ω
      simp [Set.mem_sdiff, and_comm]
    rw [this]
    exact htop.diff iht
  | iUnion f _ _ ih =>
    have : (⋃ i, f i) ∩ {ω | τ ω = ⊤} = ⋃ i, (f i ∩ {ω | τ ω = ⊤}) := by
      rw [Set.iUnion_inter]
    rw [this]
    exact MeasurableSet.iUnion ih

/-- The stopped filtration exhausts the stopping-time σ-algebra:
`⨆ n, ℱ_{τ ∧ n} = ℱ_τ`. -/
private theorem IsStoppingTime.iSup_stoppedFiltrationSub (ℱ : Filtration ℕ m0)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) :
    ⨆ n, (hτ.stoppedFiltrationSub ℱ) n = hτ.measurableSpace := by
  apply le_antisymm
  · apply iSup_le
    intro n
    show (hτ.min_const n).measurableSpace ≤ hτ.measurableSpace
    exact IsStoppingTime.measurableSpace_mono (hτ.min_const n) hτ
      (fun ω => min_le_left _ _)
  · intro s hs
    have hs_split := (hτ.measurableSet s).mp hs
    have htop_part := hτ.measurableSet_inter_eq_top_iSup_stoppedFiltrationSub ℱ hs_split.1
    have hlt_part : MeasurableSet[⨆ n, (hτ.stoppedFiltrationSub ℱ) n]
        (s ∩ {ω | τ ω < ⊤}) := by
      have hset : s ∩ {ω | τ ω < ⊤} = ⋃ (n : ℕ), (s ∩ {ω | τ ω ≤ ((n : WithTop ℕ))}) := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hsω, hlt⟩
          obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hlt)
          exact ⟨k, hsω, le_of_eq hk.symm⟩
        · rintro ⟨n, hsω, hle⟩
          exact ⟨hsω, lt_of_le_of_lt hle (WithTop.coe_lt_top n)⟩
      rw [hset]
      apply MeasurableSet.iUnion
      intro n
      have hinf : MeasurableSet[hτ.measurableSpace ⊓ ℱ n]
          (s ∩ {ω | τ ω ≤ ((n : WithTop ℕ))}) :=
        MeasurableSpace.measurableSet_inf.mpr
          ⟨hs.inter (hτ.measurableSet_le' n), hs_split.2 n⟩
      have hmin : MeasurableSet[(hτ.min_const n).measurableSpace]
          (s ∩ {ω | τ ω ≤ ((n : WithTop ℕ))}) :=
        (IsStoppingTime.measurableSpace_min_const hτ).symm ▸ hinf
      exact (le_iSup (fun k => (hτ.stoppedFiltrationSub ℱ) k) n) _ hmin
    have hsplit : s = (s ∩ {ω | τ ω = ⊤}) ∪ (s ∩ {ω | τ ω < ⊤}) := by
      ext ω
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro hsω
        rcases lt_or_eq_of_le (le_top : τ ω ≤ ⊤) with hlt | heqτ
        · exact Or.inr ⟨hsω, hlt⟩
        · exact Or.inl ⟨hsω, heqτ⟩
      · rintro (⟨hsω, -⟩ | ⟨hsω, -⟩)
        · exact hsω
        · exact hsω
    exact (congrArg
      (fun t => MeasurableSet[⨆ n, (hτ.stoppedFiltrationSub ℱ) n] t) hsplit).mpr
      (MeasurableSet.union htop_part hlt_part)

/-- **Stopped value as conditional expectation of the limit**
(private copy). For a uniformly integrable martingale `f` and any
stopping time `τ`, `f_τ =ᵐ μ[ℱ.limitProcess f μ | ℱ_τ]`. The stopped
process `n ↦ f_{τ ∧ n}` equals `μ[ℱ.limitProcess f μ | ℱ_{τ ∧ n}]` a.e.
by bounded optional sampling, and Lévy's upward theorem for the
filtration `n ↦ ℱ_{τ ∧ n}` identifies the a.e. limit of those
conditional expectations with
`μ[ℱ.limitProcess f μ | ⨆ n, ℱ_{τ ∧ n}] = μ[ℱ.limitProcess f μ | ℱ_τ]`. -/
private theorem martingale_stoppedValueAtInf_ae_eq_condExp_limitProcess
    (hf : Martingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) :
    stoppedValueAtInf f τ =ᵐ[μ] μ[ℱ.limitProcess f μ | hτ.measurableSpace] := by
  have : SigmaFiniteFiltration μ (hτ.stoppedFiltrationSub ℱ) :=
    ⟨fun n => IsStoppingTime.sigmaFinite_stopping_time (hτ.min_const n)⟩
  -- Bounded optional sampling at `τ ∧ n`.
  have hstep : ∀ n, stoppedProcess f τ n
      =ᵐ[μ] μ[ℱ.limitProcess f μ | (hτ.stoppedFiltrationSub ℱ) n] := by
    intro n
    have hpoint : stoppedProcess f τ n
        = stoppedValue f (fun ω => min (τ ω) ((n : WithTop ℕ))) := by
      funext ω
      exact (congrArg (fun a => f a ω)
        (congrArg WithTop.untopA (min_comm (τ ω) ((n : WithTop ℕ))))).symm
    calc stoppedProcess f τ n
        = stoppedValue f (fun ω => min (τ ω) ((n : WithTop ℕ))) := hpoint
      _ =ᵐ[μ] μ[f n | (hτ.stoppedFiltrationSub ℱ) n] :=
          hf.stoppedValue_ae_eq_condExp_of_le_const (hτ.min_const n)
            (fun ω => min_le_right _ _)
      _ =ᵐ[μ] μ[μ[ℱ.limitProcess f μ | ℱ n] | (hτ.stoppedFiltrationSub ℱ) n] :=
          condExp_congr_ae (hf.ae_eq_condExp_limitProcess hui n)
      _ =ᵐ[μ] μ[ℱ.limitProcess f μ | (hτ.stoppedFiltrationSub ℱ) n] :=
          condExp_condExp_of_le (by
            show (hτ.min_const n).measurableSpace ≤ ℱ n
            exact (hτ.min_const n).measurableSpace_le_of_le_const
              (fun ω => min_le_right _ _))
            (ℱ.le n)
  -- The stopped process converges a.e. to the stopped value at `τ`.
  have hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => stoppedProcess f τ n ω) atTop
      (𝓝 (stoppedValueAtInf f τ ω)) :=
    tendsto_stoppedProcess_to_stoppedValueAtInf
      (hf.submartingale.ae_tendsto_limitProcess_of_uniformIntegrable hui)
  have hstep_all : ∀ᵐ ω ∂μ, ∀ n,
      stoppedProcess f τ n ω = (μ[ℱ.limitProcess f μ | (hτ.stoppedFiltrationSub ℱ) n]) ω :=
    ae_all_iff.mpr hstep
  have hlevy : ∀ᵐ ω ∂μ, Tendsto
      (fun n => (μ[ℱ.limitProcess f μ | (hτ.stoppedFiltrationSub ℱ) n]) ω) atTop
      (𝓝 ((μ[ℱ.limitProcess f μ | ⨆ n, (hτ.stoppedFiltrationSub ℱ) n]) ω)) :=
    tendsto_ae_condExp (ℱ := hτ.stoppedFiltrationSub ℱ) (ℱ.limitProcess f μ)
  filter_upwards [hconv, hlevy, hstep_all] with ω hω hlevyω hstepω
  have hlim1 : Tendsto
      (fun n => (μ[ℱ.limitProcess f μ | (hτ.stoppedFiltrationSub ℱ) n]) ω) atTop
      (𝓝 (stoppedValueAtInf f τ ω)) :=
    hω.congr (fun n => hstepω n)
  have hfinal : stoppedValueAtInf f τ ω
      = (μ[ℱ.limitProcess f μ | ⨆ n, (hτ.stoppedFiltrationSub ℱ) n]) ω :=
    tendsto_nhds_unique hlim1 hlevyω
  rwa [hτ.iSup_stoppedFiltrationSub ℱ] at hfinal

/-- **Conditional optional stopping for uniformly integrable
martingales** (private copy). For stopping times `L ≤ M` (possibly
infinite), `f_L =ᵐ μ[f_M | ℱ_L]`. -/
private theorem martingale_stoppedValueAtInf_ae_eq_condExp_stoppedValueAtInf
    (hf : Martingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    {L M : Ω → WithTop ℕ} (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    stoppedValueAtInf f L
      =ᵐ[μ] μ[stoppedValueAtInf f M | hL.measurableSpace] := by
  have hL_eq := martingale_stoppedValueAtInf_ae_eq_condExp_limitProcess hf hui hL
  have hM_eq := martingale_stoppedValueAtInf_ae_eq_condExp_limitProcess hf hui hM
  exact (hL_eq.trans
    (condExp_condExp_of_le (IsStoppingTime.measurableSpace_mono hL hM hLM)
      hM.measurableSpace_le).symm).trans (condExp_congr_ae hM_eq).symm


/-- A sum of two finite `ℝ≥0∞` numbers is finite. -/
private theorem ennreal_add_ne_top {a b : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    a + b ≠ ⊤ := by
  rw [ne_eq, ENNReal.add_eq_top]
  exact fun h => h.elim ha hb

omit [IsProbabilityMeasure μ] in
/-- Each term of the predictable part of a process is integrable. -/
private theorem integrable_predictablePart (_hsub : Submartingale f ℱ μ) (n : ℕ) :
    Integrable (predictablePart f ℱ μ n) μ := by
  have hEq : predictablePart f ℱ μ n =
      fun ω => ∑ i ∈ Finset.range n, μ[f (i + 1) - f i | ℱ i] ω := by
    funext ω
    simp [predictablePart, Finset.sum_apply]
  rw [hEq]
  exact integrable_finsetSum _ (fun i _ => integrable_condExp)

/-- The predictable part of a submartingale is itself a submartingale:
its increments are the conditional expectations of the increments of
`f`, which are a.e. nonnegative, and the tower property turns
`μ[∑_{k ∈ [i,j)} μ[Δf_k | ℱ_k] | ℱ_i]` back into a sum of
`μ[Δf_k | ℱ_i] ≥ 0`. -/
private theorem submartingale_predictablePart (hsub : Submartingale f ℱ μ) :
    Submartingale (predictablePart f ℱ μ) ℱ μ := by
  apply submartingale_of_condExp_sub_nonneg stronglyAdapted_predictablePart'
    (integrable_predictablePart hsub)
  intro i j hij
  have hdiff : (predictablePart f ℱ μ j - predictablePart f ℱ μ i) =
      ∑ k ∈ Finset.Ico i j, μ[f (k + 1) - f k | ℱ k] := by
    simp only [predictablePart]
    rw [Finset.sum_Ico_eq_sub (fun k => μ[f (k + 1) - f k | ℱ k]) hij]
  rw [hdiff]
  have hcond : μ[∑ k ∈ Finset.Ico i j, μ[f (k + 1) - f k | ℱ k] | ℱ i] =ᵐ[μ]
      ∑ k ∈ Finset.Ico i j, μ[f (k + 1) - f k | ℱ i] :=
    condExp_finsetSum (s := Finset.Ico i j) (f := fun k => μ[f (k + 1) - f k | ℱ k])
      (fun k _ => integrable_condExp) (ℱ i) |>.trans
        (eventuallyEq_sum fun k hk => condExp_condExp_of_le
          (ℱ.mono (Finset.mem_Ico.mp hk).1) (ℱ.le k))
  have hnonneg : ∀ᵐ ω ∂μ, ∀ k, k ∈ Finset.Ico i j →
      0 ≤ μ[f (k + 1) - f k | ℱ i] ω := by
    rw [ae_all_iff]
    intro k
    by_cases hk : k ∈ Finset.Ico i j
    · have h1 : (0 : Ω → ℝ) ≤ᵐ[μ] μ[f (k + 1) - f k | ℱ k] :=
        hsub.condExp_sub_nonneg (Nat.le_succ k)
      have h2 : μ[(0 : Ω → ℝ) | ℱ i] ≤ᵐ[μ] μ[μ[f (k + 1) - f k | ℱ k] | ℱ i] :=
        condExp_mono (integrable_const (0 : ℝ)) integrable_condExp h1
      rw [condExp_zero] at h2
      have h3 := h2.trans (condExp_condExp_of_le
        (ℱ.mono (Finset.mem_Ico.mp hk).1) (ℱ.le k)).le
      filter_upwards [h3] with ω hω hkmem
      exact hω
    · filter_upwards with ω
      intro hkmem
      exact absurd hkmem hk
  filter_upwards [hcond, hnonneg] with ω hω hωnonneg
  rw [hω, Finset.sum_apply]
  exact Finset.sum_nonneg (fun k hk => hωnonneg k hk)

/-- The integral of the predictable part telescopes:
`∫ A n = ∫ f n - ∫ f 0`, since the martingale part has constant
expectation. -/
private theorem integral_predictablePart (hsub : Submartingale f ℱ μ) (n : ℕ) :
    ∫ ω, predictablePart f ℱ μ n ω ∂μ = ∫ ω, f n ω ∂μ - ∫ ω, f 0 ω ∂μ := by
  have hMt : Martingale (martingalePart f ℱ μ) ℱ μ :=
    martingale_martingalePart hsub.stronglyAdapted (fun k => hsub.integrable k)
  have hMt_int : ∫ ω, martingalePart f ℱ μ n ω ∂μ = ∫ ω, f 0 ω ∂μ := by
    simpa [setIntegral_univ] using
      (hMt.setIntegral_eq (Nat.zero_le n) (s := Set.univ) MeasurableSet.univ).symm
  have hdecomp : martingalePart f ℱ μ n + predictablePart f ℱ μ n = f n :=
    congrFun (martingalePart_add_predictablePart ℱ μ f) n
  have h1 : ∫ ω, (martingalePart f ℱ μ n ω + predictablePart f ℱ μ n ω) ∂μ
      = ∫ ω, f n ω ∂μ := by
    rw [← hdecomp]
    rfl
  rw [integral_add (integrable_martingalePart (fun k => hsub.integrable k) n)
    (integrable_predictablePart hsub n)] at h1
  linarith [h1, hMt_int]

/-- The `L¹` norm of the predictable part is bounded by the uniform
integrability bound of `f` plus `|∫ f 0|`. -/
private theorem eLpNorm_predictablePart_le (hsub : Submartingale f ℱ μ)
    {R : ℝ≥0} (hR : ∀ n, eLpNorm (f n) 1 μ ≤ (R : ℝ≥0∞)) (n : ℕ) :
    eLpNorm (predictablePart f ℱ μ n) 1 μ ≤
      (R : ℝ≥0∞) + ENNReal.ofReal |∫ ω, f 0 ω ∂μ| := by
  have hA_nonneg : ∀ᵐ ω ∂μ, 0 ≤ predictablePart f ℱ μ n ω := by
    filter_upwards [hsub.predictablePart_nonneg] with ω hω
    exact hω n
  have hA_sm : AEStronglyMeasurable (predictablePart f ℱ μ n) μ :=
    (integrable_predictablePart hsub n).aestronglyMeasurable
  have heq : eLpNorm (predictablePart f ℱ μ n) 1 μ
      = ENNReal.ofReal (∫ ω, predictablePart f ℱ μ n ω ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm hA_sm,
      ofReal_integral_eq_lintegral_ofReal (integrable_predictablePart hsub n) hA_nonneg]
    refine lintegral_congr_ae ?_
    filter_upwards [hA_nonneg] with ω hω
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hω]
  rw [heq, integral_predictablePart hsub n]
  calc ENNReal.ofReal (∫ ω, f n ω ∂μ - ∫ ω, f 0 ω ∂μ)
      ≤ ENNReal.ofReal (∫ ω, |f n ω| ∂μ + |∫ ω, f 0 ω ∂μ|) := by
        apply ENNReal.ofReal_le_ofReal
        have h1 : ∫ ω, f n ω ∂μ - ∫ ω, f 0 ω ∂μ
            ≤ |∫ ω, f n ω ∂μ| + |∫ ω, f 0 ω ∂μ| := by
          have h1a : ∫ ω, f n ω ∂μ ≤ |∫ ω, f n ω ∂μ| := le_abs_self _
          have h1b : -∫ ω, f 0 ω ∂μ ≤ |∫ ω, f 0 ω ∂μ| := neg_le_abs _
          linarith
        refine h1.trans ?_
        have h2 : |∫ ω, f n ω ∂μ| ≤ ∫ ω, |f n ω| ∂μ :=
          abs_integral_le_integral_abs
        linarith
    _ = ENNReal.ofReal (∫ ω, |f n ω| ∂μ) + ENNReal.ofReal |∫ ω, f 0 ω ∂μ| := by
        rw [ENNReal.ofReal_add (integral_nonneg (fun ω => abs_nonneg _)) (abs_nonneg _)]
    _ ≤ (R : ℝ≥0∞) + ENNReal.ofReal |∫ ω, f 0 ω ∂μ| := by
        apply add_le_add _ le_rfl
        have hfn : ENNReal.ofReal (∫ ω, |f n ω| ∂μ) = eLpNorm (f n) 1 μ := by
          rw [ofReal_integral_eq_lintegral_ofReal (hsub.integrable n).abs
              (Filter.Eventually.of_forall fun ω => abs_nonneg _),
            eLpNorm_one_eq_lintegral_enorm (hsub.integrable n).aestronglyMeasurable]
          refine lintegral_congr_ae ?_
          filter_upwards with ω
          simp [Real.enorm_eq_ofReal_abs]
        rw [hfn]
        exact hR n

/-- A uniform `L¹` bound for the predictable part, in the `ℝ≥0`-coerced
form that `Submartingale.memLp_limitProcess` and
`Submartingale.ae_tendsto_limitProcess` expect. -/
private theorem eLpNorm_predictablePart_le_nnreal (hsub : Submartingale f ℱ μ)
    {R : ℝ≥0} (hR : ∀ n, eLpNorm (f n) 1 μ ≤ (R : ℝ≥0∞)) (n : ℕ) :
    eLpNorm (predictablePart f ℱ μ n) 1 μ ≤
      (((R : ℝ≥0∞) + ENNReal.ofReal |∫ ω, f 0 ω ∂μ|).toNNReal : ℝ≥0∞) := by
  rw [ENNReal.coe_toNNReal
    (ennreal_add_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)]
  exact eLpNorm_predictablePart_le hsub hR n

/-- The limit of the predictable part is integrable: its `L¹` norms are
uniformly bounded, so `Submartingale.memLp_limitProcess` applies. -/
private theorem integrable_limitProcess_predictablePart (hsub : Submartingale f ℱ μ)
    (hui : UniformIntegrable f 1 μ) :
    Integrable (ℱ.limitProcess (predictablePart f ℱ μ) μ) μ := by
  obtain ⟨R, hR⟩ := hui.2
  exact ((submartingale_predictablePart hsub).memLp_limitProcess
    (fun n => eLpNorm_predictablePart_le_nnreal hsub hR n)).integrable le_rfl

/-- The predictable part of a uniformly integrable submartingale is
uniformly integrable: it is dominated by its integrable limit. -/
private theorem uniformIntegrable_predictablePart (hsub : Submartingale f ℱ μ)
    (hui : UniformIntegrable f 1 μ) :
    UniformIntegrable (predictablePart f ℱ μ) 1 μ := by
  obtain ⟨R, hR⟩ := hui.2
  set A := predictablePart f ℱ μ
  set Alim := ℱ.limitProcess A μ
  have hAlim_int : Integrable Alim μ := integrable_limitProcess_predictablePart hsub hui
  have hAlim_memLp : MemLp Alim 1 μ := memLp_one_iff_integrable.2 hAlim_int
  have hUI_const : UniformIntegrable (fun _ : ℕ => Alim) 1 μ :=
    uniformIntegrable_const le_rfl ENNReal.one_ne_top hAlim_memLp
  have hle : ∀ n, (‖A n ·‖ₑ) ≤ᵐ[μ] (‖Alim ·‖ₑ) := by
    intro n
    have hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => A n ω) atTop (𝓝 (Alim ω)) :=
      (submartingale_predictablePart hsub).ae_tendsto_limitProcess
        (fun m => eLpNorm_predictablePart_le_nnreal hsub hR m)
    have hmono : ∀ᵐ ω ∂μ, Monotone (fun n => A n ω) :=
      hsub.monotone_predictablePart
    filter_upwards [hconv, hmono, hsub.predictablePart_nonneg] with ω hω hmonoω hnnω
    have hleω : A n ω ≤ Alim ω := hmonoω.ge_of_tendsto hω n
    have hnn : 0 ≤ A n ω := hnnω n
    rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg hnn, abs_of_nonneg (le_trans hnn hleω)]
    exact ENNReal.ofReal_le_ofReal hleω
  refine ⟨(hUI_const.1).ae_mono (fun n => (integrable_predictablePart hsub n).aestronglyMeasurable)
    hle, ?_⟩
  refine ⟨((R : ℝ≥0∞) + ENNReal.ofReal |∫ ω, f 0 ω ∂μ|).toNNReal, fun n => ?_⟩
  rw [ENNReal.coe_toNNReal
    (ennreal_add_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top)]
  exact eLpNorm_predictablePart_le hsub hR n

/-- The martingale part of a uniformly integrable submartingale is a
uniformly integrable martingale. -/
private theorem uniformIntegrable_martingalePart (hsub : Submartingale f ℱ μ)
    (hui : UniformIntegrable f 1 μ) :
    Martingale (martingalePart f ℱ μ) ℱ μ ∧
      UniformIntegrable (martingalePart f ℱ μ) 1 μ := by
  obtain ⟨R, hR⟩ := hui.2
  set A := predictablePart f ℱ μ
  set Mt := martingalePart f ℱ μ
  have hMt_mart : Martingale Mt ℱ μ :=
    martingale_martingalePart hsub.stronglyAdapted (fun k => hsub.integrable k)
  have hA_UI := uniformIntegrable_predictablePart hsub hui
  have hMt_UI : UniformIntegrable Mt 1 μ := by
    have hMt_eq : Mt = f - A := by
      funext n ω
      simp [Mt, A, martingalePart]
    rw [hMt_eq]
    refine ⟨(hui.1).sub (hA_UI.1) le_rfl, ?_⟩
    refine ⟨((R : ℝ≥0∞) + ((R : ℝ≥0∞) + ENNReal.ofReal |∫ ω, f 0 ω ∂μ|)).toNNReal,
      fun n => ?_⟩
    rw [ENNReal.coe_toNNReal (ennreal_add_ne_top ENNReal.coe_ne_top
      (ennreal_add_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top))]
    have hsub_le : eLpNorm ((f - A) n) 1 μ ≤ eLpNorm (f n) 1 μ + eLpNorm (A n) 1 μ := by
      have hEq : (f - A) n = f n + (-A n) := by
        simp only [Pi.sub_apply, sub_eq_add_neg]
      rw [hEq]
      calc eLpNorm (f n + (-A n)) 1 μ
          ≤ eLpNorm (f n) 1 μ + eLpNorm (-A n) 1 μ := eLpNorm_add_le le_rfl
        _ = eLpNorm (f n) 1 μ + eLpNorm (A n) 1 μ := by rw [eLpNorm_neg]
    exact (hsub_le.trans (add_le_add (hR n) (eLpNorm_predictablePart_le hsub hR n)))
  exact ⟨hMt_mart, hMt_UI⟩

omit [IsProbabilityMeasure μ] in
/-- Stopped values split over sums, when both summands converge
almost everywhere. -/
private theorem stoppedValueAtInf_add {g h : ℕ → Ω → ℝ} {G H : Ω → ℝ}
    (hg : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 (G ω)))
    (hh : ∀ᵐ ω ∂μ, Tendsto (fun n => h n ω) atTop (𝓝 (H ω)))
    {τ : Ω → WithTop ℕ} :
    stoppedValueAtInf (g + h) τ =ᵐ[μ] stoppedValueAtInf g τ + stoppedValueAtInf h τ := by
  filter_upwards [hg, hh] with ω hωg hωh
  by_cases hτtop : τ ω = ⊤
  · show (if τ ω = ⊤ then limUnder atTop (fun n => (g + h) n ω)
        else stoppedValue (g + h) τ ω)
      = (if τ ω = ⊤ then limUnder atTop (fun n => g n ω) else stoppedValue g τ ω) +
        (if τ ω = ⊤ then limUnder atTop (fun n => h n ω) else stoppedValue h τ ω)
    simp only [ite_eq_left hτtop]
    have hadd : Tendsto (fun n => (g + h) n ω) atTop (𝓝 (G ω + H ω)) :=
      hωg.add hωh
    rw [hadd.limUnder_eq, hωg.limUnder_eq, hωh.limUnder_eq]
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hτtop
    show (if τ ω = ⊤ then limUnder atTop (fun n => (g + h) n ω)
        else stoppedValue (g + h) τ ω)
      = (if τ ω = ⊤ then limUnder atTop (fun n => g n ω) else stoppedValue g τ ω) +
        (if τ ω = ⊤ then limUnder atTop (fun n => h n ω) else stoppedValue h τ ω)
    simp only [ite_eq_right hτtop]
    have htop : (τ ω).untopA = k := by
      have h := coe_untopA_eq (τ ω) hτtop
      exact WithTop.coe_inj.mp (h.trans hk.symm)
    show (g + h) (τ ω).untopA ω = g (τ ω).untopA ω + h (τ ω).untopA ω
    simp only [htop, Pi.add_apply]

/-- The stopped value of `f` at any stopping time splits over the Doob
decomposition. -/
private theorem stoppedValueAtInf_decomp (hsub : Submartingale f ℱ μ)
    (hui : UniformIntegrable f 1 μ) {τ : Ω → WithTop ℕ} :
    stoppedValueAtInf f τ =ᵐ[μ] stoppedValueAtInf (martingalePart f ℱ μ) τ +
      stoppedValueAtInf (predictablePart f ℱ μ) τ := by
  obtain ⟨R, hR⟩ := hui.2
  obtain ⟨hMt_mart, hMt_UI⟩ := uniformIntegrable_martingalePart hsub hui
  have hMt_conv : ∀ᵐ ω ∂μ, Tendsto (fun n => martingalePart f ℱ μ n ω) atTop
      (𝓝 (ℱ.limitProcess (martingalePart f ℱ μ) μ ω)) :=
    hMt_mart.submartingale.ae_tendsto_limitProcess_of_uniformIntegrable hMt_UI
  have hA_conv : ∀ᵐ ω ∂μ, Tendsto (fun n => predictablePart f ℱ μ n ω) atTop
      (𝓝 (ℱ.limitProcess (predictablePart f ℱ μ) μ ω)) :=
    (submartingale_predictablePart hsub).ae_tendsto_limitProcess
      (fun m => eLpNorm_predictablePart_le_nnreal hsub hR m)
  have h := stoppedValueAtInf_add hMt_conv hA_conv (τ := τ)
  rwa [martingalePart_add_predictablePart ℱ μ f] at h

/-- The stopped value of the predictable part at any stopping time is
integrable: it is dominated by its integrable limit. -/
private theorem integrable_stoppedValueAtInf_predictablePart (hsub : Submartingale f ℱ μ)
    (hui : UniformIntegrable f 1 μ) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) :
    Integrable (stoppedValueAtInf (predictablePart f ℱ μ) τ) μ := by
  obtain ⟨R, hR⟩ := hui.2
  set A := predictablePart f ℱ μ
  set Alim := ℱ.limitProcess A μ
  have hAlim_int : Integrable Alim μ := integrable_limitProcess_predictablePart hsub hui
  have hA_sub : Submartingale A ℱ μ := submartingale_predictablePart hsub
  have hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => A n ω) atTop (𝓝 (Alim ω)) :=
    hA_sub.ae_tendsto_limitProcess (fun m => eLpNorm_predictablePart_le_nnreal hsub hR m)
  have hstop_conv : ∀ᵐ ω ∂μ, Tendsto (fun n => stoppedProcess A τ n ω) atTop
      (𝓝 (stoppedValueAtInf A τ ω)) :=
    tendsto_stoppedProcess_to_stoppedValueAtInf hconv
  have hle : ∀ᵐ ω ∂μ, ‖stoppedValueAtInf A τ ω‖ ≤ ‖Alim ω‖ := by
    filter_upwards [hconv, hstop_conv, hsub.monotone_predictablePart,
      hsub.predictablePart_nonneg] with ω hω hstopω hmonoω hnnω
    have hnn' : 0 ≤ stoppedValueAtInf A τ ω :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hstopω
        (Filter.Eventually.of_forall fun n => by
          show 0 ≤ A (min (n : WithTop ℕ) (τ ω)).untopA ω
          exact hnnω _)
    have hle' : stoppedValueAtInf A τ ω ≤ Alim ω :=
      le_of_tendsto_of_tendsto hstopω tendsto_const_nhds
        (Filter.Eventually.of_forall fun n => by
          show A (min (n : WithTop ℕ) (τ ω)).untopA ω ≤ Alim ω
          exact hmonoω.ge_of_tendsto hω _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn', Real.norm_eq_abs,
      abs_of_nonneg (le_trans hnn' hle')]
    exact hle'
  have hsm : AEStronglyMeasurable (stoppedValueAtInf A τ) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (stronglyAdapted_predictablePart'.stronglyMeasurable_stoppedProcess_of_discrete
        hτ n).aestronglyMeasurable)
      hstop_conv
  exact (hAlim_int.norm).mono' hsm hle

/-- The stopped value of the martingale part at any stopping time is
integrable: it is a.e. equal to a conditional expectation. -/
private theorem integrable_stoppedValueAtInf_martingalePart (hsub : Submartingale f ℱ μ)
    (hui : UniformIntegrable f 1 μ) {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime ℱ τ) :
    Integrable (stoppedValueAtInf (martingalePart f ℱ μ) τ) μ := by
  obtain ⟨hMt_mart, hMt_UI⟩ := uniformIntegrable_martingalePart hsub hui
  have hEq := martingale_stoppedValueAtInf_ae_eq_condExp_limitProcess hMt_mart hMt_UI hτ
  exact integrable_condExp.congr hEq.symm

/-- The predictable part satisfies the conditional optional stopping
inequality: `A_L ≤ᵐ μ[A_M | ℱ_L]`. The proof works with the stopped
process `n ↦ A_{L ∧ n}`, each term of which is `ℱ_L`-measurable, and
passes to the limit. -/
private theorem predictablePart_stoppedValueAtInf_le_condExp (hsub : Submartingale f ℱ μ)
    (hui : UniformIntegrable f 1 μ)
    {L M : Ω → WithTop ℕ} (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    stoppedValueAtInf (predictablePart f ℱ μ) L ≤ᵐ[μ]
      μ[stoppedValueAtInf (predictablePart f ℱ μ) M | hL.measurableSpace] := by
  obtain ⟨R, hR⟩ := hui.2
  set A := predictablePart f ℱ μ
  set Alim := ℱ.limitProcess A μ
  have hAlim_int : Integrable Alim μ := integrable_limitProcess_predictablePart hsub hui
  have hA_sub : Submartingale A ℱ μ := submartingale_predictablePart hsub
  have hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => A n ω) atTop (𝓝 (Alim ω)) :=
    hA_sub.ae_tendsto_limitProcess (fun m => eLpNorm_predictablePart_le_nnreal hsub hR m)
  have hgood : ∀ᵐ ω ∂μ, Monotone (fun n => A n ω) ∧ (∀ n, 0 ≤ A n ω) ∧
      Tendsto (fun n => A n ω) atTop (𝓝 (Alim ω)) := by
    filter_upwards [hsub.monotone_predictablePart, hsub.predictablePart_nonneg, hconv]
      with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  -- Pointwise bounds on the good set.
  have hbound : ∀ᵐ ω ∂μ, ∀ n, stoppedProcess A L n ω ≤ stoppedProcess A M n ω ∧
      stoppedProcess A M n ω ≤ stoppedValueAtInf A M ω ∧
      stoppedProcess A L n ω ≤ Alim ω ∧
      stoppedValueAtInf A M ω ≤ Alim ω := by
    filter_upwards [hgood] with ω ⟨hmonoω, hnnω, hlimω⟩ n
    have hleAlim : ∀ m, A m ω ≤ Alim ω := fun m => hmonoω.ge_of_tendsto hlimω m
    have hub : (min (↑n : WithTop ℕ) (L ω)).untopA ≤
        (min (↑n : WithTop ℕ) (M ω)).untopA :=
      WithTop.untopA_mono
        (ne_top_of_le_ne_top (by simp) (min_le_left _ _))
        (min_le_min le_rfl (hLM ω))
    have hLM_le : stoppedProcess A L n ω ≤ stoppedProcess A M n ω := by
      show A (min (↑n : WithTop ℕ) (L ω)).untopA ω ≤
        A (min (↑n : WithTop ℕ) (M ω)).untopA ω
      exact hmonoω hub
    have hM_n_le : stoppedProcess A M n ω ≤ stoppedValueAtInf A M ω := by
      by_cases htop : M ω = ⊤
      · have hval : stoppedValueAtInf A M ω = Alim ω := by
          show (if M ω = ⊤ then limUnder atTop (fun n => A n ω)
            else stoppedValue A M ω) = Alim ω
          rw [ite_eq_left htop]
          exact hlimω.limUnder_eq
        rw [hval]
        show A (min (↑n : WithTop ℕ) (M ω)).untopA ω ≤ Alim ω
        exact hleAlim _
      · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp htop
        have hval : stoppedValueAtInf A M ω = A k ω := by
          show (if M ω = ⊤ then limUnder atTop (fun n => A n ω)
            else stoppedValue A M ω) = A k ω
          rw [ite_eq_right htop]
          show A (M ω).untopA ω = A k ω
          rw [← hk]
          rfl
        rw [hval]
        show A (min (↑n : WithTop ℕ) (M ω)).untopA ω ≤ A k ω
        apply hmonoω
        rw [WithTop.untopA_le_iff (ne_top_of_le_ne_top (by simp) (min_le_left _ _))]
        rw [← hk]
        exact min_le_right _ _
    have hL_le : stoppedProcess A L n ω ≤ Alim ω := by
      show A (min (↑n : WithTop ℕ) (L ω)).untopA ω ≤ Alim ω
      exact hleAlim _
    have hM_le_Alim : stoppedValueAtInf A M ω ≤ Alim ω := by
      by_cases htop : M ω = ⊤
      · have hval : stoppedValueAtInf A M ω = Alim ω := by
          show (if M ω = ⊤ then limUnder atTop (fun n => A n ω)
            else stoppedValue A M ω) = Alim ω
          rw [ite_eq_left htop]
          exact hlimω.limUnder_eq
        rw [hval]
      · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp htop
        have hval : stoppedValueAtInf A M ω = A k ω := by
          show (if M ω = ⊤ then limUnder atTop (fun n => A n ω)
            else stoppedValue A M ω) = A k ω
          rw [ite_eq_right htop]
          show A (M ω).untopA ω = A k ω
          rw [← hk]
          rfl
        rw [hval]
        exact hleAlim k
    exact ⟨hLM_le, hM_n_le, hL_le, hM_le_Alim⟩
  -- Each term of the stopped process at `L` is `ℱ_L`-measurable and
  -- integrable, and bounded by the conditional expectation of the
  -- right-hand side.
  have hA_M_int : Integrable (stoppedValueAtInf A M) μ :=
    integrable_stoppedValueAtInf_predictablePart hsub hui hM
  have hstep : ∀ n, stoppedProcess A L n ≤ᵐ[μ]
      μ[stoppedValueAtInf A M | hL.measurableSpace] := by
    intro n
    have hσ : IsStoppingTime ℱ (fun ω => min (↑n : WithTop ℕ) (L ω)) :=
      (isStoppingTime_const ℱ n).min hL
    have hmeas : StronglyMeasurable[hL.measurableSpace] (stoppedProcess A L n) := by
      have h1 : Measurable[hσ.measurableSpace] (stoppedProcess A L n) := by
        have h2 : Measurable[hσ.measurableSpace]
            (stoppedValue A (fun ω => min (↑n : WithTop ℕ) (L ω))) :=
          measurable_stoppedValue
            stronglyAdapted_predictablePart'.isStronglyProgressive_of_discrete hσ
        exact h2
      have h3 : StronglyMeasurable[hσ.measurableSpace] (stoppedProcess A L n) :=
        h1.stronglyMeasurable
      exact h3.mono (IsStoppingTime.measurableSpace_mono hσ hL (fun ω => min_le_right _ _))
    have hint_L : Integrable (stoppedProcess A L n) μ := by
      have hae : AEStronglyMeasurable (stoppedProcess A L n) μ :=
        (hmeas.mono hL.measurableSpace_le).aestronglyMeasurable
      apply (hAlim_int.norm).mono' hae
      filter_upwards [hbound, hgood] with ω hω hgoodω
      obtain ⟨-, hnnω, -⟩ := hgoodω
      have h0 : 0 ≤ stoppedProcess A L n ω := by
        show 0 ≤ A (min (↑n : WithTop ℕ) (L ω)).untopA ω
        exact hnnω _
      rw [Real.norm_eq_abs, abs_of_nonneg h0, Real.norm_eq_abs,
        abs_of_nonneg (le_trans h0 (hω n).2.2.1)]
      exact (hω n).2.2.1
    have hint_M : Integrable (stoppedProcess A M n) μ := by
      have hae : AEStronglyMeasurable (stoppedProcess A M n) μ :=
        (stronglyAdapted_predictablePart'.stronglyMeasurable_stoppedProcess_of_discrete
          hM n).aestronglyMeasurable
      apply (hAlim_int.norm).mono' hae
      filter_upwards [hbound, hgood] with ω hω hgoodω
      obtain ⟨-, hnnω, -⟩ := hgoodω
      have h0 : 0 ≤ stoppedProcess A M n ω := by
        show 0 ≤ A (min (↑n : WithTop ℕ) (M ω)).untopA ω
        exact hnnω _
      rw [Real.norm_eq_abs, abs_of_nonneg h0, Real.norm_eq_abs,
        abs_of_nonneg (le_trans h0 ((hω n).2.1.trans (hω n).2.2.2))]
      exact (hω n).2.1.trans (hω n).2.2.2
    have h1 : stoppedProcess A L n =ᵐ[μ]
        μ[stoppedProcess A L n | hL.measurableSpace] :=
      Filter.EventuallyEq.of_eq
        (condExp_of_stronglyMeasurable hL.measurableSpace_le hmeas hint_L).symm
    have h2 : μ[stoppedProcess A L n | hL.measurableSpace] ≤ᵐ[μ]
        μ[stoppedProcess A M n | hL.measurableSpace] :=
      condExp_mono hint_L hint_M (by
        filter_upwards [hbound] with ω hω
        exact (hω n).1)
    have h3 : μ[stoppedProcess A M n | hL.measurableSpace] ≤ᵐ[μ]
        μ[stoppedValueAtInf A M | hL.measurableSpace] :=
      condExp_mono hint_M hA_M_int (by
        filter_upwards [hbound] with ω hω
        exact (hω n).2.1)
    exact h1.le.trans (h2.trans h3)
  -- Pass to the limit in `n`.
  have hper : ∀ᵐ ω ∂μ, ∀ n, stoppedProcess A L n ω ≤
      (μ[stoppedValueAtInf A M | hL.measurableSpace]) ω :=
    ae_all_iff.mpr hstep
  filter_upwards [tendsto_stoppedProcess_to_stoppedValueAtInf hconv, hper]
    with ω hω hperω
  exact le_of_tendsto_of_tendsto hω tendsto_const_nhds (Filter.Eventually.of_forall hperω)

/-- **Conditional optional stopping for uniformly integrable
submartingales.** For stopping times `L ≤ M` (possibly infinite),
`f_L ≤ᵐ μ[f_M | ℱ_L]`. -/
theorem Submartingale.stoppedValueAtInf_le_condExp_stoppedValueAtInf
    (hsub : Submartingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    {L M : Ω → WithTop ℕ} (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    stoppedValueAtInf f L ≤ᵐ[μ] μ[stoppedValueAtInf f M | hL.measurableSpace] := by
  obtain ⟨hMt_mart, hMt_UI⟩ := uniformIntegrable_martingalePart hsub hui
  have hAdd_L := stoppedValueAtInf_decomp hsub hui (τ := L)
  have hAdd_M := stoppedValueAtInf_decomp hsub hui (τ := M)
  have hMt_cond :=
    martingale_stoppedValueAtInf_ae_eq_condExp_stoppedValueAtInf hMt_mart hMt_UI hL hM hLM
  have hA_cond := predictablePart_stoppedValueAtInf_le_condExp hsub hui hL hM hLM
  have hsum : μ[stoppedValueAtInf (martingalePart f ℱ μ) M | hL.measurableSpace] +
        μ[stoppedValueAtInf (predictablePart f ℱ μ) M | hL.measurableSpace] =ᵐ[μ]
      μ[stoppedValueAtInf (martingalePart f ℱ μ) M +
        stoppedValueAtInf (predictablePart f ℱ μ) M | hL.measurableSpace] :=
    (condExp_add (integrable_stoppedValueAtInf_martingalePart hsub hui hM)
      (integrable_stoppedValueAtInf_predictablePart hsub hui hM) _).symm
  exact hAdd_L.le.trans
    ((hMt_cond.le.add_le_add hA_cond).trans
      (hsum.le.trans (condExp_congr_ae hAdd_M.symm).le))

/-- **Expectation form of conditional optional stopping for uniformly
integrable submartingales.** For stopping times `L ≤ M` (possibly
infinite), `∫ f_L ≤ ∫ f_M`. -/
theorem Submartingale.integral_stoppedValueAtInf_mono_of_uniformIntegrable
    (hsub : Submartingale f ℱ μ) (hui : UniformIntegrable f 1 μ)
    {L M : Ω → WithTop ℕ} (hL : IsStoppingTime ℱ L) (hM : IsStoppingTime ℱ M)
    (hLM : L ≤ M) :
    ∫ ω, stoppedValueAtInf f L ω ∂μ ≤ ∫ ω, stoppedValueAtInf f M ω ∂μ := by
  have hcond := hsub.stoppedValueAtInf_le_condExp_stoppedValueAtInf hui hL hM hLM
  have hIntL : Integrable (stoppedValueAtInf f L) μ := by
    have hAdd := stoppedValueAtInf_decomp hsub hui (τ := L)
    exact ((integrable_stoppedValueAtInf_martingalePart hsub hui hL).add
      (integrable_stoppedValueAtInf_predictablePart hsub hui hL)).congr hAdd.symm
  have hIntM : Integrable (stoppedValueAtInf f M) μ := by
    have hAdd := stoppedValueAtInf_decomp hsub hui (τ := M)
    exact ((integrable_stoppedValueAtInf_martingalePart hsub hui hM).add
      (integrable_stoppedValueAtInf_predictablePart hsub hui hM)).congr hAdd.symm
  calc ∫ ω, stoppedValueAtInf f L ω ∂μ
      ≤ ∫ ω, (μ[stoppedValueAtInf f M | hL.measurableSpace]) ω ∂μ :=
        integral_mono_ae hIntL integrable_condExp hcond
    _ = ∫ ω, stoppedValueAtInf f M ω ∂μ :=
        integral_condExp hL.measurableSpace_le


end MeasureTheory
