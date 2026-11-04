import RandomizedLog.Records

/-!
# Monochromatic cost accounting (randomized paper, §"Cost of the
monochromatic comparisons")

The counting core of the three monochromatic lemmas, in natural
numbers (comparison counts; the price factors `α`/`β` are applied at
assembly):

* `lem:bluecost` — a blue run of length `t ≥ 2` MergeSorts in at most
  `t * (log2 t + 1)` comparisons, and `t ≤ 2 * (t - 1)`, so the total
  over all blue runs is at most `2 * (log2 N + 1) * ∑ (t_j - 1)`.
* `lem:ownred` — the joiners of a final red run of size `s` each pay
  at most `K` comparisons, so the own cost is at most `(s - 1) * K`.
* `lem:foreignred` — the foreign testers of a final red run are
  threshold records at its endpoints; predecessor and successor
  threshold records at an element `a` are exactly
  `predRecords`/`succRecords` at `a`, whose expected count is the
  records bound. The counting consequence (each tester pays at most
  two comparisons) is proved here conditional on the geometric
  inclusion of testers in threshold records; that inclusion is the
  trace-level argument assembled later.
-/

namespace Bichromatic.Randomized

open Bichromatic

variable {X : Type*} [LinearOrder X] [Fintype X] (color : X → Color)

/-- `Nat.log2` is monotone (via `Nat.log`). -/
theorem log2_mono' {a b : ℕ} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  exact Nat.log_mono_right h

/-- MergeSort comparison count for one run of length `t`: `0` for
`t < 2`, else `t * (log2 t + 1)` (the paper's `t⌈log t⌉`, with
`⌈log2 t⌉ ≤ log2 t + 1`). -/
def mergeCost (t : ℕ) : ℕ := if t < 2 then 0 else t * (Nat.log2 t + 1)

theorem mergeCost_le {t N : ℕ} (ht : t ≤ N) :
    mergeCost t ≤ 2 * (Nat.log2 N + 1) * (t - 1) := by
  unfold mergeCost
  split_ifs with h
  · cases t with
    | zero => simp
    | succ t =>
      cases t with
      | zero => simp
      | succ t => omega
  · have h1 : t ≤ 2 * (t - 1) := by omega
    have h2 : Nat.log2 t + 1 ≤ Nat.log2 N + 1 :=
      Nat.add_le_add_right (log2_mono' ht) 1
    calc t * (Nat.log2 t + 1)
        ≤ (2 * (t - 1)) * (Nat.log2 N + 1) := Nat.mul_le_mul h1 h2
      _ = 2 * (Nat.log2 N + 1) * (t - 1) := by ring

/-- `lem:bluecost`, counting core: total MergeSort comparisons over
all blue runs, each of length at most `N`. -/
theorem blueCost_le (ts : List ℕ) (N : ℕ) (hN : ∀ t ∈ ts, t ≤ N) :
    (ts.map mergeCost).sum
      ≤ 2 * (Nat.log2 N + 1) * (ts.map (· - 1)).sum := by
  induction ts with
  | nil => simp
  | cons t rest ih =>
    have ht : t ≤ N := hN t (by simp)
    have hrest : ∀ x ∈ rest, x ≤ N := fun x hx => hN x (by simp [hx])
    have h := ih hrest
    simp only [List.map_cons, List.sum_cons]
    have h1 : mergeCost t ≤ 2 * (Nat.log2 N + 1) * (t - 1) := mergeCost_le ht
    calc mergeCost t + (rest.map mergeCost).sum
        ≤ 2 * (Nat.log2 N + 1) * (t - 1)
            + 2 * (Nat.log2 N + 1) * (rest.map (· - 1)).sum :=
          add_le_add h1 h
      _ = 2 * (Nat.log2 N + 1) * (t - 1 + (rest.map (· - 1)).sum) := by ring

/-- A list of comparison counts, each at most `K`, sums to at most
`length * K`. -/
theorem sum_le_length_mul (cs : List ℕ) (K : ℕ)
    (h : ∀ c ∈ cs, c ≤ K) : cs.sum ≤ cs.length * K := by
  induction cs with
  | nil => simp
  | cons c rest ih =>
    have hc : c ≤ K := h c (by simp)
    have hrest : ∀ x ∈ rest, x ≤ K := fun x hx => h x (by simp [hx])
    have h' := ih hrest
    simp only [List.sum_cons, List.length_cons]
    have hring : (rest.length + 1) * K = rest.length * K + K := by ring
    omega

/-- `lem:ownred`, counting core: the joiners of a final red run
(their comparison counts `cs`, one per joiner) pay in total at most
`(run size - 1) * K` when each joiner pays at most `K`. -/
theorem ownCost_le {s : ℕ} (cs : List ℕ) (K : ℕ)
    (hlen : cs.length = s - 1) (h : ∀ c ∈ cs, c ≤ K) :
    cs.sum ≤ (s - 1) * K := by
  have h' := sum_le_length_mul cs K h
  rw [hlen] at h'
  exact h'

/-- Expected threshold-record count at an endpoint `a`: predecessor
plus successor threshold records. These are exactly the records of
`lem:records` instantiated at `a`, so the bound is the records bound
on both sides. -/
theorem expected_threshold_le (a : X) :
    ((∑ τ ∈ InjRanks X,
        (((predRecords color τ a).card + (succRecords color τ a).card : ℕ) : ℝ))
      / (InjRanks X).card)
      ≤ 2 + Real.log (redsBelow color a).card
        + Real.log (redsAbove color a).card := by
  have hsum : (∑ τ ∈ InjRanks X,
        (((predRecords color τ a).card + (succRecords color τ a).card : ℕ) : ℝ))
      = (∑ τ ∈ InjRanks X, ((predRecords color τ a).card : ℝ))
        + (∑ τ ∈ InjRanks X, ((succRecords color τ a).card : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro τ _
    push_cast
    ring
  have hp := expected_pred_le color a
  have hs := expected_succ_le color a
  rw [hsum, add_div]
  have h := add_le_add hp hs
  linarith [h]

/-- `lem:foreignred`, counting core: if every foreign tester of a run
(at every arrival order `τ`) is a threshold record at an endpoint,
and each tester makes at most two comparisons, then the total
foreign comparison count over all `τ` is at most twice the total
threshold-record count. -/
theorem foreign_count_le {Y : Type*} (τs : Finset Y)
    (testers pred succ : Y → Finset X) (costs : Y → List ℕ)
    (hsub : ∀ τ ∈ τs, testers τ ⊆ pred τ ∪ succ τ)
    (hcost : ∀ τ ∈ τs, ∀ c ∈ costs τ, c ≤ 2)
    (hlen : ∀ τ ∈ τs, (costs τ).length = (testers τ).card) :
    (∑ τ ∈ τs, (costs τ).sum)
      ≤ 2 * (∑ τ ∈ τs, ((pred τ).card + (succ τ).card)) := by
  have h1 : ∀ τ ∈ τs, (costs τ).sum ≤ 2 * (testers τ).card := by
    intro τ hτ
    have h := sum_le_length_mul (costs τ) 2 (hcost τ hτ)
    rw [hlen τ hτ] at h
    omega
  have h2 : ∀ τ ∈ τs, (testers τ).card ≤ (pred τ).card + (succ τ).card := by
    intro τ hτ
    exact le_trans (Finset.card_le_card (hsub τ hτ)) (Finset.card_union_le (pred τ) (succ τ))
  have h3 : (∑ τ ∈ τs, (costs τ).sum)
      ≤ ∑ τ ∈ τs, (2 * ((pred τ).card + (succ τ).card)) := by
    apply Finset.sum_le_sum
    intro τ hτ
    exact le_trans (h1 τ hτ) (Nat.mul_le_mul_left 2 (h2 τ hτ))
  refine le_trans h3 ?_
  rw [Finset.mul_sum]

end Bichromatic.Randomized
