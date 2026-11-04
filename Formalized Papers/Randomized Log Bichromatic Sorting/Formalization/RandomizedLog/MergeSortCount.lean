import RandomizedLog.Definitions

/-!
# Counted MergeSort (`prop:MergeSort` of the randomized paper)

A mergesort that returns, alongside the sorted list, the number of
comparisons it performed. The paper bounds deterministic MergeSort
on `t` elements by `t ⌈log t⌉` comparisons; here the count is proved
at most `t * (log₂ (t - 1) + 1)`, which is at most the paper's bound
(and at most `MonoCost.mergeCost t` for `t ≥ 2`).
-/

namespace Bichromatic.Randomized

open Bichromatic

variable {X : Type*} [LinearOrder X]

/-- Merge two lists (the list half of the counted merge). -/
def mergeList : List X → List X → List X
  | [], l₂ => l₂
  | l₁, [] => l₁
  | a :: as, b :: bs =>
    if a ≤ b then a :: mergeList as (b :: bs)
    else b :: mergeList (a :: as) bs
termination_by l₁ l₂ => l₁.length + l₂.length

/-- Number of comparisons to merge two lists. -/
def mergeCount : List X → List X → ℕ
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs =>
    if a ≤ b then mergeCount as (b :: bs) + 1
    else mergeCount (a :: as) bs + 1
termination_by l₁ l₂ => l₁.length + l₂.length

theorem mergeList_eq : ∀ (l₁ l₂ : List X),
    mergeList l₁ l₂ = List.merge l₁ l₂ (fun a b => decide (a ≤ b))
  | [], l₂ => by simp [mergeList, List.merge]
  | l₁, [] => by cases l₁ <;> simp [mergeList, List.merge]
  | a :: as, b :: bs => by
    by_cases h : a ≤ b
    · have e1 : mergeList (a :: as) (b :: bs)
          = a :: mergeList as (b :: bs) := by simp [mergeList, h]
      have e2 : List.merge (a :: as) (b :: bs)
            (fun a b => decide (a ≤ b))
          = a :: List.merge as (b :: bs)
            (fun a b => decide (a ≤ b)) := by
        simp [List.merge, h]
      rw [e1, e2, mergeList_eq as (b :: bs)]
    · have e1 : mergeList (a :: as) (b :: bs)
          = b :: mergeList (a :: as) bs := by simp [mergeList, h]
      have e2 : List.merge (a :: as) (b :: bs)
            (fun a b => decide (a ≤ b))
          = b :: List.merge (a :: as) bs
            (fun a b => decide (a ≤ b)) := by
        simp [List.merge, h]
      rw [e1, e2, mergeList_eq (a :: as) bs]
termination_by l₁ l₂ => l₁.length + l₂.length
decreasing_by all_goals simp

theorem mergeCount_le : ∀ (l₁ l₂ : List X),
    mergeCount l₁ l₂ ≤ l₁.length + l₂.length
  | [], _ => by simp [mergeCount]
  | _ :: _, [] => by simp [mergeCount]
  | a :: as, b :: bs => by
    by_cases h : a ≤ b
    · simp only [mergeCount, if_pos h, List.length_cons]
      have ih := mergeCount_le as (b :: bs)
      simp only [List.length_cons] at ih
      omega
    · simp only [mergeCount, if_neg h, List.length_cons]
      have ih := mergeCount_le (a :: as) bs
      simp only [List.length_cons] at ih
      omega
termination_by l₁ l₂ => l₁.length + l₂.length
decreasing_by all_goals simp

theorem mergeList_length (l₁ l₂ : List X) :
    (mergeList l₁ l₂).length = l₁.length + l₂.length := by
  rw [mergeList_eq]
  have h : (List.merge l₁ l₂ (fun a b => decide (a ≤ b))).Perm
      (l₁ ++ l₂) :=
    List.merge_perm_append (fun a b => decide (a ≤ b))
  rw [List.Perm.length_eq h, List.length_append]

theorem mergeList_perm (l₁ l₂ : List X) :
    (mergeList l₁ l₂).Perm (l₁ ++ l₂) := by
  rw [mergeList_eq]
  exact List.merge_perm_append (fun a b => decide (a ≤ b))

theorem mergeList_pairwise {l₁ l₂ : List X}
    (h₁ : List.Pairwise (· ≤ ·) l₁) (h₂ : List.Pairwise (· ≤ ·) l₂) :
    List.Pairwise (· ≤ ·) (mergeList l₁ l₂) := by
  rw [mergeList_eq]
  exact List.Pairwise.merge h₁ h₂

/-- Counted mergesort: the sorted list and its comparison count. -/
def msort : List X → (List X × ℕ)
  | [] => ([], 0)
  | [a] => ([a], 0)
  | a :: b :: t =>
    let l := a :: b :: t
    let s₁ := msort (l.take (l.length / 2))
    let s₂ := msort (l.drop (l.length / 2))
    (mergeList s₁.1 s₂.1, s₁.2 + s₂.2 + mergeCount s₁.1 s₂.1)
termination_by l => l.length
decreasing_by
  all_goals
    simp only [List.length_take, List.length_drop, List.length_cons]
    omega

theorem msort_eq_of_length_ge_two {l : List X} (h : 2 ≤ l.length) :
    msort l = (mergeList (msort (l.take (l.length / 2))).1
        (msort (l.drop (l.length / 2))).1,
      (msort (l.take (l.length / 2))).2
        + (msort (l.drop (l.length / 2))).2
        + mergeCount (msort (l.take (l.length / 2))).1
          (msort (l.drop (l.length / 2))).1) := by
  cases l with
  | nil => simp at h
  | cons a t =>
    cases t with
    | nil => simp at h
    | cons b t =>
      rw [msort]

private theorem msort_length_aux :
    ∀ n : ℕ, ∀ l : List X, l.length = n →
      (msort l).1.length = l.length := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro l hl
  by_cases h2 : 2 ≤ l.length
  · have htake : (l.take (l.length / 2)).length < n := by
      rw [← hl]
      have h1 : (l.take (l.length / 2)).length ≤ l.length / 2 :=
        List.length_take_le _ _
      have h2' : l.length / 2 < l.length := by omega
      exact lt_of_le_of_lt h1 (by omega)
    have hdrop : (l.drop (l.length / 2)).length < n := by
      rw [← hl, List.length_drop]
      omega
    rw [msort_eq_of_length_ge_two h2]
    show (mergeList (msort (l.take (l.length / 2))).1
      (msort (l.drop (l.length / 2))).1).length = l.length
    rw [mergeList_length, ih _ htake _ rfl, ih _ hdrop _ rfl]
    have hadd := congrArg List.length
      (List.take_append_drop (l.length / 2) l)
    rwa [List.length_append] at hadd
  · have hl2 : l.length = 0 ∨ l.length = 1 := by omega
    cases l with
    | nil => simp [msort]
    | cons a t =>
      cases t with
      | nil => simp [msort]
      | cons b t => simp at hl2

theorem msort_length (l : List X) : (msort l).1.length = l.length :=
  msort_length_aux l.length l rfl

private theorem msort_perm_aux :
    ∀ n : ℕ, ∀ l : List X, l.length = n → (msort l).1.Perm l := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro l hl
  by_cases h2 : 2 ≤ l.length
  · have htake : (l.take (l.length / 2)).length < n := by
      rw [← hl]
      have h1 : (l.take (l.length / 2)).length ≤ l.length / 2 :=
        List.length_take_le _ _
      have h2' : l.length / 2 < l.length := by omega
      exact lt_of_le_of_lt h1 (by omega)
    have hdrop : (l.drop (l.length / 2)).length < n := by
      rw [← hl, List.length_drop]
      omega
    rw [msort_eq_of_length_ge_two h2]
    show (mergeList (msort (l.take (l.length / 2))).1
      (msort (l.drop (l.length / 2))).1).Perm l
    refine (mergeList_perm _ _).trans ?_
    exact List.Perm.append (ih _ htake _ rfl) (ih _ hdrop _ rfl) |>.trans
      (by rw [List.take_append_drop])
  · have hl2 : l.length = 0 ∨ l.length = 1 := by omega
    cases l with
    | nil => simp [msort]
    | cons a t =>
      cases t with
      | nil => simp [msort]
      | cons b t => simp at hl2

theorem msort_perm (l : List X) : (msort l).1.Perm l :=
  msort_perm_aux l.length l rfl

private theorem msort_pairwise_aux :
    ∀ n : ℕ, ∀ l : List X, l.length = n →
      List.Pairwise (· ≤ ·) (msort l).1 := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro l hl
  by_cases h2 : 2 ≤ l.length
  · have htake : (l.take (l.length / 2)).length < n := by
      rw [← hl]
      have h1 : (l.take (l.length / 2)).length ≤ l.length / 2 :=
        List.length_take_le _ _
      have h2' : l.length / 2 < l.length := by omega
      exact lt_of_le_of_lt h1 (by omega)
    have hdrop : (l.drop (l.length / 2)).length < n := by
      rw [← hl, List.length_drop]
      omega
    rw [msort_eq_of_length_ge_two h2]
    show List.Pairwise (· ≤ ·)
      (mergeList (msort (l.take (l.length / 2))).1
        (msort (l.drop (l.length / 2))).1)
    exact mergeList_pairwise (ih _ htake _ rfl) (ih _ hdrop _ rfl)
  · have hl2 : l.length = 0 ∨ l.length = 1 := by omega
    cases l with
    | nil => simp [msort]
    | cons a t =>
      cases t with
      | nil => simp [msort]
      | cons b t => simp at hl2

theorem msort_pairwise (l : List X) :
    List.Pairwise (· ≤ ·) (msort l).1 :=
  msort_pairwise_aux l.length l rfl

/-- The numeric step of `prop:MergeSort`: merging two halves of
sizes `n₁, n₂` (each at most half, rounded up) fits the bound. -/
theorem msort_count_aux {n₁ n₂ n : ℕ} (hsum : n₁ + n₂ = n)
    (h3 : 3 ≤ n) (h₁ : n₁ ≤ (n + 1) / 2) (h₂ : n₂ ≤ (n + 1) / 2) :
    n₁ * (Nat.log 2 (n₁ - 1) + 1) + n₂ * (Nat.log 2 (n₂ - 1) + 1) + n
      ≤ n * (Nat.log 2 (n - 1) + 1) := by
  have hlog : ∀ k : ℕ, k ≤ (n + 1) / 2 →
      k * (Nat.log 2 (k - 1) + 1) ≤ k * Nat.log 2 (n - 1) := by
    intro k hk
    apply Nat.mul_le_mul_left
    have hn : 1 ≤ Nat.log 2 (n - 1) :=
      Nat.log_pos (by norm_num) (by omega)
    by_cases hk0 : k ≤ 1
    · have hz : Nat.log 2 (k - 1) = 0 := by
        have h0 : k - 1 = 0 := by omega
        simp [h0]
      omega
    · have hk1 : k - 1 ≤ (n - 1) / 2 := by omega
      have hle : Nat.log 2 (k - 1) ≤ Nat.log 2 ((n - 1) / 2) :=
        Nat.log_mono_right hk1
      have hdiv : Nat.log 2 ((n - 1) / 2) = Nat.log 2 (n - 1) - 1 := by
        have h := Nat.log_div_base (b := 2) (n := n - 1)
        simpa using h
      omega
  have a1 := hlog n₁ h₁
  have a2 := hlog n₂ h₂
  calc n₁ * (Nat.log 2 (n₁ - 1) + 1) + n₂ * (Nat.log 2 (n₂ - 1) + 1) + n
      ≤ n₁ * Nat.log 2 (n - 1) + n₂ * Nat.log 2 (n - 1) + n := by omega
    _ = (n₁ + n₂) * Nat.log 2 (n - 1) + n := by rw [Nat.add_mul]
    _ = n * Nat.log 2 (n - 1) + n := by rw [hsum]
    _ = n * (Nat.log 2 (n - 1) + 1) := by rw [Nat.mul_succ]

private theorem msort_count_le_aux :
    ∀ n : ℕ, ∀ l : List X, l.length = n →
      (msort l).2 ≤ n * (Nat.log 2 (n - 1) + 1) := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro l hl
  by_cases h2 : 2 ≤ l.length
  · have htake_len : (l.take (l.length / 2)).length = l.length / 2 := by
      rw [List.length_take]
      exact min_eq_left (Nat.div_le_self _ _)
    have hdrop_len : (l.drop (l.length / 2)).length
        = l.length - l.length / 2 := List.length_drop
    have htake_lt : (l.take (l.length / 2)).length < n := by
      rw [← hl, htake_len]
      exact Nat.div_lt_self (by omega) (by norm_num)
    have hdrop_lt : (l.drop (l.length / 2)).length < n := by
      rw [← hl, hdrop_len]
      have hpos : 0 < l.length / 2 := Nat.div_pos h2 (by norm_num)
      omega
    have b1 := ih _ htake_lt _ rfl
    have b2 := ih _ hdrop_lt _ rfl
    rw [htake_len] at b1
    rw [hdrop_len] at b2
    have bm : mergeCount (msort (l.take (l.length / 2))).1
          (msort (l.drop (l.length / 2))).1
        ≤ l.length / 2 + (l.length - l.length / 2) := by
      have h := mergeCount_le (msort (l.take (l.length / 2))).1
        (msort (l.drop (l.length / 2))).1
      rwa [msort_length, msort_length, htake_len, hdrop_len] at h
    have hcount : (msort l).2
        = (msort (l.take (l.length / 2))).2
          + (msort (l.drop (l.length / 2))).2
          + mergeCount (msort (l.take (l.length / 2))).1
            (msort (l.drop (l.length / 2))).1 :=
      congrArg Prod.snd (msort_eq_of_length_ge_two h2)
    rw [hcount, ← hl]
    by_cases h3 : l.length = 2
    · -- length two: the two halves are singletons, merge costs 1
      obtain ⟨a, b, rfl⟩ : ∃ a b, l = [a, b] := by
        cases l with
        | nil => simp at h3
        | cons a t =>
          cases t with
          | nil => simp at h3
          | cons b t =>
            cases t with
            | nil => exact ⟨a, b, rfl⟩
            | cons c t => simp at h3
      by_cases hab : a ≤ b <;> simp [msort, mergeCount, hab]
    · have hge3 : 3 ≤ l.length := by omega
      refine le_trans (add_le_add (add_le_add b1 b2) bm) ?_
      have hsum : l.length / 2 + (l.length - l.length / 2) = l.length :=
        by omega
      rw [hsum]
      exact msort_count_aux hsum hge3 (by omega) (by omega)
  · have hl2 : l.length = 0 ∨ l.length = 1 := by omega
    cases l with
    | nil => simp [msort, hl]
    | cons a t =>
      cases t with
      | nil => simp [msort, hl]
      | cons b t => simp at hl2

/-- **`prop:MergeSort`.** Counted mergesort on `t` elements makes
at most `t * (log₂ (t - 1) + 1)` comparisons (at most the paper's
`t ⌈log t⌉`). -/
theorem msort_count_le (l : List X) :
    (msort l).2 ≤ l.length * (Nat.log 2 (l.length - 1) + 1) :=
  msort_count_le_aux l.length l rfl

end Bichromatic.Randomized
