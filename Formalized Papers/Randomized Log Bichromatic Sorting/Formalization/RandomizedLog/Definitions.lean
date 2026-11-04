import Mathlib

/-!
# Bichromatic sorting: common definitions

Statement-level formalization of the cost model shared by the two papers
(`Papers/randomized_log_final_draft.tex`, `Papers/deterministic_polylog_final_draft.tex`).

An instance is a finite type `X` with a strict total order (the unknown key
order `≺` of the deterministic paper) and a colouring `color : X → Color`.
Mixed comparisons cost `1`; red-red comparisons cost `α`; blue-blue cost `β`.
The benchmark `H` is the cost of comparing adjacent pairs in the sorted order:
the cost of verifying that the output is ordered (Charikar et al.'s
cheapest-proof cost).
-/

namespace Bichromatic

/-- The two colour classes: red and blue. -/
inductive Color where
  | red
  | blue
deriving DecidableEq, Repr

variable {X : Type*}

/-- Comparison cost of a pair, given monochromatic prices `α` (red-red)
and `β` (blue-blue). Mixed comparisons are normalized to cost `1`. -/
def pairCost (α β : ℝ) (color : X → Color) (x y : X) : ℝ :=
  if color x = color y then
    match color x with
    | .red => α
    | .blue => β
  else 1

/-- Sum of `pairCost` over adjacent pairs of a list. -/
def adjCost (α β : ℝ) (color : X → Color) : List X → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: t => pairCost α β color a b + adjCost α β color (b :: t)

variable [LinearOrder X] [Fintype X]

/-- The sorted enumeration of all elements of `X`. -/
def sortedList (X : Type*) [LinearOrder X] [Fintype X] : List X :=
  Finset.sort Finset.univ (· ≤ ·)

/-- The benchmark `H`: total cost of adjacent-pair comparisons in the
sorted order. `H ≥ N - 1` and `H = 0` when `N ≤ 1` (as sums of ones at
minimum / empty sums), matching both papers. -/
def benchmarkH (α β : ℝ) (color : X → Color) : ℝ :=
  adjCost α β color (sortedList X)

/-- `N`, the number of elements. -/
def instSize (X : Type*) [Fintype X] : ℕ := Fintype.card X

/-- Competitive ratio (randomized paper, p.2): the worst case, over
all inputs, of the ratio of expected cost to the benchmark `H`.
An input here is a colouring of `X`; the key order on `X` is fixed.
(The supremum ranges over the finite set of colourings.) -/
noncomputable def competitiveRatio (expected : (X → Color) → ℝ) (α β : ℝ) : ℝ :=
  ⨆ (color : X → Color), expected color / benchmarkH α β color

variable (α β : ℝ) (color : X → Color)

/-- Every pair cost is at least `1` when `α, β ≥ 1`: monochromatic pairs
pay `α` or `β`, mixed pairs pay `1`. -/
theorem pairCost_ge_one (hα : 1 ≤ α) (hβ : 1 ≤ β) (x y : X) :
    1 ≤ pairCost α β color x y := by
  unfold pairCost
  split_ifs with h
  · cases hcol : color x <;> simp [hcol, hα, hβ]
  · exact le_refl 1

/-- Adjacent-cost of a list with a head element bounds the tail length:
each step pays at least `1`. Proved by induction on the tail. -/
theorem adjCost_cons_ge (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    ∀ (a : X) (t : List X), (t.length : ℝ) ≤ adjCost α β color (a :: t) := by
  intro a t
  induction t generalizing a with
  | nil => simp [adjCost]
  | cons b t ih =>
      have h1 : (t.length : ℝ) ≤ adjCost α β color (b :: t) := ih b
      have h2 : (1 : ℝ) ≤ pairCost α β color a b := pairCost_ge_one α β color hα hβ a b
      have h3 : adjCost α β color (a :: b :: t)
          = pairCost α β color a b + adjCost α β color (b :: t) := rfl
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

/-- Adjacent cost with an arbitrary pair-weight function, so the
monochromatic parts of `H` can be isolated: `adjCost` is the case
`w = pairCost α β color`. -/
def adjCostWith (w : X → X → ℝ) : List X → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: t => w a b + adjCostWith w (b :: t)

theorem adjCost_eq_adjCostWith (l : List X) :
    adjCost α β color l = adjCostWith (pairCost α β color) l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t =>
      simp only [adjCost, adjCostWith, ih]

/-- Pointwise-smaller weights give smaller adjacent cost, provided
the larger weights are nonnegative. -/
theorem adjCostWith_le_adjCostWith (w₁ w₂ : X → X → ℝ)
    (hw : ∀ x y, w₁ x y ≤ w₂ x y) (l : List X) :
    adjCostWith w₁ l ≤ adjCostWith w₂ l := by
  induction l with
  | nil => simp [adjCostWith]
  | cons a t ih =>
    cases t with
    | nil => simp [adjCostWith]
    | cons b t =>
      simp only [adjCostWith]
      exact add_le_add (hw a b) ih

/-- Every adjacent pair costs at most `K`, so the adjacent cost of
a list is at most `K * (length - 1)`. -/
theorem adjCostWith_le (w : X → X → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hw : ∀ x y, w x y ≤ K) :
    ∀ l : List X, adjCostWith w l ≤ K * (((l.length - 1 : ℕ) : ℝ)) := by
  intro l
  induction l with
  | nil => simp [adjCostWith]
  | cons a t ih =>
    cases t with
    | nil => simp [adjCostWith]
    | cons b t =>
      have h1 : adjCostWith w (a :: b :: t)
          = w a b + adjCostWith w (b :: t) := rfl
      rw [h1]
      have hwab : w a b ≤ K := hw a b
      have hlen1 : ((a :: b :: t).length - 1 : ℕ) = (b :: t).length := by
        simp
      have hlen2 : (((b :: t).length - 1 : ℕ) : ℝ)
          = ((b :: t).length : ℝ) - 1 := by
        rw [Nat.cast_sub (by simp), Nat.cast_one]
      have hcast : (((a :: b :: t).length - 1 : ℕ) : ℝ)
          = ((b :: t).length : ℝ) := by
        rw [hlen1]
      rw [hcast]
      have hcast2 : (((b :: t).length - 1 : ℕ) : ℝ)
          = ((b :: t).length : ℝ) - 1 := by
        rw [Nat.cast_sub (by simp), Nat.cast_one]
      rw [hcast2] at ih
      calc w a b + adjCostWith w (b :: t)
          ≤ K + K * (((b :: t).length : ℝ) - 1) :=
            add_le_add hwab ih
        _ = K * ((b :: t).length : ℝ) := by ring

/-- `adjCost` is nonnegative when `α, β ≥ 1`. -/
theorem adjCost_nonneg (hα : 1 ≤ α) (hβ : 1 ≤ β) (l : List X) :
    0 ≤ adjCost α β color l := by
  cases l with
  | nil => simp [adjCost]
  | cons a t =>
      have h := adjCost_cons_ge α β color hα hβ a t
      have h' : (0 : ℝ) ≤ (t.length : ℝ) := Nat.cast_nonneg _
      linarith

/-- For every list, length minus one bounds its adjacent cost. -/
theorem adjCost_length_sub_one (hα : 1 ≤ α) (hβ : 1 ≤ β) (l : List X) :
    (l.length : ℝ) - 1 ≤ adjCost α β color l := by
  cases l with
  | nil => simp [adjCost]
  | cons a t =>
      have h := adjCost_cons_ge α β color hα hβ a t
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

/-- The elementary bound `H ≥ N - 1`: the benchmark of the sorted order
has `N - 1` adjacent pairs, each costing at least `1`. -/
theorem benchmarkH_ge (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    (instSize X : ℝ) - 1 ≤ benchmarkH α β color := by
  unfold benchmarkH instSize
  have hlen : (sortedList X).length = Fintype.card X := by
    simp [sortedList, Finset.length_sort]
  have h := adjCost_length_sub_one α β color hα hβ (sortedList X)
  rw [hlen] at h
  exact h

/-- The red weighted monochromatic sum `Σ_i α (s_i - 1)`, written as
an adjacent cost over the sorted order: only red-red adjacent pairs
contribute, each `α`. -/
def redAdjWeight (α : ℝ) (color : X → Color) : ℝ :=
  adjCostWith (fun x y => if color x = Color.red ∧ color y = Color.red
    then α else 0) (sortedList X)

/-- The blue weighted monochromatic sum `Σ_j β (t_j - 1)`. -/
def blueAdjWeight (β : ℝ) (color : X → Color) : ℝ :=
  adjCostWith (fun x y => if color x = Color.blue ∧ color y = Color.blue
    then β else 0) (sortedList X)

/-- `lem:Hbounds`, upper bound: `H ≤ max(α, β) (N - 1)`. -/
theorem benchmarkH_le_max (hα : 1 < α) (hβ : 1 < β) :
    benchmarkH α β color
      ≤ max α β * (((instSize X - 1 : ℕ) : ℝ)) := by
  have hlen : (sortedList X).length = Fintype.card X := by
    simp [sortedList, Finset.length_sort]
  have hw : ∀ x y, pairCost α β color x y ≤ max α β := by
    intro x y
    unfold pairCost
    split_ifs with h
    · cases hcol : color x <;> simp [hcol, le_max_left, le_max_right,
        le_of_lt hα, le_of_lt hβ]
    · exact le_trans (le_of_lt hα) (le_max_left α β)
  have h := adjCostWith_le (pairCost α β color) (max α β)
    (le_trans (by linarith) (le_max_left α β)) hw (sortedList X)
  rw [hlen] at h
  unfold benchmarkH instSize
  rw [adjCost_eq_adjCostWith]
  exact h

/-- `lem:Hbounds`, red part: `Σ_i α (s_i - 1) ≤ H`. -/
theorem redAdjWeight_le (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    redAdjWeight α color ≤ benchmarkH α β color := by
  unfold redAdjWeight benchmarkH
  rw [adjCost_eq_adjCostWith]
  apply adjCostWith_le_adjCostWith
  intro x y
  by_cases h : color x = Color.red ∧ color y = Color.red
  · rw [if_pos h]
    unfold pairCost
    rw [if_pos (by rw [h.1, h.2]), h.1]
  · rw [if_neg h]
    exact le_trans (by norm_num) (pairCost_ge_one α β color hα hβ x y)

/-- `lem:Hbounds`, blue part: `Σ_j β (t_j - 1) ≤ H`. -/
theorem blueAdjWeight_le (hα : 1 ≤ α) (hβ : 1 ≤ β) :
    blueAdjWeight β color ≤ benchmarkH α β color := by
  unfold blueAdjWeight benchmarkH
  rw [adjCost_eq_adjCostWith]
  apply adjCostWith_le_adjCostWith
  intro x y
  by_cases h : color x = Color.blue ∧ color y = Color.blue
  · rw [if_pos h]
    unfold pairCost
    rw [if_pos (by rw [h.1, h.2]), h.1]
  · rw [if_neg h]
    exact le_trans (by norm_num) (pairCost_ge_one α β color hα hβ x y)

end Bichromatic
