import Mathlib

/-
Scan and search costs for the randomized splice sort.

Proved: pre-split domination (runs scanned before a split contain
at most one run, no longer than the run being split --- so their
cost is absorbed), the comparison count of binary search on a
sorted list of length `q`, and the total binary-search cost over a
list of insertions. These are the cost-side inputs of the paper's
records analysis.
-/

set_option linter.unusedVariables false

namespace SpliceSort

/-- Pre-split domination: the runs preceding a run `C` in a scan are
at most one run, no longer than `C`, so their total length is
dominated by `C`'s length. -/
theorem presplit_domination {X : Type*} (pre : List (List X)) (C : List X)
    (hcount : pre.length ≤ 1) (hsize : ∀ D ∈ pre, D.length ≤ C.length) :
    (pre.map List.length).sum ≤ C.length := by
  match pre with
  | [] => simp
  | [D] =>
    have h := hsize D (by simp)
    simpa using h
  | D :: E :: rest =>
    simp only [List.length_cons] at hcount
    omega

/-- Number of comparisons of binary search on a sorted list of
length `q`. -/
def searchCost : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 1 + searchCost ((n + 2) / 2)
termination_by n => n
decreasing_by omega

/-- Binary search on `q` positions costs at most `log2 q + 1`
comparisons. -/
theorem searchCost_le : ∀ q : ℕ, searchCost q ≤ Nat.log2 q + 1 := by
  intro q
  induction' q using Nat.strong_induction_on with q ih
  rcases q with _ | _ | n
  · simp [searchCost]
  · simp [searchCost]
  · have hlt : (n + 2) / 2 < n + 2 := Nat.log2_terminates (n + 2) (by omega)
    have hIH := ih ((n + 2) / 2) hlt
    have hlog : Nat.log2 (n + 2) = Nat.log2 ((n + 2) / 2) + 1 := by
      rw [Nat.log2_def, if_pos (by omega : 2 ≤ n + 2)]
    rw [searchCost, hlog]
    omega

/-- Binary-search cost bounded by the cost at any larger length. -/
theorem searchCost_le_of_le : ∀ {q m : ℕ}, q ≤ m →
    searchCost q ≤ Nat.log2 m + 1 := by
  intro q m hqm
  induction' q using Nat.strong_induction_on with q ih generalizing m
  rcases q with _ | _ | n
  · simp [searchCost]
  · simp [searchCost]
  · have hlt : (n + 2) / 2 < n + 2 := Nat.log2_terminates (n + 2) (by omega)
    have hle : (n + 2) / 2 ≤ m / 2 := Nat.div_le_div_right hqm
    have hIH := ih ((n + 2) / 2) hlt hle
    have hm : 2 ≤ m := by omega
    have hlog : Nat.log2 m = Nat.log2 (m / 2) + 1 := by
      rw [Nat.log2_def, if_pos hm]
    have hdiv : searchCost ((n + 2) / 2) ≤ Nat.log2 (m / 2) + 1 := by
      have hIH := ih ((n + 2) / 2) hlt hle
      have hle2 : (n + 2) / 2 ≤ m / 2 := hle
      have := ih ((n + 2) / 2) hlt hle2
      omega
    rw [searchCost, hlog]
    omega

/-- Total binary-search cost over a list of insertion lengths, each
at most `m`. -/
theorem total_searchCost_le {m : ℕ} (qs : List ℕ)
    (hmax : ∀ q ∈ qs, q ≤ m) :
    (qs.map searchCost).sum ≤ qs.length * (Nat.log2 m + 1) := by
  induction qs with
  | nil => simp
  | cons q rest ih =>
    have hq := hmax q (by simp)
    have hrest : ∀ x ∈ rest, x ≤ m := fun x hx => hmax x (by simp [hx])
    have h := ih hrest
    have hle : searchCost q ≤ Nat.log2 m + 1 := searchCost_le_of_le hq
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hring : (rest.length + 1) * (Nat.log2 m + 1)
        = rest.length * (Nat.log2 m + 1) + (Nat.log2 m + 1) := by ring
    omega

end SpliceSort
