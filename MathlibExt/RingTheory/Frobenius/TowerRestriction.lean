/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Frobenius

/-!
# Powers and restrictions of arithmetic Frobenius elements

This module proves the two calculations behind ATLAS `NumberTheoryI`,
Proposition 7.22 (Frobenius elements in towers and restrictions), in
Mathlib's `IsArithFrobAt` API. In the book, for a Galois extension `L / K`
with an unramified prime `𝔮`, the Frobenius element for an intermediate field
`E` is the `[F_{𝔮_E} : F_𝔭]`-th power of the Frobenius element for `K`, and
its restriction to a Galois subextension is the Frobenius element there.
Here the two facts are stated abstractly, exactly as in the source's
tower-and-restriction lemma: a power of a Frobenius congruence is a Frobenius
congruence with the powered exponent, and a Frobenius congruence restricts
along a compatible algebra homomorphism and group homomorphism.

## Main results

* `AlgHom.IsArithFrobAt.pow_apply_sub_pow_mem`: if `φ x - x ^ q ∈ Q` for all
  `x`, then `(φ ^ f) x - x ^ q ^ f ∈ Q`.
* `IsArithFrobAt.pow_smul_sub_pow_mem`: the group-action form, with
  `q = Nat.card (R ⧸ Q.under R)`.
* `IsArithFrobAt.comap`: a Frobenius congruence restricts to `(ρ σ)` at
  `Q.comap ι` along a compatible pair `(ι, ρ)`.
* `Ideal.mem_inertia_of_forall_smul_sub_pow_mem`: two elements satisfying
  the same powered congruence differ by an element of the inertia subgroup.
* `IsArithFrobAt.pow_eq_of_forall_smul_sub_pow_mem_of_inertia_eq_bot` and
  `IsArithFrobAt.eq_comap_of_forall_smul_sub_pow_mem_of_inertia_eq_bot`:
  under trivial inertia (the book's unramified hypothesis), the power and
  restriction congruences identify the Frobenius element itself.
-/

@[expose] public section

namespace Ideal

variable {S : Type*} [CommRing S] {G : Type*} [Group G]
  [MulSemiringAction G S] {Q : Ideal S} {σ τ : G} {r : ℕ}

/-- If `a - b ∈ I`, then `a ^ n - b ^ n ∈ I` for every `n`. -/
private theorem pow_sub_pow_mem (I : Ideal S) {a b : S} (h : a - b ∈ I)
    (n : ℕ) : a ^ n - b ^ n ∈ I := by
  have h0 : Ideal.Quotient.mk I (a ^ n - b ^ n) = 0 := by
    simp only [map_sub, map_pow, Ideal.Quotient.eq.mpr h, sub_self]
  exact Ideal.Quotient.eq_zero_iff_mem.mp h0

/-- Two elements satisfying the same powered congruence differ by an
element of the inertia subgroup of `Q`. -/
theorem mem_inertia_of_forall_smul_sub_pow_mem
    (hσ : ∀ x : S, σ • x - x ^ r ∈ Q) (hτ : ∀ x : S, τ • x - x ^ r ∈ Q) :
    σ * τ⁻¹ ∈ Q.inertia G := by
  rw [Ideal.mem_inertia]
  intro x
  have h1 := hσ (τ⁻¹ • x)
  have h2 := hτ (τ⁻¹ • x)
  have hτy : τ • (τ⁻¹ • x) = x := by
    rw [← mul_smul, mul_inv_cancel, one_smul]
  have hgoal : (σ * τ⁻¹) • x - x
      = (σ • (τ⁻¹ • x) - (τ⁻¹ • x) ^ r) -
        (τ • (τ⁻¹ • x) - (τ⁻¹ • x) ^ r) := by
    rw [mul_smul, hτy]
    abel
  rw [hgoal]
  exact Q.sub_mem h1 h2

end Ideal

namespace AlgHom.IsArithFrobAt

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {φ : S →ₐ[R] S} {Q : Ideal S}

/-- Powers of an arithmetic Frobenius map satisfy the powered congruence:
if `φ x - x ^ q ∈ Q` for all `x`, then `(φ ^ f) x - x ^ q ^ f ∈ Q`. -/
theorem pow_apply_sub_pow_mem (h : φ.IsArithFrobAt Q) :
    ∀ (f : ℕ) (x : S),
      (φ ^ f) x - x ^ (Nat.card (R ⧸ Q.under R)) ^ f ∈ Q := by
  intro f
  induction f with
  | zero =>
    intro x
    simp
  | succ n ih =>
    intro x
    have e1 : (φ ^ (n + 1)) x = (φ ^ n) (φ x) := by
      rw [pow_succ, AlgHom.mul_apply]
    have e2 : x ^ (Nat.card (R ⧸ Q.under R)) ^ (n + 1)
        = (x ^ Nat.card (R ⧸ Q.under R)) ^ (Nat.card (R ⧸ Q.under R)) ^ n := by
      rw [pow_succ, mul_comm, pow_mul]
    rw [e1, e2]
    have h1 := ih (φ x)
    have h2 := Ideal.pow_sub_pow_mem Q (h x) ((Nat.card (R ⧸ Q.under R)) ^ n)
    have hsum : (φ ^ n) (φ x) - (φ x) ^ (Nat.card (R ⧸ Q.under R)) ^ n +
        ((φ x) ^ (Nat.card (R ⧸ Q.under R)) ^ n -
          (x ^ Nat.card (R ⧸ Q.under R)) ^
            (Nat.card (R ⧸ Q.under R)) ^ n) ∈ Q :=
      Q.add_mem h1 h2
    convert hsum using 1
    abel

end AlgHom.IsArithFrobAt

namespace IsArithFrobAt

variable {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]
  {G H : Type*} [Group G] [Group H]
  [MulSemiringAction G B] [SMulCommClass G R B]
  [MulSemiringAction H C] [SMulCommClass H R C]
  {σ : G} {Q : Ideal B}

/-- Powers of an arithmetic Frobenius element satisfy the powered
congruence: if `σ • x - x ^ q ∈ Q` for all `x`, with
`q = Nat.card (R ⧸ Q.under R)`, then
`(σ ^ f) • x - x ^ q ^ f ∈ Q`. -/
theorem pow_smul_sub_pow_mem (h : IsArithFrobAt R σ Q) :
    ∀ (f : ℕ) (x : B),
      (σ ^ f) • x - x ^ (Nat.card (R ⧸ Q.under R)) ^ f ∈ Q := by
  have h' : ∀ x : B,
      σ • x - x ^ Nat.card (R ⧸ Q.under R) ∈ Q := h
  intro f
  induction f with
  | zero =>
    intro x
    simp
  | succ n ih =>
    intro x
    have e1 : (σ ^ (n + 1)) • x = (σ ^ n) • (σ • x) := by
      rw [pow_succ, mul_smul]
    have e2 : x ^ (Nat.card (R ⧸ Q.under R)) ^ (n + 1)
        = (x ^ Nat.card (R ⧸ Q.under R)) ^ (Nat.card (R ⧸ Q.under R)) ^ n := by
      rw [pow_succ, mul_comm, pow_mul]
    rw [e1, e2]
    have h1 := ih (σ • x)
    have h2 := Ideal.pow_sub_pow_mem Q (h' x) ((Nat.card (R ⧸ Q.under R)) ^ n)
    have hsum : (σ ^ n) • (σ • x) - (σ • x) ^ (Nat.card (R ⧸ Q.under R)) ^ n +
        ((σ • x) ^ (Nat.card (R ⧸ Q.under R)) ^ n -
          (x ^ Nat.card (R ⧸ Q.under R)) ^
            (Nat.card (R ⧸ Q.under R)) ^ n) ∈ Q :=
      Q.add_mem h1 h2
    convert hsum using 1
    abel

/-- A Frobenius congruence restricts along a compatible pair: if
`ι : C →ₐ[R] B` and `ρ : G →* H` satisfy `ι (ρ g • c) = g • ι c`, and `σ`
is a Frobenius at `Q`, then `ρ σ` is a Frobenius at `Q.comap ι`. -/
theorem comap (ι : C →ₐ[R] B) (ρ : G →* H)
    (hcompat : ∀ (g : G) (c : C), ι (ρ g • c) = g • ι c)
    (h : IsArithFrobAt R σ Q) : IsArithFrobAt R (ρ σ) (Q.comap ι) := by
  have hunder : (Q.comap ι).under R = Q.under R := by
    rw [Ideal.under, Ideal.under]
    ext x
    simp only [Ideal.mem_comap, ι.commutes]
  intro c
  show (ρ σ) • c - c ^ Nat.card (R ⧸ (Q.comap ι).under R) ∈ Q.comap ι
  rw [hunder, Ideal.mem_comap]
  have hmap : ι ((ρ σ) • c - c ^ Nat.card (R ⧸ Q.under R))
      = σ • ι c - (ι c) ^ Nat.card (R ⧸ Q.under R) := by
    rw [map_sub, map_pow, hcompat]
  rw [hmap]
  exact h (ι c)

/-- If `σ` is a Frobenius at `Q` and `τ` satisfies the powered congruence
with exponent `q ^ f`, then `σ ^ f = τ` when the inertia subgroup of `Q` is
trivial. This is the equality form of the tower statement of
Proposition 7.22 under its unramified hypothesis. -/
theorem pow_eq_of_forall_smul_sub_pow_mem_of_inertia_eq_bot
    {f : ℕ} {τ : G}
    (h : IsArithFrobAt R σ Q)
    (hτ : ∀ x : B, τ • x - x ^ (Nat.card (R ⧸ Q.under R)) ^ f ∈ Q)
    (hbot : Q.inertia G = ⊥) : σ ^ f = τ := by
  have hpow := h.pow_smul_sub_pow_mem f
  have hmem := Ideal.mem_inertia_of_forall_smul_sub_pow_mem hpow hτ
  rw [hbot] at hmem
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)

/-- If `σ` is a Frobenius at `Q` and `τ` satisfies the Frobenius congruence
at `Q.comap ι`, then `ρ σ = τ` when the inertia subgroup of `Q.comap ι` is
trivial. This is the equality form of the restriction statement of
Proposition 7.22 under its unramified hypothesis. -/
theorem eq_comap_of_forall_smul_sub_pow_mem_of_inertia_eq_bot
    (ι : C →ₐ[R] B) (ρ : G →* H)
    (hcompat : ∀ (g : G) (c : C), ι (ρ g • c) = g • ι c)
    (h : IsArithFrobAt R σ Q)
    {τ : H}
    (hτ : ∀ x : C, τ • x - x ^ Nat.card (R ⧸ (Q.comap ι).under R) ∈ Q.comap ι)
    (hbot : (Q.comap ι).inertia H = ⊥) : ρ σ = τ := by
  have hrest : ∀ x : C,
      (ρ σ) • x - x ^ Nat.card (R ⧸ (Q.comap ι).under R) ∈ Q.comap ι :=
    h.comap ι ρ hcompat
  have hmem := Ideal.mem_inertia_of_forall_smul_sub_pow_mem hrest hτ
  rw [hbot] at hmem
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)

end IsArithFrobAt
