/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Frobenius.TowerRestriction

/-!
# Tests for powers and restrictions of arithmetic Frobenius elements

These examples exercise the six public theorems of
`MathlibExt.RingTheory.Frobenius.TowerRestriction` (the tower-and-restriction
calculations of ATLAS `NumberTheoryI`, Proposition 7.22): the power and
restriction congruences, the inertia bridge, and the two equality forms
under trivial inertia, plus a concrete check of the power congruence for
the identity map on `ZMod 2`, where it is Fermat's little theorem iterated.
-/

@[expose] public section

variable {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]
  {G H : Type*} [Group G] [Group H]
  [MulSemiringAction G B] [SMulCommClass G R B]
  [MulSemiringAction H C] [SMulCommClass H R C]

/-- The power congruence applies generically. -/
example {σ : G} {Q : Ideal B} (h : IsArithFrobAt R σ Q) (f : ℕ) (x : B) :
    (σ ^ f) • x - x ^ (Nat.card (R ⧸ Q.under R)) ^ f ∈ Q :=
  h.pow_smul_sub_pow_mem f x

/-- The `AlgHom` power congruence applies generically. -/
example {φ : B →ₐ[R] B} {Q : Ideal B} (h : φ.IsArithFrobAt Q) (f : ℕ)
    (x : B) :
    (φ ^ f) x - x ^ (Nat.card (R ⧸ Q.under R)) ^ f ∈ Q :=
  h.pow_apply_sub_pow_mem f x

/-- The restriction congruence applies generically. -/
example {σ : G} {Q : Ideal B} (ι : C →ₐ[R] B) (ρ : G →* H)
    (hcompat : ∀ (g : G) (c : C), ι (ρ g • c) = g • ι c)
    (h : IsArithFrobAt R σ Q) :
    IsArithFrobAt R (ρ σ) (Q.comap ι) :=
  h.comap ι ρ hcompat

/-- Two elements satisfying the same powered congruence differ by an
element of inertia. -/
example {σ τ : G} {Q : Ideal B} {r : ℕ}
    (hσ : ∀ x : B, σ • x - x ^ r ∈ Q) (hτ : ∀ x : B, τ • x - x ^ r ∈ Q) :
    σ * τ⁻¹ ∈ Q.inertia G :=
  Ideal.mem_inertia_of_forall_smul_sub_pow_mem hσ hτ

/-- Under trivial inertia, a Frobenius power is the unique element
satisfying the powered congruence. -/
example {σ : G} {Q : Ideal B} {f : ℕ} {τ : G}
    (h : IsArithFrobAt R σ Q)
    (hτ : ∀ x : B, τ • x - x ^ (Nat.card (R ⧸ Q.under R)) ^ f ∈ Q)
    (hbot : Q.inertia G = ⊥) : σ ^ f = τ :=
  h.pow_eq_of_forall_smul_sub_pow_mem_of_inertia_eq_bot hτ hbot

/-- Under trivial inertia, a restricted Frobenius is the unique element
satisfying the restricted congruence. -/
example {σ : G} {Q : Ideal B} (ι : C →ₐ[R] B) (ρ : G →* H)
    (hcompat : ∀ (g : G) (c : C), ι (ρ g • c) = g • ι c)
    (h : IsArithFrobAt R σ Q) {τ : H}
    (hτ : ∀ x : C, τ • x - x ^ Nat.card (R ⧸ (Q.comap ι).under R) ∈ Q.comap ι)
    (hbot : (Q.comap ι).inertia H = ⊥) : ρ σ = τ :=
  h.eq_comap_of_forall_smul_sub_pow_mem_of_inertia_eq_bot ι ρ hcompat hτ hbot

/-- The residue-field cardinality at `⊥` in `ZMod 2` over itself is `2`. -/
theorem natCard_quotient_under_bot_zmod_two :
    Nat.card ((ZMod 2) ⧸ (⊥ : Ideal (ZMod 2)).under (ZMod 2)) = 2 := by
  have hunder : (⊥ : Ideal (ZMod 2)).under (ZMod 2) = ⊥ := by
    rw [Ideal.under]
    exact Ideal.comap_bot_of_injective (algebraMap (ZMod 2) (ZMod 2))
      (fun _ _ h => h)
  rw [hunder]
  rw [Nat.card_congr (RingEquiv.quotientBot (ZMod 2)).toEquiv,
    Nat.card_eq_fintype_card]
  exact ZMod.card 2

/-- The identity map on `ZMod 2` is an arithmetic Frobenius at `⊥`:
this is `x = x ^ 2` in `ZMod 2`. -/
theorem id_isArithFrobAt_bot_zmod_two :
    (AlgHom.id (ZMod 2) (ZMod 2)).IsArithFrobAt (⊥ : Ideal (ZMod 2)) := by
  intro x
  rw [natCard_quotient_under_bot_zmod_two]
  simp only [AlgHom.id_apply]
  rw [Ideal.mem_bot]
  fin_cases x <;> decide

/-- The power congruence for the identity map on `ZMod 2` at exponent `3`:
`x - x ^ 8 = 0` in `ZMod 2`. -/
example (x : ZMod 2) :
    ((AlgHom.id (ZMod 2) (ZMod 2)) ^ 3) x -
      x ^ (Nat.card ((ZMod 2) ⧸ (⊥ : Ideal (ZMod 2)).under (ZMod 2))) ^ 3
      ∈ (⊥ : Ideal (ZMod 2)) := by
  have h := id_isArithFrobAt_bot_zmod_two.pow_apply_sub_pow_mem 3 x
  rwa [natCard_quotient_under_bot_zmod_two] at h ⊢

end
