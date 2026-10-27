/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.Ideal.Over

import Mathlib.Algebra.BigOperators.Associated

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

@[expose] public section

/-!
# Unramified above a prime iff the prime does not divide the discriminant ideal

ATLAS `NumberTheoryI`, Theorem 12.19 (discriminant half). Let `A` be a Dedekind
domain with fraction field `K`, let `L / K` be a finite separable extension, and
let `B` be the integral closure of `A` in `L`. For a nonzero prime `𝔭` of `A`,
the extension is unramified at every prime `𝔮` of `B` lying above `𝔭` if and only
if `𝔭` does not divide the discriminant ideal of `B / A`.

The discriminant ideal is stated here in `spanNorm` form,
`Ideal.spanNorm A (differentIdeal A B)`, which is `Ideal.relNorm A`
(`Ideal.spanNorm_eq`). The different-ideal half of the book's statement,
`𝔮 ∤ differentIdeal A B ↔ Algebra.IsUnramifiedAt A 𝔮`, is Mathlib's
`not_dvd_differentIdeal_iff`, used as a lemma, not re-proved.

The proof does not go through the book's lattice-discriminant counting
argument: the forward direction factors the different ideal into primes
(`Ideal.prod_normalizedFactors_eq_self`) and uses that the relative norm of a
prime above `𝔭` is a power of `𝔭` (`Ideal.exists_relNorm_eq_pow_of_isPrime`);
the reverse direction uses `Ideal.relNorm_le_comap` together with the same
power statement.

## Main results

* `Ideal.isUnramifiedAt_iff_not_dvd_spanNorm_differentIdeal`: the
  discriminant-half of Theorem 12.19.
* `Ideal.isUnramifiedAt_of_not_dvd_spanNorm_differentIdeal` and
  `Ideal.not_dvd_spanNorm_differentIdeal_of_isUnramifiedAt`: the two
  implications separately.
-/

universe u

namespace Ideal

variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsFractionRing A K]
  [FiniteDimensional K L] [IsIntegralClosure B A L] [Algebra.IsSeparable K L]
  [IsFractionRing B L]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [Module.Finite A B]

omit [FiniteDimensional K L] [IsIntegralClosure B A L] in
include K L in
/-- Separability of the fraction fields, transported from `L / K` along the
fraction-ring equivalences. This is the instance Mathlib's different-ideal
API (`not_dvd_differentIdeal_iff`) requires. -/
private theorem isSeparable_fractionRing :
    Algebra.IsSeparable (FractionRing A) (FractionRing B) := by
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
      ↑(FractionRing.algEquiv A K).symm.toRingEquiv =
        RingHom.comp ↑(FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
  exact Algebra.IsSeparable.of_equiv_equiv _ _ H

omit [FiniteDimensional K L] [IsIntegralClosure B A L] in
include K L in
/-- If the extension is unramified at every prime above `𝔭`, then `𝔭` does not
divide the discriminant ideal. -/
theorem not_dvd_spanNorm_differentIdeal_of_isUnramifiedAt
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (hall : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum B, 𝔮.asIdeal.LiesOver 𝔭.asIdeal →
      Algebra.IsUnramifiedAt A 𝔮.asIdeal) :
    ¬ (𝔭.asIdeal ∣ spanNorm A (differentIdeal A B)) := by
  have hsep : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    isSeparable_fractionRing A K L B
  have hDne : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
  rw [spanNorm_eq]
  intro hdvd
  have hprod : relNorm A (differentIdeal A B) =
      ((UniqueFactorizationMonoid.normalizedFactors (differentIdeal A B)).map
        (relNorm A)).prod := by
    conv_lhs => rw [← prod_normalizedFactors_eq_self hDne]
    rw [map_multiset_prod]
  rw [hprod] at hdvd
  obtain ⟨Q, hQmem, hQdvd⟩ := 𝔭.prime.exists_mem_multiset_map_dvd hdvd
  have hQprime : Q.IsPrime := (mem_normalizedFactors_iff hDne).mp hQmem |>.1
  have hQle : differentIdeal A B ≤ Q := (mem_normalizedFactors_iff hDne).mp hQmem |>.2
  have hQdvdD : Q ∣ differentIdeal A B := Ideal.dvd_iff_le.mpr hQle
  have hQne : Q ≠ ⊥ := by
    intro hQ
    rw [hQ] at hQle
    exact hDne (le_antisymm hQle bot_le)
  obtain ⟨s, hs⟩ := exists_relNorm_eq_pow_of_isPrime Q (Q.under A)
  rw [hs] at hQdvd
  have hp_dvd_under : 𝔭.asIdeal ∣ Q.under A := 𝔭.prime.dvd_of_dvd_pow hQdvd
  have hunder_max : (Q.under A).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime
      (fun h => hQne (Ideal.eq_bot_of_under_eq_bot h)) inferInstance
  have heq : Q.under A = 𝔭.asIdeal :=
    hunder_max.eq_of_le 𝔭.isPrime.ne_top (Ideal.dvd_iff_le.mp hp_dvd_under)
  have hQlies : Q.LiesOver 𝔭.asIdeal := ⟨heq.symm⟩
  have hunram := hall ⟨Q, hQprime, hQne⟩ hQlies
  exact (not_dvd_differentIdeal_iff.mpr hunram) hQdvdD

omit [FiniteDimensional K L] [IsIntegralClosure B A L] in
include K L in
/-- If `𝔭` does not divide the discriminant ideal, then the extension is
unramified at every prime above `𝔭`. -/
theorem isUnramifiedAt_of_not_dvd_spanNorm_differentIdeal
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (hndvd : ¬ (𝔭.asIdeal ∣ spanNorm A (differentIdeal A B)))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B) (hlies : 𝔮.asIdeal.LiesOver 𝔭.asIdeal) :
    Algebra.IsUnramifiedAt A 𝔮.asIdeal := by
  have hsep : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    isSeparable_fractionRing A K L B
  rw [spanNorm_eq] at hndvd
  rw [← not_dvd_differentIdeal_iff]
  intro hqdvd
  apply hndvd
  have h1 : 𝔭.asIdeal ∣ relNorm A 𝔮.asIdeal := by
    obtain ⟨s, hs⟩ := exists_relNorm_eq_pow_of_isPrime 𝔮.asIdeal 𝔭.asIdeal
    have hle : relNorm A 𝔮.asIdeal ≤ 𝔭.asIdeal := by
      calc relNorm A 𝔮.asIdeal
          ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal := relNorm_le_comap A 𝔮.asIdeal
        _ = 𝔭.asIdeal := by rw [← Ideal.under_def]; exact hlies.over.symm
    rw [hs] at hle
    have hspos : 0 < s := by
      by_contra h
      push Not at h
      rw [Nat.le_zero.mp h, pow_zero, one_eq_top] at hle
      exact 𝔭.isPrime.ne_top (top_unique hle)
    rw [hs]
    exact dvd_pow_self _ hspos.ne'
  have h2 : relNorm A 𝔮.asIdeal ∣ relNorm A (differentIdeal A B) := by
    rw [Ideal.dvd_iff_le]
    exact relNorm_mono A (Ideal.dvd_iff_le.mp hqdvd)
  exact dvd_trans h1 h2

omit [FiniteDimensional K L] [IsIntegralClosure B A L] in
include K L in
/-- Theorem 12.19, discriminant half: the extension is unramified at every
prime above `𝔭` if and only if `𝔭` does not divide the discriminant ideal. -/
theorem isUnramifiedAt_iff_not_dvd_spanNorm_differentIdeal
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A) :
    (∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum B, 𝔮.asIdeal.LiesOver 𝔭.asIdeal →
      Algebra.IsUnramifiedAt A 𝔮.asIdeal) ↔
    ¬ (𝔭.asIdeal ∣ spanNorm A (differentIdeal A B)) :=
  ⟨not_dvd_spanNorm_differentIdeal_of_isUnramifiedAt A K L B 𝔭,
   fun hndvd 𝔮 hlies =>
     isUnramifiedAt_of_not_dvd_spanNorm_differentIdeal A K L B 𝔭 hndvd 𝔮 hlies⟩

end Ideal
