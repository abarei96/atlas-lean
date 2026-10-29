/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.UnramifiedDiscriminant

@[expose] public section

/-!
# Direct Dedekind-extension clients

These clients use only the two rings and separability of their fraction rings.
They require no auxiliary fraction-field presentations or compatible towers.
-/

set_option autoImplicit false

attribute [local instance] FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

namespace UnramifiedDiscriminantDirectTest

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]
  [Module.Finite A B]
  [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

/-- Apply the discriminant criterion without choosing fraction-field presentations. -/
example (𝔭 : IsDedekindDomain.HeightOneSpectrum A) :
    (∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum B, 𝔮.asIdeal.LiesOver 𝔭.asIdeal →
      Algebra.IsUnramifiedAt A 𝔮.asIdeal) ↔
    ¬ (𝔭.asIdeal ∣ Ideal.discriminantIdeal A B) :=
  Ideal.isUnramifiedAt_iff_not_dvd_discriminantIdeal A B 𝔭

/-- The forward implication accepts the same direct extension data. -/
example (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (hall : ∀ 𝔮 : IsDedekindDomain.HeightOneSpectrum B, 𝔮.asIdeal.LiesOver 𝔭.asIdeal →
      Algebra.IsUnramifiedAt A 𝔮.asIdeal) :
    ¬ (𝔭.asIdeal ∣ Ideal.discriminantIdeal A B) :=
  Ideal.not_dvd_discriminantIdeal_of_isUnramifiedAt A B 𝔭 hall

/-- The reverse implication accepts the same direct extension data. -/
example (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (hndvd : ¬ (𝔭.asIdeal ∣ Ideal.discriminantIdeal A B))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B) (hlies : 𝔮.asIdeal.LiesOver 𝔭.asIdeal) :
    Algebra.IsUnramifiedAt A 𝔮.asIdeal :=
  Ideal.isUnramifiedAt_of_not_dvd_discriminantIdeal A B 𝔭 hndvd 𝔮 hlies

end UnramifiedDiscriminantDirectTest
