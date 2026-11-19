/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.RingTheory.Japanese

/-!
# Integral closure of a Japanese domain in a field containing it

Tau Ceti's `TauCeti.Ring.IsJapanese.finite_integralClosure` asks for a field `L` over a model `K`
of the fraction field of the Japanese domain `R`. This file drops `K`: for any field `L` into which
`R` embeds, essentially of finite type over `R`, the integral closure of `R` in `L` is a finite
`R`-module. The fraction field of `R` maps into `L`, and `L` is essentially of finite type over it.

* `TauCeti.Ring.IsJapanese.finite_integralClosure_of_injective`.
-/

public section

namespace TauCeti.Ring.IsJapanese

/-- The integral closure of a Japanese domain `R` in a field `L` is a finite `R`-module, for `L`
essentially of finite type over `R` and `R → L` injective. -/
theorem finite_integralClosure_of_injective {R L : Type*} [CommRing R] [IsDomain R] [IsJapanese R]
    [Field L] [Algebra R L] [Algebra.EssFiniteType R L]
    (h : Function.Injective (algebraMap R L)) :
    Module.Finite R (integralClosure R L) := by
  let : Algebra (FractionRing R) L := (IsFractionRing.lift (K := FractionRing R) h).toAlgebra
  have : IsScalarTower R (FractionRing R) L :=
    .of_algebraMap_eq fun x ↦ (IsFractionRing.lift_algebraMap h x).symm
  have : Algebra.EssFiniteType (FractionRing R) L := .of_comp R _ _
  exact finite_integralClosure (FractionRing R) L

end TauCeti.Ring.IsJapanese

end
