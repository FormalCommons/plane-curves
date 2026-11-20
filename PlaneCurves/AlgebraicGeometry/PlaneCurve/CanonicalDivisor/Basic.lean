/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Genus.Basic
public import PlaneCurves.FieldTheory.FunctionField.KaehlerDifferential

/-!
# Canonical divisors of a plane curve from adjoints

Let `k` be an algebraically closed field and `C : F = 0` an irreducible projective plane curve of
degree `d` all of whose multiple points are ordinary, with function field `K = k(C)` of genus `g`
and adjoint divisor `E`. A divisor `W` of `K` is *canonical* if its class is Tau Ceti's
`canonicalClass`; by
`PlaneCurves.divisorClass_eq_canonicalClass_iff_exists_kaehlerDifferentialDivisor_eq`
these are exactly the divisors of the nonzero Kähler differentials of `K / k`.

For a line `L` with `F ∤ L`, the divisor `E_{d-3} = (d - 3) div L - E` has degree `2g - 2` and
`ℓ(E_{d-3}) ≥ g` (part of the genus formula), so it is canonical by Stichtenoth's
characterization `TauCeti.divisorClass_eq_canonicalClass_iff`. For a form `G` of degree `d - 3`
with `F ∤ G`, `div G - E` differs from it by the principal divisor of `G / L^{d-3}`, so it is
canonical too; for `d = 3` this says that `-E` is canonical.

## Main results

* `divisorClass_sub_three_zsmul_formDivisor_sub_adjointDivisor_eq_canonicalClass`:
  `(d - 3) div L - E` is canonical for every line `L` with `F ∤ L`.
* `PlaneCurves.Projective.divisorClass_formDivisor_sub_adjointDivisor_eq_canonicalClass`:
  `div G - E` is canonical for every form `G` of degree `d - 3` with `F ∤ G`.
* `PlaneCurves.Projective.divisorClass_neg_adjointDivisor_eq_canonicalClass`: for a cubic, `-E`
  is canonical.
* `PlaneCurves.Projective.exists_kaehlerDifferentialDivisor_eq_formDivisor_sub_adjointDivisor`:
  `div G - E` is the divisor of a nonzero Kähler differential.

The degree `2g - 2` and the dimension `ℓ(W) = g` of a canonical divisor `W`
come from `TauCeti.isRiemannRochDivisor_of_divisorClass_eq_canonicalClass` with
`TauCeti.Divisor.IsRiemannRochDivisor.degree_eq` and `.dim_eq`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §8.5
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][Stichtenoth2009], §1.6
-/

public section

open MvPolynomial TauCeti TauCeti.AlgebraicGeometry

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
  {hF : F.IsHomogeneous d} [Fact (Irreducible F)]
  (hord : ∀ P, IsMultiplePoint F P → IsOrdinaryMultiplePoint F P)

include hord

/-- **`E_{d-3}` is canonical**: for a line `L` with `F ∤ L`, the divisor `(d - 3) div L - E` lies
in the canonical class of `k(C)`. -/
theorem divisorClass_sub_three_zsmul_formDivisor_sub_adjointDivisor_eq_canonicalClass
    {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1) (hFL : ¬ F ∣ L) :
    (Place.orderSystem (functionField.isFunctionField hF)).divisorClass
        (((d : ℤ) - 3) • formDivisor hF hL - adjointDivisor hF) =
      canonicalClass (functionField.isFunctionField hF) isIntegrallyClosedIn_of_isAlgClosed :=
  (divisorClass_eq_canonicalClass_iff _ _ _).2
    ⟨degree_zsmul_formDivisor_sub_adjointDivisor hord hL hFL,
      genus_le_dim_zsmul_formDivisor_sub_adjointDivisor hord hL hFL⟩

/-- **Adjoints of degree `d - 3` cut out canonical divisors**: for a form `G` of degree `d - 3`
with `F ∤ G`, where `3 ≤ d`, the divisor `div G - E` lies in the canonical class of `k(C)`. -/
theorem divisorClass_formDivisor_sub_adjointDivisor_eq_canonicalClass (hd : 3 ≤ d)
    {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous (d - 3)) (hFG : ¬ F ∣ G) :
    (Place.orderSystem (functionField.isFunctionField hF)).divisorClass
        (formDivisor hF hG - adjointDivisor hF) =
      canonicalClass (functionField.isFunctionField hF) isIntegrallyClosedIn_of_isAlgClosed := by
  have hirr : Irreducible F := Fact.out
  obtain ⟨i, hi⟩ := projectivePlaneCurve.exists_not_dvd_X hirr
  have hL : (X i : MvPolynomial (Fin 3) k).IsHomogeneous 1 := isHomogeneous_X k i
  have hLn : (X i ^ (d - 3) : MvPolynomial (Fin 3) k).IsHomogeneous (d - 3) := by
    simpa using hL.pow (d - 3)
  have hFLn : ¬ F ∣ X i ^ (d - 3) := fun h ↦ hi (hirr.prime.dvd_of_dvd_pow h)
  have hdiv : formDivisor hF hLn = ((d : ℤ) - 3) • formDivisor hF hL := by
    rw [formDivisor_congr hLn (hL.pow (d - 3)) rfl, formDivisor_pow hL hi, ← natCast_zsmul,
      Nat.cast_sub hd, Nat.cast_ofNat]
  have hprin := principal_formQuotient (hF := hF) hG hLn hFG hFLn
  rw [hdiv] at hprin
  have h0 : (Place.orderSystem (functionField.isFunctionField hF)).divisorClass
      (formDivisor hF hG - ((d : ℤ) - 3) • formDivisor hF hL) = 0 :=
    (Divisor.divisorClass_eq_zero_iff _).2 ⟨_, hprin⟩
  rw [show formDivisor hF hG - adjointDivisor hF =
      (formDivisor hF hG - ((d : ℤ) - 3) • formDivisor hF hL) +
        (((d : ℤ) - 3) • formDivisor hF hL - adjointDivisor hF) by abel,
    map_add, h0, zero_add,
    divisorClass_sub_three_zsmul_formDivisor_sub_adjointDivisor_eq_canonicalClass hord hL hi]

/-- **For a cubic, `-E` is canonical**: if `d = 3`, the divisor `-E` lies in the canonical class
of `k(C)`. -/
theorem divisorClass_neg_adjointDivisor_eq_canonicalClass (hd : d = 3) :
    (Place.orderSystem (functionField.isFunctionField hF)).divisorClass (-adjointDivisor hF) =
      canonicalClass (functionField.isFunctionField hF) isIntegrallyClosedIn_of_isAlgClosed := by
  obtain ⟨i, hi⟩ := projectivePlaneCurve.exists_not_dvd_X (Fact.out : Irreducible F)
  have h := divisorClass_sub_three_zsmul_formDivisor_sub_adjointDivisor_eq_canonicalClass
    (hF := hF) hord (isHomogeneous_X k i) hi
  subst hd
  simpa using h

/-- **Adjoints of degree `d - 3` cut out divisors of differentials**: for a form `G` of degree
`d - 3` with `F ∤ G`, where `3 ≤ d`, there is a nonzero Kähler differential `ω` of `k(C) / k`
with `div (ω) = div G - E`. -/
theorem exists_kaehlerDifferentialDivisor_eq_formDivisor_sub_adjointDivisor (hd : 3 ≤ d)
    {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous (d - 3)) (hFG : ¬ F ∣ G) :
    ∃ (ω : Ω[functionField hF⁄k]) (hω : ω ≠ 0),
      kaehlerDifferentialDivisor (functionField.isFunctionField hF)
          isIntegrallyClosedIn_of_isAlgClosed ω hω =
        formDivisor hF hG - adjointDivisor hF :=
  (divisorClass_eq_canonicalClass_iff_exists_kaehlerDifferentialDivisor_eq _ _ _).1
    (divisorClass_formDivisor_sub_adjointDivisor_eq_canonicalClass hord hd hG hFG)

end PlaneCurves.Projective

end
