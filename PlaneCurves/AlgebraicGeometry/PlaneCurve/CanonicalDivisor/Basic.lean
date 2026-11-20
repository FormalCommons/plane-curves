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
* `PlaneCurves.Projective.nonneg_and_divisorClass_eq_canonicalClass_iff`: the effective canonical
  divisors are the `div G - E` for the nonzero adjoints `G` of degree `d - 3`.
* `PlaneCurves.Projective.finrank_adjointSubmodule_sub_three`: the adjoints of degree `d - 3`
  form a space of dimension `g`.

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

omit hord in
/-- For `3 ≤ d`, the natural multiple `(d - 3) • div L` is `((d : ℤ) - 3) • div L`. -/
private theorem nsmul_formDivisor_sub_three (hd : 3 ≤ d) {L : MvPolynomial (Fin 3) k}
    (hL : L.IsHomogeneous 1) :
    (d - 3) • formDivisor hF hL = ((d : ℤ) - 3) • formDivisor hF hL := by
  rw [← natCast_zsmul, Nat.cast_sub hd, Nat.cast_ofNat]

omit [IsAlgClosed k] hord in
/-- A nonzero adjoint of degree `d - 3` is not divisible by `F`. -/
private theorem not_dvd_of_mem_adjointSubmodule_sub_three (hF : F.IsHomogeneous d) (hd : 3 ≤ d)
    {G : MvPolynomial (Fin 3) k} (hG : G ∈ adjointSubmodule F (d - 3)) (hG0 : G ≠ 0) :
    ¬ F ∣ G := fun h ↦
  (Fact.out : Irreducible F).not_isUnit
    ((hF.isRelPrime_of_irreducible Fact.out (mem_adjointSubmodule_iff.1 hG).1 hG0
      (by omega)) dvd_rfl h)

/-- **Effective canonical divisors are cut out by adjoints of degree `d - 3`**: for `3 ≤ d`, a
divisor `W` of `k(C)` is effective and canonical exactly when `W = div G - E` for a nonzero
adjoint `G` of degree `d - 3`. -/
theorem nonneg_and_divisorClass_eq_canonicalClass_iff (hd : 3 ≤ d)
    {W : Divisor k (functionField hF)} :
    0 ≤ W ∧ (Place.orderSystem (functionField.isFunctionField hF)).divisorClass W =
        canonicalClass (functionField.isFunctionField hF) isIntegrallyClosedIn_of_isAlgClosed ↔
      ∃ (G : MvPolynomial (Fin 3) k) (hG : G ∈ adjointSubmodule F (d - 3)), G ≠ 0 ∧
        W = formDivisor hF (mem_adjointSubmodule_iff.1 hG).1 - adjointDivisor hF := by
  have hK := functionField.isFunctionField hF
  constructor
  · rintro ⟨hW, hWK⟩
    obtain ⟨i, hi⟩ := projectivePlaneCurve.exists_not_dvd_X (Fact.out : Irreducible F)
    have hL : (X i : MvPolynomial (Fin 3) k).IsHomogeneous 1 := isHomogeneous_X k i
    have hE := divisorClass_sub_three_zsmul_formDivisor_sub_adjointDivisor_eq_canonicalClass
      (hF := hF) hord hL hi
    rw [← nsmul_formDivisor_sub_three hd hL] at hE
    -- `W - E_{d-3}` is the divisor of a function `z ∈ L(E_{d-3})`.
    obtain ⟨z, hz⟩ := (Divisor.divisorClass_eq_zero_iff hK).1
      (show (Place.orderSystem hK).divisorClass
          (W - ((d - 3) • formDivisor hF hL - adjointDivisor hF)) = 0 by
        rw [map_sub, hWK, hE, sub_self])
    have hzL : (z : functionField hF) ∈
        riemannRochSpace ((d - 3) • formDivisor hF hL - adjointDivisor hF) := by
      rw [mem_riemannRochSpace_units_iff hK, hz, sub_add_cancel]
      exact hW
    obtain ⟨G, hGz⟩ := adjointToRiemannRochSpace_surjective hord hL hi ⟨_, hzL⟩
    have hGd := (mem_adjointSubmodule_iff.1 G.2).1
    have hLm : (X i ^ (d - 3) : MvPolynomial (Fin 3) k).IsHomogeneous (d - 3) := by
      simpa using hL.pow (d - 3)
    have hFLm := not_dvd_pow_of_not_dvd hi (d - 3)
    have hG0 : (G : MvPolynomial (Fin 3) k) ≠ 0 := by
      intro h
      have : G = 0 := Subtype.ext h
      rw [this, map_zero] at hGz
      exact z.ne_zero (congrArg Subtype.val hGz).symm
    have hFG := not_dvd_of_mem_adjointSubmodule_sub_three hF hd G.2 hG0
    have hzq : formQuotient hF hGd hLm hFG hFLm = z := by
      refine Units.ext ?_
      rw [coe_formQuotient, ← coe_adjointToRiemannRochSpace_apply hord hL hi hLm G]
      exact congrArg Subtype.val hGz
    refine ⟨G, G.2, hG0, ?_⟩
    rw [sub_eq_iff_eq_add.1 hz.symm, ← hzq, principal_formQuotient,
      formDivisor_congr hLm (hL.pow (d - 3)) rfl, formDivisor_pow hL hi]
    abel
  · rintro ⟨G, hG, hG0, rfl⟩
    have hGd := (mem_adjointSubmodule_iff.1 hG).1
    have hFG := not_dvd_of_mem_adjointSubmodule_sub_three hF hd hG hG0
    exact ⟨sub_nonneg.2 ((isAdjoint_iff_le_formDivisor hord hGd hFG).1
      (mem_adjointSubmodule_iff.1 hG).2),
      divisorClass_formDivisor_sub_adjointDivisor_eq_canonicalClass hord hd hGd hFG⟩

/-- **The adjoints of degree `d - 3` have dimension `g`**: for `3 ≤ d`, the space `V_{d-3}` of
adjoints of degree `d - 3` has dimension the genus of `k(C)`. -/
theorem finrank_adjointSubmodule_sub_three (hd : 3 ≤ d) :
    Module.finrank k (adjointSubmodule F (d - 3)) = genus k (functionField hF) := by
  have hK := functionField.isFunctionField hF
  obtain ⟨i, hi⟩ := projectivePlaneCurve.exists_not_dvd_X (Fact.out : Irreducible F)
  have hL : (X i : MvPolynomial (Fin 3) k).IsHomogeneous 1 := isHomogeneous_X k i
  have hE := divisorClass_sub_three_zsmul_formDivisor_sub_adjointDivisor_eq_canonicalClass
    (hF := hF) hord hL hi
  rw [← nsmul_formDivisor_sub_three hd hL] at hE
  rw [← dim_eq_finrank_adjointSubmodule (hF := hF) hord hL hi (m := d - 3) (by omega)]
  exact (isRiemannRochDivisor_of_divisorClass_eq_canonicalClass hK _ hE).dim_eq hK
    isIntegrallyClosedIn_of_isAlgClosed

end PlaneCurves.Projective

end
