/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.IntersectionNumber.Properties
public import PlaneCurves.RingTheory.Valuation.ValuationSubring
public import TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring

/-!
# The place at a simple point of a projective plane curve

Let `k` be an algebraically closed field and `C : F = 0` an irreducible projective plane curve
with function field `k(C)`, the field of fractions of every local ring `𝒪_P(C)`
(`ProjectiveSpace.isFractionRing_localSubring`). If `P` is a simple point of `C`, then
`𝒪_P(C) ≅ 𝒪_P(ℙ²) ⧸ (F_*)` is a discrete valuation ring, hence a valuation ring of `k(C)`
(`LocalSubring.toValuationSubring`), and it is the valuation ring of exactly one place of `k(C)`,
the **place at `P`**. It is the only place over `P`, since a discrete valuation ring is maximal
for domination.

If `C` is nonsingular, the centre map is therefore a bijection from the places of `k(C)` onto the
points of `C`, with inverse `P ↦` the place at `P`.

## Main definitions

* `PlaneCurves.Projective.placeAt hF hP`: the place of `k(C)` whose valuation ring is `𝒪_P(C)`.
* `PlaneCurves.Projective.centerEquiv hF hns`: for a nonsingular `F`, the centre map as a
  bijection from the places of `k(C)` onto `C`.

## Main results

* `isDiscreteValuationRing_localSubring`: `𝒪_P(C)` is a discrete valuation ring at a simple
  point.
* `integers_toSubring_placeAt`, `center_placeAt`, `placesOver_eq_singleton`: the place at `P` has
  valuation ring `𝒪_P(C)`, is centred at `P`, and is the only place over `P`.
* `center_bijective`: for a nonsingular curve the centre map is bijective.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.1
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti
open TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
  (hF : F.IsHomogeneous d) [Fact (Irreducible F)]
  {P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))}

/-! ### The local ring at a simple point -/

variable {hF}

/-- **The local ring of `C` at a simple point is a discrete valuation ring**: it is
`𝒪_P(ℙ²) ⧸ (F_*)` (`quotientLocalEquationEquiv`), which is one
(`exists_isDiscreteValuationRing_quotient_iff`). -/
theorem isDiscreteValuationRing_localSubring (hP : IsSimplePoint F P.1) :
    IsDiscreteValuationRing (localSubring hF P).toSubring := by
  obtain ⟨_, _⟩ := (exists_isDiscreteValuationRing_quotient_iff hF hP.eval_rep_eq_zero).2 hP
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (quotientLocalEquationEquiv hF P).toRingEquiv

/-! ### The place at a simple point -/

variable (hF) in
/-- The **place at a simple point** `P` of `C`: the unique place of `k(C)` whose valuation ring
is the local ring `𝒪_P(C)` (`integers_toSubring_placeAt`). It is the only place over `P`
(`placesOver_eq_singleton`). -/
noncomputable def placeAt (hP : IsSimplePoint F P.1) : Place k (functionField hF) :=
  have := isDiscreteValuationRing_localSubring hP
  Place.ofValuationSubring (A := (localSubring hF P).toValuationSubring)
    (functionField.isFunctionField hF)
    (fun c ↦ LocalSubring.mem_toValuationSubring.2
      (algebraMap k (localSubring hF P).toSubring c).2)
    (localSubring hF P).toValuationSubring_ne_top

theorem placeAt_def (hP : IsSimplePoint F P.1) :
    have := isDiscreteValuationRing_localSubring hP
    placeAt hF hP = Place.ofValuationSubring (A := (localSubring hF P).toValuationSubring)
      (functionField.isFunctionField hF)
      (fun c ↦ LocalSubring.mem_toValuationSubring.2
        (algebraMap k (localSubring hF P).toSubring c).2)
      (localSubring hF P).toValuationSubring_ne_top :=
  (rfl)

/-- The valuation ring of the place at a simple point `P` is `𝒪_P(C)`. -/
@[simp]
theorem integers_toSubring_placeAt (hP : IsSimplePoint F P.1) :
    (placeAt hF hP).integers.toSubring = (localSubring hF P).toSubring := by
  have := isDiscreteValuationRing_localSubring hP
  rw [placeAt_def, Place.integers_ofValuationSubring, LocalSubring.toSubring_toValuationSubring]

/-- The valuation ring of the place at a simple point `P` is `𝒪_P(C)`, as a local subring. -/
theorem integers_toLocalSubring_placeAt (hP : IsSimplePoint F P.1) :
    (placeAt hF hP).integers.toLocalSubring = localSubring hF P :=
  LocalSubring.toSubring_injective (integers_toSubring_placeAt hP)

/-- The place at a simple point `P` is the only place whose valuation ring is `𝒪_P(C)`. -/
theorem eq_placeAt_iff (hP : IsSimplePoint F P.1) {Q : Place k (functionField hF)} :
    Q = placeAt hF hP ↔ Q.integers.toSubring = (localSubring hF P).toSubring := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ Place.integers_injective ?_⟩
  exact ValuationSubring.toSubring_injective (h.trans (integers_toSubring_placeAt hP).symm)

variable [IsAlgClosed k]

/-- The place at a simple point `P` is centred at `P`. -/
@[simp]
theorem center_placeAt (hP : IsSimplePoint F P.1) : center hF (placeAt hF hP) = P := by
  rw [center_eq_iff_le, integers_toSubring_placeAt]

/-- **The unique place over a simple point.** The place at a simple point `P` is the only place
of `k(C)` centred at `P`: a place over `P` has a valuation ring containing the discrete valuation
ring `𝒪_P(C)`, hence equal to it. -/
theorem placesOver_eq_singleton (hP : IsSimplePoint F P.1) :
    placesOver hF P = {placeAt hF hP} := by
  ext Q
  rw [Set.mem_singleton_iff, mem_placesOver_iff_le]
  refine ⟨fun h ↦ (Place.eq_of_integers_le (P := placeAt hF hP) ?_).symm, fun h ↦ ?_⟩
  · exact fun x hx ↦ h (by rwa [← integers_toSubring_placeAt hP])
  · rw [h, integers_toSubring_placeAt]

/-- A place is the place at its centre, if the centre is a simple point. -/
theorem placeAt_center {Q : Place k (functionField hF)} (hQ : IsSimplePoint F (center hF Q).1) :
    placeAt hF hQ = Q :=
  ((Set.ext_iff.1 (placesOver_eq_singleton hQ) Q).1 (mem_placesOver_center Q)).symm

/-! ### Nonsingular curves -/

omit [Fact (Irreducible F)] [IsAlgClosed k] in
/-- Every point of a nonsingular curve is a simple point. -/
theorem IsNonsingular.isSimplePoint (hns : IsNonsingular F)
    (P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))) :
    IsSimplePoint F P.1 := by
  refine (isNonsingular_iff_forall_isSimplePoint hF).1 hns P.1 ?_
  rw [mem_zeroLocus_iff_eval_rep (by simpa using ⟨d, hF⟩), Set.forall_mem_singleton]
  exact (mem_zeroLocus_ideal_iff hF).1 P.2

variable (hF) in
/-- **The points of a nonsingular projective plane curve are the places of its function field.**
For a nonsingular `F`, the centre map is a bijection from the places of `k(C)` onto the points of
`C`, with inverse the place at a point (`placeAt`). -/
noncomputable def centerEquiv (hns : IsNonsingular F) :
    Place k (functionField hF) ≃
      zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)) where
  toFun := center hF
  invFun P := placeAt hF (hns.isSimplePoint P)
  left_inv _ := placeAt_center _
  right_inv _ := center_placeAt _

@[simp]
theorem centerEquiv_apply (hns : IsNonsingular F) (Q : Place k (functionField hF)) :
    centerEquiv hF hns Q = center hF Q :=
  (rfl)

@[simp]
theorem centerEquiv_symm_apply (hns : IsNonsingular F)
    (P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))) :
    (centerEquiv hF hns).symm P = placeAt hF (hns.isSimplePoint P) :=
  (rfl)

variable (hF) in
/-- For a nonsingular curve the centre map is bijective. -/
theorem center_bijective (hns : IsNonsingular F) : Function.Bijective (center hF) :=
  (centerEquiv hF hns).bijective

end PlaneCurves.Projective

end
