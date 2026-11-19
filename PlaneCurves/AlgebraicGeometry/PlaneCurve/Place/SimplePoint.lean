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
public import TauCeti.FieldTheory.FunctionField.HolomorphyRing.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.LocalRing
public import PlaneCurves.AlgebraicGeometry.AffineSpace.PlaneCurveDimension

/-!
# The place at a simple point of a plane curve

Let `k` be an algebraically closed field and `C : F = 0` an irreducible projective plane curve
with function field `k(C)`, the field of fractions of every local ring `𝒪_P(C)`
(`ProjectiveSpace.isFractionRing_localSubring`). If `P` is a simple point of `C`, then
`𝒪_P(C) ≅ 𝒪_P(ℙ²) ⧸ (F_*)` is a discrete valuation ring, hence a valuation ring of `k(C)`
(`LocalSubring.toValuationSubring`), and it is the valuation ring of exactly one place of `k(C)`,
the **place at `P`**. It is the only place over `P`, since a discrete valuation ring is maximal
for domination. Its order function is Chapter 3's order at `P`: the order of vanishing
`Ring.ord` in `𝒪_{φᵢ(P)}(𝔸²) ⧸ (F_(i))` of the dehomogenization of a form, read in `WithTop ℤ`,
since `Ring.ord` is the additive valuation of a discrete valuation ring.

If `C` is nonsingular, the centre map is therefore a bijection from the places of `k(C)` onto the
points of `C`, with inverse `P ↦` the place at `P`, and the functions regular on a set `U` of
points are those regular at the places centred in `U`.

The same construction gives the place at a simple point `P` of an irreducible affine plane curve
`F = 0`, with valuation ring `𝒪_P(F) ≅ 𝒪_P(𝔸²) ⧸ (F)`.

## Main definitions

* `PlaneCurves.Projective.placeAt hF hP`: the place of `k(C)` whose valuation ring is `𝒪_P(C)`.
* `PlaneCurves.Projective.centerEquiv hF hns`: for a nonsingular `F`, the centre map as a
  bijection from the places of `k(C)` onto `C`.
* `PlaneCurves.Affine.placeAt hP`: the place of `k(F)` whose valuation ring is `𝒪_P(F)`, for an
  affine plane curve.

## Main results

* `isDiscreteValuationRing_localSubring`: `𝒪_P(C)` is a discrete valuation ring at a simple
  point.
* `integers_toSubring_placeAt`, `center_placeAt`, `placesOver_eq_singleton`: the place at `P` has
  valuation ring `𝒪_P(C)`, is centred at `P`, and is the only place over `P`.
* `center_bijective`: for a nonsingular curve the centre map is bijective.
* `map_natCast_ord_eq_ordForm_placeAt`: at a simple point, `Ring.ord` of the class of `G_(i)` in
  `𝒪_{φᵢ(P)}(𝔸²) ⧸ (F_(i))` is the order of the form `G` at the place at `P`;
  `Affine.map_natCast_ord_eq_addValuation_placeAt` for affine curves.
* `IsNonsingular.iInter_localSubring_eq_holomorphyRing`: for a nonsingular curve,
  `⋂_{P ∈ U} 𝒪_P(C)` is the holomorphy ring of the places centred in `U`.
* `placeAt_spec`: the milestone, the points of a nonsingular projective plane curve are the
  places of its function field, with the comparison of orders at simple points.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.2, §7.1
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


/-! ### Orders at a simple point -/

omit [IsAlgClosed k] in
/-- The local ring `𝒪_P(C) ≅ 𝒪_{φᵢ(P)}(𝔸²) ⧸ (F_(i))` sends the class of the dehomogenization
`G_(i)` of a polynomial `G` to the class of `G_(i)` in the function field, carried to `k(C)` by
the inverse of the chart isomorphism. -/
theorem coe_chartQuotientEquiv_symm_mk {i : Fin 3} (hPi : P.1 ∈ affineOpen i)
    (G : MvPolynomial (Fin 3) k) :
    haveI := isPrime_span_dehomogenize hF (not_dvd_X_of_mem_affineOpen hF P hPi)
    ((localSubring.chartQuotientEquiv hF i P hPi).symm
        (Ideal.Quotient.mk _ (algebraMap _ _ (dehomogenize i G))) : functionField hF) =
      (functionField.chartEquiv hF i (not_dvd_X_of_mem_affineOpen hF P hPi)).symm
        (algebraMap _ _
          (Ideal.Quotient.mk (Ideal.span {dehomogenize i F}) (dehomogenize i G))) := by
  have := isPrime_span_dehomogenize hF (not_dvd_X_of_mem_affineOpen hF P hPi)
  rw [eq_comm, AlgEquiv.symm_apply_eq, ← localSubring.coe_chartEquiv hF P hPi,
    localSubring.chartQuotientEquiv_def]
  rw [AlgEquiv.symm_trans_apply, AlgEquiv.symm_trans_apply, AlgEquiv.apply_symm_apply,
    Ideal.quotientEquivAlgOfEq_symm, Ideal.quotientEquivAlgOfEq_mk,
    AffineSpace.quotientAlgEquiv_symm_mk]
  rfl

/-- **Orders at a simple point.** Let `P` be a simple point of `C` in the chart `Xᵢ ≠ 0`. For every
form `G`, the order of vanishing (`Ring.ord`, a length in `ℕ∞`) of the class of the
dehomogenization `G_(i)` in the discrete valuation ring `𝒪_{φᵢ(P)}(𝔸²) ⧸ (F_(i))` is, read in
`WithTop ℤ`, the order of `G` at the place at `P`. -/
theorem map_natCast_ord_eq_ordForm_placeAt (hP : IsSimplePoint F P.1) {i : Fin 3}
    (hPi : P.1 ∈ affineOpen i) {m : ℕ} {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m) :
    (Ring.ord (AffineSpace.localRing k (affineChart i P.1) ⧸
        Ideal.span {algebraMap _ (AffineSpace.localRing k (affineChart i P.1)) (dehomogenize i F)})
      (Ideal.Quotient.mk _ (algebraMap _ _ (dehomogenize i G)))).map (Nat.cast : ℕ → ℤ) =
      ordForm hF (placeAt hF hP) hG := by
  have hQ : (center hF (placeAt hF hP)).1 ∈ affineOpen i := by rwa [center_placeAt]
  let e : (localSubring hF P).toSubring ≃+* (placeAt hF hP).integers :=
    RingEquiv.subringCongr (integers_toSubring_placeAt hP).symm
  have h := (placeAt hF hP).map_natCast_ord_ringEquiv_eq_addValuation
    (R := AffineSpace.localRing k (affineChart i P.1) ⧸
      Ideal.span {algebraMap _ (AffineSpace.localRing k (affineChart i P.1)) (dehomogenize i F)})
    ((localSubring.chartQuotientEquiv hF i P hPi).symm.toRingEquiv.trans e)
    (Ideal.Quotient.mk _ (algebraMap _ _ (dehomogenize i G)))
  rw [h, ordForm_eq_addValuation_chartEquiv_symm hQ hG]
  congr 1
  exact coe_chartQuotientEquiv_symm_mk hPi G

/-! ### Regular functions on an open set -/

/-- **Regular functions on a nonsingular curve.** For a nonsingular `F` and any set `U` of points
of `C`, the functions regular at every point of `U`, `⋂_{P ∈ U} 𝒪_P(C)`, are the holomorphy ring
of the places centred in `U`. -/
theorem IsNonsingular.iInter_localSubring_eq_holomorphyRing (hns : IsNonsingular F)
    (U : Set (zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)))) :
    ⋂ P ∈ U, ((localSubring hF P).toSubring : Set (functionField hF)) =
      holomorphyRing {Q | center hF Q ∈ U} := by
  ext z
  simp only [Set.mem_iInter, SetLike.mem_coe, mem_holomorphyRing_iff]
  refine ⟨fun h Q hQ ↦ ?_, fun h P hP ↦ ?_⟩
  · have := h _ hQ
    rwa [← integers_toSubring_placeAt (hns.isSimplePoint _), placeAt_center] at this
  · have := h (placeAt hF (hns.isSimplePoint P)) (by simpa using hP)
    rwa [← integers_toSubring_placeAt (hns.isSimplePoint P)]

end PlaneCurves.Projective

/-! ### Affine plane curves -/

namespace PlaneCurves.Affine

open AffineSpace

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 2) k} [(Ideal.span {F}).IsPrime]
  {P : Fin 2 → k}

omit [(Ideal.span {F}).IsPrime] in
/-- A point of an affine plane curve `F = 0` gives a local ring `𝒪_P(F)` of its function field:
`(F)` lies in the ideal of `P`. -/
theorem span_le_vanishingIdeal (hP : eval P F = 0) : Ideal.span {F} ≤ vanishingIdeal k {P} :=
  span_singleton_le_vanishingIdeal_singleton_iff.2 (by simpa using hP)

/-- `𝒪_P(F) ≅ 𝒪_P(𝔸²) ⧸ (F)`, Problem 2.44 for the ideal `(F)`. -/
private noncomputable def localSubringQuotientEquiv (hP : eval P F = 0) :
    (AffineSpace.localSubring P (span_le_vanishingIdeal hP)).toSubring ≃ₐ[k]
      localRing k P ⧸ Ideal.span {algebraMap _ (localRing k P) F} :=
  (quotientAlgEquiv P _).trans
    (Ideal.quotientEquivAlgOfEq k (by rw [Ideal.map_span, Set.image_singleton]))

private theorem coe_localSubringQuotientEquiv_symm_mk (hP : eval P F = 0)
    (G : MvPolynomial (Fin 2) k) :
    ((localSubringQuotientEquiv hP).symm
        (Ideal.Quotient.mk _ (algebraMap _ (localRing k P) G)) : functionField (Ideal.span {F})) =
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) G) := by
  rw [localSubringQuotientEquiv, AlgEquiv.symm_trans_apply, Ideal.quotientEquivAlgOfEq_symm,
    Ideal.quotientEquivAlgOfEq_mk, quotientAlgEquiv_symm_mk]
  rfl

/-- **The local ring of an affine plane curve at a simple point is a discrete valuation ring**:
it is `𝒪_P(𝔸²) ⧸ (F)`, which is one (`exists_isDiscreteValuationRing_quotient_iff`). -/
theorem isDiscreteValuationRing_localSubring (hP : IsSimplePoint F P) :
    IsDiscreteValuationRing
      (AffineSpace.localSubring P (span_le_vanishingIdeal hP.eval_eq_zero)).toSubring := by
  obtain ⟨_, _⟩ := (exists_isDiscreteValuationRing_quotient_iff hP.eval_eq_zero).2 hP
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (localSubringQuotientEquiv hP.eval_eq_zero).symm.toRingEquiv

/-- An affine plane curve `F = 0` through a simple point, with `(F)` prime, is irreducible. -/
theorem IsSimplePoint.irreducible (hP : IsSimplePoint F P) : Irreducible F :=
  ((Ideal.span_singleton_prime hP.ne_zero).1 inferInstance).irreducible

/-- The **place at a simple point** `P` of an irreducible affine plane curve `F = 0`: the unique
place of the function field `k(F)` whose valuation ring is the local ring `𝒪_P(F)`
(`integers_toSubring_placeAt`). -/
noncomputable def placeAt (hP : IsSimplePoint F P) :
    Place k (functionField (Ideal.span {F})) :=
  have := isDiscreteValuationRing_localSubring hP
  Place.ofValuationSubring
    (A := (AffineSpace.localSubring P (span_le_vanishingIdeal hP.eval_eq_zero)).toValuationSubring)
    (isFunctionField_functionField_span_singleton hP.irreducible)
    (fun c ↦ LocalSubring.mem_toValuationSubring.2
      (algebraMap k (AffineSpace.localSubring P (span_le_vanishingIdeal hP.eval_eq_zero)).toSubring
        c).2)
    (AffineSpace.localSubring P (span_le_vanishingIdeal hP.eval_eq_zero)).toValuationSubring_ne_top

theorem placeAt_def (hP : IsSimplePoint F P) :
    have := isDiscreteValuationRing_localSubring hP
    placeAt hP = Place.ofValuationSubring
      (A := (AffineSpace.localSubring P
        (span_le_vanishingIdeal hP.eval_eq_zero)).toValuationSubring)
      (isFunctionField_functionField_span_singleton hP.irreducible)
      (fun c ↦ LocalSubring.mem_toValuationSubring.2
        (algebraMap k
          (AffineSpace.localSubring P (span_le_vanishingIdeal hP.eval_eq_zero)).toSubring c).2)
      (AffineSpace.localSubring P
        (span_le_vanishingIdeal hP.eval_eq_zero)).toValuationSubring_ne_top :=
  (rfl)

/-- The valuation ring of the place at a simple point `P` is `𝒪_P(F)`. -/
@[simp]
theorem integers_toSubring_placeAt (hP : IsSimplePoint F P) :
    (placeAt hP).integers.toSubring =
      (AffineSpace.localSubring P (span_le_vanishingIdeal hP.eval_eq_zero)).toSubring := by
  have := isDiscreteValuationRing_localSubring hP
  rw [placeAt_def, Place.integers_ofValuationSubring, LocalSubring.toSubring_toValuationSubring]

/-- The place at a simple point `P` is the only place whose valuation ring is `𝒪_P(F)`. -/
theorem eq_placeAt_iff (hP : IsSimplePoint F P) {Q : Place k (functionField (Ideal.span {F}))} :
    Q = placeAt hP ↔ Q.integers.toSubring =
      (AffineSpace.localSubring P (span_le_vanishingIdeal hP.eval_eq_zero)).toSubring := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ Place.integers_injective ?_⟩
  exact ValuationSubring.toSubring_injective (h.trans (integers_toSubring_placeAt hP).symm)

/-- **Orders at a simple point of an affine plane curve.** For a simple point `P` of `F = 0` and
a polynomial `G`, the order of vanishing (`Ring.ord`, a length in `ℕ∞`) of the class of `G` in the
discrete valuation ring `𝒪_P(𝔸²) ⧸ (F)` is, read in `WithTop ℤ`, the order of `G` at the place at
`P`. -/
theorem map_natCast_ord_eq_addValuation_placeAt (hP : IsSimplePoint F P)
    (G : MvPolynomial (Fin 2) k) :
    (Ring.ord (localRing k P ⧸ Ideal.span {algebraMap _ (localRing k P) F})
      (Ideal.Quotient.mk _ (algebraMap _ _ G))).map (Nat.cast : ℕ → ℤ) =
      (placeAt hP).addValuation (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) G)) := by
  let e : (AffineSpace.localSubring P (span_le_vanishingIdeal hP.eval_eq_zero)).toSubring ≃+*
      (placeAt hP).integers :=
    RingEquiv.subringCongr (integers_toSubring_placeAt hP).symm
  rw [(placeAt hP).map_natCast_ord_ringEquiv_eq_addValuation
    (R := localRing k P ⧸ Ideal.span {algebraMap _ (localRing k P) F})
    ((localSubringQuotientEquiv hP.eval_eq_zero).symm.toRingEquiv.trans e)]
  exact congrArg _ (coe_localSubringQuotientEquiv_symm_mk hP.eval_eq_zero G)

end PlaneCurves.Affine

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
  (hF : F.IsHomogeneous d) [Fact (Irreducible F)]

/-- **The points of a nonsingular projective plane curve are the places of its function field.**
Let `k` be algebraically closed and `C : F = 0` an irreducible projective plane curve.

* (a) If `C` is nonsingular, every local ring `𝒪_P(C)` is a discrete valuation ring, the
  valuation ring of exactly one place of `k(C)`, and every place of `k(C)` has the local ring of
  exactly one point as valuation ring: `P ↦ 𝒪_P(C)` is a bijection from `C` onto the discrete
  valuation rings of `k(C)` over `k` (Tau Ceti's places). For every set `U` of points of `C`,
  the functions regular on `U`, `⋂_{P ∈ U} 𝒪_P(C)`, form the holomorphy ring of the places
  centred in `U`.
* (b) At a simple point `P` of `C`, possibly singular elsewhere, `𝒪_P(C)` is the valuation ring
  of exactly one place, the place at `P`; for `P` in the chart `Xᵢ ≠ 0` and every form `G`, the
  order of vanishing `Ring.ord` of the class of `G_(i)` in `𝒪_{φᵢ(P)}(𝔸²) ⧸ (F_(i))`, read in
  `WithTop ℤ`, is the order of `G` at that place. The same holds for an irreducible affine plane
  curve `F' = 0`, a simple point `P'` and a polynomial `G`, in `𝒪_{P'}(𝔸²) ⧸ (F')`.

Milestone: *Points of a nonsingular projective curve are the places of its function field*. -/
theorem placeAt_spec :
    -- (a)
    (IsNonsingular F →
      (∀ P, IsDiscreteValuationRing (localSubring hF P).toSubring) ∧
      (∀ P, ∃! Q : Place k (functionField hF),
        Q.integers.toSubring = (localSubring hF P).toSubring) ∧
      (∀ Q : Place k (functionField hF),
        ∃! P, (localSubring hF P).toSubring = Q.integers.toSubring) ∧
      ∀ U : Set (zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))),
        ⋂ P ∈ U, ((localSubring hF P).toSubring : Set (functionField hF)) =
          holomorphyRing {Q | center hF Q ∈ U}) ∧
    -- (b), projective
    (∀ P (hP : IsSimplePoint F P.1),
      (∃! Q : Place k (functionField hF), Q.integers.toSubring = (localSubring hF P).toSubring) ∧
      ∀ (i : Fin 3) (hPi : P.1 ∈ affineOpen i) (m : ℕ) (G : MvPolynomial (Fin 3) k)
        (hG : G.IsHomogeneous m),
        (Ring.ord (AffineSpace.localRing k (affineChart i P.1) ⧸
            Ideal.span
              {algebraMap _ (AffineSpace.localRing k (affineChart i P.1)) (dehomogenize i F)})
          (Ideal.Quotient.mk _ (algebraMap _ _ (dehomogenize i G)))).map (Nat.cast : ℕ → ℤ) =
          ordForm hF (placeAt hF hP) hG) ∧
    -- (b), affine
    (∀ (F' : MvPolynomial (Fin 2) k) [(Ideal.span {F'}).IsPrime] (P' : Fin 2 → k)
      (hP' : Affine.IsSimplePoint F' P'),
      (∃! Q : Place k (AffineSpace.functionField (Ideal.span {F'})),
        Q.integers.toSubring = (AffineSpace.localSubring P'
          (Affine.span_le_vanishingIdeal hP'.eval_eq_zero)).toSubring) ∧
      ∀ G : MvPolynomial (Fin 2) k,
        (Ring.ord (AffineSpace.localRing k P' ⧸
            Ideal.span {algebraMap _ (AffineSpace.localRing k P') F'})
          (Ideal.Quotient.mk _ (algebraMap _ _ G))).map (Nat.cast : ℕ → ℤ) =
          (Affine.placeAt hP').addValuation
            (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F'}) G))) := by
  refine ⟨fun hns ↦ ⟨fun P ↦ isDiscreteValuationRing_localSubring (hns.isSimplePoint P),
    fun P ↦ ⟨_, integers_toSubring_placeAt (hns.isSimplePoint P), fun Q h ↦
      (eq_placeAt_iff _).2 h⟩, fun Q ↦ ⟨center hF Q, ?_, fun P h ↦ (center_eq_iff_le.2 h.le).symm⟩,
    hns.iInter_localSubring_eq_holomorphyRing⟩,
    fun P hP ↦ ⟨⟨_, integers_toSubring_placeAt hP, fun Q h ↦ (eq_placeAt_iff hP).2 h⟩,
      fun i hPi _ _ hG ↦ map_natCast_ord_eq_ordForm_placeAt hP hPi hG⟩,
    fun F' _ P' hP' ↦ ⟨⟨_, Affine.integers_toSubring_placeAt hP',
      fun Q h ↦ (Affine.eq_placeAt_iff hP').2 h⟩,
      Affine.map_natCast_ord_eq_addValuation_placeAt hP'⟩⟩
  dsimp only
  rw [← integers_toSubring_placeAt (hns.isSimplePoint _), placeAt_center]

end PlaneCurves.Projective

end
