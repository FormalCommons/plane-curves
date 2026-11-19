/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.Basic
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.ChangeOfCoordinates
public import PlaneCurves.RingTheory.MvPolynomial.LinearSubst

/-!
# Places, centres and orders of forms under a projective change of coordinates

Let `C : F = 0` be an irreducible projective plane curve, of degree `d`, and `M` an invertible
`3 × 3` matrix. The curve `C^M : F^M = 0`, with `F^M = linearSubst M F`, is again irreducible,
and a point `Q` of `C^M` corresponds to the point `P = M·Q` of `C`. The change of coordinates
induces an isomorphism `k(C) ≅ k(C^M)`, `G / H ↦ G^M / H^M`, carrying `𝒪_P(C)` onto
`𝒪_Q(C^M)`. Places move along it by `TauCeti.Place.map`, and this file shows that centres, the
places over a point and the orders of forms move with them.

## Main definitions

* `PlaneCurves.Projective.functionField.linearSubstEquiv hF M`: the isomorphism
  `k(C) ≅ k(C^M)`, `G / H ↦ G^M / H^M` (`functionField.linearSubstEquiv_mk`).
* `PlaneCurves.Projective.placesOverLinearSubstEquiv hF hQP`: the bijection between the places
  of `C` over `P` and the places of `C^M` over `Q`, for `M·Q = P`.

## Main results

* `linearSubstIdeal_ideal`: the ideal `(F)^M` is the ideal `(F^M)` of `C^M`.
* `map_localSubring_linearSubstEquiv`: `k(C) ≅ k(C^M)` carries `𝒪_P(C)` onto `𝒪_Q(C^M)` for
  `M·Q = P`.
* `center_map_linearSubstEquiv_eq_iff`, `map_center_map_linearSubstEquiv`: the centre of the
  moved place is the moved centre.
* `placesOver_linearSubst`: the places of `C^M` over `Q` are the moved places of `C` over `M·Q`.
* `ordForm_linearSubst`: `ord_{Q^M}(G^M) = ord_Q(G)` for a form `G` and a place `Q` of `k(C)`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.1
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti
open TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization
open Matrix (mulVec_injective_of_isUnit)

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {d : ℕ}

/-- A linear change of coordinates of an irreducible polynomial is irreducible. -/
instance fact_irreducible_linearSubst [Fact (Irreducible F)] (M : GL (Fin 3) k) :
    Fact (Irreducible (linearSubst M.1 F)) :=
  ⟨(irreducible_linearSubst_iff ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit)).2 Fact.out⟩

variable (hF : F.IsHomogeneous d) (M : GL (Fin 3) k)

/-- The image `(F)^M` of the ideal of `C : F = 0` under the change of coordinates `M` is the
ideal `(F^M)` of `C^M : F^M = 0`. -/
theorem linearSubstIdeal_ideal :
    linearSubstIdeal M (projectivePlaneCurve.ideal hF) =
      projectivePlaneCurve.ideal (hF.linearSubst M.1) := by
  refine HomogeneousIdeal.toIdeal_injective ?_
  rw [linearSubstIdeal_toIdeal, projectivePlaneCurve.toIdeal_ideal,
    projectivePlaneCurve.toIdeal_ideal, Ideal.map_span, Set.image_singleton]

variable [Fact (Irreducible F)]

/-- The isomorphism `k(C) ≅ k(C^M)` of the function fields of `C : F = 0` and of
`C^M : F^M = 0` induced by the change of coordinates `M`, sending `G / H` to `G^M / H^M`
(`functionField.linearSubstEquiv_mk`). -/
noncomputable def functionField.linearSubstEquiv :
    functionField hF ≃ₐ[k] functionField (hF.linearSubst M.1) :=
  (ProjectiveSpace.functionField.linearSubstEquiv M (projectivePlaneCurve.ideal hF)).trans
    (ProjectiveSpace.functionField.equivOfEq (linearSubstIdeal_ideal hF M))

theorem functionField.linearSubstEquiv_def :
    functionField.linearSubstEquiv hF M =
      (ProjectiveSpace.functionField.linearSubstEquiv M (projectivePlaneCurve.ideal hF)).trans
        (ProjectiveSpace.functionField.equivOfEq (linearSubstIdeal_ideal hF M)) :=
  (rfl)

variable {hF M} {m : ℕ} {G H : MvPolynomial (Fin 3) k}

/-- The isomorphism `k(C) ≅ k(C^M)` sends `G / H` to `G^M / H^M`. -/
theorem functionField.linearSubstEquiv_mk (hG : G.IsHomogeneous m) (hH : H.IsHomogeneous m)
    (hHI : H ∉ projectivePlaneCurve.ideal hF) :
    functionField.linearSubstEquiv hF M (functionField.mk hG hH hHI) =
      functionField.mk (hG.linearSubst M.1) (hH.linearSubst M.1)
        (linearSubstIdeal_ideal hF M ▸ linearSubst_mem_linearSubstIdeal_iff.not.2 hHI) := by
  rw [functionField.linearSubstEquiv_def, AlgEquiv.trans_apply,
    ProjectiveSpace.functionField.linearSubstEquiv_mk, functionField.equivOfEq_mk]

variable {P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))}
  {P' : zeroLocus (projectivePlaneCurve.ideal (hF.linearSubst M.1) :
    Set (MvPolynomial (Fin 3) k))}

/-- **`𝒪_P(C) ≅ 𝒪_Q(C^M)` for `M·Q = P`.** The isomorphism `k(C) ≅ k(C^M)` carries the local
ring of `C` at `P` onto the local ring of `C^M` at `Q`, when `M·Q = P`. -/
theorem map_localSubring_linearSubstEquiv
    (hQP : map M.1.mulVecLin (mulVec_injective_of_isUnit M.isUnit) P'.1 = P.1) :
    (localSubring hF P).map (functionField.linearSubstEquiv hF M : functionField hF →+* _) =
      localSubring (hF.linearSubst M.1) P' := by
  have hP : P'.1 ∈ zeroLocus (linearSubstIdeal M (projectivePlaneCurve.ideal hF) :
      Set (MvPolynomial (Fin 3) k)) := by rw [linearSubstIdeal_ideal]; exact P'.2
  have h1 := congrArg LocalSubring.toSubring
    (ProjectiveSpace.map_localSubring_linearSubstEquiv (P := P) (Q := ⟨_, hP⟩) hQP)
  have h2 := congrArg LocalSubring.toSubring
    (ProjectiveSpace.map_localSubring_equivOfEq (linearSubstIdeal_ideal hF M) ⟨_, hP⟩ P' rfl)
  refine LocalSubring.toSubring_injective ?_
  rw [LocalSubring.map_toSubring] at h1 h2 ⊢
  rw [← h2, ← h1, Subring.map_map]
  rfl

variable [IsAlgClosed k]

/-- **Centres under a change of coordinates.** For `M·Q = P`, a place of `k(C)`, moved to
`k(C^M)`, is centred at `Q` iff it is centred at `P`. -/
theorem center_map_linearSubstEquiv_eq_iff
    (hQP : map M.1.mulVecLin (mulVec_injective_of_isUnit M.isUnit) P'.1 = P.1)
    {Q : Place k (functionField hF)} :
    center (hF.linearSubst M.1) (Q.map (functionField.linearSubstEquiv hF M)) = P' ↔
      center hF Q = P := by
  rw [center_eq_iff_le, center_eq_iff_le, ← map_localSubring_linearSubstEquiv hQP,
    LocalSubring.map_toSubring, Subring.map_le_iff_le_comap]
  refine ⟨fun h z hz ↦ ?_, fun h z hz ↦ ?_⟩
  · simpa using (Place.mem_integers_map_iff _ Q).1 (h hz)
  · exact (Place.mem_integers_map_iff _ Q).2 (by simpa using h hz)

/-- **The centre of the moved place is the moved centre**: `M` sends the centre on `C^M` of a
place of `k(C)`, moved to `k(C^M)`, to its centre on `C`. -/
theorem map_center_map_linearSubstEquiv (Q : Place k (functionField hF)) :
    map M.1.mulVecLin (mulVec_injective_of_isUnit M.isUnit)
        (center (hF.linearSubst M.1) (Q.map (functionField.linearSubstEquiv hF M))).1 =
      (center hF Q).1 := by
  set P' := center (hF.linearSubst M.1) (Q.map (functionField.linearSubstEquiv hF M))
  have hP : map M.1.mulVecLin (mulVec_injective_of_isUnit M.isUnit) P'.1 ∈
      zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)) := by
    rw [mem_zeroLocus_ideal_iff hF, ← eval_rep_linearSubst_eq_zero_iff M hF]
    exact (mem_zeroLocus_ideal_iff _).1 P'.2
  have h := (center_map_linearSubstEquiv_eq_iff (P := ⟨_, hP⟩) rfl).1 rfl
  rw [h]

/-- **Places over a point under a change of coordinates.** For `M·Q = P`, the places of `C^M`
over `Q` are the places of `C` over `P`, moved to `k(C^M)`. -/
theorem placesOver_linearSubst
    (hQP : map M.1.mulVecLin (mulVec_injective_of_isUnit M.isUnit) P'.1 = P.1) :
    placesOver (hF.linearSubst M.1) P' =
      Place.map (functionField.linearSubstEquiv hF M) '' placesOver hF P := by
  ext R
  refine ⟨fun hR ↦ ⟨R.map (functionField.linearSubstEquiv hF M).symm, ?_, ?_⟩, ?_⟩
  · rw [mem_placesOver_iff, ← center_map_linearSubstEquiv_eq_iff hQP, Place.map_map_symm]
    exact mem_placesOver_iff.1 hR
  · exact Place.map_map_symm _ R
  · rintro ⟨Q, hQ, rfl⟩
    exact mem_placesOver_iff.2
      ((center_map_linearSubstEquiv_eq_iff hQP).2 (mem_placesOver_iff.1 hQ))

variable (hF M) in
/-- The bijection between the places of `C` over `P` and the places of `C^M` over `Q`, for
`M·Q = P`, given by moving places along `k(C) ≅ k(C^M)`. -/
noncomputable def placesOverLinearSubstEquiv
    (hQP : map M.1.mulVecLin (mulVec_injective_of_isUnit M.isUnit) P'.1 = P.1) :
    placesOver hF P ≃ placesOver (hF.linearSubst M.1) P' where
  toFun Q := ⟨Q.1.map (functionField.linearSubstEquiv hF M), mem_placesOver_iff.2
    ((center_map_linearSubstEquiv_eq_iff hQP).2 (mem_placesOver_iff.1 Q.2))⟩
  invFun R := ⟨R.1.map (functionField.linearSubstEquiv hF M).symm, mem_placesOver_iff.2
    ((center_map_linearSubstEquiv_eq_iff hQP).1 (by
      rw [Place.map_map_symm]; exact mem_placesOver_iff.1 R.2))⟩
  left_inv Q := Subtype.ext (Place.map_symm_map _ _)
  right_inv R := Subtype.ext (Place.map_map_symm _ _)

@[simp]
theorem coe_placesOverLinearSubstEquiv
    (hQP : map M.1.mulVecLin (mulVec_injective_of_isUnit M.isUnit) P'.1 = P.1)
    (Q : placesOver hF P) :
    (placesOverLinearSubstEquiv hF M hQP Q : Place k (functionField (hF.linearSubst M.1))) =
      Q.1.map (functionField.linearSubstEquiv hF M) :=
  (rfl)

/-- **Orders of forms under a change of coordinates.** The order of the form `G^M` at a place of
`k(C)` moved to `k(C^M)` is the order of `G` at the place. -/
theorem ordForm_linearSubst (Q : Place k (functionField hF)) (hG : G.IsHomogeneous m) :
    ordForm (hF.linearSubst M.1) (Q.map (functionField.linearSubstEquiv hF M))
        (hG.linearSubst M.1) = ordForm hF Q hG := by
  obtain ⟨i, hi⟩ := (center hF Q).1.exists_mem_affineOpen
  have hXQ : eval (center hF Q).1.rep (X i ^ m) ≠ 0 := by
    simpa using pow_ne_zero m ((mem_affineOpen_iff _ _).1 hi)
  have hXQ' : eval (center (hF.linearSubst M.1)
      (Q.map (functionField.linearSubstEquiv hF M))).1.rep (linearSubst M.1 (X i ^ m)) ≠ 0 := by
    rwa [Ne, eval_rep_linearSubst_eq_zero_iff M (isHomogeneous_X_pow i m),
      map_center_map_linearSubstEquiv]
  rw [ordForm_eq_addValuation_mk hG (isHomogeneous_X_pow i m) hXQ,
    ordForm_eq_addValuation_mk _ ((isHomogeneous_X_pow i m).linearSubst M.1) hXQ',
    ← functionField.linearSubstEquiv_mk, Place.addValuation_map_apply]

end PlaneCurves.Projective

end
