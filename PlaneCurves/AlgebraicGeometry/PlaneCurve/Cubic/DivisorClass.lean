/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Cubic.GroupLaw
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Divisor
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Genus.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.SimplePoint
public import TauCeti.FieldTheory.FunctionField.Elliptic.Basic
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Equiv

/-!
# The chord–tangent group of a nonsingular cubic as its divisor class group

Let `k` be algebraically closed, `C : F = 0` a nonsingular plane cubic with function field
`K = k(C)`, and `O` a point of `C`. Every point `A` of `C` is simple, and so is the centre of
exactly one place of `K`, the place at `A` (`CubicGroup.place`); every place of `K` arises so.
The curve has genus one (`genus_functionField_of_isNonsingular`, the nonsingular case of the
genus formula). Then, writing `≡` for linear equivalence of divisors on the nonsingular model:

* (a) `A ≡ B` iff `A = B`, since `C` has positive genus;
* (b) `A + B ≡ C + D` iff the chords through `A`, `B` and through `C`, `D` have the same third
  point: the quotient of the two chord lines has divisor `A + B + φ(A, B) - C - D - φ(C, D)`
  (`formDivisor_chordLine`), and (a) applies to the third points;
* (c) `A ⊕ B = C` iff `A + B ≡ C + O`, by (b) and `φ(A, B) = φ(O, O) - A - B`;
* (d) `A ↦ [A - O]` is an isomorphism of groups from `(C, ⊕)` onto the group `Cl⁰(K)` of
  divisor classes of degree zero: it is a bijection by Tau Ceti's
  `TauCeti.Place.degreeOneEquivDegreeZeroClassGroup`, and additive by (c).

The proof uses neither Max Noether's theorem nor the residue theorem.

## Main definitions

* `PlaneCurves.Projective.CubicGroup.place`: the place of `k(C)` at a point of the group.
* `PlaneCurves.Projective.CubicGroup.placeEquiv`: for a nonsingular cubic, the points of the group
  are the places of `k(C)`, all of degree one.
* `PlaneCurves.Projective.CubicGroup.classGroupEquiv`: the isomorphism `A ↦ [A - O]` onto
  `Cl⁰(k(C))`.

## Main results

* `PlaneCurves.Projective.CubicGroup.formDivisor_chordLine`: `div L = A + B + φ(A, B)` for the
  chord line `L` through `A` and `B`.
* `PlaneCurves.Projective.CubicGroup.linearlyEquivalent_ofPoint_place_iff`,
  `PlaneCurves.Projective.CubicGroup.linearlyEquivalent_add_iff_chord_eq`,
  `PlaneCurves.Projective.CubicGroup.add_eq_iff_linearlyEquivalent`: (a), (b) and (c).
* `PlaneCurves.Projective.CubicGroup.classGroupEquiv_spec`: the milestone.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §8.1, Problems 8.3 and 8.6; §5.6
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti
open TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k}

namespace CubicGroup

variable {O : ℙ k (Fin 3 → k)} [hF : Fact (F.IsHomogeneous 3)] [hirr : Fact (Irreducible F)]

/-! ### The place at a point of the group -/

/-- The **place at a point** `A` of the group of simple points of an irreducible cubic `C`: the
unique place of `k(C)` centred at `A` (`PlaneCurves.Projective.placeAt`). -/
noncomputable def place (A : CubicGroup F O) : Place k (functionField hF.out) :=
  placeAt hF.out (P := ⟨A.point, (mem_zeroLocus_ideal_iff hF.out).2
    A.isSimplePoint.eval_rep_eq_zero⟩) A.isSimplePoint

theorem place_def (A : CubicGroup F O) :
    A.place = placeAt hF.out (P := ⟨A.point, (mem_zeroLocus_ideal_iff hF.out).2
      A.isSimplePoint.eval_rep_eq_zero⟩) A.isSimplePoint :=
  (rfl)

variable [IsAlgClosed k]

/-- The place at `A` is centred at `A`. -/
@[simp]
theorem center_place (A : CubicGroup F O) : (center hF.out A.place).1 = A.point := by
  rw [place_def, center_placeAt]

/-- The place at `A` is the place `Q` iff `A` is the centre of `Q`. -/
theorem place_eq_iff {A : CubicGroup F O} {Q : Place k (functionField hF.out)} :
    A.place = Q ↔ A.point = (center hF.out Q).1 := by
  refine ⟨fun h ↦ h ▸ (center_place A).symm, fun h ↦ ?_⟩
  have hQ : IsSimplePoint F (center hF.out Q).1 := h ▸ A.isSimplePoint
  have h1 : A.place ∈ placesOver hF.out (center hF.out Q) :=
    mem_placesOver_iff.2 (Subtype.ext ((center_place A).trans h))
  have h2 := mem_placesOver_center Q
  rw [placesOver_eq_singleton hQ] at h1 h2
  exact h1.trans h2.symm

theorem place_injective : Function.Injective (place : CubicGroup F O → _) :=
  fun _ B h ↦ CubicGroup.ext ((place_eq_iff.1 h).trans (center_place B))

@[simp]
theorem place_inj {A B : CubicGroup F O} : A.place = B.place ↔ A = B :=
  place_injective.eq_iff

/-- On a nonsingular cubic, every place of `k(C)` is the place at a point of the group. -/
theorem exists_place_eq (hns : IsNonsingular F) (Q : Place k (functionField hF.out)) :
    ∃ A : CubicGroup F O, A.place = Q :=
  ⟨⟨(center hF.out Q).1, hns.isSimplePoint (center hF.out Q)⟩, place_eq_iff.2 rfl⟩

/-- The coefficient of the point divisor of the place at `A`, at a place `Q`, is `1` if `A` is the
centre of `Q` and `0` otherwise. -/
theorem coeff_ofPoint_place (A : CubicGroup F O) (Q : Place k (functionField hF.out)) :
    (WeilDivisor.ofPoint A.place : Divisor k (functionField hF.out)).coeff Q =
      (Finsupp.single A.point 1 (center hF.out Q).1 : ℕ) := by
  by_cases h : A.point = (center hF.out Q).1
  · rw [place_eq_iff.2 h, ← h, Finsupp.single_eq_same, WeilDivisor.coeff_ofPoint_self,
      Nat.cast_one]
  · rw [Finsupp.single_eq_of_ne' h,
      WeilDivisor.coeff_ofPoint_of_ne fun h' ↦ h (place_eq_iff.1 h'.symm), Nat.cast_zero]

/-! ### The divisor of a chord line -/

omit [IsAlgClosed k] in
/-- An irreducible cubic does not divide a chord line through a simple point. -/
theorem not_dvd_chordLine (A B : CubicGroup F O) : ¬ F ∣ chordLine F A.point B.point :=
  fun h ↦ hirr.out.not_isUnit (isRelPrime_chordLine hF.out hirr.out (by norm_num)
    (Or.inr A.isSimplePoint) h dvd_rfl)

/-- The coefficient of the divisor of the chord line through `A` and `B`, at a place `Q`, is the
intersection number of the line and `C` at the centre of `Q`. -/
theorem coeff_formDivisor_chordLine (A B : CubicGroup F O) (Q : Place k (functionField hF.out)) :
    (formDivisor hF.out (isHomogeneous_chordLine F A.point B.point)).coeff Q =
      (intersectionCycle (chordLine F A.point B.point) F (center hF.out Q).1 : ℕ) := by
  classical
  have hL := isHomogeneous_chordLine F A.point B.point
  have hrel := isRelPrime_chordLine hF.out hirr.out (by norm_num) (Or.inr A.isSimplePoint)
    (Q := B.point)
  have hZ := intersectionCycle_chordLine hF.out hirr.out A.isSimplePoint B.isSimplePoint
  by_cases hv : eval (center hF.out Q).1.rep (chordLine F A.point B.point) = 0
  · have hsupp :
        (center hF.out Q).1 ∈ (intersectionCycle (chordLine F A.point B.point) F).support :=
      (mem_support_intersectionCycle_iff hL hF.out hrel).2
        ⟨hv, (mem_zeroLocus_ideal_iff hF.out).1 (center hF.out Q).2⟩
    have hQ : IsSimplePoint F (center hF.out Q).1 := by
      rw [hZ] at hsupp
      rcases Finset.mem_union.1 (Finsupp.support_add hsupp) with h | h
      · rcases Finset.mem_union.1 (Finsupp.support_add h) with h | h
        · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)]
          exact A.isSimplePoint
        · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)]
          exact B.isSimplePoint
      · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)]
        exact isSimplePoint_thirdPoint hF.out hirr.out A.isSimplePoint B.isSimplePoint
    rw [coeff_formDivisor_of_isSimplePoint hL (not_dvd_chordLine A B) hQ,
      intersectionNumber_comm, ← intersectionCycle_apply hL hF.out hrel, ENat.toNat_natCast]
  · have h0 : intersectionCycle (chordLine F A.point B.point) F (center hF.out Q).1 = 0 :=
      Finsupp.notMem_support_iff.1 fun h ↦
        hv ((mem_support_intersectionCycle_iff hL hF.out hrel).1 h).1
    rw [h0, coeff_formDivisor_eq_untopD, ordForm_eq_zero_of_eval_ne_zero hL hv]
    rfl

/-- **The divisor of a chord line**: for points `A`, `B` of the group of an irreducible cubic `C`,
the chord line `L` through `A` and `B` (the tangent if `A = B`) cuts out
`div L = A + B + φ(A, B)` on the nonsingular model of `C`. -/
theorem formDivisor_chordLine (A B : CubicGroup F O) :
    formDivisor hF.out (isHomogeneous_chordLine F A.point B.point) =
      WeilDivisor.ofPoint A.place + WeilDivisor.ofPoint B.place +
        WeilDivisor.ofPoint (chord A B).place := by
  refine WeilDivisor.ext fun Q ↦ ?_
  rw [coeff_formDivisor_chordLine, intersectionCycle_chordLine hF.out hirr.out A.isSimplePoint
    B.isSimplePoint, WeilDivisor.coeff_add, WeilDivisor.coeff_add, coeff_ofPoint_place,
    coeff_ofPoint_place, coeff_ofPoint_place, point_chord]
  simp only [Finsupp.add_apply, Nat.cast_add]

/-! ### Linear equivalence of points -/

/-- **(a) Points of a nonsingular cubic are linearly equivalent only if equal**: `A ≡ B` iff
`A = B`, since a nonsingular cubic has genus one. -/
theorem linearlyEquivalent_ofPoint_place_iff (hns : IsNonsingular F) {A B : CubicGroup F O} :
    (Place.orderSystem (functionField.isFunctionField hF.out)).LinearlyEquivalent
      (WeilDivisor.ofPoint A.place) (WeilDivisor.ofPoint B.place) ↔ A = B := by
  have hK := functionField.isFunctionField hF.out
  refine ⟨fun h ↦ place_injective (Place.eq_of_linearlyEquivalent_ofPoint_of_genus_pos hK ?_
    (Place.degree_eq_one_of_isAlgClosed_of_isFunctionField _ hK) h),
    fun h ↦ h ▸ WeilDivisor.OrderSystem.LinearlyEquivalent.refl _ _⟩
  rw [genus_functionField_of_isNonsingular hF.out hns]
  norm_num

/-- **(b) Linear equivalence of pairs of points of a nonsingular cubic**: `A + B ≡ C + D` iff
the chords through `A`, `B` and through `C`, `D` meet the cubic again in the same point. -/
theorem linearlyEquivalent_add_iff_chord_eq (hns : IsNonsingular F) {A B C D : CubicGroup F O} :
    (Place.orderSystem (functionField.isFunctionField hF.out)).LinearlyEquivalent
      (WeilDivisor.ofPoint A.place + WeilDivisor.ofPoint B.place)
      (WeilDivisor.ofPoint C.place + WeilDivisor.ofPoint D.place) ↔ chord A B = chord C D := by
  have hP := principal_formQuotient (hF := hF.out) (isHomogeneous_chordLine F A.point B.point)
    (isHomogeneous_chordLine F C.point D.point) (not_dvd_chordLine A B) (not_dvd_chordLine C D)
  rw [formDivisor_chordLine, formDivisor_chordLine] at hP
  have hc := (Divisor.linearlyEquivalent_iff (functionField.isFunctionField hF.out)).2 ⟨_, hP⟩
  rw [← WeilDivisor.OrderSystem.divisorClass_eq_iff, map_add,
    map_add (WeilDivisor.OrderSystem.divisorClass _) (_ + _)] at hc
  rw [← linearlyEquivalent_ofPoint_place_iff hns, ← WeilDivisor.OrderSystem.divisorClass_eq_iff,
    ← WeilDivisor.OrderSystem.divisorClass_eq_iff]
  constructor
  · intro h
    rw [h] at hc
    exact add_left_cancel hc
  · intro h
    rw [h] at hc
    exact add_right_cancel hc

variable [hO : Fact (IsSimplePoint F O)]

/-- **(c) The group law of a nonsingular cubic is linear equivalence**: `A ⊕ B = C` iff
`A + B ≡ C + O`. -/
theorem add_eq_iff_linearlyEquivalent (hns : IsNonsingular F) {A B C : CubicGroup F O} :
    A + B = C ↔ (Place.orderSystem (functionField.isFunctionField hF.out)).LinearlyEquivalent
      (WeilDivisor.ofPoint A.place + WeilDivisor.ofPoint B.place)
      (WeilDivisor.ofPoint C.place + WeilDivisor.ofPoint (0 : CubicGroup F O).place) := by
  rw [linearlyEquivalent_add_iff_chord_eq hns, chord_eq_sub, chord_eq_sub C 0, sub_zero, sub_sub,
    sub_right_inj]

/-! ### The isomorphism with the degree-zero divisor class group -/

/-- For a nonsingular cubic, the points of the group are the places of `k(C)`, all of degree
one: `A ↦` the place at `A`. -/
noncomputable def placeEquiv (hns : IsNonsingular F) :
    CubicGroup F O ≃ {Q : Place k (functionField hF.out) // Q.degree = 1} where
  toFun A := ⟨A.place, Place.degree_eq_one_of_isAlgClosed_of_isFunctionField _
    (functionField.isFunctionField hF.out)⟩
  invFun Q := ⟨(center hF.out Q.1).1, hns.isSimplePoint (center hF.out Q.1)⟩
  left_inv A := CubicGroup.ext (center_place A)
  right_inv _ := Subtype.ext (place_eq_iff.2 rfl)

omit hO in
@[simp]
theorem coe_placeEquiv_apply (hns : IsNonsingular F) (A : CubicGroup F O) :
    (placeEquiv hns A : Place k (functionField hF.out)) = A.place :=
  (rfl)

omit hO in
@[simp]
theorem point_placeEquiv_symm_apply (hns : IsNonsingular F)
    (Q : {Q : Place k (functionField hF.out) // Q.degree = 1}) :
    ((placeEquiv (O := O) hns).symm Q).point = (center hF.out Q.1).1 :=
  (rfl)

omit hO in
/-- A nonsingular cubic has genus one. -/
theorem genus_functionField_eq_one (hns : IsNonsingular F) :
    genus k (functionField hF.out) = 1 := by
  rw [genus_functionField_of_isNonsingular hF.out hns]

/-- **The chord–tangent group of a nonsingular cubic is its degree-zero divisor class group**:
`A ↦ [A - O]` is an isomorphism of groups from `CubicGroup F O` onto `Cl⁰(k(C))`
(`classGroupEquiv_apply`). -/
noncomputable def classGroupEquiv (hns : IsNonsingular F) :
    CubicGroup F O ≃+ (Divisor.degreeClass (functionField.isFunctionField hF.out)).ker :=
  AddEquiv.mk' ((placeEquiv hns).trans (Place.degreeOneEquivDegreeZeroClassGroup
      (functionField.isFunctionField hF.out) (genus_functionField_eq_one hns)
      (Place.degree_eq_one_of_isAlgClosed_of_isFunctionField (0 : CubicGroup F O).place
        (functionField.isFunctionField hF.out))))
    fun _ _ ↦ ((Place.degreeOneEquivDegreeZeroClassGroup_add_eq_iff _ _ _ _ _ _).2
      ((add_eq_iff_linearlyEquivalent hns).1 rfl)).symm

/-- The isomorphism sends `A` to the class of `A - O`. -/
theorem classGroupEquiv_apply (hns : IsNonsingular F) (A : CubicGroup F O) :
    (classGroupEquiv hns A :
        (Place.orderSystem (functionField.isFunctionField hF.out)).ClassGroup) =
      (Place.orderSystem (functionField.isFunctionField hF.out)).divisorClass
        (WeilDivisor.ofPoint A.place - WeilDivisor.ofPoint (0 : CubicGroup F O).place) := by
  rw [classGroupEquiv]
  exact Place.val_degreeOneEquivDegreeZeroClassGroup_apply _ _ _ _

end CubicGroup

/-! ### The milestone -/

/-- **The chord–tangent group of a nonsingular cubic as its divisor class group** (Fulton, §8.1,
Problems 8.3 and 8.6). Let `k` be algebraically closed, `C : F = 0` a nonsingular plane cubic,
`O` a point of `C`, and `⊕` the chord–tangent addition with zero `O` on `CubicGroup F O`, the
points of `C` (`CubicGroup.equivZeroLocus`). Write `A ≡ B` for linear equivalence of the
divisors of the places at the points on the nonsingular model of `C`, and `φ(A, B)` for the third
point of the chord through `A` and `B` (the tangent if `A = B`). Then

* (a) `A ≡ B` iff `A = B`;
* (b) `A + B ≡ C + D` iff `φ(A, B) = φ(C, D)`;
* (c) `A ⊕ B = C` iff `A + B ≡ C + O`;
* (d) `A ↦ [A - O]` is an isomorphism of groups from `(C, ⊕)` onto the group `Cl⁰` of divisor
  classes of degree zero of `k(C)`.

Milestone: *Chord–tangent group of a nonsingular cubic as its divisor class group*. -/
theorem CubicGroup.classGroupEquiv_spec [IsAlgClosed k] {O : ℙ k (Fin 3 → k)}
    (hF : F.IsHomogeneous 3) (hns : IsNonsingular F) (hO : O ∈ ProjectiveSpace.zeroLocus {F}) :
    letI : Fact (F.IsHomogeneous 3) := ⟨hF⟩
    letI : Fact (Irreducible F) := ⟨hns.irreducible hF three_ne_zero⟩
    letI : Fact (IsSimplePoint F O) := ⟨(isNonsingular_iff_forall_isSimplePoint hF).1 hns O hO⟩
    (∀ A B : CubicGroup F O,
      (Place.orderSystem (functionField.isFunctionField hF)).LinearlyEquivalent
        (WeilDivisor.ofPoint A.place) (WeilDivisor.ofPoint B.place) ↔ A = B) ∧
    (∀ A B C D : CubicGroup F O,
      (Place.orderSystem (functionField.isFunctionField hF)).LinearlyEquivalent
        (WeilDivisor.ofPoint A.place + WeilDivisor.ofPoint B.place)
        (WeilDivisor.ofPoint C.place + WeilDivisor.ofPoint D.place) ↔
        thirdPoint F A.point B.point = thirdPoint F C.point D.point) ∧
    (∀ A B C : CubicGroup F O, A + B = C ↔
      (Place.orderSystem (functionField.isFunctionField hF)).LinearlyEquivalent
        (WeilDivisor.ofPoint A.place + WeilDivisor.ofPoint B.place)
        (WeilDivisor.ofPoint C.place + WeilDivisor.ofPoint (0 : CubicGroup F O).place)) ∧
    ∃ e : CubicGroup F O ≃+ (Divisor.degreeClass (functionField.isFunctionField hF)).ker,
      ∀ A : CubicGroup F O,
        (e A : (Place.orderSystem (functionField.isFunctionField hF)).ClassGroup) =
          (Place.orderSystem (functionField.isFunctionField hF)).divisorClass
            (WeilDivisor.ofPoint A.place - WeilDivisor.ofPoint (0 : CubicGroup F O).place) := by
  let : Fact (F.IsHomogeneous 3) := ⟨hF⟩
  let : Fact (Irreducible F) := ⟨hns.irreducible hF three_ne_zero⟩
  let : Fact (IsSimplePoint F O) := ⟨(isNonsingular_iff_forall_isSimplePoint hF).1 hns O hO⟩
  exact ⟨fun _ _ ↦ CubicGroup.linearlyEquivalent_ofPoint_place_iff hns,
    fun A B C D ↦ (CubicGroup.linearlyEquivalent_add_iff_chord_eq hns).trans
      (by rw [← CubicGroup.point_inj, CubicGroup.point_chord, CubicGroup.point_chord]),
    fun _ _ _ ↦ CubicGroup.add_eq_iff_linearlyEquivalent hns,
    CubicGroup.classGroupEquiv hns, CubicGroup.classGroupEquiv_apply hns⟩

end PlaneCurves.Projective

end
