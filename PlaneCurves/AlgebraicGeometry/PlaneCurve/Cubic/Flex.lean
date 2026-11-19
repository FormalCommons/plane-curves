/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Cubic.GroupLaw
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Hessian.Flex

/-!
# Flexes of a plane cubic and torsion of its group

Let `F` be an irreducible cubic over an algebraically closed field. A simple point `P` of `F` is a
flex iff the tangent at `P` meets `F` in `3P`, that is, iff `φ(P, P) = P`. When the base point `O`
of the chord–tangent group `CubicGroup F O` is a flex, `φ(O, O) = O`, so three simple points are
the intersection of `F` with a line iff their sum is zero. Then ([Fulton2008], §5.6,
Problems 5.34, 5.37):

* a simple point `A` is a flex iff `3A = 0`, so the flexes form the subgroup of `3`-torsion;
* the line through two flexes meets `F` in a third flex;
* a point `A ≠ O` has order two iff the tangent at `A` passes through `O`.

These hold in every characteristic, and for the simple points of any irreducible cubic.

## Main results

* `PlaneCurves.Projective.isFlex_iff_thirdPoint_self_eq`: a simple point `P` is a flex iff
  `φ(P, P) = P`.
* `PlaneCurves.Projective.eval_tangentLine_eq_zero_iff_thirdPoint_self_eq`: for simple points
  `P ≠ Q`, the tangent at `P` passes through `Q` iff `φ(P, P) = Q`.
* `PlaneCurves.Projective.isFlex_thirdPoint`: the third point on the line through two flexes
  is a flex.
* `PlaneCurves.Projective.CubicGroup.chord_zero_zero_of_isFlex`: `φ(O, O) = O` for a flex `O`.
* `PlaneCurves.Projective.CubicGroup.exists_line_iff_add_add_eq_zero`: for a flex `O`, three
  simple points are the intersection of `F` with a line iff their sum is zero.
* `PlaneCurves.Projective.CubicGroup.isFlex_iff_three_nsmul_eq_zero`: for a flex `O`, `A` is a
  flex iff `3A = 0`.
* `PlaneCurves.Projective.CubicGroup.mem_torsionBy_three_iff_isFlex`: the `3`-torsion subgroup
  consists of the flexes.
* `PlaneCurves.Projective.CubicGroup.two_nsmul_eq_zero_iff`: for a flex `O` and `A ≠ O`,
  `2A = 0` iff the tangent at `A` passes through `O`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.6
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization
open Finsupp (single)
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k}
  {O P Q : ℙ k (Fin 3 → k)}
/-! ### Flexes and the third point -/

/-- A simple point `P` of an irreducible cubic `F` is a flex iff the tangent at `P` meets `F`
again at `P`: `φ(P, P) = P`. -/
theorem isFlex_iff_thirdPoint_self_eq (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hP : IsSimplePoint F P) : IsFlex F P ↔ thirdPoint F P P = P := by
  have hZ := intersectionCycle_chordLine hF hirr hP hP
  have hL := isHomogeneous_chordLine F P P
  have hrel := isRelPrime_chordLine (Q := P) hF hirr (by norm_num) (Or.inr hP)
  have h := intersectionCycle_apply hL hF hrel P
  rw [hZ, intersectionNumber_comm, chordLine_self] at h
  rw [isFlex_def, and_iff_right hP, ← h]
  by_cases hR : thirdPoint F P P = P
  · simp [hR]
  · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne' hR, hR, iff_false, not_le]
    norm_num

/-- For simple points `P ≠ Q` of an irreducible cubic `F`, the tangent at `P` passes through `Q`
iff `φ(P, P) = Q`. -/
theorem eval_tangentLine_eq_zero_iff_thirdPoint_self_eq (hF : F.IsHomogeneous 3)
    (hirr : Irreducible F) (hP : IsSimplePoint F P) (hQ : IsSimplePoint F Q) (hPQ : P ≠ Q) :
    eval Q.rep (tangentLine F P.rep) = 0 ↔ thirdPoint F P P = Q := by
  have hZ := intersectionCycle_chordLine hF hirr hP hP
  have hL := isHomogeneous_chordLine F P P
  have hrel := isRelPrime_chordLine (Q := P) hF hirr (by norm_num) (Or.inr hP)
  have h := mem_support_intersectionCycle_iff (P := Q) hL hF hrel
  rw [hZ, chordLine_self] at h
  rw [← h.trans (and_iff_left hQ.eval_rep_eq_zero), Finsupp.mem_support_iff]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_of_ne hPQ.symm, zero_add, ne_eq,
    Finsupp.single_apply_eq_zero, one_ne_zero, imp_false, not_not]
  exact eq_comm

namespace CubicGroup

variable [hF : Fact (F.IsHomogeneous 3)] [hirr : Fact (Irreducible F)]
  [hO : Fact (IsSimplePoint F O)]

/-- If the base point `O` is a flex, then `φ(O, O) = O`. -/
theorem chord_zero_zero_of_isFlex (hO' : IsFlex F O) : chord (0 : CubicGroup F O) 0 = 0 :=
  CubicGroup.ext <| by
    rw [point_chord, point_zero]
    exact (isFlex_iff_thirdPoint_self_eq hF.out hirr.out hO.out).1 hO'

/-- **The collinearity criterion for a flex as base point** ([Fulton2008], §5.6). If the base
point `O` is a flex, then simple points `A`, `B`, `C` of `F` are the intersection
`L • F = A + B + C` of `F` with a line `L` iff `A + B + C = 0`. -/
theorem exists_line_iff_add_add_eq_zero (hO' : IsFlex F O) (A B C : CubicGroup F O) :
    (∃ L : MvPolynomial (Fin 3) k, L.IsHomogeneous 1 ∧ L ≠ 0 ∧
      intersectionCycle L F = single A.point 1 + single B.point 1 + single C.point 1) ↔
      A + B + C = 0 := by
  rw [exists_line_iff_add_add_eq, chord_zero_zero_of_isFlex hO']

/-- If the base point `O` is a flex, then `φ(A, B) = -A - B`. -/
theorem chord_eq_neg_sub_of_isFlex (hO' : IsFlex F O) (A B : CubicGroup F O) :
    chord A B = -A - B := by
  rw [chord_eq_sub, chord_zero_zero_of_isFlex hO', zero_sub]

/-- **Flexes are the points of order dividing three** ([Fulton2008], Problem 5.37 (b)). If the
base point `O` of the group of an irreducible cubic `F` is a flex, then a simple point `A` is a
flex iff `3A = 0`. -/
theorem isFlex_iff_three_nsmul_eq_zero (hO' : IsFlex F O) (A : CubicGroup F O) :
    IsFlex F A.point ↔ 3 • A = 0 := by
  rw [isFlex_iff_thirdPoint_self_eq hF.out hirr.out A.isSimplePoint, ← point_chord, point_inj,
    chord_eq_neg_sub_of_isFlex hO', ← sub_eq_zero, show -A - A - A = -(3 • A) by abel,
    neg_eq_zero]

/-- If the base point `O` is a flex, then the `3`-torsion subgroup of the group of `F` consists
of the flexes of `F` ([Fulton2008], Problem 5.37 (c)). -/
theorem mem_torsionBy_three_iff_isFlex (hO' : IsFlex F O) {A : CubicGroup F O} :
    A ∈ AddSubgroup.torsionBy (CubicGroup F O) 3 ↔ IsFlex F A.point := by
  rw [isFlex_iff_three_nsmul_eq_zero hO']
  exact_mod_cast AddSubgroup.torsionBy.nsmul_iff (A := CubicGroup F O) (n := 3) (x := A)

/-- **Points of order two** ([Fulton2008], Problem 5.37 (c)). If the base point `O` is a flex,
then a point `A ≠ O` of the group of `F` has `2A = 0` iff the tangent at `A` passes through
`O`. -/
theorem two_nsmul_eq_zero_iff (hO' : IsFlex F O) {A : CubicGroup F O} (hA : A ≠ 0) :
    2 • A = 0 ↔ eval O.rep (tangentLine F A.point.rep) = 0 := by
  rw [eval_tangentLine_eq_zero_iff_thirdPoint_self_eq hF.out hirr.out A.isSimplePoint hO.out
    (fun h ↦ hA (CubicGroup.ext h)), ← point_chord]
  refine Iff.trans ?_ (point_inj (B := 0)).symm
  rw [chord_eq_neg_sub_of_isFlex hO', two_nsmul, neg_sub_left, neg_eq_zero]

end CubicGroup

/-- **The line through two flexes** ([Fulton2008], Problem 5.34). The line through two flexes
`P`, `Q` of an irreducible cubic, the tangent if `P = Q`, meets it in a third flex. -/
theorem isFlex_thirdPoint (hF : F.IsHomogeneous 3) (hirr : Irreducible F) (hP : IsFlex F P)
    (hQ : IsFlex F Q) : IsFlex F (thirdPoint F P Q) := by
  let : Fact (F.IsHomogeneous 3) := ⟨hF⟩
  let : Fact (Irreducible F) := ⟨hirr⟩
  let : Fact (IsSimplePoint F P) := ⟨hP.isSimplePoint⟩
  let B : CubicGroup F P := ⟨Q, hQ.isSimplePoint⟩
  have hB := (CubicGroup.isFlex_iff_three_nsmul_eq_zero hP B).1 hQ
  have h := (CubicGroup.isFlex_iff_three_nsmul_eq_zero hP (CubicGroup.chord 0 B)).2 (by
    rw [CubicGroup.chord_eq_neg_sub_of_isFlex hP, neg_zero, zero_sub, smul_neg, hB, neg_zero])
  rwa [CubicGroup.point_chord, CubicGroup.point_zero] at h

end PlaneCurves.Projective

end
