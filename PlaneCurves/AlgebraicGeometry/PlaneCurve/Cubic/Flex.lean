/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Cubic.GroupLaw
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Cubic.Weierstrass
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Hessian.Flex
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Surjective
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure
public import TauCeti.Algebra.Module.Torsion.Basic

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

When `F` is nonsingular, the group is, through the isomorphism with the group of a Weierstrass
curve (`PlaneCurves.Projective.exists_addEquiv_weierstrass_of_isFlex`), that of an elliptic
curve, so Tau Ceti's structure of its torsion gives: the `N`-torsion is `ℤ/N × ℤ/N` when `N` is
invertible in `k`. In particular a nonsingular cubic with a flex has nine flexes when `3 ≠ 0`,
and four points killed by `2` when `2 ≠ 0`; on the Legendre cubic `Y²Z = X(X - Z)(X - λZ)` the
three points of order two are `[0 : 0 : 1]`, `[1 : 0 : 1]` and `[λ : 0 : 1]`.

Every point is also divisible by `2` when `2 ≠ 0`, so for a point `P` the equation `2Q = -P` has
four solutions; these are the points `Q ≠ P`, besides `Q = P` when `P` is a flex, whose tangent
passes through `P`, and distinct ones have distinct tangents. So four tangents to `F` at points
other than `P` pass through `P`, and three if `P` is a flex (Problem 5.37 (f)).

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
* `PlaneCurves.Projective.CubicGroup.nonempty_torsionBy_addEquiv_prod`: for `F` nonsingular,
  a flex `O` and `N ≠ 0` in `k`, the `N`-torsion of `CubicGroup F O` is `ℤ/N × ℤ/N`; the cases
  `N = 3` and `N = 2` are `nonempty_torsionBy_three_addEquiv_prod` and
  `nonempty_torsionBy_two_addEquiv_prod`.
* `PlaneCurves.Projective.IsFlex.ncard_setOf_isFlex`: a nonsingular cubic with a flex has nine
  flexes when `3 ≠ 0`.
* `WeierstrassCurve.Projective.point_image_setOf_addOrderOf_eq_two_of_legendre`: the points of
  order two on a Legendre cubic.
* `PlaneCurves.Projective.CubicGroup.nsmul_surjective`: for `F` nonsingular, a flex `O` and
  `n ≠ 0` in `k`, every point of `CubicGroup F O` is divisible by `n`.
* `PlaneCurves.Projective.IsNonsingular.ncard_setOf_eval_tangentLine_eq_zero`: when `2 ≠ 0`,
  a point `P` of a nonsingular cubic lies on the tangent at exactly four points `Q ≠ P`, or
  three if `P` is a flex; `IsNonsingular.ncard_setOf_span_tangentLine` counts these tangents as
  lines.
* `PlaneCurves.Projective.isFlex_cubicGroup_torsion_spec`: all of the above together.

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

/-! ### Torsion of the group of a nonsingular cubic -/

namespace CubicGroup

variable [Fact (F.IsHomogeneous 3)] [Fact (Irreducible F)] [Fact (IsSimplePoint F O)]

/-- **The `N`-torsion of the group of a nonsingular cubic.** If `F` is a nonsingular cubic over
an algebraically closed field, `O` is a flex of `F` and `N` is invertible in `k`, then the
`N`-torsion subgroup of the chord–tangent group `CubicGroup F O` is isomorphic to
`ℤ/N × ℤ/N`. -/
theorem nonempty_torsionBy_addEquiv_prod (hns : IsNonsingular F) (hO' : IsFlex F O) (N : ℕ)
    (hN : (N : k) ≠ 0) :
    Nonempty (AddSubgroup.torsionBy (CubicGroup F O) (N : ℤ) ≃+ ZMod N × ZMod N) := by
  classical
  obtain ⟨W, hΔ, ⟨e⟩⟩ := exists_addEquiv_weierstrass_of_isFlex hO'
  have : W.IsElliptic := ⟨(hΔ hns).isUnit⟩
  obtain ⟨f⟩ := W.torsion_addEquiv_prod N hN
  exact ⟨(AddEquiv.torsionByCongr (e.trans
    (WeierstrassCurve.Projective.Point.toAffineAddEquiv W.toProjective)) N).trans f⟩

/-- **The `3`-torsion of the group of a nonsingular cubic** ([Fulton2008], Problem 5.37 (c)). If
`F` is a nonsingular cubic over an algebraically closed field with `3 ≠ 0`, and `O` is a flex
of `F`, then the `3`-torsion subgroup of `CubicGroup F O`, the subgroup of flexes, is isomorphic
to `ℤ/3 × ℤ/3`. -/
theorem nonempty_torsionBy_three_addEquiv_prod (hns : IsNonsingular F) (hO' : IsFlex F O)
    (h3 : (3 : k) ≠ 0) :
    Nonempty (AddSubgroup.torsionBy (CubicGroup F O) 3 ≃+ ZMod 3 × ZMod 3) :=
  nonempty_torsionBy_addEquiv_prod hns hO' 3 (by exact_mod_cast h3)

/-- **The `2`-torsion of the group of a nonsingular cubic** ([Fulton2008], Problem 5.37 (e)). If
`F` is a nonsingular cubic over an algebraically closed field with `2 ≠ 0`, and `O` is a flex
of `F`, then the `2`-torsion subgroup of `CubicGroup F O` is isomorphic to `ℤ/2 × ℤ/2`. -/
theorem nonempty_torsionBy_two_addEquiv_prod (hns : IsNonsingular F) (hO' : IsFlex F O)
    (h2 : (2 : k) ≠ 0) :
    Nonempty (AddSubgroup.torsionBy (CubicGroup F O) 2 ≃+ ZMod 2 × ZMod 2) :=
  nonempty_torsionBy_addEquiv_prod hns hO' 2 (by exact_mod_cast h2)

end CubicGroup

/-- **A nonsingular cubic with a flex has nine flexes** ([Fulton2008], Problem 5.37 (c)). If `F`
is a nonsingular cubic over an algebraically closed field with `3 ≠ 0`, and `F` has a flex, then
`F` has exactly nine flexes. Unlike `IsNonsingular.ncard_setOf_isFlex`, this allows
characteristic `2`. -/
theorem IsFlex.ncard_setOf_isFlex (hF : F.IsHomogeneous 3) (hns : IsNonsingular F)
    (hO : IsFlex F O) (h3 : (3 : k) ≠ 0) : {P | IsFlex F P}.ncard = 9 := by
  have : Fact (F.IsHomogeneous 3) := ⟨hF⟩
  have : Fact (Irreducible F) := ⟨hns.irreducible hF three_ne_zero⟩
  have : Fact (IsSimplePoint F O) := ⟨hO.isSimplePoint⟩
  obtain ⟨e⟩ := CubicGroup.nonempty_torsionBy_three_addEquiv_prod hns hO h3
  have hS : {P | IsFlex F P} =
      CubicGroup.point '' (AddSubgroup.torsionBy (CubicGroup F O) 3 : Set (CubicGroup F O)) := by
    ext P
    refine ⟨fun hP ↦ ⟨⟨P, hP.isSimplePoint⟩, ?_, rfl⟩, ?_⟩
    · exact (CubicGroup.mem_torsionBy_three_iff_isFlex hO).2 hP
    · rintro ⟨A, hA, rfl⟩
      exact (CubicGroup.mem_torsionBy_three_iff_isFlex hO).1 hA
  rw [hS, Set.ncard_image_of_injective _ CubicGroup.point_injective, ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe, Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod]

/-! ### Tangent lines through a point of a nonsingular cubic -/

/-- The tangent at a simple point `Q` of an irreducible cubic `F` meets `F` in at most one point
other than `Q`: if it passes through `P ≠ Q` and `R ≠ Q`, then `P = R`. -/
theorem eq_of_eval_tangentLine_eq_zero (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    {R : ℙ k (Fin 3 → k)} (hQ : IsSimplePoint F Q) (hP : IsSimplePoint F P)
    (hR : IsSimplePoint F R) (hQP : Q ≠ P) (hQR : Q ≠ R)
    (hP' : eval P.rep (tangentLine F Q.rep) = 0) (hR' : eval R.rep (tangentLine F Q.rep) = 0) :
    P = R :=
  ((eval_tangentLine_eq_zero_iff_thirdPoint_self_eq hF hirr hQ hP hQP).1 hP').symm.trans
    ((eval_tangentLine_eq_zero_iff_thirdPoint_self_eq hF hirr hQ hR hQR).1 hR')

namespace CubicGroup

variable [hF : Fact (F.IsHomogeneous 3)] [hirr : Fact (Irreducible F)]
  [Fact (IsSimplePoint F O)]

/-- If the base point `O` is a flex, then for points `B ≠ A` of the group of `F`, the tangent
at `B` passes through `A` iff `2B = -A`. -/
theorem eval_tangentLine_eq_zero_iff_two_nsmul_eq_neg (hO' : IsFlex F O) {A B : CubicGroup F O}
    (hBA : B ≠ A) : eval A.point.rep (tangentLine F B.point.rep) = 0 ↔ 2 • B = -A := by
  rw [eval_tangentLine_eq_zero_iff_thirdPoint_self_eq hF.out hirr.out B.isSimplePoint
    A.isSimplePoint (fun h ↦ hBA (CubicGroup.ext h)), ← point_chord, point_inj,
    chord_eq_neg_sub_of_isFlex hO']
  constructor <;> intro h
  · rw [← h]; abel
  · rw [← neg_neg A, ← h]; abel

/-- **Points of the group of a nonsingular cubic are divisible.** If `F` is a nonsingular cubic
over an algebraically closed field, `O` is a flex of `F` and `n` is invertible in `k`, then
`A ↦ n • A` is surjective on `CubicGroup F O`. -/
theorem nsmul_surjective (hns : IsNonsingular F) (hO' : IsFlex F O) {n : ℕ} (hn : (n : k) ≠ 0) :
    Function.Surjective fun A : CubicGroup F O ↦ n • A := by
  classical
  obtain ⟨W, hΔ, ⟨e⟩⟩ := exists_addEquiv_weierstrass_of_isFlex hO'
  have : W.IsElliptic := ⟨(hΔ hns).isUnit⟩
  let f := e.trans (WeierstrassCurve.Projective.Point.toAffineAddEquiv W.toProjective)
  intro B
  obtain ⟨P, hP⟩ := W.toAffine.nsmul_surjective hn (f B)
  refine ⟨f.symm P, ?_⟩
  dsimp only at hP ⊢
  rw [← map_nsmul, hP, AddEquiv.symm_apply_apply]

/-- If `F` is a nonsingular cubic over an algebraically closed field with `2 ≠ 0`, and `O` is a
flex of `F`, then every point `A` of `CubicGroup F O` has exactly four halves: the solutions
of `2B = A` are a coset of the `2`-torsion. -/
theorem ncard_setOf_two_nsmul_eq (hns : IsNonsingular F) (hO' : IsFlex F O) (h2 : (2 : k) ≠ 0)
    (A : CubicGroup F O) : {B : CubicGroup F O | 2 • B = A}.ncard = 4 := by
  obtain ⟨B₀, hB₀⟩ := nsmul_surjective hns hO' (n := 2) (by exact_mod_cast h2) A
  dsimp only at hB₀
  obtain ⟨e⟩ := nonempty_torsionBy_two_addEquiv_prod hns hO' h2
  have hmem (T : CubicGroup F O) : T ∈ AddSubgroup.torsionBy (CubicGroup F O) 2 ↔ 2 • T = 0 := by
    exact_mod_cast AddSubgroup.torsionBy.nsmul_iff (A := CubicGroup F O) (n := 2) (x := T)
  have hS : {B : CubicGroup F O | 2 • B = A} =
      (B₀ + ·) '' (AddSubgroup.torsionBy (CubicGroup F O) 2 : Set (CubicGroup F O)) := by
    ext B
    simp only [Set.mem_ofPred_eq, Set.mem_image, SetLike.mem_coe, hmem]
    refine ⟨fun h ↦ ⟨B - B₀, by rw [smul_sub, h, hB₀, sub_self], add_sub_cancel _ _⟩, ?_⟩
    rintro ⟨T, hT, rfl⟩
    rw [smul_add, hT, add_zero, hB₀]
  rw [hS, Set.ncard_image_of_injective _ (add_right_injective B₀), ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe, Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zmod]

open scoped Classical in
/-- If `F` is a nonsingular cubic over an algebraically closed field with `2 ≠ 0`, and `O` is a
flex of `F`, then a point `A` of `CubicGroup F O` has four solutions `B ≠ A` of `2B = -A`, or
three if `3A = 0`. -/
theorem ncard_setOf_ne_and_two_nsmul_eq_neg (hns : IsNonsingular F) (hO' : IsFlex F O)
    (h2 : (2 : k) ≠ 0) (A : CubicGroup F O) :
    {B : CubicGroup F O | B ≠ A ∧ 2 • B = -A}.ncard = if 3 • A = 0 then 3 else 4 := by
  have hS : {B : CubicGroup F O | B ≠ A ∧ 2 • B = -A} = {B | 2 • B = -A} \ {A} := by
    ext; simp [and_comm]
  have hA : 2 • A = -A ↔ 3 • A = 0 := by rw [eq_neg_iff_add_eq_zero, ← succ_nsmul]
  have h4 := ncard_setOf_two_nsmul_eq hns hO' h2 (-A)
  rw [hS]
  split_ifs with h
  · rw [Set.ncard_sdiff_singleton_of_mem (s := {B | 2 • B = -A}) (hA.2 h), h4]
  · rwa [Set.sdiff_singleton_eq_self fun h' ↦ h (hA.1 h')]

end CubicGroup

open scoped Classical in
/-- **Tangents from a point of a nonsingular cubic, counted by their points of contact.** Let `F`
be a nonsingular cubic over an algebraically closed field with `2 ≠ 0`, and `P` a point of `F`.
There are exactly four points `Q ≠ P` of `F` whose tangent passes through `P`, and three if `P`
is a flex. -/
theorem IsNonsingular.ncard_setOf_eval_tangentLine_eq_zero (hF : F.IsHomogeneous 3)
    (hns : IsNonsingular F) (h2 : (2 : k) ≠ 0) (hP : P ∈ ProjectiveSpace.zeroLocus {F}) :
    {Q | Q ∈ ProjectiveSpace.zeroLocus {F} ∧ Q ≠ P ∧ eval P.rep (tangentLine F Q.rep) = 0}.ncard =
      if IsFlex F P then 3 else 4 := by
  obtain ⟨O, hO⟩ := hns.exists_isFlex hF le_rfl (by
    have := mul_ne_zero h2 h2; norm_num at this ⊢; exact this)
  have : Fact (F.IsHomogeneous 3) := ⟨hF⟩
  have : Fact (Irreducible F) := ⟨hns.irreducible hF three_ne_zero⟩
  have : Fact (IsSimplePoint F O) := ⟨hO.isSimplePoint⟩
  have hsimple := (isNonsingular_iff_forall_isSimplePoint hF).1 hns
  let A : CubicGroup F O := ⟨P, hsimple P hP⟩
  have hS : {Q | Q ∈ ProjectiveSpace.zeroLocus {F} ∧ Q ≠ P ∧
      eval P.rep (tangentLine F Q.rep) = 0} =
      CubicGroup.point '' {B : CubicGroup F O | B ≠ A ∧ 2 • B = -A} := by
    ext Q
    constructor
    · rintro ⟨hQ, hQP, h⟩
      have hBA : (⟨Q, hsimple Q hQ⟩ : CubicGroup F O) ≠ A := fun h' ↦
        hQP (congrArg CubicGroup.point h')
      exact ⟨(⟨Q, hsimple Q hQ⟩ : CubicGroup F O),
        ⟨hBA, (CubicGroup.eval_tangentLine_eq_zero_iff_two_nsmul_eq_neg hO hBA).1 h⟩, rfl⟩
    · rintro ⟨B, ⟨hBA, h⟩, rfl⟩
      exact ⟨B.isSimplePoint.mem_zeroLocus hF, fun h' ↦ hBA (CubicGroup.ext h'),
        (CubicGroup.eval_tangentLine_eq_zero_iff_two_nsmul_eq_neg hO hBA).2 h⟩
  rw [hS, Set.ncard_image_of_injective _ CubicGroup.point_injective,
    CubicGroup.ncard_setOf_ne_and_two_nsmul_eq_neg hns hO h2]
  have hA : IsFlex F P ↔ 3 • A = 0 := CubicGroup.isFlex_iff_three_nsmul_eq_zero hO A
  simp only [hA]

open scoped Classical in
/-- **Tangent lines from a point of a nonsingular cubic** ([Fulton2008], Problem 5.37 (f)). Let
`F` be a nonsingular cubic over an algebraically closed field with `2 ≠ 0`, and `P` a point of
`F`. The number of lines through `P` that are tangent to `F` at some point `Q ≠ P` is four if
`P` is not a flex, and three if it is. A line is a linear form up to a scalar, the span
`k ∙ L` of the form `L`; the tangent at `Q` is `tangentLine F Q.rep`. -/
theorem IsNonsingular.ncard_setOf_span_tangentLine (hF : F.IsHomogeneous 3)
    (hns : IsNonsingular F) (h2 : (2 : k) ≠ 0) (hP : P ∈ ProjectiveSpace.zeroLocus {F}) :
    {L : Submodule k (MvPolynomial (Fin 3) k) | ∃ Q ∈ ProjectiveSpace.zeroLocus {F}, Q ≠ P ∧
      eval P.rep (tangentLine F Q.rep) = 0 ∧ L = k ∙ tangentLine F Q.rep}.ncard =
      if IsFlex F P then 3 else 4 := by
  rw [← hns.ncard_setOf_eval_tangentLine_eq_zero hF h2 hP]
  have hS : {L : Submodule k (MvPolynomial (Fin 3) k) | ∃ Q ∈ ProjectiveSpace.zeroLocus {F},
      Q ≠ P ∧ eval P.rep (tangentLine F Q.rep) = 0 ∧ L = k ∙ tangentLine F Q.rep} =
      (fun Q ↦ k ∙ tangentLine F Q.rep) '' {Q | Q ∈ ProjectiveSpace.zeroLocus {F} ∧ Q ≠ P ∧
        eval P.rep (tangentLine F Q.rep) = 0} := by
    ext L
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨Q, hQ, hQP, h, rfl⟩
      exact ⟨Q, ⟨hQ, hQP, h⟩, rfl⟩
    · rintro ⟨Q, ⟨hQ, hQP, h⟩, rfl⟩
      exact ⟨Q, hQ, hQP, h, rfl⟩
  rw [hS, Set.InjOn.ncard_image]
  rintro Q₁ ⟨hQ₁, hQ₁P, h₁⟩ Q₂ ⟨hQ₂, hQ₂P, -⟩ hL
  have hsimple := (isNonsingular_iff_forall_isSimplePoint hF).1 hns
  by_contra hne
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1
    ((Set.ext_iff.1 (congrArg SetLike.coe hL) _).1 (Submodule.mem_span_singleton_self _))
  have h₁₂ : eval Q₂.rep (tangentLine F Q₁.rep) = 0 := by
    rw [← ha, smul_eval, eval_tangentLine_self hF (hsimple Q₂ hQ₂).eval_rep_eq_zero, mul_zero]
  exact hQ₂P (eq_of_eval_tangentLine_eq_zero hF (hns.irreducible hF three_ne_zero)
    (hsimple Q₁ hQ₁) (hsimple Q₂ hQ₂) (hsimple P hP) hne hQ₁P h₁₂ h₁)

end PlaneCurves.Projective

/-! ### Points of order two on a Legendre cubic -/

namespace WeierstrassCurve.Projective

open MvPolynomial Projectivization PlaneCurves.Projective

variable {k : Type*} [Field k] [IsAlgClosed k] {W : WeierstrassCurve.Projective k} {l : k}

/-- **The points of order two on a Legendre cubic** ([Fulton2008], Problem 5.37 (d)). Let `W` be
the Weierstrass curve `Y²Z = X(X - Z)(X - λZ)`, that is `a₂ = -(1 + λ)`, `a₄ = λ` and the other
coefficients `0`, with `λ ≠ 0, 1`, over an algebraically closed field with `2 ≠ 0`. Then the
points of order two of the group of `W.polynomial` with zero `O = [0 : 1 : 0]` are the points
`[0 : 0 : 1]`, `[1 : 0 : 1]` and `[λ : 0 : 1]`. -/
theorem point_image_setOf_addOrderOf_eq_two_of_legendre (ha₁ : W.a₁ = 0)
    (ha₂ : W.a₂ = -(1 + l)) (ha₃ : W.a₃ = 0) (ha₄ : W.a₄ = l) (ha₆ : W.a₆ = 0) (hl₀ : l ≠ 0)
    (hl₁ : l ≠ 1) (h2 : (2 : k) ≠ 0) :
    CubicGroup.point '' {A : CubicGroup W.polynomial (0 : W.Point).toProjectivization |
        addOrderOf A = 2} =
      {Projectivization.mk k ![0, 0, 1] (by simp), Projectivization.mk k ![1, 0, 1] (by simp),
        Projectivization.mk k ![l, 0, 1] (by simp)} := by
  classical
  have key (x y : k) : W.toAffine.Equation x y ∧ W.toAffine.polynomialY.evalEval x y = 0 ↔
      y = 0 ∧ (x = 0 ∨ x = 1 ∨ x = l) := by
    rw [Affine.equation_iff', Affine.evalEval_polynomialY, ha₁, ha₂, ha₃, ha₄, ha₆]
    constructor
    · rintro ⟨he, hy⟩
      have hy : y = 0 := by simpa [h2] using hy
      subst hy
      have : x * (x - 1) * (x - l) = 0 := by linear_combination -he
      simpa [sub_eq_zero, or_assoc] using this
    · rintro ⟨rfl, hx⟩
      rcases hx with rfl | rfl | rfl <;> constructor <;> ring
  have back (x : k) (hx : x = 0 ∨ x = 1 ∨ x = l) :
      ∃ h : W.toAffine.Nonsingular x 0,
        addOrderOf (Point.toCubicGroup (Point.fromAffine (.some x 0 h))) = 2 := by
    obtain ⟨he, hy⟩ := (key x 0).2 ⟨rfl, hx⟩
    have h : W.toAffine.Nonsingular x 0 := by
      refine (Affine.nonsingular_iff' x 0).2 ⟨he, Or.inl ?_⟩
      rw [ha₁, ha₂, ha₄]
      rcases hx with rfl | rfl | rfl
      · simpa using hl₀
      · intro h0; exact hl₁ (by linear_combination h0)
      · intro h0; exact (mul_ne_zero hl₀ (sub_ne_zero.2 hl₁)) (by linear_combination -h0)
    refine ⟨h, ?_⟩
    rw [AddEquiv.addOrderOf_eq, ← Point.toAffineAddEquiv_symm_apply, AddEquiv.addOrderOf_eq]
    refine addOrderOf_eq_prime ?_ (Affine.Point.some_ne_zero h)
    rw [two_nsmul, (Affine.Point.some_add_self_eq_zero_iff h).2 hy]
  ext P
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨Q, rfl⟩ := Point.toCubicGroup.surjective A
    obtain ⟨R, rfl⟩ := (Point.toAffineAddEquiv W).symm.surjective Q
    rw [Set.mem_ofPred_eq, AddEquiv.addOrderOf_eq, AddEquiv.addOrderOf_eq] at hA
    rcases R with _ | ⟨x, y, h⟩
    · exact absurd hA (by
        rw [show (Affine.Point.zero : W.toAffine.Point) = 0 from rfl, addOrderOf_zero]
        norm_num)
    have h2R := addOrderOf_nsmul_eq_zero (Affine.Point.some x y h)
    rw [hA, two_nsmul, Affine.Point.some_add_self_eq_zero_iff h] at h2R
    obtain ⟨rfl, hx⟩ := (key x y).1 ⟨h.1, h2R⟩
    rw [Point.point_toCubicGroup_apply, Point.toAffineAddEquiv_symm_apply,
      Point.toProjectivization_fromAffine_some]
    rcases hx with rfl | rfl | rfl <;> simp
  · have mem (x : k) (hx : x = 0 ∨ x = 1 ∨ x = l) :
        Projectivization.mk k ![x, 0, 1] (by simp) ∈ CubicGroup.point ''
          {A : CubicGroup W.polynomial (0 : W.Point).toProjectivization | addOrderOf A = 2} := by
      obtain ⟨h, hA⟩ := back x hx
      exact ⟨_, hA, by rw [Point.point_toCubicGroup_apply,
        Point.toProjectivization_fromAffine_some]⟩
    rintro (rfl | rfl | rfl)
    · exact mem 0 (by simp)
    · exact mem 1 (by simp)
    · exact mem l (by simp)

end WeierstrassCurve.Projective

namespace PlaneCurves.Projective

open MvPolynomial Projectivization
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k}
  {O : ℙ k (Fin 3 → k)}

open scoped Classical in
/-- **Flexes of a nonsingular cubic and the torsion of its group** ([Fulton2008], §5.6,
Problems 5.34, 5.37). Let `k` be algebraically closed, `F` a nonsingular cubic and `O` a flex of
`F`, the zero of the group `CubicGroup F O`.

* (a) A point `A` is a flex iff `3A = 0`.
* (b) The line through two flexes `P`, `Q` (the tangent if `P = Q`) meets `F` in a third flex
  `φ(P, Q)`.
* (c) The flexes are the `3`-torsion subgroup; if `3 ≠ 0` in `k`, it is isomorphic to
  `ℤ/3 × ℤ/3`, and `F` has exactly nine flexes.
* (d) A point `A ≠ O` has order two iff the tangent at `A` passes through `O`; if `2 ≠ 0` in
  `k`, the `2`-torsion subgroup is isomorphic to `ℤ/2 × ℤ/2`; and on the Legendre cubic
  `Y²Z = X(X - Z)(X - λZ)`, `λ ≠ 0, 1`, with `O = [0 : 1 : 0]` and `2 ≠ 0`, the points of order
  two are `[0 : 0 : 1]`, `[1 : 0 : 1]` and `[λ : 0 : 1]`.
* (e) If `2 ≠ 0` in `k`, the number of lines through a point `P` of `F` that are tangent to `F`
  at some point `Q ≠ P` is four if `P` is not a flex and three if it is.

Milestone: *Flexes of a nonsingular cubic and the torsion of its group*. -/
theorem isFlex_cubicGroup_torsion_spec (hF : F.IsHomogeneous 3) (hns : IsNonsingular F)
    (hO : IsFlex F O) :
    letI : Fact (F.IsHomogeneous 3) := ⟨hF⟩
    letI : Fact (Irreducible F) := ⟨hns.irreducible hF three_ne_zero⟩
    letI : Fact (IsSimplePoint F O) := ⟨hO.isSimplePoint⟩
    (∀ A : CubicGroup F O, IsFlex F A.point ↔ 3 • A = 0) ∧
    (∀ P Q, IsFlex F P → IsFlex F Q → IsFlex F (thirdPoint F P Q)) ∧
    ((∀ A : CubicGroup F O, A ∈ AddSubgroup.torsionBy (CubicGroup F O) 3 ↔ IsFlex F A.point) ∧
      ((3 : k) ≠ 0 → Nonempty (AddSubgroup.torsionBy (CubicGroup F O) 3 ≃+ ZMod 3 × ZMod 3) ∧
        {P | IsFlex F P}.ncard = 9)) ∧
    ((∀ A : CubicGroup F O, A ≠ 0 →
        (addOrderOf A = 2 ↔ eval O.rep (tangentLine F A.point.rep) = 0)) ∧
      ((2 : k) ≠ 0 → Nonempty (AddSubgroup.torsionBy (CubicGroup F O) 2 ≃+ ZMod 2 × ZMod 2)) ∧
      ∀ (W : WeierstrassCurve.Projective k) (l : k), W.a₁ = 0 → W.a₂ = -(1 + l) → W.a₃ = 0 →
        W.a₄ = l → W.a₆ = 0 → l ≠ 0 → l ≠ 1 → (2 : k) ≠ 0 →
        CubicGroup.point '' {A : CubicGroup W.polynomial (0 : W.Point).toProjectivization |
            addOrderOf A = 2} =
          {Projectivization.mk k ![0, 0, 1] (by simp),
            Projectivization.mk k ![1, 0, 1] (by simp),
            Projectivization.mk k ![l, 0, 1] (by simp)}) ∧
    ((2 : k) ≠ 0 → ∀ P ∈ ProjectiveSpace.zeroLocus {F},
      {L : Submodule k (MvPolynomial (Fin 3) k) | ∃ Q ∈ ProjectiveSpace.zeroLocus {F}, Q ≠ P ∧
        eval P.rep (tangentLine F Q.rep) = 0 ∧ L = k ∙ tangentLine F Q.rep}.ncard =
        if IsFlex F P then 3 else 4) := by
  let : Fact (F.IsHomogeneous 3) := ⟨hF⟩
  let : Fact (Irreducible F) := ⟨hns.irreducible hF three_ne_zero⟩
  let : Fact (IsSimplePoint F O) := ⟨hO.isSimplePoint⟩
  refine ⟨CubicGroup.isFlex_iff_three_nsmul_eq_zero hO,
    fun P Q hP hQ ↦ isFlex_thirdPoint hF (hns.irreducible hF three_ne_zero) hP hQ,
    ⟨fun A ↦ CubicGroup.mem_torsionBy_three_iff_isFlex hO, fun h3 ↦
      ⟨CubicGroup.nonempty_torsionBy_three_addEquiv_prod hns hO h3,
        hO.ncard_setOf_isFlex hF hns h3⟩⟩,
    ⟨fun A hA ↦ ?_, CubicGroup.nonempty_torsionBy_two_addEquiv_prod hns hO,
      fun W l ha₁ ha₂ ha₃ ha₄ ha₆ hl₀ hl₁ h2 ↦
        WeierstrassCurve.Projective.point_image_setOf_addOrderOf_eq_two_of_legendre ha₁ ha₂ ha₃
          ha₄ ha₆ hl₀ hl₁ h2⟩,
    fun h2 P hP ↦ hns.ncard_setOf_span_tangentLine hF h2 hP⟩
  rw [← CubicGroup.two_nsmul_eq_zero_iff hO hA]
  exact ⟨fun h ↦ h ▸ addOrderOf_nsmul_eq_zero A, fun h ↦ addOrderOf_eq_prime h hA⟩

end PlaneCurves.Projective

end
