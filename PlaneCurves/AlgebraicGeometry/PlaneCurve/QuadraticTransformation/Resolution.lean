/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Logic.Relation
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.FunctionField
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Singularities.NonOrdinary

/-!
# Sequences of quadratic transformations

A form `G` is a *quadratic transformation* of a form `F` if it is a quadratic transformation of
`F` centred at some point (`IsQuadraticTransformAt`): the proper transform of `F` after a
projective change of coordinates `T` that moves `[0 : 0 : 1]` to the centre and puts `F` in
excellent position. A sequence `F = F₁, …, F_m` of successive quadratic transformations is
`List.IsChain IsQuadraticTransform (F :: l)`, and `Relation.ReflTransGen IsQuadraticTransform`
is its uncounted form.

Along a quadratic transformation the curve stays irreducible, its virtual genus does not
increase, and its function field does not change: the change of coordinates and the standard
quadratic transformation give an isomorphism `k(F) ≅ k(G)` that carries the local ring of `F` at
`T R` onto the local ring of `G` at `Q(R)`, for every point `R` of `F^T` off the fundamental
triangle (`IsQuadraticTransformAt.exists_algEquiv`, in `FunctionField.lean`).

Every irreducible curve over an algebraically closed field is carried by a finite sequence of
quadratic transformations to a curve with only ordinary multiple points (Fulton, §7.4, Theorem 2,
and Appendix A). A quadratic transformation centred at a non-ordinary multiple point lowers
`N(F) + g*(F)`, `N(F)` being the number of non-ordinary multiple points. If that point is
terrible, a quadratic transformation centred at a simple point or a point off the curve, which
changes neither `N` nor `g*`, first makes it not terrible. So `2 (N(F) + g*(F))` steps suffice,
and `N(F) + g*(F)` in characteristic zero, where no point is terrible.

## Main definitions

* `PlaneCurves.Projective.IsQuadraticTransform F G`: `G` is a quadratic transformation of `F`
  centred at some point.

## Main results

* `PlaneCurves.Projective.IsQuadraticTransform.irreducible`,
  `PlaneCurves.Projective.IsQuadraticTransform.virtualGenus_le`,
  `PlaneCurves.Projective.IsQuadraticTransform.nonempty_algEquiv`: one step keeps the curve
  irreducible and its function field, and does not increase its virtual genus.
* `PlaneCurves.Projective.irreducible_of_reflTransGen_isQuadraticTransform`,
  `PlaneCurves.Projective.virtualGenus_le_of_reflTransGen_isQuadraticTransform`,
  `PlaneCurves.Projective.nonempty_algEquiv_of_reflTransGen_isQuadraticTransform`: the same for
  a sequence of quadratic transformations.
* `PlaneCurves.Projective.exists_isQuadraticTransformAt_of_isTerriblePoint`: the auxiliary
  quadratic transformation at a terrible point.
* `PlaneCurves.Projective.exists_finite_injOn_properTransform_linearSubst`: off a finite set,
  one step is injective on points, onto a cofinite set of simple points, and carries local
  rings onto local rings along one isomorphism of function fields.
* `PlaneCurves.Projective.exists_isChain_isQuadraticTransform_lt`: one or two quadratic
  transformations lower `N + g*`.
* `PlaneCurves.Projective.exists_reduction`: **reduction to ordinary multiple points**.
* `PlaneCurves.Projective.exists_reduction_avoiding`: the reduction, with points, local rings and
  function field followed along it off a finite set disjoint from given simple points.
* `PlaneCurves.Projective.exists_ordinary_model`: an irreducible curve has a birational plane
  model with only ordinary multiple points and virtual genus not larger.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.4, Problem 7.13, and Appendix A
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti TauCeti.AlgebraicGeometry PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {F G : MvPolynomial (Fin 3) k} {P : ℙ k (Fin 3 → k)} {n m : ℕ}

/-! ### The step relation -/

/-- A form `G` is a *quadratic transformation* of a form `F` if it is a quadratic transformation
of `F` centred at some point. -/
def IsQuadraticTransform (F G : MvPolynomial (Fin 3) k) : Prop :=
  ∃ P, IsQuadraticTransformAt F P G

theorem isQuadraticTransform_def :
    IsQuadraticTransform F G ↔ ∃ P, IsQuadraticTransformAt F P G :=
  Iff.rfl

/-- A quadratic transformation centred at a point is a quadratic transformation. -/
theorem IsQuadraticTransformAt.isQuadraticTransform (h : IsQuadraticTransformAt F P G) :
    IsQuadraticTransform F G :=
  ⟨P, h⟩

/-- The proper transform of a curve in excellent position is a quadratic transformation of it. -/
theorem IsExcellentPosition.isQuadraticTransform (h : IsExcellentPosition F) :
    IsQuadraticTransform F (properTransform F) :=
  h.isQuadraticTransformAt.isQuadraticTransform

namespace IsQuadraticTransform

/-- A quadratic transformation of a form is a form. -/
theorem exists_isHomogeneous (h : IsQuadraticTransform F G) (hF : F.IsHomogeneous n) :
    ∃ d, G.IsHomogeneous d :=
  let ⟨_, hP⟩ := h
  ⟨_, hP.isHomogeneous hF⟩

/-- A quadratic transformation of an irreducible form is irreducible. -/
theorem irreducible (h : IsQuadraticTransform F G) (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) : Irreducible G :=
  let ⟨_, hP⟩ := h
  hP.irreducible hF hirr

/-- A quadratic transformation does not increase the virtual genus of an irreducible curve, over
an algebraically closed field. -/
theorem virtualGenus_le [IsAlgClosed k] (h : IsQuadraticTransform F G) (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) : virtualGenus G ≤ virtualGenus F := by
  obtain ⟨P, hP⟩ := h
  rw [hP.virtualGenus hF hirr, sub_le_self_iff]
  exact finsum_nonneg fun Q ↦ finsum_nonneg fun _ ↦ by positivity

/-- **A quadratic transformation is birational**: an irreducible curve and its quadratic
transformation have isomorphic function fields. -/
theorem nonempty_algEquiv (h : IsQuadraticTransform F G) (hF : F.IsHomogeneous n)
    (hG : G.IsHomogeneous m) [Fact (Irreducible F)] [Fact (Irreducible G)] :
    Nonempty (functionField hF ≃ₐ[k] functionField hG) :=
  let ⟨_, hP⟩ := h
  let ⟨_, _, _, _, _, e, _⟩ := hP.exists_algEquiv hF hG
  ⟨e⟩

end IsQuadraticTransform

/-! ### Sequences of quadratic transformations -/

/-- A curve obtained from a form by a sequence of quadratic transformations is a form. -/
theorem exists_isHomogeneous_of_reflTransGen_isQuadraticTransform
    (h : Relation.ReflTransGen IsQuadraticTransform F G) (hF : F.IsHomogeneous n) :
    ∃ d, G.IsHomogeneous d := by
  induction h with
  | refl => exact ⟨n, hF⟩
  | tail _ hbc ih =>
    obtain ⟨d, hd⟩ := ih
    exact hbc.exists_isHomogeneous hd

/-- A curve obtained from an irreducible form by a sequence of quadratic transformations is
irreducible. -/
theorem irreducible_of_reflTransGen_isQuadraticTransform
    (h : Relation.ReflTransGen IsQuadraticTransform F G) (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) : Irreducible G := by
  induction h with
  | refl => exact hirr
  | tail hab hbc ih =>
    obtain ⟨d, hd⟩ := exists_isHomogeneous_of_reflTransGen_isQuadraticTransform hab hF
    exact hbc.irreducible hd ih

/-- A sequence of quadratic transformations does not increase the virtual genus of an
irreducible curve, over an algebraically closed field. -/
theorem virtualGenus_le_of_reflTransGen_isQuadraticTransform [IsAlgClosed k]
    (h : Relation.ReflTransGen IsQuadraticTransform F G) (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) : virtualGenus G ≤ virtualGenus F := by
  induction h with
  | refl => exact le_rfl
  | tail hab hbc ih =>
    obtain ⟨d, hd⟩ := exists_isHomogeneous_of_reflTransGen_isQuadraticTransform hab hF
    exact (hbc.virtualGenus_le hd
      (irreducible_of_reflTransGen_isQuadraticTransform hab hF hirr)).trans ih

/-- **A sequence of quadratic transformations is birational**: an irreducible curve and a curve
obtained from it by a sequence of quadratic transformations have isomorphic function fields. -/
theorem nonempty_algEquiv_of_reflTransGen_isQuadraticTransform
    (h : Relation.ReflTransGen IsQuadraticTransform F G) (hF : F.IsHomogeneous n)
    (hG : G.IsHomogeneous m) [Fact (Irreducible F)] [hGi : Fact (Irreducible G)] :
    Nonempty (functionField hF ≃ₐ[k] functionField hG) := by
  induction h generalizing m hGi with
  | refl => exact ⟨ProjectiveSpace.functionField.equivOfEq (HomogeneousIdeal.toIdeal_injective
      (by rw [projectivePlaneCurve.toIdeal_ideal, projectivePlaneCurve.toIdeal_ideal]))⟩
  | @tail b c hab hbc ih =>
    obtain ⟨d, hd⟩ := exists_isHomogeneous_of_reflTransGen_isQuadraticTransform hab hF
    have := Fact.mk (irreducible_of_reflTransGen_isQuadraticTransform hab hF Fact.out)
    obtain ⟨e₁⟩ := ih hd
    obtain ⟨e₂⟩ := hbc.nonempty_algEquiv hd hG
    exact ⟨e₁.trans e₂⟩

/-! ### Points off the fundamental triangle through a change of coordinates -/

section OffTriangle

variable {M : Matrix (Fin 3) (Fin 3) k} {R : ℙ k (Fin 3 → k)}

/-- Off the fundamental triangle, the proper transform of `F^T` has at `Q(R)` the multiplicity of
`F` at `T R`. -/
theorem mult_properTransform_linearSubst_quadraticMap (hF : F.IsHomogeneous n)
    (hM : Function.Injective M.mulVecLin) (hR : R ∉ fundamentalTriangle) :
    mult (properTransform (linearSubst M F)) (quadraticMap R) = mult F (map M.mulVecLin hM R) := by
  rw [mult_properTransform_of_notMem_fundamentalTriangle (hF.linearSubst M)
    (bijOn_quadraticMap_compl_fundamentalTriangle.mapsTo hR), quadraticMap_quadraticMap hR,
    mult_linearSubst hF hM]

/-- Off the fundamental triangle, `Q(R)` is an ordinary multiple point of the proper transform of
`F^T` exactly when `T R` is one of `F`. -/
theorem isOrdinaryMultiplePoint_properTransform_linearSubst_quadraticMap_iff [IsAlgClosed k]
    (hF : F.IsHomogeneous n) (hM : Function.Injective M.mulVecLin) (hR : R ∉ fundamentalTriangle) :
    IsOrdinaryMultiplePoint (properTransform (linearSubst M F)) (quadraticMap R) ↔
      IsOrdinaryMultiplePoint F (map M.mulVecLin hM R) := by
  rw [isOrdinaryMultiplePoint_properTransform_iff_of_notMem_fundamentalTriangle (hF.linearSubst M)
    (bijOn_quadraticMap_compl_fundamentalTriangle.mapsTo hR), quadraticMap_quadraticMap hR,
    isOrdinaryMultiplePoint_linearSubst_iff hF hM]

/-- Off the fundamental triangle, `Q(R)` is a non-ordinary multiple point of the proper transform
of `F^T` exactly when `T R` is one of `F`. -/
theorem quadraticMap_mem_nonOrdinaryMultiplePoints_properTransform_linearSubst_iff [IsAlgClosed k]
    (hF : F.IsHomogeneous n) (hM : Function.Injective M.mulVecLin) (hR : R ∉ fundamentalTriangle) :
    quadraticMap R ∈ nonOrdinaryMultiplePoints (properTransform (linearSubst M F)) ↔
      map M.mulVecLin hM R ∈ nonOrdinaryMultiplePoints F := by
  rw [mem_nonOrdinaryMultiplePoints_iff, mem_nonOrdinaryMultiplePoints_iff, isMultiplePoint_def,
    isMultiplePoint_def, mult_properTransform_linearSubst_quadraticMap hF hM hR,
    isOrdinaryMultiplePoint_properTransform_linearSubst_quadraticMap_iff hF hM hR]

end OffTriangle

/-! ### The auxiliary step at a terrible point -/

/-- An irreducible curve of positive degree `n` over an algebraically closed field has, outside
any finite set, a point `Q` with `m_Q(F) ≤ 1` and `n - m_Q(F) ≠ 0` in `k`: a point off the curve if
`n ≠ 0` in `k`, and a simple point otherwise. -/
theorem exists_mult_le_one_natCast_sub_ne_zero [IsAlgClosed k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) (hn : n ≠ 0) {S : Set (ℙ k (Fin 3 → k))} (hS : S.Finite) :
    ∃ Q ∉ S, mult F Q ≤ 1 ∧ ((n - (mult F Q).toNat : ℕ) : k) ≠ 0 := by
  by_cases hn0 : (n : k) = 0
  · have hinf : (zeroLocus ({F} : Set (MvPolynomial (Fin 3) k))).Infinite :=
      zeroLocus_singleton_infinite (n := 2) le_rfl hF hn
    obtain ⟨Q, hQ, hQS⟩ := (hinf.sdiff
      (hS.union (finite_setOf_isMultiplePoint_of_irreducible hF hirr))).nonempty
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, isMultiplePoint_def, not_le] at hQS
    have hpos := (mult_pos_iff hF).2 hQ
    obtain ⟨r, hr⟩ : ∃ r : ℕ, mult F Q = r :=
      (ENat.ne_top_iff_exists.1 (mult_ne_top hirr.ne_zero)).imp fun _ h ↦ h.symm
    rw [hr] at hpos hQS
    norm_cast at hpos hQS
    obtain rfl : r = 1 := by omega
    refine ⟨Q, hQS.1, hr.le, ?_⟩
    rw [hr, ENat.toNat_natCast, Nat.cast_sub (by omega), hn0]
    simp
  · obtain ⟨Q, hQ, hQS⟩ := exists_eval_rep_ne_zero_notMem (n := 2) two_ne_zero hF hirr.ne_zero hS
    have hQ0 : mult F Q = 0 := nonpos_iff_eq_zero.1 (not_lt.1 (mt mult_pos_iff_eval_rep.1 hQ))
    exact ⟨Q, hQS, by simp [hQ0], by simpa [hQ0] using hn0⟩

/-- **The auxiliary quadratic transformation at a terrible point** (Fulton, Appendix A). Let `F`
be an irreducible form of degree `n` over an algebraically closed field, `P` a terrible point of
`F`, and `S` a finite set of points. There is a point `Q ∉ S`, `Q ≠ P`, with `m_Q(F) ≤ 1`, and a
change of coordinates `T`, given by an invertible matrix `M`, with `T([0 : 0 : 1]) = Q`, `F^T` in
excellent position and `T⁻¹(S ∪ {P})` off the fundamental triangle, such that for `T R = P` the
point `Q(R)` is not terrible for the quadratic transformation `G` of `F^T`.

Indeed `G` has degree `2n - m_Q(F)` and multiplicity `r = m_P(F)` at `Q(R)`, and `Q` is chosen so
that `n - m_Q(F) ≠ 0` in `k`, while `n - r = 0` in `k` since `P` is terrible; so
`2n - m_Q(F) - r ≠ 0` in `k`, and `Q(R)` is not terrible. -/
theorem exists_isQuadraticTransformAt_of_isTerriblePoint [IsAlgClosed k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) (hP : IsTerriblePoint F P.rep) {S : Set (ℙ k (Fin 3 → k))}
    (hS : S.Finite) :
    ∃ Q ∉ S, Q ≠ P ∧ mult F Q ≤ 1 ∧
      ∃ (M : Matrix (Fin 3) (Fin 3) k) (hM : Function.Injective M.mulVecLin),
        map M.mulVecLin hM (fundamentalPoint 2) = Q ∧ IsExcellentPosition (linearSubst M F) ∧
        (∀ R, map M.mulVecLin hM R ∈ insert P S → R ∉ fundamentalTriangle) ∧
        ∀ R, map M.mulVecLin hM R = P →
          ¬IsTerriblePoint (properTransform (linearSubst M F)) (quadraticMap R).rep := by
  have hn : 2 ≤ n := hF.totalDegree hirr.ne_zero ▸ hP.two_le_totalDegree
  obtain ⟨Q, hQS, hQ1, hQn⟩ :=
    exists_mult_le_one_natCast_sub_ne_zero hF hirr (by omega) (hS.insert P)
  have hQP : Q ≠ P := fun h ↦ hQS (h ▸ Set.mem_insert Q S)
  have hQ : ¬IsTerriblePoint F Q.rep := fun h ↦ hQP <| by
    simpa using (hP.mk_eq_mk hF hirr P.rep_ne_zero Q.rep_ne_zero h).symm
  obtain ⟨M, hM, hTQ, hE, hav⟩ :=
    exists_isExcellentPosition_avoiding hF hirr hQ (hS.insert P) hQS
  refine ⟨Q, fun h ↦ hQS (Set.mem_insert_of_mem P h), hQP, hQ1, M, hM, hTQ, hE, hav,
    fun R hR hT ↦ ?_⟩
  have hRt : R ∉ fundamentalTriangle := hav R (hR ▸ Set.mem_insert P S)
  have hG := (isQuadraticTransformAt_def.2 ⟨M, hM, hTQ, hE, rfl⟩ :
    IsQuadraticTransformAt F Q _).isHomogeneous hF
  obtain ⟨r, hr⟩ : ∃ r : ℕ, mult F P = r :=
    (ENat.ne_top_iff_exists.1 (mult_ne_top hirr.ne_zero)).imp fun _ h ↦ h.symm
  have hrn : r < n := by exact_mod_cast hr ▸ hP.mult_lt hF hirr P
  have hPr := hP.natCast_sub_eq_zero hF P.rep_ne_zero (r := r) (by rwa [mk_rep])
  have hGr := hT.natCast_sub_eq_zero hG (quadraticMap R).rep_ne_zero (r := r) (by
    rw [mk_rep, mult_properTransform_linearSubst_quadraticMap hF hM hRt, hR, hr])
  obtain ⟨m, hm⟩ : ∃ m : ℕ, mult F Q = m :=
    (ENat.ne_top_iff_exists.1 (mult_ne_top hirr.ne_zero)).imp fun _ h ↦ h.symm
  rw [hm, ENat.toNat_natCast] at hGr
  rw [hm, ENat.toNat_natCast] at hQn
  have hm1 : m ≤ 1 := by exact_mod_cast hm ▸ hQ1
  rw [show 2 * n - m - r = (n - m) + (n - r) by omega, Nat.cast_add, hPr, add_zero] at hGr
  exact hQn hGr

/-! ### Points, local rings and function fields along a quadratic transformation -/

section Avoiding

open Matrix (mulVec_injective_of_isUnit)

/-- An irreducible curve with no coordinate line as a component meets the fundamental triangle in
finitely many points. -/
theorem finite_zeroLocus_inter_fundamentalTriangle (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) (hX : ∀ i, ¬ X i ∣ F) :
    (zeroLocus {F} ∩ fundamentalTriangle).Finite := by
  have hXF (i : Fin 3) : ¬ F ∣ X i := fun h ↦ hX i (hirr.dvd_symm prime_X.irreducible h)
  rw [fundamentalTriangle_def, ← zeroLocus_insert]
  exact finite_zeroLocus_pair_of_isRelPrime hF
    (((isHomogeneous_X k 0).mul (isHomogeneous_X k 1)).mul (isHomogeneous_X k 2))
    (hirr.isRelPrime_iff_not_dvd.2 (by simp [hirr.prime.dvd_mul, hXF]))

/-- **Points and local rings along a change of coordinates and a quadratic transformation**
(Fulton, Problem 7.13). Let `F` be an irreducible form over a perfect field, `T` the change of
coordinates of an invertible matrix `M` such that no coordinate line is a component of `F^T`,
`G = (F^T)'`, and `φ` a map with `φ (T R) = Q(R)` for every point `R`. Let `S` be a set of simple
points of `F` with `T⁻¹(S)` off the fundamental triangle. There is a finite set `B`, disjoint
from `S` and containing the multiple points of `F`, such that `φ` is injective on `V(F) ∖ B`, the
image `φ(V(F) ∖ B)` is cofinite in `V(G)` and consists of simple points of `G`, and the
isomorphism `k(F) ≅ k(G)` (`linearSubstQuadraticFunctionFieldEquiv`) carries the local ring of
`F` at each point `R` of `V(F) ∖ B` onto the local ring of `G` at `φ R`. -/
theorem exists_finite_injOn_properTransform_linearSubst [PerfectField k] (hF : F.IsHomogeneous n)
    (M : GL (Fin 3) k) (hX : ∀ i, ¬ X i ∣ linearSubst M.1 F) (hG : G.IsHomogeneous m)
    (hGF : G = properTransform (linearSubst M.1 F)) [Fact (Irreducible F)]
    [Fact (Irreducible G)] {φ : ℙ k (Fin 3 → k) → ℙ k (Fin 3 → k)}
    (hφ : ∀ R, φ (map M.1.mulVecLin (mulVec_injective_of_isUnit M.isUnit) R) = quadraticMap R)
    {S : Set (ℙ k (Fin 3 → k))} (hSF : ∀ P ∈ S, IsSimplePoint F P)
    (hST : ∀ R, map M.1.mulVecLin (mulVec_injective_of_isUnit M.isUnit) R ∈ S →
      R ∉ fundamentalTriangle) :
    ∃ B : Set (ℙ k (Fin 3 → k)), B.Finite ∧ Disjoint S B ∧ {Q | IsMultiplePoint F Q} ⊆ B ∧
      Set.InjOn φ (zeroLocus {F} \ B) ∧ (zeroLocus {G} \ φ '' (zeroLocus {F} \ B)).Finite ∧
      (∀ R ∈ zeroLocus {F} \ B, IsSimplePoint G (φ R)) ∧
      ∀ (R : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)))
        (R' : zeroLocus (projectivePlaneCurve.ideal hG : Set (MvPolynomial (Fin 3) k))),
        R.1 ∉ B → φ R.1 = R'.1 →
          (localSubring hF R).map
              (linearSubstQuadraticFunctionFieldEquiv hF M hX hG hGF : functionField hF →+* _) =
            localSubring hG R' := by
  set T := map M.1.mulVecLin (mulVec_injective_of_isUnit M.isUnit)
  have hirr : Irreducible F := Fact.out
  have hTb : Function.Bijective T := bijective_map_mulVecLin M
  have hF' := hF.linearSubst M.1
  have hirr' : Irreducible (linearSubst M.1 F) :=
    (irreducible_linearSubst_iff ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit)).2 hirr
  have hmemT (R : ℙ k (Fin 3 → k)) : T R ∈ zeroLocus {F} ↔ R ∈ zeroLocus {linearSubst M.1 F} := by
    rw [← mult_pos_iff hF, ← mult_pos_iff hF',
      mult_linearSubst hF (mulVec_injective_of_isUnit M.isUnit)]
  set B := T '' (zeroLocus {linearSubst M.1 F} ∩ fundamentalTriangle) ∪
    {Q | IsMultiplePoint F Q}
  have hB (R : ℙ k (Fin 3 → k)) (h : T R ∈ zeroLocus {F} \ B) :
      R ∈ zeroLocus {linearSubst M.1 F} ∧ R ∉ fundamentalTriangle ∧
        ¬IsMultiplePoint F (T R) :=
    ⟨(hmemT R).1 h.1, fun hR ↦ h.2 (Or.inl ⟨R, ⟨(hmemT R).1 h.1, hR⟩, rfl⟩),
      fun hR ↦ h.2 (Or.inr hR)⟩
  have hnB (R : ℙ k (Fin 3 → k)) (hR : R ∉ fundamentalTriangle) (hm : ¬IsMultiplePoint F (T R)) :
      T R ∉ B := by
    rintro (⟨R₁, ⟨-, hR₁⟩, h⟩ | h)
    · exact hR (hTb.1 h ▸ hR₁)
    · exact hm h
  have hsimple (R : ℙ k (Fin 3 → k)) (h : T R ∈ zeroLocus {F} \ B) : IsSimplePoint G (φ (T R)) := by
    obtain ⟨-, hRt, hm⟩ := hB R h
    rw [hφ, isSimplePoint_def, hGF, mult_properTransform_linearSubst_quadraticMap hF _ hRt,
      ← isSimplePoint_def]
    exact (isSimplePoint_or_isMultiplePoint hF h.1).resolve_right hm
  refine ⟨B, ((finite_zeroLocus_inter_fundamentalTriangle hF' hirr' hX).image T).union
      (finite_setOf_isMultiplePoint_of_irreducible hF hirr), ?_, Set.subset_union_right, ?_, ?_,
    ?_, ?_⟩
  · refine Set.disjoint_left.2 fun s hs hsB ↦ ?_
    obtain ⟨R, rfl⟩ := hTb.2 s
    exact hnB R (hST R hs) (fun h ↦ h.not_isSimplePoint (hSF _ hs)) hsB
  · intro a ha b hb hab
    obtain ⟨a, rfl⟩ := hTb.2 a
    obtain ⟨b, rfl⟩ := hTb.2 b
    rw [hφ, hφ] at hab
    rw [bijOn_quadraticMap_compl_fundamentalTriangle.injOn (hB a ha).2.1 (hB b hb).2.1 hab]
  · refine ((finite_zeroLocus_inter_fundamentalTriangle hG Fact.out
      (hGF ▸ not_X_dvd_properTransform hF' hirr'.ne_zero)).union
      ((finite_setOf_isMultiplePoint_of_irreducible hF hirr).image φ)).subset ?_
    rintro Q ⟨hQG, hQn⟩
    by_cases hQt : Q ∈ fundamentalTriangle
    · exact Or.inl ⟨hQG, hQt⟩
    rw [hGF] at hQG
    obtain ⟨R, ⟨hRC, hRt⟩, rfl⟩ := (bijOn_quadraticMap hF').surjOn ⟨hQG, hQt⟩
    by_cases hm : IsMultiplePoint F (T R)
    · exact Or.inr ⟨T R, hm, hφ R⟩
    · exact (hQn ⟨T R, ⟨(hmemT R).2 hRC, hnB R hRt hm⟩, hφ R⟩).elim
  · intro R hR
    obtain ⟨R₀, rfl⟩ := hTb.2 R
    exact hsimple R₀ hR
  · intro R R' hRB hRR'
    obtain ⟨R₀, hR₀⟩ := hTb.2 R.1
    have hRC := (zeroLocus_ideal hF).le R.2
    obtain ⟨-, hR₀t, -⟩ := hB R₀ (hR₀ ▸ ⟨hRC, hRB⟩)
    exact map_localSubring_linearSubstQuadraticFunctionFieldEquiv hF M hX hG hGF hR₀t hR₀
      (by rw [← hφ, hR₀, hRR'])

/-- The data that `exists_reduction_avoiding` gives along a sequence of quadratic transformations
from `F` to `G`: a finite set `B` disjoint from `S` and containing the multiple points of `F`, off
which `φ` is injective on `V(F)`, with cofinite image in `V(G)` consisting of simple points, and
with local rings carried onto local rings by `e`. -/
private abbrev Avoids (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous m) [Fact (Irreducible F)]
    [Fact (Irreducible G)] (S B : Set (ℙ k (Fin 3 → k)))
    (φ : ℙ k (Fin 3 → k) → ℙ k (Fin 3 → k)) (e : functionField hF ≃ₐ[k] functionField hG) :
    Prop :=
  B.Finite ∧ Disjoint S B ∧ {Q | IsMultiplePoint F Q} ⊆ B ∧
    Set.InjOn φ (zeroLocus {F} \ B) ∧ (zeroLocus {G} \ φ '' (zeroLocus {F} \ B)).Finite ∧
    (∀ R ∈ zeroLocus {F} \ B, IsSimplePoint G (φ R)) ∧
    ∀ (R : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)))
      (R' : zeroLocus (projectivePlaneCurve.ideal hG : Set (MvPolynomial (Fin 3) k))),
      R.1 ∉ B → φ R.1 = R'.1 →
        (localSubring hF R).map (e : functionField hF →+* _) = localSubring hG R'

private theorem avoids_refl [PerfectField k] (hF : F.IsHomogeneous n) [Fact (Irreducible F)]
    {S : Set (ℙ k (Fin 3 → k))} (hSF : ∀ P ∈ S, IsSimplePoint F P) :
    Avoids hF hF S {Q | IsMultiplePoint F Q} id (AlgEquiv.refl) := by
  have hfin := finite_setOf_isMultiplePoint_of_irreducible hF (Fact.out : Irreducible F)
  refine ⟨hfin, Set.disjoint_left.2 fun s hs h ↦ h.not_isSimplePoint (hSF s hs), subset_rfl,
    Set.injOn_id _, hfin.subset fun Q ⟨hQC, hQn⟩ ↦ ?_,
    fun R hR ↦ (isSimplePoint_or_isMultiplePoint hF hR.1).resolve_right hR.2,
    fun R R' _ h ↦ ?_⟩
  · by_contra h
    exact hQn ⟨Q, ⟨hQC, h⟩, rfl⟩
  · obtain rfl : R = R' := Subtype.ext h
    refine LocalSubring.toSubring_injective ?_
    rw [LocalSubring.map_toSubring]
    exact Subring.map_id _

private theorem Avoids.trans {G₁ : MvPolynomial (Fin 3) k} {d : ℕ} {hF : F.IsHomogeneous n}
    {hG₁ : G₁.IsHomogeneous d} {hG : G.IsHomogeneous m} [Fact (Irreducible F)]
    [Fact (Irreducible G₁)] [Fact (Irreducible G)] {S B₁ B₂ : Set (ℙ k (Fin 3 → k))}
    {φ₁ φ₂ : ℙ k (Fin 3 → k) → ℙ k (Fin 3 → k)} {e₁ : functionField hF ≃ₐ[k] functionField hG₁}
    {e₂ : functionField hG₁ ≃ₐ[k] functionField hG} (h₁ : Avoids hF hG₁ S B₁ φ₁ e₁)
    (h₂ : Avoids hG₁ hG (φ₁ '' S) B₂ φ₂ e₂) :
    Avoids hF hG S (B₁ ∪ (zeroLocus {F} \ B₁) ∩ φ₁ ⁻¹' B₂) (φ₂ ∘ φ₁) (e₁.trans e₂) := by
  obtain ⟨hB₁, hS₁, hm₁, hi₁, hc₁, hs₁, hl₁⟩ := h₁
  obtain ⟨hB₂, hS₂, -, hi₂, hc₂, hs₂, hl₂⟩ := h₂
  have hmem (R) (hR : R ∈ zeroLocus {F} \ (B₁ ∪ (zeroLocus {F} \ B₁) ∩ φ₁ ⁻¹' B₂)) :
      R ∈ zeroLocus {F} \ B₁ ∧ φ₁ R ∈ zeroLocus {G₁} \ B₂ := by
    obtain ⟨hRC, hRB⟩ := hR
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_preimage, not_or,
      not_and] at hRB
    exact ⟨⟨hRC, hRB.1⟩, (hs₁ R ⟨hRC, hRB.1⟩).mem_zeroLocus hG₁, hRB.2 ⟨hRC, hRB.1⟩⟩
  refine ⟨hB₁.union (Set.Finite.of_finite_image (hB₂.subset (by rintro _ ⟨R, hR, rfl⟩; exact hR.2))
      (hi₁.mono Set.inter_subset_left)),
    Set.disjoint_left.2 fun s hs hsB ↦ hsB.elim (Set.disjoint_left.1 hS₁ hs)
      fun h ↦ Set.disjoint_left.1 hS₂ ⟨s, hs, rfl⟩ h.2,
    hm₁.trans Set.subset_union_left,
    fun a ha b hb hab ↦ hi₁ (hmem a ha).1 (hmem b hb).1 (hi₂ (hmem a ha).2 (hmem b hb).2 hab),
    (hc₂.union ((hc₁.union hB₂).image φ₂)).subset ?_, fun R hR ↦ hs₂ _ (hmem R hR).2, ?_⟩
  · rintro Q ⟨hQC, hQn⟩
    by_cases hQ : Q ∈ φ₂ '' (zeroLocus {G₁} \ B₂)
    · obtain ⟨Q₁, ⟨hQ₁C, hQ₁B⟩, rfl⟩ := hQ
      refine Or.inr ⟨Q₁, ?_, rfl⟩
      by_contra hne
      simp only [Set.mem_union, Set.mem_sdiff, not_or, not_and, not_not] at hne
      obtain ⟨R, hR, rfl⟩ := hne.1 hQ₁C
      refine hQn ⟨R, ⟨hR.1, ?_⟩, rfl⟩
      rintro (h | h)
      · exact hR.2 h
      · exact hQ₁B h.2
    · exact Or.inl ⟨hQC, hQ⟩
  · intro R R' hRB hRR'
    have hR := hmem R.1 ⟨(zeroLocus_ideal hF).le R.2, hRB⟩
    let R₁ : zeroLocus (projectivePlaneCurve.ideal hG₁ : Set (MvPolynomial (Fin 3) k)) :=
      ⟨φ₁ R.1, (zeroLocus_ideal hG₁).ge hR.2.1⟩
    have h1 := congrArg LocalSubring.toSubring (hl₁ R R₁ hR.1.2 rfl)
    have h2 := congrArg LocalSubring.toSubring (hl₂ R₁ R' hR.2.2 hRR')
    refine LocalSubring.toSubring_injective ?_
    rw [LocalSubring.map_toSubring] at h1 h2 ⊢
    rw [← h2, ← h1, Subring.map_map]
    rfl

/-- A quadratic transformation at a point that is not terrible, through a change of coordinates
that keeps a finite set `S ∌ P` of simple points off the fundamental triangle, with the data of
`exists_finite_injOn_properTransform_linearSubst`. -/
private theorem exists_avoids_of_not_isTerriblePoint [IsAlgClosed k] (hF : F.IsHomogeneous n)
    [Fact (Irreducible F)] (hP : ¬IsTerriblePoint F P.rep) {S : Set (ℙ k (Fin 3 → k))}
    (hS : S.Finite) (hSF : ∀ P ∈ S, IsSimplePoint F P) (hPS : P ∉ S) :
    ∃ (G : MvPolynomial (Fin 3) k) (d : ℕ) (hG : G.IsHomogeneous d) (hirrG : Irreducible G),
      IsQuadraticTransformAt F P G ∧
      haveI := Fact.mk hirrG
      ∃ B φ e, Avoids hF hG S B φ e := by
  obtain ⟨M, hM, hTP, hE, hav⟩ := exists_isExcellentPosition_avoiding hF Fact.out hP hS hPS
  obtain ⟨M', rfl⟩ : ∃ M' : GL (Fin 3) k, M'.1 = M :=
    ⟨Matrix.nonsingInvUnit M (Matrix.isUnit_det_of_mulVecLin_injective hM), rfl⟩
  have h : IsQuadraticTransformAt F P (properTransform (linearSubst M'.1 F)) :=
    isQuadraticTransformAt_def.2 ⟨M'.1, hM, hTP, hE, rfl⟩
  have hirrG := h.irreducible hF Fact.out
  have := Fact.mk hirrG
  obtain ⟨B, hB⟩ := exists_finite_injOn_properTransform_linearSubst hF M' hE.not_X_dvd
    (h.isHomogeneous hF) rfl (φ := fun R ↦ quadraticMap (map (M'⁻¹).1.mulVecLin
      (mulVec_injective_of_isUnit (M'⁻¹).isUnit) R)) (fun R ↦ by rw [map_inv_map_mulVecLin])
    hSF hav
  exact ⟨_, _, h.isHomogeneous hF, hirrG, h, B, _, _, hB⟩

/-! ### The reduction -/

/-- `exists_isChain_isQuadraticTransform_lt`, with the data of `exists_reduction_avoiding` for a
finite set `S` of simple points. -/
private theorem exists_isChain_isQuadraticTransform_lt_avoids [IsAlgClosed k]
    (hF : F.IsHomogeneous n) [Fact (Irreducible F)] (hP : P ∈ nonOrdinaryMultiplePoints F)
    {S : Set (ℙ k (Fin 3 → k))} (hS : S.Finite) (hSF : ∀ P ∈ S, IsSimplePoint F P) :
    ∃ (l : List (MvPolynomial (Fin 3) k)) (G : MvPolynomial (Fin 3) k) (d : ℕ)
      (hG : G.IsHomogeneous d) (hirrG : Irreducible G),
      List.IsChain IsQuadraticTransform (F :: (l ++ [G])) ∧
      ((nonOrdinaryMultiplePoints G).ncard : ℤ) + virtualGenus G <
        (nonOrdinaryMultiplePoints F).ncard + virtualGenus F ∧
      virtualGenus G ≤ virtualGenus F ∧ l.length ≤ 1 ∧ (CharZero k → l = []) ∧
      haveI := Fact.mk hirrG
      ∃ B φ e, Avoids hF hG S B φ e := by
  have hirr : Irreducible F := Fact.out
  have hPS : P ∉ S := fun h ↦ IsMultiplePoint.not_isSimplePoint
    (mem_nonOrdinaryMultiplePoints_iff.1 hP).1 (hSF P h)
  by_cases hT : IsTerriblePoint F P.rep
  · obtain ⟨Q, -, -, hQ1, M, hM, hTQ, hE, hav, hnt⟩ :=
      exists_isQuadraticTransformAt_of_isTerriblePoint hF hirr hT hS
    obtain ⟨M', rfl⟩ : ∃ M' : GL (Fin 3) k, M'.1 = M :=
      ⟨Matrix.nonsingInvUnit M (Matrix.isUnit_det_of_mulVecLin_injective hM), rfl⟩
    have h₁ : IsQuadraticTransformAt F Q (properTransform (linearSubst M'.1 F)) :=
      isQuadraticTransformAt_def.2 ⟨M'.1, hM, hTQ, hE, rfl⟩
    have hG₁ := h₁.isHomogeneous hF
    have hirr₁ := h₁.irreducible hF hirr
    have := Fact.mk hirr₁
    set φ₁ := fun R ↦ quadraticMap (map (M'⁻¹).1.mulVecLin
      (mulVec_injective_of_isUnit (M'⁻¹).isUnit) R)
    have hφ₁ (R : ℙ k (Fin 3 → k)) :
        φ₁ (map M'.1.mulVecLin (mulVec_injective_of_isUnit M'.isUnit) R) = quadraticMap R := by
      simp only [φ₁, map_inv_map_mulVecLin]
    obtain ⟨B₁, hA₁⟩ := exists_finite_injOn_properTransform_linearSubst hF M' hE.not_X_dvd hG₁
      rfl hφ₁ hSF fun R hR ↦ hav R (Set.mem_insert_of_mem P hR)
    obtain ⟨R, hR⟩ := (bijective_map_mulVecLin M').2 P
    have hRt : R ∉ fundamentalTriangle := hav R (hR ▸ Set.mem_insert P S)
    have hP₁ := (quadraticMap_mem_nonOrdinaryMultiplePoints_properTransform_linearSubst_iff hF hM
      hRt).2 (hR ▸ hP)
    have hS₁ : ∀ P ∈ φ₁ '' S, IsSimplePoint (properTransform (linearSubst M'.1 F)) P := by
      rintro _ ⟨s, hs, rfl⟩
      exact hA₁.2.2.2.2.2.1 s ⟨(hSF s hs).mem_zeroLocus hF, Set.disjoint_left.1 hA₁.2.1 hs⟩
    have hPS₁ : quadraticMap R ∉ φ₁ '' S := by
      rintro ⟨s, hs, hse⟩
      obtain ⟨Rs, rfl⟩ := (bijective_map_mulVecLin M').2 s
      rw [hφ₁] at hse
      obtain rfl := bijOn_quadraticMap_compl_fundamentalTriangle.injOn
        (hav Rs (Set.mem_insert_of_mem P hs)) hRt hse
      exact hPS (hR ▸ hs)
    obtain ⟨G, d, hG, hirrG, h₂, B₂, φ₂, e₂, hA₂⟩ :=
      exists_avoids_of_not_isTerriblePoint hG₁ (hnt R hR) (hS.image φ₁) hS₁ hPS₁
    have hN := h₁.ncard_nonOrdinaryMultiplePoints_eq hF (Or.inl hQ1)
    have := Fact.mk hirrG
    have hg := (h₁.virtualGenus_eq hF hirr (Or.inl hQ1)).1
    refine ⟨[properTransform (linearSubst M'.1 F)], G, d, hG, hirrG, ?_, ?_, ?_, by simp,
      fun _ ↦ absurd hT (not_isTerriblePoint hF hirr P.rep_ne_zero), _, _, _,
      Avoids.trans hA₁ hA₂⟩
    · simpa using ⟨h₁.isQuadraticTransform, h₂.isQuadraticTransform⟩
    · simpa [hN, hg] using h₂.ncard_add_virtualGenus_lt hG₁ hirr₁ hP₁
    · simpa [hg] using h₂.isQuadraticTransform.virtualGenus_le hG₁ hirr₁
  · obtain ⟨G, d, hG, hirrG, h, B, φ, e, hA⟩ :=
      exists_avoids_of_not_isTerriblePoint hF hT hS hSF hPS
    exact ⟨[], G, d, hG, hirrG, by simpa using h.isQuadraticTransform,
      h.ncard_add_virtualGenus_lt hF hirr hP, h.isQuadraticTransform.virtualGenus_le hF hirr,
      by simp, fun _ ↦ rfl, B, φ, e, hA⟩

/-- **One or two quadratic transformations lower `N + g*`** (Fulton, §7.4, proof of Theorem 2,
and Appendix A). Let `F` be an irreducible form over an algebraically closed field with a
non-ordinary multiple point. There is a sequence `F, l, G` of quadratic transformations, with
`l` of length at most one and empty in characteristic zero, such that `G` is an irreducible form
with `N(G) + g*(G) < N(F) + g*(F)` and `g*(G) ≤ g*(F)`, `N` counting the non-ordinary multiple
points. -/
theorem exists_isChain_isQuadraticTransform_lt [IsAlgClosed k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) (hP : P ∈ nonOrdinaryMultiplePoints F) :
    ∃ (l : List (MvPolynomial (Fin 3) k)) (G : MvPolynomial (Fin 3) k) (d : ℕ),
      List.IsChain IsQuadraticTransform (F :: (l ++ [G])) ∧ G.IsHomogeneous d ∧ Irreducible G ∧
      ((nonOrdinaryMultiplePoints G).ncard : ℤ) + virtualGenus G <
        (nonOrdinaryMultiplePoints F).ncard + virtualGenus F ∧
      virtualGenus G ≤ virtualGenus F ∧ l.length ≤ 1 ∧ (CharZero k → l = []) := by
  have := Fact.mk hirr
  obtain ⟨l, G, d, hG, hirrG, hc, hlt, hg, hl, hl0, -⟩ :=
    exists_isChain_isQuadraticTransform_lt_avoids hF hP Set.finite_empty (by simp)
  exact ⟨l, G, d, hc, hG, hirrG, hlt, hg, hl, hl0⟩

/-- **Reduction to ordinary multiple points, along a finite set of simple points** (Fulton, §7.4,
Theorem 2, Problem 7.13, and Appendix A). Let `F` be an irreducible form over an algebraically
closed field and `S` a finite set of simple points of `F`. There is a finite sequence
`F = F₁, …, F_m = G` of quadratic transformations such that `G` is an irreducible form with only
ordinary multiple points and `g*(G) ≤ g*(F)`, the number of steps `m - 1` being at most
`2 (N(F) + g*(F))`, and at most `N(F) + g*(F)` in characteristic zero, where `N(F)` is the number
of non-ordinary multiple points of `F` and `g*` the virtual genus. Moreover there are a finite
set `B` of points, disjoint from `S` and containing the multiple points of `F`, a map
`φ : ℙ² → ℙ²` and an isomorphism `e : k(F) ≅ k(G)` such that `φ` is injective on `V(F) ∖ B`,
its image `φ(V(F) ∖ B)` is cofinite in `V(G)` and consists of simple points of `G`, and `e`
carries the local ring of `F` at each point `R` of `V(F) ∖ B` onto the local ring of `G` at
`φ R`. -/
theorem exists_reduction_avoiding [IsAlgClosed k] (hF : F.IsHomogeneous n) (hirr : Irreducible F)
    {S : Set (ℙ k (Fin 3 → k))} (hS : S.Finite) (hSF : ∀ P ∈ S, IsSimplePoint F P) :
    ∃ (l : List (MvPolynomial (Fin 3) k)) (G : MvPolynomial (Fin 3) k) (d : ℕ)
      (hG : G.IsHomogeneous d) (hirrG : Irreducible G),
      List.IsChain IsQuadraticTransform (F :: l) ∧ (F :: l).getLast (List.cons_ne_nil F l) = G ∧
      (∀ Q, IsMultiplePoint G Q → IsOrdinaryMultiplePoint G Q) ∧
      (l.length : ℤ) ≤ 2 * ((nonOrdinaryMultiplePoints F).ncard + virtualGenus F) ∧
      (CharZero k → (l.length : ℤ) ≤ (nonOrdinaryMultiplePoints F).ncard + virtualGenus F) ∧
      virtualGenus G ≤ virtualGenus F ∧
      haveI := Fact.mk hirr
      haveI := Fact.mk hirrG
      ∃ (B : Set (ℙ k (Fin 3 → k))) (φ : ℙ k (Fin 3 → k) → ℙ k (Fin 3 → k))
        (e : functionField hF ≃ₐ[k] functionField hG),
        B.Finite ∧ Disjoint S B ∧ {Q | IsMultiplePoint F Q} ⊆ B ∧
        Set.InjOn φ (zeroLocus {F} \ B) ∧ (zeroLocus {G} \ φ '' (zeroLocus {F} \ B)).Finite ∧
        (∀ R ∈ zeroLocus {F} \ B, IsSimplePoint G (φ R)) ∧
        ∀ (R : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)))
          (R' : zeroLocus (projectivePlaneCurve.ideal hG : Set (MvPolynomial (Fin 3) k))),
          R.1 ∉ B → φ R.1 = R'.1 →
            (localSubring hF R).map (e : functionField hF →+* _) = localSubring hG R' := by
  induction hμ : (((nonOrdinaryMultiplePoints F).ncard : ℤ) + virtualGenus F).toNat
    using Nat.strong_induction_on generalizing F n S with
  | _ μ ih =>
  have := Fact.mk hirr
  have hg := virtualGenus_nonneg hF hirr
  by_cases h0 : nonOrdinaryMultiplePoints F = ∅
  · exact ⟨[], F, n, hF, hirr, List.isChain_singleton F, rfl,
      nonOrdinaryMultiplePoints_eq_empty_iff.1 h0, by simp; omega, fun _ ↦ by simp; omega,
      le_rfl, _, _, _, avoids_refl hF hSF⟩
  obtain ⟨P, hP⟩ := Set.nonempty_iff_ne_empty.2 h0
  obtain ⟨l₁, G₁, d₁, hG₁, hirr₁, hc₁, hlt, hgle, hl₁, hl₁0, B₁, φ₁, e₁, hA₁⟩ :=
    exists_isChain_isQuadraticTransform_lt_avoids hF hP hS hSF
  have := Fact.mk hirr₁
  have hg₁ := virtualGenus_nonneg hG₁ hirr₁
  have hS₁ : ∀ P ∈ φ₁ '' S, IsSimplePoint G₁ P := by
    rintro _ ⟨s, hs, rfl⟩
    exact hA₁.2.2.2.2.2.1 s ⟨(hSF s hs).mem_zeroLocus hF, Set.disjoint_left.1 hA₁.2.1 hs⟩
  obtain ⟨l₂, G, d, hG, hirrG, hc₂, hl₂G, hord, h2, h0', hgG, B₂, φ₂, e₂, hA₂⟩ :=
    ih _ (by omega) hG₁ hirr₁ (hS.image φ₁) hS₁ rfl
  have := Fact.mk hirrG
  refine ⟨l₁ ++ G₁ :: l₂, G, d, hG, hirrG, List.isChain_cons_split.2 ⟨hc₁, hc₂⟩, ?_, hord, ?_,
    fun h ↦ ?_, hgG.trans hgle, _, _, _, Avoids.trans hA₁ hA₂⟩
  · rw [← hl₂G, List.getLast_cons (by simp), List.getLast_append_of_ne_nil (by simp)]
  · simp only [List.length_append, List.length_cons]
    push_cast
    omega
  · obtain rfl := hl₁0 h
    have := h0' h
    simp only [List.nil_append, List.length_cons]
    push_cast
    omega

/-- **Reduction to ordinary multiple points** (Fulton, §7.4, Theorem 2, and Appendix A). Let `F`
be an irreducible form over an algebraically closed field. There is a finite sequence
`F = F₁, …, F_m = G` of quadratic transformations such that `G` is an irreducible form with only
ordinary multiple points and `g*(G) ≤ g*(F)`. The number of steps `m - 1` is at most
`2 (N(F) + g*(F))`, and at most `N(F) + g*(F)` in characteristic zero, where `N(F)` is the number
of non-ordinary multiple points of `F` and `g*` the virtual genus. -/
theorem exists_reduction [IsAlgClosed k] (hF : F.IsHomogeneous n) (hirr : Irreducible F) :
    ∃ (l : List (MvPolynomial (Fin 3) k)) (G : MvPolynomial (Fin 3) k) (d : ℕ),
      List.IsChain IsQuadraticTransform (F :: l) ∧ (F :: l).getLast (List.cons_ne_nil F l) = G ∧
      G.IsHomogeneous d ∧ Irreducible G ∧
      (∀ Q, IsMultiplePoint G Q → IsOrdinaryMultiplePoint G Q) ∧
      (l.length : ℤ) ≤ 2 * ((nonOrdinaryMultiplePoints F).ncard + virtualGenus F) ∧
      (CharZero k → (l.length : ℤ) ≤ (nonOrdinaryMultiplePoints F).ncard + virtualGenus F) ∧
      virtualGenus G ≤ virtualGenus F := by
  obtain ⟨l, G, d, hG, hirrG, hc, hlG, hord, h2, h0, hg, -⟩ :=
    exists_reduction_avoiding hF hirr Set.finite_empty (S := ∅) (by simp)
  exact ⟨l, G, d, hc, hlG, hG, hirrG, hord, h2, h0, hg⟩

end Avoiding

/-- **An ordinary plane model** (Fulton, §7.4, Theorem 2). Let `F` be an irreducible form over an
algebraically closed field. There is an irreducible form `G` with only ordinary multiple points,
`g*(G) ≤ g*(F)`, and function field isomorphic to that of `F`. -/
theorem exists_ordinary_model [IsAlgClosed k] (hF : F.IsHomogeneous n) (hirr : Irreducible F) :
    ∃ (G : MvPolynomial (Fin 3) k) (d : ℕ) (hG : G.IsHomogeneous d) (hirrG : Irreducible G),
      (∀ Q, IsMultiplePoint G Q → IsOrdinaryMultiplePoint G Q) ∧
      virtualGenus G ≤ virtualGenus F ∧
      haveI := Fact.mk hirr
      haveI := Fact.mk hirrG
      Nonempty (functionField hF ≃ₐ[k] functionField hG) := by
  obtain ⟨l, G, d, hc, hlG, hG, hirrG, hord, -, -, hg⟩ := exists_reduction hF hirr
  have := Fact.mk hirr
  have := Fact.mk hirrG
  exact ⟨G, d, hG, hirrG, hord, hg, nonempty_algEquiv_of_reflTransGen_isQuadraticTransform
    (List.relationReflTransGen_of_exists_isChain_cons l hc hlG) hF hG⟩

end PlaneCurves.Projective

end
