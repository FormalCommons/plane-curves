/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Logic.Relation
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.FunctionField
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Singularities.Genus

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

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.4
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

end PlaneCurves.Projective

end
