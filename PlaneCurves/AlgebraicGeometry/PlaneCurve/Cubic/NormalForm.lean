/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.MultiplePoints

/-!
# Normal forms of irreducible cubics

This file describes the singular points of an irreducible plane cubic `F` over an algebraically
closed field, in every characteristic (Problem 5.13 of Fulton). By the bound on the multiple
points, `F` has at most one multiple point (`eq_of_isMultiplePoint_of_degree_three`), and it is
a double point (`mult_eq_two_of_degree_three`). A double point is a *node*, an ordinary double
point with two distinct tangents, or a *cusp*, with a single tangent of multiplicity `2`
(`isOrdinaryMultiplePoint_or_exists_tangentMultiplicity_eq_two`).

## Main results

All in the namespace `PlaneCurves.Projective`.

* `isOrdinaryMultiplePoint_or_exists_tangentMultiplicity_eq_two_of_degree_three`:
  a multiple point of an irreducible cubic is a node or a cusp.
* `isNonsingular_or_exists_isMultiplePoint_iff_of_degree_three`: an
  irreducible cubic is nonsingular, or it has exactly one multiple point, a double point that is a
  node or a cusp.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], Problem 5.13
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k}

/-- A multiple point `P` of an irreducible cubic `F` is a *node*, an ordinary double point, or a
*cusp*: `F` has a single tangent `L` at `P`, of multiplicity `2`. -/
theorem isOrdinaryMultiplePoint_or_exists_tangentMultiplicity_eq_two_of_degree_three
    (hF : F.IsHomogeneous 3) (hirr : Irreducible F) {P : ℙ k (Fin 3 → k)}
    (hP : IsMultiplePoint F P) :
    IsOrdinaryMultiplePoint F P ∨ ∃ L, IsTangentAt F P L ∧ tangentMultiplicity F P L = 2 :=
  isOrdinaryMultiplePoint_or_exists_tangentMultiplicity_eq_two hF
    (mult_eq_two_of_degree_three hF hirr hP)

/-- **Singular points of an irreducible cubic.** An irreducible plane cubic `F` over an
algebraically closed field is nonsingular, or it has exactly one multiple point `P`; then `P` is a
double point, and it is a node (an ordinary double point) or a cusp (a single tangent `L`, of
multiplicity `2`). -/
theorem isNonsingular_or_exists_isMultiplePoint_iff_of_degree_three (hF : F.IsHomogeneous 3)
    (hirr : Irreducible F) :
    IsNonsingular F ∨ ∃ P : ℙ k (Fin 3 → k), (∀ Q, IsMultiplePoint F Q ↔ Q = P) ∧
      mult F P = 2 ∧
        (IsOrdinaryMultiplePoint F P ∨ ∃ L, IsTangentAt F P L ∧ tangentMultiplicity F P L = 2) := by
  refine or_iff_not_imp_left.2 fun hns ↦ ?_
  obtain ⟨P, hPF, hPs⟩ : ∃ P ∈ zeroLocus {F}, ¬IsSimplePoint F P := by
    simpa [isNonsingular_iff_forall_isSimplePoint hF] using hns
  have hP := (isSimplePoint_or_isMultiplePoint hF hPF).resolve_left hPs
  refine ⟨P, fun Q ↦ ⟨fun hQ ↦ eq_of_isMultiplePoint_of_degree_three hF hirr hQ hP,
    fun h ↦ h ▸ hP⟩, mult_eq_two_of_degree_three hF hirr hP,
    isOrdinaryMultiplePoint_or_exists_tangentMultiplicity_eq_two_of_degree_three hF hirr hP⟩

end PlaneCurves.Projective

end
