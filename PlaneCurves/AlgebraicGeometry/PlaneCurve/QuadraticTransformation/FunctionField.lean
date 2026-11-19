/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.ChangeOfCoordinates
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Birational
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Position

/-!
# The function field along a quadratic transformation centred at a point

A quadratic transformation `G` of a form `F` centred at a point (`IsQuadraticTransformAt`) is the
proper transform of `F^M` for a change of coordinates `M`. The function fields of `F` and `G`
are isomorphic, through the composite `k(F) ≅ k(F^M) ≅ k((F^M)') = k(G)` of the isomorphism along
the change of coordinates (`functionField.linearSubstEquiv`), the quadratic transformation of
function fields (`quadraticFunctionFieldEquiv`), and the identification of the function fields
of two forms with the same ideal (`ProjectiveSpace.functionField.equivOfEq`). This file names
that composite and shows that it carries the local ring of `F` at `M R` onto the local ring of
`G` at `Q(R)`, for every point `R` of `F^M` off the fundamental triangle.

## Main definitions

* `PlaneCurves.Projective.linearSubstQuadraticFunctionFieldEquiv`: the isomorphism
  `k(F) ≅ k(G)` for `G = (F^M)'`.

## Main results

* `PlaneCurves.Projective.map_localSubring_linearSubstQuadraticFunctionFieldEquiv`: the
  isomorphism carries `𝒪_{M R}(F)` onto `𝒪_{Q(R)}(G)` for `R` off the fundamental triangle.
* `PlaneCurves.Projective.IsQuadraticTransformAt.exists_algEquiv`: an isomorphism
  `k(F) ≅ k(G)` compatible with the local rings at the points off the fundamental triangle.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.4
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti TauCeti.AlgebraicGeometry PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization
open Matrix (mulVec_injective_of_isUnit)

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {F G : MvPolynomial (Fin 3) k} {n m : ℕ}

/-- The curves `G = 0` and `(F^M)' = 0` have the same ideal when `G = (F^M)'`. -/
theorem ideal_properTransform_linearSubst_eq (hF : F.IsHomogeneous n) (M : GL (Fin 3) k)
    (hG : G.IsHomogeneous m) (hGF : G = properTransform (linearSubst M.1 F)) :
    projectivePlaneCurve.ideal (hF.linearSubst M.1).properTransform =
      projectivePlaneCurve.ideal hG :=
  HomogeneousIdeal.toIdeal_injective (by
    rw [projectivePlaneCurve.toIdeal_ideal, projectivePlaneCurve.toIdeal_ideal, hGF])

variable [Fact (Irreducible F)] [Fact (Irreducible G)]

/-- **The function field along a change of coordinates and a quadratic transformation.** For a
change of coordinates `M` such that no coordinate `Xᵢ` divides `F^M`, and `G = (F^M)'`, the
isomorphism `k(F) ≅ k(G)`: the composite of `k(F) ≅ k(F^M)` (`functionField.linearSubstEquiv`),
`k(F^M) ≅ k((F^M)')`, `A / B ↦ A^Q / B^Q` (`quadraticFunctionFieldEquiv`), and
`k((F^M)') = k(G)` (`ProjectiveSpace.functionField.equivOfEq`). -/
noncomputable def linearSubstQuadraticFunctionFieldEquiv (hF : F.IsHomogeneous n)
    (M : GL (Fin 3) k) (hX : ∀ i, ¬ X i ∣ linearSubst M.1 F) (hG : G.IsHomogeneous m)
    (hGF : G = properTransform (linearSubst M.1 F)) :
    functionField hF ≃ₐ[k] functionField hG :=
  haveI : Fact (Irreducible (properTransform (linearSubst M.1 F))) := ⟨hGF ▸ Fact.out⟩
  ((functionField.linearSubstEquiv hF M).trans
    (quadraticFunctionFieldEquiv (hF.linearSubst M.1) hX)).trans
      (ProjectiveSpace.functionField.equivOfEq
        (ideal_properTransform_linearSubst_eq hF M hG hGF))

theorem linearSubstQuadraticFunctionFieldEquiv_def (hF : F.IsHomogeneous n)
    (M : GL (Fin 3) k) (hX : ∀ i, ¬ X i ∣ linearSubst M.1 F) (hG : G.IsHomogeneous m)
    (hGF : G = properTransform (linearSubst M.1 F)) :
    haveI : Fact (Irreducible (properTransform (linearSubst M.1 F))) := ⟨hGF ▸ Fact.out⟩
    linearSubstQuadraticFunctionFieldEquiv hF M hX hG hGF =
      ((functionField.linearSubstEquiv hF M).trans
        (quadraticFunctionFieldEquiv (hF.linearSubst M.1) hX)).trans
          (ProjectiveSpace.functionField.equivOfEq
            (ideal_properTransform_linearSubst_eq hF M hG hGF)) :=
  (rfl)

/-- **Local rings along a change of coordinates and a quadratic transformation.** For a point
`R` of `F^M` off the fundamental triangle, the isomorphism `k(F) ≅ k(G)` carries the local ring
of `F` at `M R` onto the local ring of `G = (F^M)'` at `Q(R)`. -/
theorem map_localSubring_linearSubstQuadraticFunctionFieldEquiv (hF : F.IsHomogeneous n)
    (M : GL (Fin 3) k) (hX : ∀ i, ¬ X i ∣ linearSubst M.1 F) (hG : G.IsHomogeneous m)
    (hGF : G = properTransform (linearSubst M.1 F)) {R₀ : ℙ k (Fin 3 → k)}
    {R : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))}
    {R' : zeroLocus (projectivePlaneCurve.ideal hG : Set (MvPolynomial (Fin 3) k))}
    (hR₀ : R₀ ∉ fundamentalTriangle)
    (hR₀R : map M.1.mulVecLin (mulVec_injective_of_isUnit M.isUnit) R₀ = R.1)
    (hR₀R' : quadraticMap R₀ = R'.1) :
    (localSubring hF R).map
        (linearSubstQuadraticFunctionFieldEquiv hF M hX hG hGF : functionField hF →+* _) =
      localSubring hG R' := by
  have : Fact (Irreducible (properTransform (linearSubst M.1 F))) := ⟨hGF ▸ Fact.out⟩
  have hF' := hF.linearSubst M.1
  have hI := ideal_properTransform_linearSubst_eq hF M hG hGF
  have hR₀F : R₀ ∈ zeroLocus (projectivePlaneCurve.ideal hF' : Set (MvPolynomial (Fin 3) k)) := by
    rw [mem_zeroLocus_ideal_iff, eval_rep_linearSubst_eq_zero_iff M hF,
      ← mem_zeroLocus_ideal_iff hF]
    exact hR₀R ▸ R.2
  have hR₀G : quadraticMap R₀ ∈ zeroLocus
      (projectivePlaneCurve.ideal hF'.properTransform : Set (MvPolynomial (Fin 3) k)) :=
    hI ▸ hR₀R' ▸ R'.2
  have h1 := congrArg LocalSubring.toSubring
    (map_localSubring_linearSubstEquiv (M := M) (P' := ⟨R₀, hR₀F⟩) hR₀R)
  have h2 := congrArg LocalSubring.toSubring
    (map_localSubring_quadraticFunctionFieldEquiv hF' hX (R := ⟨R₀, hR₀F⟩)
      (R' := ⟨_, hR₀G⟩) hR₀ rfl)
  have h3 := congrArg LocalSubring.toSubring
    (ProjectiveSpace.map_localSubring_equivOfEq hI ⟨_, hR₀G⟩ R' hR₀R'.symm)
  refine LocalSubring.toSubring_injective ?_
  rw [LocalSubring.map_toSubring] at h1 h2 h3 ⊢
  rw [← h3, ← h2, ← h1, Subring.map_map, Subring.map_map]
  rfl

/-- **The function field along a quadratic transformation centred at a point.** Let `G` be a
quadratic transformation of an irreducible form `F` centred at `P`. There are a change of
coordinates `T`, given by a matrix `M` as in `IsQuadraticTransformAt`, and an isomorphism
`e : k(F) ≅ k(G)` such that, for every point `R` of `F^T` off the fundamental triangle, `e`
carries the local ring of `F` at `T R` onto the local ring of `G` at `Q(R)`. -/
theorem IsQuadraticTransformAt.exists_algEquiv {P : ℙ k (Fin 3 → k)}
    (h : IsQuadraticTransformAt F P G) (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous m) :
    ∃ (M : Matrix (Fin 3) (Fin 3) k) (hM : Function.Injective M.mulVecLin),
      map M.mulVecLin hM (fundamentalPoint 2) = P ∧ IsExcellentPosition (linearSubst M F) ∧
        G = properTransform (linearSubst M F) ∧
        ∃ e : functionField hF ≃ₐ[k] functionField hG,
          ∀ (R₀ : ℙ k (Fin 3 → k)) (R : zeroLocus (projectivePlaneCurve.ideal hF :
              Set (MvPolynomial (Fin 3) k)))
            (R' : zeroLocus (projectivePlaneCurve.ideal hG : Set (MvPolynomial (Fin 3) k))),
            R₀ ∉ fundamentalTriangle → map M.mulVecLin hM R₀ = R.1 →
              quadraticMap R₀ = R'.1 →
              (localSubring hF R).map (e : functionField hF →+* _) = localSubring hG R' := by
  obtain ⟨M, hM, hMP, hE, hGF⟩ := isQuadraticTransformAt_def.1 h
  obtain ⟨M', rfl⟩ : ∃ M' : GL (Fin 3) k, M'.1 = M :=
    ⟨Matrix.nonsingInvUnit M (Matrix.isUnit_det_of_mulVecLin_injective hM), rfl⟩
  exact ⟨M'.1, hM, hMP, hE, hGF, linearSubstQuadraticFunctionFieldEquiv hF M' hE.not_X_dvd hG hGF,
    fun _ _ _ hR₀ hR₀R hR₀R' ↦
      map_localSubring_linearSubstQuadraticFunctionFieldEquiv hF M' _ hG hGF hR₀ hR₀R hR₀R'⟩

end PlaneCurves.Projective

end
