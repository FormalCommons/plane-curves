/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.IntersectionNumber.Properties
public import TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring

/-!
# The place at a simple point of a projective plane curve

Let `k` be an algebraically closed field and `C : F = 0` an irreducible projective plane curve
with function field `k(C)`. The function field is the field of fractions of every local ring
`𝒪_P(C)`. If `P` is a simple point of `C`, then `𝒪_P(C) ≅ 𝒪_P(ℙ²) ⧸ (F_*)` is a discrete
valuation ring, hence a valuation ring of `k(C)`, and it is the valuation ring of exactly one
place of `k(C)`, the **place at `P`**. It is the only place over `P`, since a discrete valuation
ring is maximal for domination.

If `C` is nonsingular, the centre map is therefore a bijection from the places of `k(C)` onto the
points of `C`, with inverse `P ↦` the place at `P`.

## Main definitions

* `PlaneCurves.Projective.valuationSubringOfIsSimplePoint hF hP`: `𝒪_P(C)` as a valuation
  subring of `k(C)`, for a simple point `P`.
* `PlaneCurves.Projective.placeAt hF hP`: the place of `k(C)` whose valuation ring is `𝒪_P(C)`.
* `PlaneCurves.Projective.centerEquiv hF hns`: for a nonsingular `F`, the centre map as a
  bijection from the places of `k(C)` onto `C`.

## Main results

* `isFractionRing_localSubring`: `k(C)` is the field of fractions of `𝒪_P(C)`.
* `isDiscreteValuationRing_localSubring`: `𝒪_P(C)` is a discrete valuation ring at a simple
  point.
* `integers_placeAt`, `center_placeAt`, `placesOver_eq_singleton`: the place at `P` has
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

variable (P) in
/-- **`k(C)` is the field of fractions of `𝒪_P(C)`**: `f / g = (f / Xᵢᵐ) / (g / Xᵢᵐ)` for a
coordinate `Xᵢ` not vanishing at `P`. -/
theorem isFractionRing_localSubring :
    IsFractionRing (localSubring hF P).toSubring (functionField hF) := by
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  obtain ⟨i, hi⟩ := P.1.exists_mem_affineOpen
  have hiP : eval P.1.rep (X i) ≠ 0 := by simpa using (mem_affineOpen_iff _ _).1 hi
  obtain ⟨m, f, g, hf, hg, hgI, rfl⟩ := ProjectiveSpace.functionField.exists_eq_mk z
  have hXP : eval P.1.rep (X i ^ m) ≠ 0 := by simpa using pow_ne_zero m hiP
  have hXI := notMem_of_eval_rep_ne_zero P.2 (isHomogeneous_X_pow i m) hXP
  refine ⟨⟨_, mem_localSubring_iff.2 ⟨m, f, _, hf, isHomogeneous_X_pow i m, hXP, rfl⟩⟩,
    ⟨_, mem_localSubring_iff.2 ⟨m, g, _, hg, isHomogeneous_X_pow i m, hXP, rfl⟩⟩, ?_⟩
  exact (ProjectiveSpace.functionField.mk_div_mk hf hg _ hgI hXI).symm

variable {hF}

/-- **The local ring of `C` at a simple point is a discrete valuation ring**: it is
`𝒪_P(ℙ²) ⧸ (F_*)` (`quotientLocalEquationEquiv`), which is one
(`exists_isDiscreteValuationRing_quotient_iff`). -/
theorem isDiscreteValuationRing_localSubring (hP : IsSimplePoint F P.1) :
    IsDiscreteValuationRing (localSubring hF P).toSubring := by
  obtain ⟨_, _⟩ := (exists_isDiscreteValuationRing_quotient_iff hF hP.eval_rep_eq_zero).2 hP
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (quotientLocalEquationEquiv hF P).toRingEquiv

/-- The local ring `𝒪_P(C)` at a simple point `P`, as a valuation subring of `k(C)`: an element
of `k(C)` or its inverse lies in the discrete valuation ring `𝒪_P(C)`. -/
noncomputable def valuationSubringOfIsSimplePoint (hP : IsSimplePoint F P.1) :
    ValuationSubring (functionField hF) where
  toSubring := (localSubring hF P).toSubring
  mem_or_inv_mem' z := by
    have := isDiscreteValuationRing_localSubring hP
    have := isFractionRing_localSubring hF P
    rcases ValuationRing.isInteger_or_isInteger (localSubring hF P).toSubring z with
      ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inl (ha ▸ a.2)
    · exact Or.inr (ha ▸ a.2)

@[simp]
theorem toSubring_valuationSubringOfIsSimplePoint (hP : IsSimplePoint F P.1) :
    (valuationSubringOfIsSimplePoint hP).toSubring = (localSubring hF P).toSubring :=
  (rfl)

@[simp]
theorem mem_valuationSubringOfIsSimplePoint {hP : IsSimplePoint F P.1} {z : functionField hF} :
    z ∈ valuationSubringOfIsSimplePoint hP ↔ z ∈ (localSubring hF P).toSubring :=
  Iff.rfl

/-- `𝒪_P(C)` as a valuation subring has `𝒪_P(C)` as its local subring. -/
@[simp]
theorem toLocalSubring_valuationSubringOfIsSimplePoint (hP : IsSimplePoint F P.1) :
    (valuationSubringOfIsSimplePoint hP).toLocalSubring = localSubring hF P :=
  LocalSubring.toSubring_injective (rfl)

/-- The constants lie in `𝒪_P(C)`. -/
theorem algebraMap_mem_localSubring (P : zeroLocus
    (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))) (c : k) :
    algebraMap k (functionField hF) c ∈ (localSubring hF P).toSubring :=
  coe_algebraMap_localSubring (projectivePlaneCurve.ideal hF) P c ▸
    (algebraMap k (localSubring hF P).toSubring c).2

variable [IsAlgClosed k]

/-- `𝒪_P(C)` is not all of `k(C)`, since its maximal ideal is nonzero. -/
theorem valuationSubringOfIsSimplePoint_ne_top (hP : IsSimplePoint F P.1) :
    valuationSubringOfIsSimplePoint hP ≠ ⊤ := by
  intro h
  obtain ⟨z, hzm, hz0⟩ := exists_ne_zero_mem_maximalIdeal_localSubring hF P
  have hinv : (z : functionField hF)⁻¹ ∈ (localSubring hF P).toSubring := by
    rw [← mem_valuationSubringOfIsSimplePoint (hP := hP), h]
    exact ValuationSubring.mem_top _
  refine (IsLocalRing.mem_maximalIdeal _).1 hzm (isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, ?_⟩)
  exact Subtype.ext (mul_inv_cancel₀ (by simpa using hz0))

/-! ### The place at a simple point -/

variable (hF) in
/-- The **place at a simple point** `P` of `C`: the unique place of `k(C)` whose valuation ring
is the local ring `𝒪_P(C)` (`integers_placeAt`). It is the only place over `P`
(`placesOver_eq_singleton`). -/
noncomputable def placeAt (hP : IsSimplePoint F P.1) : Place k (functionField hF) :=
  Place.ofValuationSubring (functionField.isFunctionField hF)
    (fun c ↦ mem_valuationSubringOfIsSimplePoint.2 (algebraMap_mem_localSubring P c))
    (valuationSubringOfIsSimplePoint_ne_top hP)

theorem placeAt_def (hP : IsSimplePoint F P.1) :
    placeAt hF hP = Place.ofValuationSubring (functionField.isFunctionField hF)
      (fun c ↦ mem_valuationSubringOfIsSimplePoint.2 (algebraMap_mem_localSubring P c))
      (valuationSubringOfIsSimplePoint_ne_top hP) :=
  (rfl)

/-- The valuation ring of the place at a simple point `P` is `𝒪_P(C)`. -/
@[simp]
theorem integers_placeAt (hP : IsSimplePoint F P.1) :
    (placeAt hF hP).integers = valuationSubringOfIsSimplePoint hP :=
  Place.integers_ofValuationSubring _ _ _

/-- The valuation ring of the place at a simple point `P` is `𝒪_P(C)`, as a local subring. -/
theorem integers_toLocalSubring_placeAt (hP : IsSimplePoint F P.1) :
    (placeAt hF hP).integers.toLocalSubring = localSubring hF P := by
  simp

/-- The place at a simple point `P` is the only place whose valuation ring is `𝒪_P(C)`. -/
theorem eq_placeAt_iff (hP : IsSimplePoint F P.1) {Q : Place k (functionField hF)} :
    Q = placeAt hF hP ↔ Q.integers.toSubring = (localSubring hF P).toSubring := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ Place.integers_injective ?_⟩
  rw [integers_placeAt]
  exact ValuationSubring.toSubring_injective h

/-- The place at a simple point `P` is centred at `P`. -/
@[simp]
theorem center_placeAt (hP : IsSimplePoint F P.1) : center hF (placeAt hF hP) = P := by
  rw [center_eq_iff_le, integers_placeAt, toSubring_valuationSubringOfIsSimplePoint]

/-- **The unique place over a simple point.** The place at a simple point `P` is the only place
of `k(C)` centred at `P`: a place over `P` has a valuation ring containing the discrete valuation
ring `𝒪_P(C)`, hence equal to it. -/
theorem placesOver_eq_singleton (hP : IsSimplePoint F P.1) :
    placesOver hF P = {placeAt hF hP} := by
  ext Q
  rw [Set.mem_singleton_iff, mem_placesOver_iff_le]
  refine ⟨fun h ↦ (Place.eq_of_integers_le (P := placeAt hF hP) ?_).symm, fun h ↦ ?_⟩
  · rw [integers_placeAt]
    exact h
  · rw [h, integers_placeAt, toSubring_valuationSubringOfIsSimplePoint]

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
