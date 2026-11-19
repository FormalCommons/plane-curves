/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.NonsingularModel.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.OrdinaryMultiplePoint
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Finiteness

/-!
# Resolution of a plane curve with only ordinary multiple points

Let `k` be algebraically closed and `C : F = 0` an irreducible projective plane curve whose
multiple points `P₁, …, P_t` are all ordinary. Fulton (§7.3, Proposition 1) blows up `ℙ²` at the
`Pᵢ` and shows that the proper transform `C'` of `C` is a nonsingular curve with a birational
morphism `f : C' → C`, an isomorphism over `C ∖ {P₁, …, P_t}`, with `f⁻¹(Pᵢ)` in bijection with
the tangents of `C` at `Pᵢ`.

This file proves the statement for the nonsingular model of `C` (`center_spec`): the places of
`k(C)` with the centre map `center hF`. This is the route the atlas recommends: `C'` and the
nonsingular model are the nonsingular projective curves with function field `k(C)` over `C`,
and the nonsingular model needs no multiprojective varieties.

## Main definitions

* `PlaneCurves.Projective.centerEquivSimplePoints`: the centre map is a bijection from the places
  centred at simple points onto the simple points of `C`.
* `PlaneCurves.Projective.placesOverEquivTangents`: the places over an ordinary multiple point
  `P` are in bijection with the tangents of `C` at `P`.

## Main results

* `PlaneCurves.Projective.ncard_tangents_of_isOrdinaryMultiplePoint`: an ordinary multiple point
  `P` has `m_P(C)` tangents.
* `PlaneCurves.Projective.center_spec_of_isOrdinaryMultiplePoint`: the milestone.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.3, Proposition 1
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti
open TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
  {hF : F.IsHomogeneous d} [Fact (Irreducible F)]
  {P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))}

variable (hF) in
/-- **The nonsingular model over the simple points.** The centre map is a bijection from the
places of `k(C)` centred at simple points onto the simple points of `C`, with inverse the place
at a point (`placeAt`), whose valuation ring is the local ring `𝒪_P(C)`. -/
noncomputable def centerEquivSimplePoints :
    {Q : Place k (functionField hF) // IsSimplePoint F (center hF Q).1} ≃
      {P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)) //
        IsSimplePoint F P.1} where
  toFun Q := ⟨center hF Q, Q.2⟩
  invFun P := ⟨placeAt hF P.2, by rw [center_placeAt]; exact P.2⟩
  left_inv Q := Subtype.ext (placeAt_center Q.2)
  right_inv P := Subtype.ext (center_placeAt P.2)

@[simp]
theorem coe_centerEquivSimplePoints_apply
    (Q : {Q : Place k (functionField hF) // IsSimplePoint F (center hF Q).1}) :
    (centerEquivSimplePoints hF Q : zeroLocus
      (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))) = center hF Q :=
  (rfl)

@[simp]
theorem coe_centerEquivSimplePoints_symm_apply
    (P : {P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)) //
      IsSimplePoint F P.1}) :
    ((centerEquivSimplePoints hF).symm P : Place k (functionField hF)) = placeAt hF P.2 :=
  (rfl)

/-- **The places over an ordinary multiple point and the tangents.** For an ordinary multiple
point `P` of `C` there is a bijection from the places over `P` onto the tangent lines of `C` at
`P`, sending `Q` to a tangent `L_Q` such that every nonzero form `G` of which `L_Q` is not a
tangent at `P` has order `m_P(G)` at `Q`. -/
theorem exists_bijective_placesOver_tangents (h : IsOrdinaryMultiplePoint F P.1) :
    ∃ f : placesOver hF P → tangents F P.1, Function.Bijective f ∧
      ∀ Q, ∃ L, IsTangentAt F P.1 L ∧ Associates.mk L = f Q ∧
        ∀ {m : ℕ} {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m), G ≠ 0 →
          ¬IsTangentAt G P.1 L → ordForm hF Q hG = (mult G P.1).toNat := by
  obtain ⟨L, hLt, hLu, hLG⟩ := exists_isTangentAt_and_ordForm_eq_mult h
  refine ⟨fun Q ↦ ⟨Associates.mk (L Q), (hLt Q Q.2).mk_mem_tangents⟩,
    ⟨fun Q Q' hQQ' ↦ ?_, fun a ↦ ?_⟩,
    fun Q ↦ ⟨L Q, hLt Q Q.2, rfl, fun hG hG0 hT ↦ hLG hG hG0 Q Q.2 hT⟩⟩
  · have hmk := Associates.mk_eq_mk_iff_associated.1 (congrArg Subtype.val hQQ')
    obtain ⟨_, -, hu⟩ := hLu (L Q) (hLt Q Q.2)
    exact Subtype.ext ((hu Q ⟨Q.2, Associated.refl _⟩).trans (hu Q' ⟨Q'.2, hmk⟩).symm)
  · obtain ⟨a, ha⟩ := a
    obtain ⟨L', hL', rfl⟩ := mem_tangents_iff.1 ha
    obtain ⟨Q, ⟨hQ, hQa⟩, -⟩ := hLu L' hL'
    exact ⟨⟨Q, hQ⟩, Subtype.ext (Associates.mk_eq_mk_iff_associated.2 hQa).symm⟩

variable (hF P) in
/-- The bijection from the places over an ordinary multiple point `P` of `C` onto the tangents
of `C` at `P`, given by `exists_bijective_placesOver_tangents`. -/
noncomputable def placesOverEquivTangents (h : IsOrdinaryMultiplePoint F P.1) :
    placesOver hF P ≃ tangents F P.1 :=
  Equiv.ofBijective _ (exists_bijective_placesOver_tangents h).choose_spec.1

/-- The tangent `L_Q` attached to a place `Q` over an ordinary multiple point by
`placesOverEquivTangents`: a nonzero form `G` of which `L_Q` is not a tangent at `P` has order
`m_P(G)` at `Q`. -/
theorem exists_placesOverEquivTangents_eq (h : IsOrdinaryMultiplePoint F P.1)
    (Q : placesOver hF P) :
    ∃ L, IsTangentAt F P.1 L ∧ Associates.mk L = placesOverEquivTangents hF P h Q ∧
      ∀ {m : ℕ} {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m), G ≠ 0 →
        ¬IsTangentAt G P.1 L → ordForm hF Q hG = (mult G P.1).toNat :=
  (exists_bijective_placesOver_tangents h).choose_spec.2 Q

/-- **The number of tangents at an ordinary multiple point.** An ordinary multiple point `P` of
an irreducible projective plane curve `C` has exactly `m_P(C)` tangents. -/
theorem ncard_tangents_of_isOrdinaryMultiplePoint (h : IsOrdinaryMultiplePoint F P.1) :
    (tangents F P.1).ncard = (mult F P.1).toNat := by
  rw [← ncard_placesOver_of_isOrdinaryMultiplePoint h, ← Nat.card_coe_set_eq,
    ← Nat.card_coe_set_eq, Nat.card_congr (placesOverEquivTangents hF P h)]

/-- **Resolution of a plane curve with only ordinary multiple points.** Let `k` be algebraically
closed and `C : F = 0` an irreducible projective plane curve all of whose multiple points
`P₁, …, P_t` are ordinary. Let `C'` be the nonsingular model of `C`, the places `Q` of
`K = k(C)` with their valuation rings `𝒪_Q` as local rings, and `f : C' → C` the centre map,
which is birational since `C'` has function field `K`. Then:

* the multiple points `P₁, …, P_t` are finitely many;
* `C'` is nonsingular: every `𝒪_Q` is a discrete valuation ring of `K` over `k`;
* `f` maps `C'` onto `C`;
* `f` is an isomorphism over `C ∖ {P₁, …, P_t}`: over each other point `P` lies exactly one
  place, and its valuation ring is `𝒪_P(C)`;
* for each `Pᵢ`, the fibre `f⁻¹(Pᵢ)` has `m_{Pᵢ}(C)` points and is in bijection with the
  tangents of `C` at `Pᵢ`, the place `Q` going to a tangent `L_Q` such that every nonzero form
  `G` of which `L_Q` is not a tangent at `Pᵢ` has order `m_{Pᵢ}(G)` at `Q`.

Milestone: *Resolution of a plane curve with only ordinary multiple points by blowing up*. -/
theorem center_spec_of_isOrdinaryMultiplePoint
    (hord : ∀ P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)),
      IsMultiplePoint F P.1 → IsOrdinaryMultiplePoint F P.1) :
    {P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)) |
      IsMultiplePoint F P.1}.Finite ∧
    (∀ Q : Place k (functionField hF), IsDiscreteValuationRing Q.integers) ∧
    Function.Surjective (center hF) ∧
    (∀ P, ¬IsMultiplePoint F P.1 →
      (∃! Q : Place k (functionField hF), center hF Q = P) ∧
      ∀ Q : Place k (functionField hF), center hF Q = P →
        Q.integers.toSubring = (localSubring hF P).toSubring) ∧
    (∀ P, IsMultiplePoint F P.1 →
      (placesOver hF P).ncard = (mult F P.1).toNat ∧
      ∃ f : placesOver hF P ≃ tangents F P.1, ∀ Q, ∃ L, IsTangentAt F P.1 L ∧
        Associates.mk L = f Q ∧
        ∀ {m : ℕ} {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m), G ≠ 0 →
          ¬IsTangentAt G P.1 L → ordForm hF Q hG = (mult G P.1).toNat) := by
  obtain ⟨-, -, hsurj, -, hsimple, -⟩ := center_spec hF
  refine ⟨(finite_setOf_isMultiplePoint_of_irreducible hF Fact.out).preimage
      Subtype.val_injective.injOn, fun Q ↦ inferInstance, hsurj,
    fun P hP ↦ hsimple P (by_contra fun h ↦ hP (isMultiplePoint_iff_not_isSimplePoint.2
      ⟨(mem_zeroLocus_ideal_iff hF).1 P.2, h⟩)),
    fun P hP ↦ ?_⟩
  exact ⟨ncard_placesOver_of_isOrdinaryMultiplePoint (hord P hP),
    placesOverEquivTangents hF P (hord P hP), exists_placesOverEquivTangents_eq (hord P hP)⟩

end PlaneCurves.Projective

end
