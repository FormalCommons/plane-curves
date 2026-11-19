/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.Blowup
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.IntersectionNumber

/-!
# Noether's formula for intersection numbers, local form

Let `k` be algebraically closed and `F, G ∈ k[X, Y]`, with multiplicities `r = m_0(F)` and
`s = m_0(G)` at the origin, and suppose that the line `X = 0` is not tangent to `F` at the
origin. Let `F' = X⁻ʳ F(X, XZ)` and `G' = X⁻ˢ G(X, XZ)` be the strict transforms
(`PlaneCurves.Affine.blowupStrictTransform`). Then
`I(0, F ∩ G) = r s + ∑_α I((0, α), F' ∩ G')`,
a finite sum: only the points `(0, α)` of `F'` on the exceptional line contribute, the roots of
`F_r(1, Z)`. The curves may be reducible, have multiple components, share components (then both
sides are `⊤`), or not pass through the origin (then both sides are `0`).

The proof follows the atlas. Both sides are additive in `F` (property (6) of intersection
numbers, `blowupStrictTransform_mul` and the additivity of multiplicities), so it suffices to
treat an irreducible `F` through the origin. There Proposition 2 of §7.5
(`PlaneCurves.Affine.map_natCast_intersectionNumber_eq_sum_addValuation`) writes
`I(0, F ∩ G)` as `∑_Q ord_Q(G)` over the places `Q` of `k(F)` over the origin. At each of them
`ord_Q(G) = s · ord_Q(x) + ord_Q(G'(x, z))` (`addValuation_algebraMap_mk_eq_nsmul_add`); the
first terms add up to `s · I(0, F ∩ X) = r s` since `X` is not tangent, and the places over the
origin are the places of `k(F')` over the points `(0, α)` of `F'`
(`localSubring_le_integers_iff`), so the second terms add up, by Proposition 2 for `F'`, to
`∑_α I((0, α), F' ∩ G')`.

## Main results

* `PlaneCurves.Affine.intersectionNumber_eq_mul_add_sum_blowupStrictTransform`: Noether's
  formula, with the sum over any finite set of `α` containing the points of `F'` on the
  exceptional line, and the multiplicities as natural numbers.
* `PlaneCurves.Affine.intersectionNumber_eq_mul_add_finsum_blowupStrictTransform`: Noether's
  formula, local form, `I(0, F ∩ G) = m_0(F) m_0(G) + ∑ᶠ α, I((0, α), F' ∩ G')`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.4, §7.5
-/

public section

open MvPolynomial TauCeti

namespace PlaneCurves.Affine

open AffineSpace

variable {k : Type*} [Field k]

/-- `ℕ∞ → WithTop ℤ`, as an additive monoid homomorphism. -/
private noncomputable abbrev castHom : ℕ∞ →+ WithTop ℤ := (Nat.castAddMonoidHom ℤ).withTopMap

private theorem castHom_apply (n : ℕ∞) : castHom n = n.map (Nat.cast : ℕ → ℤ) := (rfl)

private theorem castHom_injective : Function.Injective castHom :=
  WithTop.map_injective Nat.cast_injective

/-- The strict transform of a curve that does not pass through the origin does not meet the
exceptional line. -/
theorem eval_zero_blowupStrictTransform_ne_zero {F : MvPolynomial (Fin 2) k} (h0 : eval 0 F ≠ 0)
    (α : k) : eval ![0, α] (blowupStrictTransform F) ≠ 0 := by
  rw [eval_zero_blowupStrictTransform, leadingFormAt_of_eval_ne_zero h0, eval_C]
  exact h0

/-- The formula for a curve `F` that does not pass through the origin: both sides vanish. -/
private theorem eq_of_eval_ne_zero {F : MvPolynomial (Fin 2) k} (h0 : eval 0 F ≠ 0)
    (G : MvPolynomial (Fin 2) k) (A : Finset k) :
    intersectionNumber 0 F G = ((F.orderAt 0).toNat * (G.orderAt 0).toNat : ℕ) +
      ∑ α ∈ A, intersectionNumber ![0, α] (blowupStrictTransform F) (blowupStrictTransform G) := by
  rw [intersectionNumber_eq_zero_of_eval_ne_zero_left h0, orderAt_eq_zero_iff.2 h0,
    Finset.sum_eq_zero fun α _ ↦ intersectionNumber_eq_zero_of_eval_ne_zero_left
      (eval_zero_blowupStrictTransform_ne_zero h0 α)]
  simp

/-- A curve to which `X = 0` is not tangent at the origin is not associated to `X`. -/
private theorem not_associated_X_zero_of_not_isTangentAt {F : MvPolynomial (Fin 2) k}
    (hT : ¬IsTangentAt F 0 (X 0)) : ¬Associated F (X 0) := by
  rintro h
  obtain ⟨u, hu⟩ := h.symm
  refine hT (isTangentAt_def.2 ⟨isHomogeneous_X k 0, X_ne_zero 0, ?_⟩)
  rw [← hu, leadingFormAt_mul, (isHomogeneous_X k 0).leadingFormAt_zero]
  exact dvd_mul_right _ _

/-- The line `X = 0` is tangent to the zero polynomial. -/
private theorem ne_zero_of_not_isTangentAt {F : MvPolynomial (Fin 2) k}
    (hT : ¬IsTangentAt F 0 (X 0)) : F ≠ 0 := by
  rintro rfl
  exact hT (isTangentAt_def.2 ⟨isHomogeneous_X k 0, X_ne_zero 0, by simp [leadingFormAt_zero]⟩)

/-- If `X = 0` is not tangent to `F` at the origin, `I(0, F ∩ X) = m_0(F)`. -/
theorem intersectionNumber_X_zero_of_not_isTangentAt {F : MvPolynomial (Fin 2) k}
    (hT : ¬IsTangentAt F 0 (X 0)) : intersectionNumber 0 F (X 0) = F.orderAt 0 := by
  have hF := ne_zero_of_not_isTangentAt hT
  have h := (isTangentAt_iff_orderAt_lt_intersectionNumber (P := 0) hF (isHomogeneous_X k 0)
    (X_ne_zero 0)).not.1 hT
  have hle := mul_orderAt_le_intersectionNumber (0 : Fin 2 → k) F (X 0)
  rw [(isHomogeneous_X k 0).orderAt_zero (X_ne_zero 0), Nat.cast_one, mul_one] at hle
  rw [neg_zero, taylor_zero] at h
  exact le_antisymm (not_lt.1 h) hle

variable [IsAlgClosed k]

open Classical in
/-- The places over a point `P` of an irreducible curve `f`, as a finset; empty if `P ∉ f`. -/
private noncomputable def placesOverFinset {f : MvPolynomial (Fin 2) k} [(Ideal.span {f}).IsPrime]
    (hf : Irreducible f) (P : Fin 2 → k) :
    Finset (Place k (AffineSpace.functionField (Ideal.span {f}))) :=
  if hP : eval P f = 0 then
    (finite_setOf_localSubring_le_integers P (span_le_vanishingIdeal hP)
      (isFunctionField_functionField_span_singleton hf)).toFinset
  else ∅

private theorem mem_placesOverFinset {f : MvPolynomial (Fin 2) k} [(Ideal.span {f}).IsPrime]
    (hf : Irreducible f) {P : Fin 2 → k}
    {Q : Place k (AffineSpace.functionField (Ideal.span {f}))} :
    Q ∈ placesOverFinset hf P ↔ ∃ hP : eval P f = 0,
      (localSubring P (span_le_vanishingIdeal hP)).toSubring ≤ Q.integers.toSubring := by
  unfold placesOverFinset
  split_ifs with hP
  · simp [hP]
  · simp [hP]

private theorem map_natCast_intersectionNumber_eq_sum_placesOverFinset
    {f : MvPolynomial (Fin 2) k} [(Ideal.span {f}).IsPrime] (hf : Irreducible f) (P : Fin 2 → k)
    (g : MvPolynomial (Fin 2) k) :
    (intersectionNumber P f g).map (Nat.cast : ℕ → ℤ) =
      ∑ Q ∈ placesOverFinset hf P,
        Q.addValuation (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {f}) g)) := by
  by_cases hP : eval P f = 0
  · rw [map_natCast_intersectionNumber_eq_sum_addValuation hf hP]
    unfold placesOverFinset
    simp only [hP, ↓reduceDIte]
  · unfold placesOverFinset
    simp only [hP, ↓reduceDIte, Finset.sum_empty,
      intersectionNumber_eq_zero_of_eval_ne_zero_left hP]
    rfl

open Classical in
/-- The places of `k(F)` over the origin, carried to `k(F')`, are the places of `k(F')` over the
points `(0, α)` of the strict transform. -/
private theorem image_map_eq_biUnion
    {F : MvPolynomial (Fin 2) k} [(Ideal.span {F}).IsPrime]
    [(Ideal.span {blowupStrictTransform F}).IsPrime] (hF : Irreducible F)
    (hX : ¬Associated F (X 0)) (h0 : eval 0 F = 0) (hT : ¬IsTangentAt F 0 (X 0))
    (hF' : Irreducible (blowupStrictTransform F)) {A : Finset k}
    (hA : ∀ α, eval ![0, α] (blowupStrictTransform F) = 0 → α ∈ A) :
    (finite_setOf_localSubring_le_integers 0 (span_le_vanishingIdeal h0)
        (isFunctionField_functionField_span_singleton hF)).toFinset.image
        (·.map (blowupFunctionFieldEquiv hF hX)) =
      A.biUnion fun α ↦ placesOverFinset hF' ![0, α] := by
  ext Q'
  simp only [Finset.mem_image, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
    mem_placesOverFinset]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨α, hα, h⟩ := (localSubring_le_integers_iff hF hX h0 hT).1 hQ
    exact ⟨α, hA α hα, hα, h⟩
  · rintro ⟨α, -, hα, h⟩
    refine ⟨Q'.map (blowupFunctionFieldEquiv hF hX).symm,
      (localSubring_le_integers_iff hF hX h0 hT).2 ⟨α, hα, ?_⟩, Place.map_map_symm _ _⟩
    rwa [Place.map_map_symm]

/-- Noether's formula for an irreducible curve `F` through the origin, in `WithTop ℤ`. -/
private theorem map_natCast_eq_of_irreducible {F : MvPolynomial (Fin 2) k} (hF : Irreducible F)
    (h0 : eval 0 F = 0) (hT : ¬IsTangentAt F 0 (X 0)) (G : MvPolynomial (Fin 2) k)
    {A : Finset k} (hA : ∀ α, eval ![0, α] (blowupStrictTransform F) = 0 → α ∈ A) :
    castHom (intersectionNumber 0 F G) =
      castHom (((F.orderAt 0).toNat * (G.orderAt 0).toNat : ℕ) +
        ∑ α ∈ A, intersectionNumber ![0, α] (blowupStrictTransform F)
          (blowupStrictTransform G)) := by
  classical
  have hX := not_associated_X_zero_of_not_isTangentAt hT
  have : (Ideal.span {F}).IsPrime := (Ideal.span_singleton_prime hF.ne_zero).2 hF.prime
  have := isPrime_span_blowupStrictTransform hF hX
  have hF' := irreducible_blowupStrictTransform hF hX
  set e := blowupFunctionFieldEquiv hF hX
  set S := (finite_setOf_localSubring_le_integers 0 (span_le_vanishingIdeal h0)
    (isFunctionField_functionField_span_singleton hF)).toFinset
  have hr : ∑ Q ∈ S, Q.addValuation (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0))) =
      (((F.orderAt 0).toNat : ℕ) : WithTop ℤ) := by
    rw [← map_natCast_intersectionNumber_eq_sum_addValuation hF h0,
      intersectionNumber_X_zero_of_not_isTangentAt hT,
      ← ENat.natCast_toNat (orderAt_eq_top_iff.not.2 hF.ne_zero), ENat.toNat_natCast]
    rfl
  have hdisj : (A : Set k).PairwiseDisjoint fun α ↦ placesOverFinset hF' ![0, α] := by
    intro α _ β _ hne
    refine Finset.disjoint_left.2 fun Q hα hβ ↦ hne ?_
    obtain ⟨_, hQα⟩ := (mem_placesOverFinset hF').1 hα
    obtain ⟨_, hQβ⟩ := (mem_placesOverFinset hF').1 hβ
    simpa using congrFun (AffineSpace.eq_of_localSubring_le_integers
      (isFunctionField_functionField_span_singleton hF') hQα hQβ) 1
  have hinj : Set.InjOn (fun Q : Place k (AffineSpace.functionField (Ideal.span {F})) ↦ Q.map e)
      (S : Set _) := fun Q _ Q' _ h ↦ by
    simpa only [Place.map_symm_map] using congrArg (fun Q' ↦ Place.map e.symm Q') h
  rw [castHom_apply, map_natCast_intersectionNumber_eq_sum_addValuation hF h0, map_add, map_sum]
  simp only [castHom_apply]
  rw [Finset.sum_congr rfl fun α _ ↦
    map_natCast_intersectionNumber_eq_sum_placesOverFinset hF' ![0, α] (blowupStrictTransform G)]
  rw [← Finset.sum_biUnion hdisj, ← image_map_eq_biUnion hF hX h0 hT hF' hA,
    Finset.sum_image hinj]
  rw [Finset.sum_congr rfl fun Q _ ↦ addValuation_algebraMap_mk_eq_nsmul_add hF hX Q G]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, hr, ENat.map_natCast]
  congr 1
  rw [mul_comm, ← smul_eq_mul]
  exact (map_nsmul ((WithTop.addHom (α := ℤ)).comp (Nat.castAddMonoidHom ℤ)) _ _).symm

/-- Noether's formula for an irreducible curve `F`. -/
private theorem eq_of_irreducible {F : MvPolynomial (Fin 2) k} (hF : Irreducible F)
    (hT : ¬IsTangentAt F 0 (X 0)) (G : MvPolynomial (Fin 2) k) {A : Finset k}
    (hA : ∀ α, eval ![0, α] (blowupStrictTransform F) = 0 → α ∈ A) :
    intersectionNumber 0 F G = ((F.orderAt 0).toNat * (G.orderAt 0).toNat : ℕ) +
      ∑ α ∈ A, intersectionNumber ![0, α] (blowupStrictTransform F) (blowupStrictTransform G) := by
  by_cases h0 : eval 0 F = 0
  · exact castHom_injective (map_natCast_eq_of_irreducible hF h0 hT G hA)
  · exact eq_of_eval_ne_zero h0 G A

/-- **Noether's formula for intersection numbers, local form.** Let `k` be algebraically closed,
`F, G ∈ k[X, Y]`, `r = m_0(F)`, `s = m_0(G)`, and suppose that the line `X = 0` is not tangent to
`F` at the origin. Let `F'`, `G'` be the strict transforms of `F`, `G` under the blow-up of the
origin, and `A` a finite set containing every `α` with `F'(0, α) = 0`. Then
`I(0, F ∩ G) = r s + ∑_{α ∈ A} I((0, α), F' ∩ G')`.
The multiplicities are read as natural numbers (`ENat.toNat`). -/
theorem intersectionNumber_eq_mul_add_sum_blowupStrictTransform {F : MvPolynomial (Fin 2) k}
    (hT : ¬IsTangentAt F 0 (X 0)) (G : MvPolynomial (Fin 2) k) {A : Finset k}
    (hA : ∀ α, eval ![0, α] (blowupStrictTransform F) = 0 → α ∈ A) :
    intersectionNumber 0 F G = ((F.orderAt 0).toNat * (G.orderAt 0).toNat : ℕ) +
      ∑ α ∈ A, intersectionNumber ![0, α] (blowupStrictTransform F) (blowupStrictTransform G) := by
  induction F using UniqueFactorizationMonoid.induction_on_prime generalizing A with
  | h₁ => exact (hT (isTangentAt_def.2 ⟨isHomogeneous_X k 0, X_ne_zero 0,
      by simp [leadingFormAt_zero]⟩)).elim
  | h₂ u hu =>
    exact eq_of_eval_ne_zero ((hu.map (eval 0)).ne_zero) G A
  | h₃ a p ha hp ih =>
    have hTp : ¬IsTangentAt p 0 (X 0) := fun h ↦ hT (isTangentAt_def.2
      ⟨h.isHomogeneous, h.ne_zero, by rw [leadingFormAt_mul]; exact h.dvd.mul_right _⟩)
    have hTa : ¬IsTangentAt a 0 (X 0) := fun h ↦ hT (isTangentAt_def.2
      ⟨h.isHomogeneous, h.ne_zero, by rw [leadingFormAt_mul]; exact h.dvd.mul_left _⟩)
    have hAp : ∀ α, eval ![0, α] (blowupStrictTransform p) = 0 → α ∈ A := fun α h ↦
      hA α (by rw [blowupStrictTransform_mul, eval_mul, h, zero_mul])
    have hAa : ∀ α, eval ![0, α] (blowupStrictTransform a) = 0 → α ∈ A := fun α h ↦
      hA α (by rw [blowupStrictTransform_mul, eval_mul, h, mul_zero])
    rw [intersectionNumber_mul_left, eq_of_irreducible hp.irreducible hTp G hAp, ih hTa hAa,
      orderAt_mul, ENat.toNat_add (orderAt_eq_top_iff.not.2 hp.ne_zero)
        (orderAt_eq_top_iff.not.2 ha), blowupStrictTransform_mul]
    simp_rw [intersectionNumber_mul_left]
    rw [Finset.sum_add_distrib]
    push_cast
    ring

/-- **Noether's formula for intersection numbers, local form.** Let `k` be algebraically closed,
`F, G ∈ k[X, Y]` with `G ≠ 0`, and suppose that the line `X = 0` is not tangent to `F` at the
origin (so `F ≠ 0`). Let `F' = X⁻ʳ F(X, XZ)` and `G' = X⁻ˢ G(X, XZ)` be the strict transforms of
`F` and `G`, with `r = m_0(F)` and `s = m_0(G)`. Then
`I(0, F ∩ G) = m_0(F) m_0(G) + ∑_α I((0, α), F' ∩ G')`,
a finite sum: only the `α` with `F'(0, α) = 0`, the roots of `F_r(1, Z)`, contribute. The curves
need not be irreducible nor pass through the origin; if they have a common component through
the origin, both sides are `⊤`. -/
theorem intersectionNumber_eq_mul_add_finsum_blowupStrictTransform {F G : MvPolynomial (Fin 2) k}
    (hG : G ≠ 0) (hT : ¬IsTangentAt F 0 (X 0)) :
    intersectionNumber 0 F G = F.orderAt 0 * G.orderAt 0 +
      ∑ᶠ α, intersectionNumber ![0, α] (blowupStrictTransform F) (blowupStrictTransform G) := by
  have hF := ne_zero_of_not_isTangentAt hT
  obtain ⟨A, hA, -⟩ := exists_finset_eval_zero_blowupStrictTransform hF hT
  rw [finsum_eq_sum_of_support_subset (s := A) _ fun α hα ↦ (hA α).2 ?_,
    intersectionNumber_eq_mul_add_sum_blowupStrictTransform hT G fun α ↦ (hA α).2, Nat.cast_mul,
    ENat.natCast_toNat (orderAt_eq_top_iff.not.2 hF),
    ENat.natCast_toNat (orderAt_eq_top_iff.not.2 hG)]
  by_contra h
  exact hα (intersectionNumber_eq_zero_of_eval_ne_zero_left h)

end PlaneCurves.Affine

end
