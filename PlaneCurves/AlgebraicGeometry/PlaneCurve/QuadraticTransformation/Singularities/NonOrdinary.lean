/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Singularities.Genus

/-!
# Non-ordinary multiple points under a quadratic transformation

The *non-ordinary multiple points* of a plane curve `F` are its multiple points that are not
ordinary; for an irreducible curve over a perfect field they are finitely many, and we write
`N(F)` for their number.

For a curve `F` in excellent position with proper transform `F'`, the non-ordinary multiple points
of `F'` are the images under the quadratic map of those of `F` other than the centre
`[0 : 0 : 1]`, together with the non-ordinary multiple points of `F'` over the centre (Fulton,
§7.4, Step (7)): the fundamental points of `F'` are ordinary. So a quadratic transformation
centred at a non-ordinary multiple point lowers `N(F) + g*(F)` (the proof of Theorem 2 of §7.4),
and one centred at a simple point, at a point off the curve or at an ordinary multiple point
leaves `N(F)` unchanged.

## Main definitions

* `PlaneCurves.Projective.nonOrdinaryMultiplePoints`: the set of non-ordinary multiple points.

## Main results

* `PlaneCurves.Projective.nonOrdinaryMultiplePoints_finite`,
  `nonOrdinaryMultiplePoints_linearSubst`, `ncard_nonOrdinaryMultiplePoints_linearSubst`: its
  API.
* `PlaneCurves.Projective.mem_nonOrdinaryMultiplePoints_mul_iff`,
  `PlaneCurves.Projective.mem_nonOrdinaryMultiplePoints_prod_iff`: the non-ordinary multiple
  points of a product are those of its factors and the common tangents of two factors.
* `PlaneCurves.Projective.IsExcellentPosition.nonOrdinaryMultiplePoints_properTransform`: the
  non-ordinary multiple points of the proper transform.
* `PlaneCurves.Projective.IsExcellentPosition.ncard_add_virtualGenus_properTransform_lt`:
  `N(F') + g*(F') < N(F) + g*(F)` when the centre is a non-ordinary multiple point, and
  `PlaneCurves.Projective.IsExcellentPosition.ncard_add_virtualGenus_properTransform_le`:
  `N(F') + g*(F') ≤ N(F) + g*(F)` wherever the centre is.
* `PlaneCurves.Projective.IsQuadraticTransformAt.ncard_add_virtualGenus_lt` and
  `PlaneCurves.Projective.IsQuadraticTransformAt.ncard_nonOrdinaryMultiplePoints_eq`: the same
  for a quadratic transformation centred at a point.
* `PlaneCurves.Projective.IsQuadraticTransformAt.forall_isOrdinaryMultiplePoint`: a quadratic
  transformation centred at a point of multiplicity at most one or at an ordinary multiple point
  of a curve with only ordinary multiple points gives a curve with only ordinary multiple points.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.4, Step (7), Theorem 2
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F G : MvPolynomial (Fin 3) k} {n : ℕ} {P Q : ℙ k (Fin 3 → k)}

/-! ### The non-ordinary multiple points -/

/-- The set of *non-ordinary multiple points* of a plane curve `F`: the multiple points of `F`
that are not ordinary. -/
def nonOrdinaryMultiplePoints (F : MvPolynomial (Fin 3) k) : Set (ℙ k (Fin 3 → k)) :=
  {P | IsMultiplePoint F P ∧ ¬IsOrdinaryMultiplePoint F P}

theorem nonOrdinaryMultiplePoints_def (F : MvPolynomial (Fin 3) k) :
    nonOrdinaryMultiplePoints F = {P | IsMultiplePoint F P ∧ ¬IsOrdinaryMultiplePoint F P} :=
  (rfl)

@[simp]
theorem mem_nonOrdinaryMultiplePoints_iff :
    P ∈ nonOrdinaryMultiplePoints F ↔ IsMultiplePoint F P ∧ ¬IsOrdinaryMultiplePoint F P :=
  Iff.rfl

theorem nonOrdinaryMultiplePoints_subset (F : MvPolynomial (Fin 3) k) :
    nonOrdinaryMultiplePoints F ⊆ {P | IsMultiplePoint F P} :=
  fun _ hP ↦ (mem_nonOrdinaryMultiplePoints_iff.1 hP).1

/-- A point of multiplicity at most one is not a non-ordinary multiple point. -/
theorem notMem_nonOrdinaryMultiplePoints_of_mult_le_one (hP : mult F P ≤ 1) :
    P ∉ nonOrdinaryMultiplePoints F := fun h ↦
  absurd ((isMultiplePoint_def.1 (mem_nonOrdinaryMultiplePoints_iff.1 h).1).trans hP)
    (by norm_num)

/-- An ordinary multiple point is not a non-ordinary multiple point. -/
theorem IsOrdinaryMultiplePoint.notMem_nonOrdinaryMultiplePoints
    (hP : IsOrdinaryMultiplePoint F P) : P ∉ nonOrdinaryMultiplePoints F := fun h ↦
  (mem_nonOrdinaryMultiplePoints_iff.1 h).2 hP

/-- An irreducible curve over a perfect field has finitely many non-ordinary multiple points. -/
theorem nonOrdinaryMultiplePoints_finite [PerfectField k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) : (nonOrdinaryMultiplePoints F).Finite :=
  (finite_setOf_isMultiplePoint_of_irreducible hF hirr).subset
    (nonOrdinaryMultiplePoints_subset F)

/-- The non-ordinary multiple points do not change when `F` is multiplied by a nonzero scalar. -/
@[simp]
theorem nonOrdinaryMultiplePoints_smul {c : k} (hc : c ≠ 0) (F : MvPolynomial (Fin 3) k) :
    nonOrdinaryMultiplePoints (c • F) = nonOrdinaryMultiplePoints F := by
  ext P
  simp [hc]

/-- The non-ordinary multiple points of `F(MX)` are the preimages of those of `F` under the
change of coordinates `T` of `M`. -/
theorem nonOrdinaryMultiplePoints_linearSubst (hF : F.IsHomogeneous n)
    {M : Matrix (Fin 3) (Fin 3) k} (hM : Function.Injective M.mulVecLin) :
    nonOrdinaryMultiplePoints (linearSubst M F) =
      map M.mulVecLin hM ⁻¹' nonOrdinaryMultiplePoints F := by
  ext Q
  simp only [mem_nonOrdinaryMultiplePoints_iff, Set.mem_preimage, isMultiplePoint_def,
    mult_linearSubst hF hM, isOrdinaryMultiplePoint_linearSubst_iff hF hM]

/-- A change of coordinates does not change the number of non-ordinary multiple points. -/
theorem ncard_nonOrdinaryMultiplePoints_linearSubst (hF : F.IsHomogeneous n)
    {M : Matrix (Fin 3) (Fin 3) k} (hM : Function.Injective M.mulVecLin) :
    (nonOrdinaryMultiplePoints (linearSubst M F)).ncard = (nonOrdinaryMultiplePoints F).ncard := by
  have hbij : Function.Bijective (map M.mulVecLin hM) :=
    bijective_map_mulVecLin ((Matrix.isUnit_iff_isUnit_det M).2
      (Matrix.isUnit_det_of_mulVecLin_injective hM)).unit
  rw [nonOrdinaryMultiplePoints_linearSubst hF hM,
    Set.ncard_preimage_of_injective_subset_range hbij.1 (by simp [hbij.2.range_eq])]

/-- A curve has no non-ordinary multiple points exactly when its multiple points are ordinary. -/
theorem nonOrdinaryMultiplePoints_eq_empty_iff :
    nonOrdinaryMultiplePoints F = ∅ ↔ ∀ Q, IsMultiplePoint F Q → IsOrdinaryMultiplePoint F Q := by
  simp [Set.eq_empty_iff_forall_notMem]

/-- A nonsingular curve has no non-ordinary multiple points. -/
theorem nonOrdinaryMultiplePoints_eq_empty_of_isNonsingular (hF : F.IsHomogeneous n)
    (hns : IsNonsingular F) : nonOrdinaryMultiplePoints F = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun P ↦ notMem_nonOrdinaryMultiplePoints_of_mult_le_one ?_
  by_cases hP : P ∈ zeroLocus {F}
  · exact (isSimplePoint_def.1 ((isNonsingular_iff_forall_isSimplePoint hF).1 hns P hP)).le
  · exact ((mult_eq_zero_iff hF).2 hP).le.trans zero_le_one

/-- A line has no non-ordinary multiple points. -/
example : nonOrdinaryMultiplePoints (X 0 : MvPolynomial (Fin 3) k) = ∅ :=
  nonOrdinaryMultiplePoints_eq_empty_of_isNonsingular (isHomogeneous_X k 0)
    (isNonsingular_def.2 fun v _ _ ↦ ⟨0, by simp [pderiv_X]⟩)

/-- The nodal cubic `Y²Z = X²(X + Z)` has no non-ordinary multiple points when `2 ≠ 0`: its only
multiple point is the node `[0 : 0 : 1]`. -/
example [IsAlgClosed k] (h2 : (2 : k) ≠ 0) :
    nonOrdinaryMultiplePoints (X 1 ^ 2 * X 2 - X 0 ^ 2 * (X 0 + X 2) : MvPolynomial (Fin 3) k) =
      ∅ := by
  have hX (j : Fin 3) : (X j : MvPolynomial (Fin 3) k).IsHomogeneous 1 := isHomogeneous_X k j
  have hN : (X 1 ^ 2 * X 2 - X 0 ^ 2 * (X 0 + X 2) : MvPolynomial (Fin 3) k).IsHomogeneous 3 :=
    (((hX 1).pow 2).mul (hX 2)).sub (((hX 0).pow 2).mul ((hX 0).add (hX 2)))
  have hO := isOrdinaryMultiplePoint_X_sq_mul_X_sub_X_sq_mul_X_add_X h2
  refine nonOrdinaryMultiplePoints_eq_empty_iff.2 fun Q hQ ↦ ?_
  rwa [eq_of_isMultiplePoint_of_degree_three hN irreducible_X_sq_mul_X_sub_X_sq_mul_X_add_X hQ
    ((isOrdinaryMultiplePoint_def.1 hO).1)]

/-- The cuspidal cubic `Y²Z = X³` has exactly one non-ordinary multiple point, the cusp
`[0 : 0 : 1]`. -/
example [IsAlgClosed k] :
    nonOrdinaryMultiplePoints (X 1 ^ 2 * X 2 - X 0 ^ 3 : MvPolynomial (Fin 3) k) =
      {mk k ![0, 0, 1] (by simp)} := by
  have hN : (X 1 ^ 2 * X 2 - X 0 ^ 3 : MvPolynomial (Fin 3) k).IsHomogeneous 3 :=
    ((isHomogeneous_X k 1).pow 2).mul (isHomogeneous_X k 2) |>.sub ((isHomogeneous_X k 0).pow 3)
  have hM := isMultiplePoint_X_sq_mul_X_sub_X_pow_three (k := k)
  ext Q
  rw [mem_nonOrdinaryMultiplePoints_iff, Set.mem_singleton_iff]
  refine ⟨fun hQ ↦ eq_of_isMultiplePoint_of_degree_three hN irreducible_X_sq_mul_X_sub_X_pow_three
    hQ.1 hM, ?_⟩
  rintro rfl
  refine ⟨hM, fun h ↦ ?_⟩
  have hsq := associated_leadingForm_X_sq_mul_X_sub_X_pow_three.squarefree_iff.1
    (isOrdinaryMultiplePoint_def.1 h).2
  exact (prime_X : Prime (X 1 : MvPolynomial (Fin 3) k)).not_isUnit (hsq _ (by rw [sq]))

/-! ### Products -/

/-- **The non-ordinary multiple points of a product.** Over an algebraically closed field, a
point is a non-ordinary multiple point of the product `F G` of a nonzero form `F` and a nonzero
polynomial `G` exactly when it is one of `F` or of `G`, or `F` and `G` have a common tangent
there. -/
theorem mem_nonOrdinaryMultiplePoints_mul_iff [IsAlgClosed k] (hF : F.IsHomogeneous n)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) :
    P ∈ nonOrdinaryMultiplePoints (F * G) ↔ P ∈ nonOrdinaryMultiplePoints F ∨
      P ∈ nonOrdinaryMultiplePoints G ∨ ∃ L, IsTangentAt F P L ∧ IsTangentAt G P L := by
  have two_le {a : ℕ∞} (h : ¬a ≤ 1) : 2 ≤ a := by
    rw [not_le, ← ENat.add_one_le_iff ENat.one_ne_top, one_add_one_eq_two] at h
    exact h
  have hsF := fun h ↦ two_le (mt (squarefree_leadingForm_of_mult_le_one (P := P) hF0) h)
  have hsG := fun h ↦ two_le (mt (squarefree_leadingForm_of_mult_le_one (P := P) hG0) h)
  simp only [mem_nonOrdinaryMultiplePoints_iff, isOrdinaryMultiplePoint_def, isMultiplePoint_def,
    mult_mul, leadingForm_mul, squarefree_mul_iff, isRelPrime_leadingForm_iff hF hF0]
  have hT : (∃ L, IsTangentAt F P L ∧ IsTangentAt G P L) → 2 ≤ mult F P + mult G P := by
    rintro ⟨L, hFL, hGL⟩
    rw [← one_add_one_eq_two]
    exact add_le_add (Order.one_le_iff_pos.2 (mult_pos_iff_eval_rep.2 hFL.eval_rep_eq_zero))
      (Order.one_le_iff_pos.2 (mult_pos_iff_eval_rep.2 hGL.eval_rep_eq_zero))
  have ha : 2 ≤ mult F P → 2 ≤ mult F P + mult G P := fun h ↦ h.trans le_self_add
  have hb : 2 ≤ mult G P → 2 ≤ mult F P + mult G P := fun h ↦ h.trans le_add_self
  clear two_le
  generalize (∃ L, IsTangentAt F P L ∧ IsTangentAt G P L) = T at *
  generalize Squarefree (leadingForm F P) = sF at *
  generalize Squarefree (leadingForm G P) = sG at *
  tauto

/-- **The non-ordinary multiple points of a finite product.** Over an algebraically closed field,
a point is a non-ordinary multiple point of a finite product `∏ a ∈ s, q a` of nonzero forms
exactly when it is one of some `q a`, or two of the factors have a common tangent there. -/
theorem mem_nonOrdinaryMultiplePoints_prod_iff [IsAlgClosed k] {ι : Type*} {s : Finset ι}
    {q : ι → MvPolynomial (Fin 3) k} {d : ι → ℕ} (hq : ∀ a ∈ s, (q a).IsHomogeneous (d a))
    (hq0 : ∀ a ∈ s, q a ≠ 0) :
    P ∈ nonOrdinaryMultiplePoints (∏ a ∈ s, q a) ↔
      (∃ a ∈ s, P ∈ nonOrdinaryMultiplePoints (q a)) ∨
        ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ L, IsTangentAt (q a) P L ∧ IsTangentAt (q b) P L := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    exact iff_of_false (fun h ↦ h.2 (isOrdinaryMultiplePoint_def.2 ⟨h.1, by simp⟩)) (by simp)
  | insert a s has ih =>
    have hqs (b : ι) (hb : b ∈ s) := hq b (Finset.mem_insert_of_mem hb)
    have hq0s (b : ι) (hb : b ∈ s) := hq0 b (Finset.mem_insert_of_mem hb)
    rw [Finset.prod_insert has, mem_nonOrdinaryMultiplePoints_mul_iff
      (hq a (Finset.mem_insert_self a s)) (hq0 a (Finset.mem_insert_self a s))
      (Finset.prod_ne_zero_iff.2 hq0s), ih hqs hq0s]
    simp only [isTangentAt_prod_iff, Finset.exists_mem_insert, ne_eq, not_true_eq_false,
      false_and, false_or]
    constructor
    · rintro (h | (⟨b, hb, h⟩ | ⟨b, hb, c, hc, hbc, h⟩) | ⟨L, hL, b, hb, hbL⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨b, hb, h⟩)
      · exact Or.inr (Or.inr ⟨b, hb, Or.inr ⟨c, hc, hbc, h⟩⟩)
      · exact Or.inr (Or.inl ⟨b, hb, fun h ↦ has (h ▸ hb), L, hL, hbL⟩)
    · rintro ((h | ⟨b, hb, h⟩) | ⟨b, hb, -, L, hL, hbL⟩ |
        ⟨b, hb, ⟨-, L, hbL, hL⟩ | ⟨c, hc, hbc, h⟩⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl ⟨b, hb, h⟩))
      · exact Or.inr (Or.inr ⟨L, hL, b, hb, hbL⟩)
      · exact Or.inr (Or.inr ⟨L, hL, b, hb, hbL⟩)
      · exact Or.inr (Or.inl (Or.inr ⟨b, hb, c, hc, hbc, h⟩))

/-! ### One quadratic transformation -/

namespace IsExcellentPosition

/-- **The non-ordinary multiple points of the proper transform** (Fulton, §7.4, Step (7)). For a
curve `F` in excellent position with proper transform `F'`, the non-ordinary multiple points of
`F'` are the images under the quadratic map of those of `F` other than `[0 : 0 : 1]`, and those
of `F'` over the centre. -/
theorem nonOrdinaryMultiplePoints_properTransform [IsAlgClosed k] (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) :
    nonOrdinaryMultiplePoints (properTransform F) =
      quadraticMap '' (nonOrdinaryMultiplePoints F \ {fundamentalPoint 2}) ∪
        (nonOrdinaryMultiplePoints (properTransform F) ∩ pointsOverCentre F) := by
  ext Q
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_image, Set.mem_sdiff,
    Set.mem_singleton_iff, mem_nonOrdinaryMultiplePoints_iff]
  constructor
  · rintro ⟨hQ, hQo⟩
    rcases (h.isMultiplePoint_properTransform_iff hF).1 hQ with ⟨hQT, hQF⟩ | ⟨i, rfl, -⟩ | ⟨hO, -⟩
    · refine Or.inl ⟨quadraticMap Q, ⟨⟨hQF, fun ho ↦ hQo ?_⟩, fun h2 ↦ ?_⟩,
        quadraticMap_quadraticMap hQT⟩
      · exact (isOrdinaryMultiplePoint_properTransform_iff_of_notMem_fundamentalTriangle hF
          hQT).2 ho
      · exact bijOn_quadraticMap_compl_fundamentalTriangle.mapsTo hQT
          (h2 ▸ fundamentalPoint_mem_fundamentalTriangle 2)
    · exact absurd (h.isOrdinaryMultiplePoint_properTransform_fundamentalPoint hF hQ) hQo
    · exact Or.inr ⟨⟨hQ, hQo⟩, hO⟩
  · rintro (⟨R, ⟨⟨hR, hRo⟩, hR2⟩, rfl⟩ | ⟨hQ, -⟩)
    · have hRT := h.notMem_fundamentalTriangle_of_isMultiplePoint hF hR hR2
      have hQT := bijOn_quadraticMap_compl_fundamentalTriangle.mapsTo hRT
      refine ⟨?_, fun ho ↦ hRo ?_⟩
      · rw [isMultiplePoint_def, mult_properTransform_quadraticMap hF hRT]
        exact isMultiplePoint_def.1 hR
      · rwa [isOrdinaryMultiplePoint_properTransform_iff_of_notMem_fundamentalTriangle hF hQT,
          quadraticMap_quadraticMap hRT] at ho
    · exact hQ

/-- The quadratic map is injective on the non-ordinary multiple points of a curve in excellent
position other than `[0 : 0 : 1]`. -/
theorem injOn_quadraticMap_nonOrdinaryMultiplePoints (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) :
    Set.InjOn quadraticMap (nonOrdinaryMultiplePoints F \ {fundamentalPoint 2}) :=
  bijOn_quadraticMap_compl_fundamentalTriangle.injOn.mono fun _ hR ↦
    h.notMem_fundamentalTriangle_of_isMultiplePoint hF hR.1.1 hR.2

/-- **A quadratic transformation centred at a non-ordinary multiple point.** For an irreducible
curve `F` in excellent position over an algebraically closed field, with `[0 : 0 : 1]` a
non-ordinary multiple point, the proper transform `F'` has
`N(F') + 1 ≤ N(F) + #(non-ordinary multiple points of F' over the centre)`. -/
theorem ncard_nonOrdinaryMultiplePoints_properTransform_le [IsAlgClosed k]
    (h : IsExcellentPosition F) (hF : F.IsHomogeneous n) (hirr : Irreducible F)
    (hP : fundamentalPoint 2 ∈ nonOrdinaryMultiplePoints F) :
    (nonOrdinaryMultiplePoints (properTransform F)).ncard + 1 ≤
      (nonOrdinaryMultiplePoints F).ncard +
        (nonOrdinaryMultiplePoints (properTransform F) ∩ pointsOverCentre F).ncard := by
  have hU := Set.ncard_union_le
    (quadraticMap '' (nonOrdinaryMultiplePoints F \ {fundamentalPoint 2}))
    (nonOrdinaryMultiplePoints (properTransform F) ∩ pointsOverCentre F)
  rw [← h.nonOrdinaryMultiplePoints_properTransform hF,
    (h.injOn_quadraticMap_nonOrdinaryMultiplePoints hF).ncard_image] at hU
  have hD := Set.ncard_sdiff_singleton_add_one hP (nonOrdinaryMultiplePoints_finite hF hirr)
  omega

/-- **A quadratic transformation centred at a simple point, at a point off the curve or at an
ordinary multiple point does not change the number of non-ordinary multiple points.** -/
theorem ncard_nonOrdinaryMultiplePoints_properTransform [IsAlgClosed k]
    (h : IsExcellentPosition F) (hF : F.IsHomogeneous n)
    (hP : mult F (fundamentalPoint 2) ≤ 1 ∨ IsOrdinaryMultiplePoint F (fundamentalPoint 2)) :
    (nonOrdinaryMultiplePoints (properTransform F)).ncard =
      (nonOrdinaryMultiplePoints F).ncard := by
  have hO : nonOrdinaryMultiplePoints (properTransform F) ∩ pointsOverCentre F = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun Q hQ ↦ notMem_nonOrdinaryMultiplePoints_of_mult_le_one
      (isSimplePoint_def.1 (h.isSimplePoint_of_mem_pointsOverCentre hF hP hQ.2)).le hQ.1
  have h2 : fundamentalPoint 2 ∉ nonOrdinaryMultiplePoints F :=
    hP.elim notMem_nonOrdinaryMultiplePoints_of_mult_le_one
      IsOrdinaryMultiplePoint.notMem_nonOrdinaryMultiplePoints
  have hinj := h.injOn_quadraticMap_nonOrdinaryMultiplePoints hF
  rw [Set.sdiff_singleton_eq_self h2] at hinj
  rw [h.nonOrdinaryMultiplePoints_properTransform hF, hO, Set.union_empty,
    Set.sdiff_singleton_eq_self h2, hinj.ncard_image]

/-- The non-ordinary multiple points over the centre are at most the contribution
`∑ᵢ m_{Pᵢ}(F')(m_{Pᵢ}(F') - 1)/2` of the points over the centre to the virtual genus. -/
theorem ncard_nonOrdinaryMultiplePoints_inter_pointsOverCentre_le [IsAlgClosed k]
    (h : IsExcellentPosition F) (hF : F.IsHomogeneous n) :
    ((nonOrdinaryMultiplePoints (properTransform F) ∩ pointsOverCentre F).ncard : ℤ) ≤
      ∑ᶠ Q ∈ pointsOverCentre F, ((mult (properTransform F) Q).toNat.choose 2 : ℤ) := by
  have hF0 : properTransform F ≠ 0 := (properTransform_eq_zero_iff hF).not.2 h.ne_zero
  have hO := h.pointsOverCentre_finite hF
  have hA := hO.subset (Set.inter_subset_right (s := nonOrdinaryMultiplePoints (properTransform F)))
  rw [Set.ncard_eq_toFinset_card _ hA, finsum_mem_eq_finite_toFinset_sum _ hO,
    Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  refine (Finset.sum_le_sum fun Q hQ ↦ ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (by simp)
      fun _ _ _ ↦ Nat.cast_nonneg _)
  have hQ' := (choose_two_toNat_mult_ne_zero_iff hF0 Q).2
    (mem_nonOrdinaryMultiplePoints_iff.1 (hA.mem_toFinset.1 hQ).1).1
  have := Nat.cast_nonneg (α := ℤ) ((mult (properTransform F) Q).toNat.choose 2)
  omega

/-- **A quadratic transformation centred at a non-ordinary multiple point lowers `N + g*`**
(Fulton, §7.4, proof of Theorem 2). For an irreducible curve `F` in excellent position over an
algebraically closed field, with `[0 : 0 : 1]` a non-ordinary multiple point, the proper transform
`F'` has `N(F') + g*(F') < N(F) + g*(F)`, `N` counting the non-ordinary multiple points. -/
theorem ncard_add_virtualGenus_properTransform_lt [IsAlgClosed k] (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) (hirr : Irreducible F)
    (hP : fundamentalPoint 2 ∈ nonOrdinaryMultiplePoints F) :
    ((nonOrdinaryMultiplePoints (properTransform F)).ncard : ℤ) +
        Projective.virtualGenus (properTransform F) <
      (nonOrdinaryMultiplePoints F).ncard + Projective.virtualGenus F := by
  have h1 := h.ncard_nonOrdinaryMultiplePoints_properTransform_le hF hirr hP
  have h2 := h.ncard_nonOrdinaryMultiplePoints_inter_pointsOverCentre_le hF
  rw [h.virtualGenus_properTransform hF hirr]
  omega

/-- **A quadratic transformation does not raise `N + g*`.** For an irreducible curve `F` in
excellent position over an algebraically closed field, the proper transform `F'` has
`N(F') + g*(F') ≤ N(F) + g*(F)`, `N` counting the non-ordinary multiple points, wherever the
centre `[0 : 0 : 1]` is. -/
theorem ncard_add_virtualGenus_properTransform_le [IsAlgClosed k] (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) (hirr : Irreducible F) :
    ((nonOrdinaryMultiplePoints (properTransform F)).ncard : ℤ) +
        Projective.virtualGenus (properTransform F) ≤
      (nonOrdinaryMultiplePoints F).ncard + Projective.virtualGenus F := by
  by_cases hP : fundamentalPoint 2 ∈ nonOrdinaryMultiplePoints F
  · exact (h.ncard_add_virtualGenus_properTransform_lt hF hirr hP).le
  have hP' : mult F (fundamentalPoint 2) ≤ 1 ∨ IsOrdinaryMultiplePoint F (fundamentalPoint 2) := by
    by_cases h2 : IsMultiplePoint F (fundamentalPoint 2)
    · exact Or.inr (by simpa [h2] using hP)
    · exact Or.inl (Order.le_of_lt_add_one (not_le.1 (isMultiplePoint_def.not.1 h2)))
  have h0 : 0 ≤ ∑ᶠ Q ∈ pointsOverCentre F, ((mult (properTransform F) Q).toNat.choose 2 : ℤ) :=
    finsum_nonneg fun _ ↦ finsum_nonneg fun _ ↦ Nat.cast_nonneg _
  rw [h.ncard_nonOrdinaryMultiplePoints_properTransform hF hP', h.virtualGenus_properTransform hF
    hirr]
  omega

end IsExcellentPosition

/-- If an irreducible curve `G` over a perfect field has at most as many non-ordinary multiple
points as a curve `F` whose multiple points are all ordinary, then the multiple points of `G` are
all ordinary. -/
theorem forall_isOrdinaryMultiplePoint_of_ncard_le [PerfectField k] {m : ℕ}
    (hG : G.IsHomogeneous m) (hirrG : Irreducible G)
    (hN : (nonOrdinaryMultiplePoints G).ncard ≤ (nonOrdinaryMultiplePoints F).ncard)
    (hord : ∀ Q, IsMultiplePoint F Q → IsOrdinaryMultiplePoint F Q) :
    ∀ Q, IsMultiplePoint G Q → IsOrdinaryMultiplePoint G Q := by
  rw [nonOrdinaryMultiplePoints_eq_empty_iff.2 hord, Set.ncard_empty, Nat.le_zero,
    Set.ncard_eq_zero (nonOrdinaryMultiplePoints_finite hG hirrG)] at hN
  exact nonOrdinaryMultiplePoints_eq_empty_iff.1 hN

namespace IsQuadraticTransformAt

/-- **A quadratic transformation centred at a non-ordinary multiple point lowers `N + g*`**
(Fulton, §7.4, proof of Theorem 2). If `G` is a quadratic transformation of an irreducible curve
`F` centred at a non-ordinary multiple point `P`, over an algebraically closed field, then
`N(G) + g*(G) < N(F) + g*(F)`, `N` counting the non-ordinary multiple points. -/
theorem ncard_add_virtualGenus_lt [IsAlgClosed k] (h : IsQuadraticTransformAt F P G)
    (hF : F.IsHomogeneous n) (hirr : Irreducible F) (hP : P ∈ nonOrdinaryMultiplePoints F) :
    ((nonOrdinaryMultiplePoints G).ncard : ℤ) + Projective.virtualGenus G <
      (nonOrdinaryMultiplePoints F).ncard + Projective.virtualGenus F := by
  obtain ⟨M, hM, hMP, hE, rfl⟩ := isQuadraticTransformAt_def.1 h
  have hP' : fundamentalPoint 2 ∈ nonOrdinaryMultiplePoints (linearSubst M F) := by
    rwa [nonOrdinaryMultiplePoints_linearSubst hF hM, Set.mem_preimage, hMP]
  have := hE.ncard_add_virtualGenus_properTransform_lt (hF.linearSubst M)
    ((irreducible_linearSubst_iff (Matrix.isUnit_det_of_mulVecLin_injective hM)).2 hirr) hP'
  rwa [ncard_nonOrdinaryMultiplePoints_linearSubst hF hM, virtualGenus_linearSubst hF hM] at this

/-- **A quadratic transformation centred at a simple point, at a point off the curve or at an
ordinary multiple point does not change the number of non-ordinary multiple points.** If `G` is a
quadratic transformation of `F` centred at `P`, over an algebraically closed field, and
`m_P(F) ≤ 1` or `P` is an ordinary multiple point of `F`, then `N(G) = N(F)`. -/
theorem ncard_nonOrdinaryMultiplePoints_eq [IsAlgClosed k] (h : IsQuadraticTransformAt F P G)
    (hF : F.IsHomogeneous n) (hP : mult F P ≤ 1 ∨ IsOrdinaryMultiplePoint F P) :
    (nonOrdinaryMultiplePoints G).ncard = (nonOrdinaryMultiplePoints F).ncard := by
  obtain ⟨M, hM, hMP, hE, rfl⟩ := isQuadraticTransformAt_def.1 h
  have hP' : mult (linearSubst M F) (fundamentalPoint 2) ≤ 1 ∨
      IsOrdinaryMultiplePoint (linearSubst M F) (fundamentalPoint 2) := by
    rwa [mult_linearSubst hF hM, isOrdinaryMultiplePoint_linearSubst_iff hF hM, hMP]
  rw [hE.ncard_nonOrdinaryMultiplePoints_properTransform (hF.linearSubst M) hP',
    ncard_nonOrdinaryMultiplePoints_linearSubst hF hM]

/-- **A quadratic transformation centred at a simple point, at a point off the curve or at an
ordinary multiple point keeps the multiple points ordinary.** If `G` is an irreducible quadratic
transformation of `F` centred at `P`, over an algebraically closed field, the multiple points of
`F` are all ordinary, and `m_P(F) ≤ 1` or `P` is an ordinary multiple point of `F`, then the
multiple points of `G` are all ordinary. -/
theorem forall_isOrdinaryMultiplePoint [IsAlgClosed k] (h : IsQuadraticTransformAt F P G)
    (hF : F.IsHomogeneous n) {m : ℕ} (hG : G.IsHomogeneous m) (hirrG : Irreducible G)
    (hord : ∀ Q, IsMultiplePoint F Q → IsOrdinaryMultiplePoint F Q)
    (hP : mult F P ≤ 1 ∨ IsOrdinaryMultiplePoint F P) :
    ∀ Q, IsMultiplePoint G Q → IsOrdinaryMultiplePoint G Q :=
  forall_isOrdinaryMultiplePoint_of_ncard_le hG hirrG
    (h.ncard_nonOrdinaryMultiplePoints_eq hF hP).le hord

end IsQuadraticTransformAt

end PlaneCurves.Projective

end
