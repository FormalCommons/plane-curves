/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Cubic.NormalForm
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.MultiplePoints
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Singularities.Chart

/-!
# The virtual genus and the singularities of a quadratic transformation

The *virtual genus* of a plane curve `F` of degree `n` is
`g*(F) = (n - 1)(n - 2)/2 - ∑_P m_P(F)(m_P(F) - 1)/2`, the sum running over the finitely many
multiple points of `F`. By Theorem 2 of §5.4 (**5-bound**) it is nonnegative for irreducible `F`
over an algebraically closed field.

For a curve `C = V(F)` in excellent position with proper transform `C' = V(F')`, the multiple
points of `C'` are the images of the multiple points of `C` off the fundamental triangle, the
fundamental points, and the points `P₁, …, Pₛ` over the centre `[0 : 0 : 1]` (Fulton, §7.4, Step
(7)), and the virtual genus drops by the contribution of the points over the centre:
`g*(C') = g*(C) - ∑ᵢ m_{Pᵢ}(C')(m_{Pᵢ}(C') - 1)/2` (Step (8)). A quadratic transformation
centred at a simple point, at a point off the curve or at an ordinary multiple point leaves `g*`
unchanged (Problem 7.14 (a)).

## Main definitions

* `PlaneCurves.Projective.virtualGenus`: the virtual genus `g*(F)`, an integer.

## Main results

* `PlaneCurves.Projective.two_mul_virtualGenus`, `virtualGenus_smul`,
  `virtualGenus_linearSubst`, `virtualGenus_nonneg`, `virtualGenus_eq_of_isNonsingular`: its
  API.
* `PlaneCurves.Projective.IsExcellentPosition.isMultiplePoint_properTransform_iff`: the multiple
  points of the proper transform of a curve in excellent position.
* `PlaneCurves.Projective.IsExcellentPosition.virtualGenus_properTransform`: Step (8).
* `PlaneCurves.Projective.IsQuadraticTransformAt.virtualGenus` and
  `PlaneCurves.Projective.IsQuadraticTransformAt.virtualGenus_eq`: the same for a quadratic
  transformation centred at a point, and Problem 7.14 (a).
* `PlaneCurves.Projective.quadraticTransform_centre_singularities`: the quadratic transformation
  centred at a point and its new singularities, collected.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.4, Steps (5)–(8), Lemma 1, Problem 7.14 (a);
  Appendix A
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F G : MvPolynomial (Fin 3) k} {n : ℕ} {P : ℙ k (Fin 3 → k)}

/-! ### The virtual genus -/

/-- The *virtual genus* `g*(F) = (n - 1)(n - 2)/2 - ∑_P m_P(F)(m_P(F) - 1)/2` of a plane curve
`F` of degree `n ≥ 1`, the sum running over all points of `ℙ²` (Fulton, §7.4, Step (8)). Only the
multiple points contribute; for an irreducible curve over a perfect field they are finitely many.
When they are infinitely many, that is when `F` has a multiple component, the `finsum` is `0` and
the value is meaningless. -/
noncomputable def virtualGenus (F : MvPolynomial (Fin 3) k) : ℤ :=
  ((F.totalDegree - 1).choose 2 : ℤ) - ∑ᶠ P, ((mult F P).toNat.choose 2 : ℤ)

theorem virtualGenus_def (F : MvPolynomial (Fin 3) k) :
    virtualGenus F = ((F.totalDegree - 1).choose 2 : ℤ) - ∑ᶠ P, ((mult F P).toNat.choose 2 : ℤ) :=
  (rfl)

/-- `2 * m.choose 2 = m (m - 1)` in `ℤ`. -/
private theorem two_mul_choose_two (m : ℕ) : 2 * (m.choose 2 : ℤ) = m * (m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
    push_cast
    linear_combination ih

/-- The term `m_P(F)(m_P(F) - 1)/2` of the virtual genus is nonzero exactly at the multiple
points of `F ≠ 0`. -/
theorem choose_two_toNat_mult_ne_zero_iff (hF0 : F ≠ 0) (P : ℙ k (Fin 3 → k)) :
    ((mult F P).toNat.choose 2 : ℤ) ≠ 0 ↔ IsMultiplePoint F P := by
  rw [Nat.cast_ne_zero, Ne, Nat.choose_eq_zero_iff, not_lt, isMultiplePoint_def,
    ← natCast_toNat_mult hF0]
  exact_mod_cast Iff.rfl

/-- The support of the terms of the virtual genus is the set of multiple points. -/
theorem support_choose_two_toNat_mult (hF0 : F ≠ 0) :
    Function.support (fun P ↦ ((mult F P).toNat.choose 2 : ℤ)) = {P | IsMultiplePoint F P} :=
  Set.ext fun P ↦ choose_two_toNat_mult_ne_zero_iff hF0 P

/-- The term `m_P(F)(m_P(F) - 1)/2` vanishes at a point of multiplicity at most one. -/
theorem choose_two_toNat_mult_eq_zero (hP : mult F P ≤ 1) :
    ((mult F P).toNat.choose 2 : ℤ) = 0 := by
  have : (mult F P).toNat ≤ 1 := ENat.toNat_le_of_le_natCast (by exact_mod_cast hP)
  rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

/-- **The virtual genus, without halves**: `2 g*(F) = (n - 1)(n - 2) - ∑_P m_P(F)(m_P(F) - 1)` for
a nonzero form `F` of degree `n ≥ 1`. -/
theorem two_mul_virtualGenus (hF : F.IsHomogeneous n) (hF0 : F ≠ 0) (hn : n ≠ 0) :
    2 * virtualGenus F = ((n : ℤ) - 1) * ((n : ℤ) - 2) -
      ∑ᶠ P, ((mult F P).toNat : ℤ) * ((mult F P).toNat - 1) := by
  rw [virtualGenus_def, hF.totalDegree hF0, mul_sub, mul_finsum, two_mul_choose_two,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hn)]
  simp_rw [two_mul_choose_two]
  ring

/-- The virtual genus does not change when `F` is multiplied by a nonzero scalar. -/
@[simp]
theorem virtualGenus_smul {c : k} (hc : c ≠ 0) (F : MvPolynomial (Fin 3) k) :
    virtualGenus (c • F) = virtualGenus F := by
  by_cases hF0 : F = 0
  · rw [hF0, smul_zero]
  have hdeg : (c • F).totalDegree = F.totalDegree := by
    rw [smul_eq_C_mul, totalDegree_mul_of_isDomain (C_ne_zero.2 hc) hF0, totalDegree_C, zero_add]
  simp only [virtualGenus_def, mult_smul hc, hdeg]

/-- **The virtual genus is invariant under a change of coordinates**: `g*(F(MX)) = g*(F)` for a
form `F` and an invertible matrix `M`. -/
theorem virtualGenus_linearSubst (hF : F.IsHomogeneous n) {M : Matrix (Fin 3) (Fin 3) k}
    (hM : Function.Injective M.mulVecLin) : virtualGenus (linearSubst M F) = virtualGenus F := by
  have hdet := Matrix.isUnit_det_of_mulVecLin_injective hM
  have hbij : Function.Bijective (map M.mulVecLin hM) :=
    bijective_map_mulVecLin ((Matrix.isUnit_iff_isUnit_det M).2 hdet).unit
  simp only [virtualGenus_def, totalDegree_linearSubst hdet, mult_linearSubst hF hM]
  exact congrArg (_ - ·)
    (finsum_comp_equiv (Equiv.ofBijective _ hbij) (f := fun P ↦ ((mult F P).toNat.choose 2 : ℤ)))

/-- **The virtual genus of an irreducible curve is nonnegative** (Theorem 2 of §5.4). -/
theorem virtualGenus_nonneg [IsAlgClosed k] (hF : F.IsHomogeneous n) (hirr : Irreducible F) :
    0 ≤ virtualGenus F := by
  have hF0 := hirr.ne_zero
  have hfin : (Function.support fun P ↦ ((mult F P).toNat.choose 2 : ℕ)).Finite := by
    refine (finite_setOf_isMultiplePoint_of_irreducible hF hirr).subset fun P hP ↦ ?_
    exact (choose_two_toNat_mult_ne_zero_iff hF0 P).1 (by exact_mod_cast hP)
  have h := finsum_toNat_mult_mul_sub_one_div_two_le hF hirr
  simp_rw [← Nat.choose_two_right] at h
  rw [show (n - 1) * (n - 2) / 2 = (n - 1).choose 2 by
    rw [Nat.choose_two_right, show n - 1 - 1 = n - 2 by omega]] at h
  have hcast := (Nat.castAddMonoidHom ℤ).map_finsum hfin
  simp only [Nat.coe_castAddMonoidHom] at hcast
  rw [virtualGenus_def, hF.totalDegree hF0, sub_nonneg, ← hcast]
  exact_mod_cast h

/-- The virtual genus of a nonsingular curve of degree `n` is `(n - 1)(n - 2)/2`. -/
theorem virtualGenus_eq_of_isNonsingular (hF : F.IsHomogeneous n) (hF0 : F ≠ 0)
    (hns : IsNonsingular F) : virtualGenus F = ((n - 1).choose 2 : ℤ) := by
  rw [virtualGenus_def, hF.totalDegree hF0, sub_eq_self]
  refine finsum_eq_zero_of_forall_eq_zero fun P ↦ choose_two_toNat_mult_eq_zero ?_
  by_cases hP : P ∈ zeroLocus {F}
  · exact (isSimplePoint_def.1 ((isNonsingular_iff_forall_isSimplePoint hF).1 hns P hP)).le
  · exact ((mult_eq_zero_iff hF).2 hP).le.trans zero_le_one

/-- The virtual genus is at most `(n - 1)(n - 2)/2` minus the contribution of any one point, for an
irreducible curve of degree `n` over an algebraically closed field. -/
theorem virtualGenus_le_sub_choose_two [IsAlgClosed k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) (P : ℙ k (Fin 3 → k)) :
    virtualGenus F ≤ ((n - 1).choose 2 : ℤ) - ((mult F P).toNat.choose 2 : ℤ) := by
  rw [virtualGenus_def, hF.totalDegree hirr.ne_zero]
  refine sub_le_sub_left (single_le_finsum P ?_ fun _ ↦ Nat.cast_nonneg _) _
  rw [Function.HasFiniteSupport, support_choose_two_toNat_mult hirr.ne_zero]
  exact finite_setOf_isMultiplePoint_of_irreducible hF hirr

/-- An irreducible cubic with a multiple point has virtual genus `0`. -/
theorem virtualGenus_eq_zero_of_isMultiplePoint [IsAlgClosed k] (hF : F.IsHomogeneous 3)
    (hirr : Irreducible F) {P : ℙ k (Fin 3 → k)} (hP : IsMultiplePoint F P) :
    virtualGenus F = 0 := by
  have h2 : 2 ≤ (mult F P).toNat := by
    have := isMultiplePoint_def.1 hP
    rw [← natCast_toNat_mult hirr.ne_zero] at this
    exact_mod_cast this
  have hle := virtualGenus_le_sub_choose_two hF hirr P
  have h1 : 1 ≤ (mult F P).toNat.choose 2 :=
    Nat.one_le_iff_ne_zero.2 (Nat.choose_eq_zero_iff.not.2 (by omega))
  have : ((3 - 1).choose 2 : ℤ) = 1 := by decide
  have := virtualGenus_nonneg hF hirr
  push_cast at *
  omega

/-- A line has virtual genus `0`. -/
example : virtualGenus (X 0 : MvPolynomial (Fin 3) k) = 0 := by
  have hns : IsNonsingular (X 0 : MvPolynomial (Fin 3) k) :=
    isNonsingular_def.2 fun v _ _ ↦ ⟨0, by simp [pderiv_X]⟩
  rw [virtualGenus_eq_of_isNonsingular (isHomogeneous_X k 0) (X_ne_zero 0) hns]
  rfl

/-- The conic `XY = Z²` is nonsingular, so it has virtual genus `0`. -/
example : virtualGenus (X 0 * X 1 - X 2 ^ 2 : MvPolynomial (Fin 3) k) = 0 := by
  have hns : IsNonsingular (X 0 * X 1 - X 2 ^ 2 : MvPolynomial (Fin 3) k) := by
    refine isNonsingular_def.2 fun v hv h0 ↦ ?_
    by_cases h1 : v 1 = 0
    · by_cases h00 : v 0 = 0
      · refine absurd (funext fun i ↦ ?_) hv
        have h2 : v 2 = 0 := by simpa [h1] using h0
        fin_cases i <;> simp [h00, h1, h2]
      · exact ⟨1, by simpa [pderiv_X] using h00⟩
    · exact ⟨0, by simpa [pderiv_X] using h1⟩
  have hF : (X 0 * X 1 - X 2 ^ 2 : MvPolynomial (Fin 3) k).IsHomogeneous 2 :=
    ((isHomogeneous_X k 0).mul (isHomogeneous_X k 1)).sub
      (by simpa using (isHomogeneous_X k 2).pow 2)
  have hF0 : (X 0 * X 1 - X 2 ^ 2 : MvPolynomial (Fin 3) k) ≠ 0 := fun h ↦ by
    simpa using congrArg (eval ![1, 1, 0]) h
  rw [virtualGenus_eq_of_isNonsingular hF hF0 hns]
  rfl

/-- The cuspidal cubic `Y²Z = X³` has virtual genus `0`. -/
example [IsAlgClosed k] : virtualGenus (X 1 ^ 2 * X 2 - X 0 ^ 3 : MvPolynomial (Fin 3) k) = 0 :=
  virtualGenus_eq_zero_of_isMultiplePoint
    (((isHomogeneous_X k 1).pow 2).mul (isHomogeneous_X k 2) |>.sub ((isHomogeneous_X k 0).pow 3))
    irreducible_X_sq_mul_X_sub_X_pow_three isMultiplePoint_X_sq_mul_X_sub_X_pow_three

/-! ### The multiple points of the proper transform -/

namespace IsExcellentPosition

variable {Q : ℙ k (Fin 3 → k)}

/-- **The multiple points of the proper transform** (Fulton, §7.4, Step (7)). For a curve in
excellent position with proper transform `F'`, a multiple point of `F'` is either off the
fundamental triangle, the image under the quadratic map of a multiple point of `F`, or a
fundamental point, or a point over the centre. Their multiplicities are
`mult_properTransform_of_notMem_fundamentalTriangle`, `mult_properTransform_fundamentalPoint_two`,
`mult_properTransform_fundamentalPoint` and `mult_le_intersectionNumber_of_mem_pointsOverCentre`.
-/
theorem isMultiplePoint_properTransform_iff (h : IsExcellentPosition F) (hF : F.IsHomogeneous n) :
    IsMultiplePoint (properTransform F) Q ↔
      (Q ∉ fundamentalTriangle ∧ IsMultiplePoint F (quadraticMap Q)) ∨
        (∃ i, Q = fundamentalPoint i ∧ IsMultiplePoint (properTransform F) Q) ∨
          (Q ∈ pointsOverCentre F ∧ IsMultiplePoint (properTransform F) Q) := by
  refine ⟨fun hQ ↦ ?_, ?_⟩
  · by_cases hQT : Q ∈ fundamentalTriangle
    · have hQF : Q ∈ zeroLocus {properTransform F} := (mult_pos_iff hF.properTransform).1
        (lt_of_lt_of_le (by norm_num) (isMultiplePoint_def.1 hQ))
      rcases h.eq_fundamentalPoint_or_mem_pointsOverCentre hF hQF hQT with ⟨i, hi⟩ | hO
      exacts [Or.inr (Or.inl ⟨i, hi, hQ⟩), Or.inr (Or.inr ⟨hO, hQ⟩)]
    · refine Or.inl ⟨hQT, ?_⟩
      rw [isMultiplePoint_def] at hQ ⊢
      rwa [← mult_properTransform_of_notMem_fundamentalTriangle hF hQT]
  · rintro (⟨hQT, hQ⟩ | ⟨_, _, hQ⟩ | ⟨_, hQ⟩)
    · rw [isMultiplePoint_def] at hQ ⊢
      rwa [mult_properTransform_of_notMem_fundamentalTriangle hF hQT]
    exacts [hQ, hQ]

/-! ### The virtual genus of the proper transform -/

/-- The multiple points of `F` on the fundamental triangle: only `[0 : 0 : 1]`. -/
private theorem finsum_mem_fundamentalTriangle (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) :
    ∑ᶠ Q ∈ fundamentalTriangle, ((mult F Q).toNat.choose 2 : ℤ) =
      ((mult F (fundamentalPoint 2)).toNat.choose 2 : ℤ) := by
  rw [← finsum_mem_singleton (a := fundamentalPoint 2)
    (f := fun Q ↦ ((mult F Q).toNat.choose 2 : ℤ))]
  refine finsum_mem_inter_support_eq' _ _ _ fun Q hQ ↦ ?_
  rw [support_choose_two_toNat_mult h.ne_zero] at hQ
  refine ⟨fun hQT ↦ ?_, fun hQ2 ↦ ?_⟩
  · by_contra hne
    exact h.notMem_fundamentalTriangle_of_isMultiplePoint hF hQ hne hQT
  · rw [Set.mem_singleton_iff.1 hQ2]
    exact fundamentalPoint_mem_fundamentalTriangle 2

/-- The multiple points of `F'` on the fundamental triangle: the fundamental points and the
points over the centre. -/
private theorem finsum_mem_fundamentalTriangle_properTransform (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) :
    ∑ᶠ Q ∈ fundamentalTriangle, ((mult (properTransform F) Q).toNat.choose 2 : ℤ) =
      (n.choose 2 : ℤ) + 2 * ((n - (mult F (fundamentalPoint 2)).toNat).choose 2 : ℤ) +
        ∑ᶠ Q ∈ pointsOverCentre F, ((mult (properTransform F) Q).toNat.choose 2 : ℤ) := by
  set c := fun Q ↦ ((mult (properTransform F) Q).toNat.choose 2 : ℤ)
  have hO := h.pointsOverCentre_finite hF
  have hnO (i : Fin 3) : fundamentalPoint i ∉ pointsOverCentre F := fun hi ↦ by
    rw [pointsOverCentre_def] at hi
    exact hi.2 i rfl
  have hF0 : properTransform F ≠ 0 := (properTransform_eq_zero_iff hF).not.2 h.ne_zero
  rw [finsum_mem_inter_support_eq' c fundamentalTriangle
    (insert (fundamentalPoint 2) (insert (fundamentalPoint 0)
      (insert (fundamentalPoint 1) (pointsOverCentre F)))) fun Q hQ ↦ ?_]
  · have h01 : fundamentalPoint (k := k) 0 ≠ fundamentalPoint 1 := by
      simp [fundamentalPoint_inj]
    have h02 : fundamentalPoint (k := k) 2 ≠ fundamentalPoint 0 := by
      simp [fundamentalPoint_inj]
    have h12 : fundamentalPoint (k := k) 2 ≠ fundamentalPoint 1 := by
      simp [fundamentalPoint_inj]
    rw [finsum_mem_insert _ (by simp [h02, h12, hnO]) (by simpa using hO),
      finsum_mem_insert _ (by simp [h01, hnO]) (by simpa using hO),
      finsum_mem_insert _ (hnO 1) hO]
    simp only [c, h.mult_properTransform_fundamentalPoint_two hF,
      h.mult_properTransform_fundamentalPoint hF (i := 0) (by decide),
      h.mult_properTransform_fundamentalPoint hF (i := 1) (by decide), ENat.toNat_natCast]
    ring
  · rw [support_choose_two_toNat_mult hF0] at hQ
    simp only [Set.mem_insert_iff]
    refine ⟨fun hQT ↦ ?_, ?_⟩
    · have hQF : Q ∈ zeroLocus {properTransform F} := (mult_pos_iff hF.properTransform).1
        (lt_of_lt_of_le (by norm_num) (isMultiplePoint_def.1 hQ))
      rcases h.eq_fundamentalPoint_or_mem_pointsOverCentre hF hQF hQT with ⟨i, rfl⟩ | hO
      · fin_cases i <;> simp
      · exact Or.inr (Or.inr (Or.inr hO))
    · rintro (rfl | rfl | rfl | hO)
      iterate 3 exact fundamentalPoint_mem_fundamentalTriangle _
      exact pointsOverCentre_subset_fundamentalTriangle hO

/-- **The virtual genus of the proper transform** (Fulton, §7.4, Step (8)). For an irreducible
curve `F` in excellent position over an algebraically closed field, with proper transform `F'`,
`g*(F') = g*(F) - ∑ᵢ m_{Pᵢ}(F')(m_{Pᵢ}(F') - 1)/2`, the sum running over the points `Pᵢ` over the
centre. -/
theorem virtualGenus_properTransform [IsAlgClosed k] (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) (hirr : Irreducible F) :
    virtualGenus (properTransform F) = virtualGenus F -
      ∑ᶠ Q ∈ pointsOverCentre F, ((mult (properTransform F) Q).toNat.choose 2 : ℤ) := by
  set r := (mult F (fundamentalPoint 2)).toNat with hr
  have hrn : r ≤ n := ENat.toNat_le_of_le_natCast (mult_le_degree hF h.ne_zero _)
  have hn : n ≠ 0 := hF.degree_ne_zero_of_irreducible hirr
  have hF' := h.isHomogeneous_properTransform hF
  have hirr' := irreducible_properTransform hF hirr h.not_X_dvd
  have hfin := finite_setOf_isMultiplePoint_of_irreducible hF hirr
  have hfin' := finite_setOf_isMultiplePoint_of_irreducible hF' hirr'
  rw [← support_choose_two_toNat_mult h.ne_zero] at hfin
  rw [← support_choose_two_toNat_mult hirr'.ne_zero] at hfin'
  rw [virtualGenus_def, virtualGenus_def, hF.totalDegree h.ne_zero,
    hF'.totalDegree hirr'.ne_zero,
    ← finsum_mem_univ fun Q ↦ ((mult F Q).toNat.choose 2 : ℤ),
    ← finsum_mem_univ fun Q ↦ ((mult (properTransform F) Q).toNat.choose 2 : ℤ),
    ← finsum_mem_add_sdiff' (Set.subset_univ fundamentalTriangle) (by simpa using hfin'),
    ← finsum_mem_add_sdiff' (Set.subset_univ fundamentalTriangle) (by simpa using hfin),
    ← Set.compl_eq_univ_sdiff, h.finsum_mem_fundamentalTriangle hF,
    h.finsum_mem_fundamentalTriangle_properTransform hF]
  have hU := finsum_mem_eq_of_bijOn quadraticMap bijOn_quadraticMap_compl_fundamentalTriangle
    (f := fun Q ↦ ((mult F Q).toNat.choose 2 : ℤ))
    (g := fun Q ↦ ((mult (properTransform F) Q).toNat.choose 2 : ℤ))
    fun Q hQ ↦ by rw [mult_properTransform_quadraticMap hF hQ]
  rw [← hr]
  have key : 2 * ((2 * n - r - 1).choose 2 : ℤ) - 2 * (n.choose 2 : ℤ) -
      2 * (2 * ((n - r).choose 2 : ℤ)) = 2 * ((n - 1).choose 2 : ℤ) - 2 * (r.choose 2 : ℤ) := by
    rw [mul_left_comm, two_mul_choose_two, two_mul_choose_two, two_mul_choose_two,
      two_mul_choose_two, two_mul_choose_two, Nat.cast_sub (by omega), Nat.cast_sub (by omega),
      Nat.cast_sub hrn, Nat.cast_sub (by omega)]
    push_cast
    ring
  linarith [hU]

end IsExcellentPosition

/-! ### Quadratic transformations centred at a point -/

namespace IsQuadraticTransformAt

/-- **The virtual genus of a quadratic transformation** (Fulton, §7.4, Step (8)). If `G` is a
quadratic transformation of an irreducible curve `F` centred at `P`, over an algebraically closed
field, then `g*(G) = g*(F) - ∑ᵢ m_{Pᵢ}(G)(m_{Pᵢ}(G) - 1)/2`, the sum running over the points `Pᵢ`
of `G` on `V(Z)` that are not fundamental points, the points over the centre. -/
theorem virtualGenus [IsAlgClosed k] (h : IsQuadraticTransformAt F P G) (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) :
    Projective.virtualGenus G = Projective.virtualGenus F -
      ∑ᶠ Q ∈ {Q | Q ∈ zeroLocus {G, X 2} ∧ ∀ i, Q ≠ fundamentalPoint i},
        ((mult G Q).toNat.choose 2 : ℤ) := by
  obtain ⟨M, hM, -, hE, rfl⟩ := isQuadraticTransformAt_def.1 h
  rw [hE.virtualGenus_properTransform (hF.linearSubst M)
    ((irreducible_linearSubst_iff (Matrix.isUnit_det_of_mulVecLin_injective hM)).2 hirr),
    virtualGenus_linearSubst hF hM, pointsOverCentre_def]

/-- **A quadratic transformation centred at an ordinary multiple point, a simple point or a point
off the curve leaves the virtual genus unchanged** (Fulton, §7.4, Problem 7.14 (a)). If `G` is a
quadratic transformation of an irreducible curve `F` of degree `n` centred at `P`, over an
algebraically closed field, and `m_P(F) ≤ 1` or `P` is an ordinary multiple point of `F`, then
`g*(G) = g*(F)`, and `G` has degree `2n - r`, `r = m_P(F)`: `2n`, `2n - 1` or `2n - r`. -/
theorem virtualGenus_eq [IsAlgClosed k] (h : IsQuadraticTransformAt F P G)
    (hF : F.IsHomogeneous n) (hirr : Irreducible F)
    (hP : mult F P ≤ 1 ∨ IsOrdinaryMultiplePoint F P) :
    Projective.virtualGenus G = Projective.virtualGenus F ∧
      G.IsHomogeneous (2 * n - (mult F P).toNat) := by
  refine ⟨?_, h.isHomogeneous hF⟩
  rw [h.virtualGenus hF hirr, sub_eq_self]
  obtain ⟨M, hM, hMP, hE, rfl⟩ := isQuadraticTransformAt_def.1 h
  have hP' : mult (linearSubst M F) (fundamentalPoint 2) ≤ 1 ∨
      IsOrdinaryMultiplePoint (linearSubst M F) (fundamentalPoint 2) := by
    rwa [mult_linearSubst hF hM, isOrdinaryMultiplePoint_linearSubst_iff hF hM, hMP]
  refine finsum_mem_eq_zero_of_forall_eq_zero fun Q hQ ↦ choose_two_toNat_mult_eq_zero ?_
  rw [← pointsOverCentre_def] at hQ
  exact (isSimplePoint_def.1 (hE.isSimplePoint_of_mem_pointsOverCentre (hF.linearSubst M) hP'
    hQ)).le

end IsQuadraticTransformAt

/-! ### The milestone -/

/-- **Quadratic transformation centred at a point and its new singularities** (Fulton, §7.4,
Steps (5)–(8), Lemma 1, Problem 7.14 (a), Appendix A). Let `k` be algebraically closed and `F` an
irreducible form of degree `n`.

1. *Existence.* For every point `P` of `ℙ²` that is not terrible for `F`, on `F` or not, there is
   a projective change of coordinates `T`, given by an invertible matrix `M`, with
   `T([0 : 0 : 1]) = P` and `F^T = F(MX)` in excellent position; its proper transform is a
   quadratic transformation of `F` centred at `P`. In characteristic zero no point is terrible,
   so this holds at every point (the book's Lemma 1).
2. *Singularities.* If `F` is in excellent position, `r = m_{[0:0:1]}(F)` and `F'` is its proper
   transform, then `F'` has degree `2n - r` and its multiple points are
   (a) the images `Q` under the quadratic map of the multiple points of `F` off the fundamental
   triangle, with the same multiplicities, ordinary ones corresponding to ordinary ones;
   (b) the fundamental points, of multiplicities `n`, `n - r`, `n - r`, ordinary when they are
   multiple points;
   (c) the points `Pᵢ` over the centre, with `m_{Pᵢ}(F') ≤ I(Pᵢ, F' ∩ Z)` and
   `∑ᵢ I(Pᵢ, F' ∩ Z) = r`; `F'` meets `V(Y)` and `V(X)` only in fundamental points. Near the
   centre the quadratic transformation is the blow-up: `F'(x, 1, xz) = x^(n - r) g(z, x)`, for
   `g` the strict transform of `F(x, y, 1)` (with the local isomorphisms
   `IsExcellentPosition.localRingEquivPointsOverCentre`).
3. *The virtual genus.* `g*(F') = g*(F) - ∑ᵢ m_{Pᵢ}(F')(m_{Pᵢ}(F') - 1)/2`.
4. A quadratic transformation centred at an ordinary multiple point, at a simple point or at a
   point not on `F` has degree `2n - r`, `2n - 1` or `2n`, and the same virtual genus.

Milestone: *Quadratic transformation centred at a point and its new singularities*. -/
theorem quadraticTransform_centre_singularities [IsAlgClosed k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) :
    (∀ P : ℙ k (Fin 3 → k), ¬ IsTerriblePoint F P.rep →
      ∃ (M : Matrix (Fin 3) (Fin 3) k) (hM : Function.Injective M.mulVecLin),
        map M.mulVecLin hM (fundamentalPoint 2) = P ∧ IsExcellentPosition (linearSubst M F) ∧
          IsQuadraticTransformAt F P (properTransform (linearSubst M F))) ∧
    (CharZero k → ∀ P : ℙ k (Fin 3 → k),
      ∃ (M : Matrix (Fin 3) (Fin 3) k) (hM : Function.Injective M.mulVecLin),
        map M.mulVecLin hM (fundamentalPoint 2) = P ∧ IsExcellentPosition (linearSubst M F)) ∧
    (IsExcellentPosition F →
      (properTransform F).IsHomogeneous (2 * n - (mult F (fundamentalPoint 2)).toNat) ∧
      (∀ Q, IsMultiplePoint (properTransform F) Q ↔
        (Q ∉ fundamentalTriangle ∧ IsMultiplePoint F (quadraticMap Q)) ∨
          (∃ i, Q = fundamentalPoint i ∧ IsMultiplePoint (properTransform F) Q) ∨
            (Q ∈ pointsOverCentre F ∧ IsMultiplePoint (properTransform F) Q)) ∧
      (∀ Q ∉ fundamentalTriangle, mult (properTransform F) Q = mult F (quadraticMap Q) ∧
        (IsOrdinaryMultiplePoint (properTransform F) Q ↔
          IsOrdinaryMultiplePoint F (quadraticMap Q))) ∧
      mult (properTransform F) (fundamentalPoint 2) = n ∧
      (∀ i ≠ 2, mult (properTransform F) (fundamentalPoint i) =
        (n - (mult F (fundamentalPoint 2)).toNat : ℕ)) ∧
      (∀ i, IsMultiplePoint (properTransform F) (fundamentalPoint i) →
        IsOrdinaryMultiplePoint (properTransform F) (fundamentalPoint i)) ∧
      (∀ Q ∈ pointsOverCentre F,
        mult (properTransform F) Q ≤ intersectionNumber Q (properTransform F) (X 2)) ∧
      ∑ᶠ Q ∈ pointsOverCentre F, intersectionNumber Q (properTransform F) (X 2) =
        mult F (fundamentalPoint 2) ∧
      zeroLocus {properTransform F, X 1} ⊆ {fundamentalPoint 0, fundamentalPoint 2} ∧
      zeroLocus {properTransform F, X 0} ⊆ {fundamentalPoint 1, fundamentalPoint 2} ∧
      aeval ![X 0, X 0 * X 1] (dehomogenize 1 (properTransform F)) =
        X 0 ^ (n - (mult F (fundamentalPoint 2)).toNat) *
          rename (Equiv.swap 0 1) (Affine.blowupStrictTransform (dehomogenize 2 F)) ∧
      virtualGenus (properTransform F) = virtualGenus F -
        ∑ᶠ Q ∈ pointsOverCentre F, ((mult (properTransform F) Q).toNat.choose 2 : ℤ)) ∧
    (∀ (P : ℙ k (Fin 3 → k)) (G : MvPolynomial (Fin 3) k), IsQuadraticTransformAt F P G →
      (mult F P ≤ 1 ∨ IsOrdinaryMultiplePoint F P) →
        virtualGenus G = virtualGenus F ∧ G.IsHomogeneous (2 * n - (mult F P).toNat)) := by
  refine ⟨fun P hP ↦ ?_, fun _ P ↦ exists_isExcellentPosition_of_charZero hF hirr P,
    fun h ↦ ⟨h.isHomogeneous_properTransform hF,
      fun Q ↦ h.isMultiplePoint_properTransform_iff hF,
      fun Q hQ ↦ ⟨mult_properTransform_of_notMem_fundamentalTriangle hF hQ,
        isOrdinaryMultiplePoint_properTransform_iff_of_notMem_fundamentalTriangle hF hQ⟩,
      h.mult_properTransform_fundamentalPoint_two hF,
      fun i hi ↦ h.mult_properTransform_fundamentalPoint hF hi,
      fun i ↦ h.isOrdinaryMultiplePoint_properTransform_fundamentalPoint hF,
      fun Q hQ ↦ mult_le_intersectionNumber_of_mem_pointsOverCentre hF hQ,
      h.finsum_intersectionNumber_pointsOverCentre hF,
      h.zeroLocus_properTransform_X_one_subset hF,
      h.zeroLocus_properTransform_X_zero_subset hF,
      h.dehomogenize_properTransform_blowup hF,
      h.virtualGenus_properTransform hF hirr⟩,
    fun P G hG hP ↦ hG.virtualGenus_eq hF hirr hP⟩
  · obtain ⟨M, hM, hTP, hE⟩ := exists_isExcellentPosition hF hirr hP
    exact ⟨M, hM, hTP, hE, isQuadraticTransformAt_def.2 ⟨M, hM, hTP, hE, rfl⟩⟩
end PlaneCurves.Projective

end
