/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.FunctionField
public import PlaneCurves.RingTheory.MvPolynomial.LinearSubst

/-!
# Projective changes of coordinates

An invertible matrix `M` over a field `k` gives the linear change of coordinates
`F ↦ F^T = linearSubst M F` of `R = k[X₀, …, Xₙ]` and the projective change of coordinates
`T = map M.mulVecLin` of `ℙⁿ`, with `F^T(Q) = F(T(Q))`. For a homogeneous ideal `I` with zero
locus `V`, the ideal `I^T` has zero locus `V^T = T⁻¹(V)`. This file shows that `T` induces
isomorphisms of the homogeneous coordinate rings `Γ_h(V) ≅ Γ_h(V^T)`, of the function fields
`k(V) ≅ k(V^T)` and of the local rings `𝒪_P(V) ≅ 𝒪_Q(V^T)` for `T(Q) = P`, all explicit on
fractions, and collects these with the description of `k(V)` and `𝒪_P(V)` from
`PlaneCurves.AlgebraicGeometry.ProjectiveSpace.FunctionField`.

## Main definitions

* `PlaneCurves.ProjectiveSpace.linearSubstIdeal M I`: the homogeneous ideal `I^T`, spanned by
  the `F^T` with `F ∈ I`.
* `PlaneCurves.ProjectiveSpace.coordinateRingLinearSubstEquiv M I`: the isomorphism
  `R ⧸ I ≅ R ⧸ I^T` of `k`-algebras, `[F] ↦ [F^T]`, and its graded versions
  `coordinateRingLinearSubstGradedRingHom M I` and `coordinateRingLinearSubstGradedRingHomSymm M I`.
* `PlaneCurves.ProjectiveSpace.functionField.linearSubstEquiv M I`: the isomorphism
  `k(V) ≅ k(V^T)`, `f / g ↦ f^T / g^T`, for a homogeneous prime `I`.
* `PlaneCurves.ProjectiveSpace.localSubring.linearSubstEquiv M I hQP`: the isomorphism
  `𝒪_P(V) ≅ 𝒪_Q(V^T)` for `T(Q) = P`.

## Main results

* `bijective_map_mulVecLin`: a projective change of coordinates is a bijection of `ℙⁿ`.
* `zeroLocus_linearSubstIdeal`: `V(I^T) = T⁻¹(V(I))`, and
  `vanishingIdeal_preimage_map_mulVecLin`: `I(T⁻¹(X)) = I(X)^T`.
* `isPrime_linearSubstIdeal_iff`, `zeroLocus_vanishingIdeal_preimage_map_mulVecLin_eq_iff`,
  `isPrime_vanishingIdeal_preimage_map_mulVecLin_iff`: `V` is algebraic, resp. a variety, iff
  `V^T` is.
* `coordinateRingLinearSubstEquiv_mem_quotientGrading_iff`: `Γ_h(V) ≅ Γ_h(V^T)` preserves
  degrees.
* `functionField.linearSubstEquiv_mk`: `k(V) ≅ k(V^T)` sends `f / g` to `f^T / g^T`.
* `map_localSubring_linearSubstEquiv`: `k(V) ≅ k(V^T)` carries `𝒪_P(V)` onto `𝒪_Q(V^T)` when
  `T(Q) = P`.
* `functionField_localSubring_and_linearSubstEquiv`: the function field and local rings of a
  projective variety, and their behaviour under projective changes of coordinates.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008]
-/

public section

noncomputable section

open MvPolynomial Projectivization
open scoped LinearAlgebra.Projectivization Matrix

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Matrix.GeneralLinearGroup

/-- An invertible matrix acts injectively on column vectors. -/
theorem injective_mulVecLin {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (M : GL ι K) : Function.Injective (M : Matrix ι ι K).mulVecLin :=
  Matrix.mulVec_injective_iff_isUnit.2 (Units.isUnit M)

end Matrix.GeneralLinearGroup

namespace PlaneCurves.ProjectiveSpace

variable {k : Type*} [Field k] {n : ℕ} (M : GL (Fin (n + 1)) k)

/-! ### Projective changes of coordinates of points -/

/-- The projective change of coordinates `M⁻¹` undoes `M`. -/
@[simp]
theorem map_inv_map_mulVecLin (P : ℙ k (Fin (n + 1) → k)) :
    map (M⁻¹).1.mulVecLin (M⁻¹).injective_mulVecLin
      (map M.1.mulVecLin M.injective_mulVecLin P) = P := by
  induction P using Projectivization.ind with | h v hv =>
  simp only [map_mk, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  congr 1
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

/-- The projective change of coordinates `M` undoes `M⁻¹`. -/
@[simp]
theorem map_map_inv_mulVecLin (P : ℙ k (Fin (n + 1) → k)) :
    map M.1.mulVecLin M.injective_mulVecLin
      (map (M⁻¹).1.mulVecLin (M⁻¹).injective_mulVecLin P) =
      P := by
  simpa using map_inv_map_mulVecLin M⁻¹ P

/-- A projective change of coordinates is a bijection of `ℙⁿ`. -/
theorem bijective_map_mulVecLin :
    Function.Bijective (map M.1.mulVecLin M.injective_mulVecLin) :=
  Function.bijective_iff_has_inverse.2 ⟨_, map_inv_map_mulVecLin M, map_map_inv_mulVecLin M⟩

/-- A form vanishes after the change of coordinates `M` at `Q` iff it vanishes at `T(Q)`, where
`T` is the projective change of coordinates of `M`. -/
theorem eval_rep_linearSubst_eq_zero_iff {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ}
    (hf : f.IsHomogeneous d) (Q : ℙ k (Fin (n + 1) → k)) :
    eval Q.rep (linearSubst M.1 f) = 0 ↔
      eval (map M.1.mulVecLin M.injective_mulVecLin Q).rep f = 0 := by
  have hv : M.1 *ᵥ Q.rep ≠ 0 := fun h ↦
    Q.rep_ne_zero (M.injective_mulVecLin (by simpa using h))
  rw [eval_linearSubst, ← mem_pointIdeal_mk_iff_of_isHomogeneous hf hv,
    ← mem_pointIdeal_iff_of_isHomogeneous hf]
  conv_rhs => rw [← Q.mk_rep, map_mk]
  rfl

/-! ### The ideal of `V^T` -/

variable (I J : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k))

/-- The homogeneous ideal `I^T = (F^T : F ∈ I)` obtained from `I` by the linear change of
coordinates `M`, where `F^T = linearSubst M F`. For `I = I(V)` it is the ideal of
`V^T = T⁻¹(V)` (`vanishingIdeal_preimage_map_mulVecLin`). -/
def linearSubstIdeal : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k) :=
  I.map (linearSubstGradedRingHom M.1)

theorem linearSubstIdeal_toIdeal :
    (linearSubstIdeal M I).toIdeal = I.toIdeal.map (linearSubst M.1) := by
  rw [linearSubstIdeal, HomogeneousIdeal.toIdeal_map, Ideal.map, coe_linearSubstGradedRingHom,
    Ideal.map]

variable {M I} in
/-- A polynomial lies in `I^T` iff the inverse change of coordinates sends it into `I`. -/
theorem mem_linearSubstIdeal_iff {f : MvPolynomial (Fin (n + 1)) k} :
    f ∈ linearSubstIdeal M I ↔ linearSubst (M⁻¹).1 f ∈ I := by
  rw [← HomogeneousIdeal.mem_iff, linearSubstIdeal_toIdeal]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hle : I.toIdeal.map (linearSubst M.1) ≤ I.toIdeal.comap (linearSubst (M⁻¹).1) :=
      Ideal.map_le_iff_le_comap.2 fun g hg ↦ by
        rw [Ideal.mem_comap, Ideal.mem_comap, linearSubst_inv_linearSubst]
        exact hg
    exact hle h
  · have := Ideal.mem_map_of_mem (linearSubst M.1) h
    rwa [linearSubst_linearSubst_inv] at this

variable {M I} in
@[simp]
theorem linearSubst_mem_linearSubstIdeal_iff {f : MvPolynomial (Fin (n + 1)) k} :
    linearSubst M.1 f ∈ linearSubstIdeal M I ↔ f ∈ I := by
  rw [mem_linearSubstIdeal_iff, linearSubst_inv_linearSubst]

/-- The change of coordinates `M⁻¹` undoes `M` on homogeneous ideals. -/
@[simp]
theorem linearSubstIdeal_inv_linearSubstIdeal :
    linearSubstIdeal M⁻¹ (linearSubstIdeal M I) = I := by
  ext f
  rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_iff, mem_linearSubstIdeal_iff, inv_inv,
    linearSubst_mem_linearSubstIdeal_iff]

/-- The change of coordinates `M` undoes `M⁻¹` on homogeneous ideals. -/
@[simp]
theorem linearSubstIdeal_linearSubstIdeal_inv :
    linearSubstIdeal M (linearSubstIdeal M⁻¹ I) = I := by
  simpa using linearSubstIdeal_inv_linearSubstIdeal M⁻¹ I

variable {M I J} in
theorem linearSubstIdeal_le_iff :
    linearSubstIdeal M I ≤ J ↔ I ≤ linearSubstIdeal M⁻¹ J := by
  refine ⟨fun h f hf ↦ ?_, fun h f hf ↦ ?_⟩
  · rw [mem_linearSubstIdeal_iff, inv_inv]
    exact h (linearSubst_mem_linearSubstIdeal_iff.2 hf)
  · rw [← linearSubstIdeal_linearSubstIdeal_inv M J]
    exact (show linearSubstIdeal M I ≤ linearSubstIdeal M (linearSubstIdeal M⁻¹ J) from
      fun g hg ↦ by
        rw [mem_linearSubstIdeal_iff] at hg ⊢
        exact h hg) hf

/-- A homogeneous ideal is prime iff its image under a change of coordinates is. -/
theorem isPrime_linearSubstIdeal_iff :
    (linearSubstIdeal M I).toIdeal.IsPrime ↔ I.toIdeal.IsPrime := by
  have key : ∀ (N : GL (Fin (n + 1)) k)
      (I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)),
      I.toIdeal.IsPrime → (linearSubstIdeal N I).toIdeal.IsPrime := fun N I hI ↦ by
    rw [linearSubstIdeal_toIdeal, ← toAlgHom_linearSubstAlgEquiv]
    exact Ideal.map_isPrime_of_equiv ((linearSubstAlgEquiv N).toRingEquiv)
  exact ⟨fun h ↦ by simpa using key M⁻¹ _ h, key M I⟩

instance [I.toIdeal.IsPrime] : (linearSubstIdeal M I).toIdeal.IsPrime :=
  (isPrime_linearSubstIdeal_iff M I).2 ‹_›

/-- **`V(I^T) = T⁻¹(V(I))`.** The zero locus of `I^T` is the preimage of the zero locus of `I`
under the projective change of coordinates `T` of `M`. -/
theorem zeroLocus_linearSubstIdeal :
    zeroLocus (linearSubstIdeal M I : Set (MvPolynomial (Fin (n + 1)) k)) =
      map M.1.mulVecLin M.injective_mulVecLin ⁻¹'
        zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) := by
  rw [← zeroLocus_linearSubst M.1 M.injective_mulVecLin]
  change zeroLocus ((linearSubstIdeal M I).toIdeal : Set (MvPolynomial (Fin (n + 1)) k)) = _
  rw [linearSubstIdeal_toIdeal, Ideal.map, zeroLocus_span]
  rfl

/-- **`I(T⁻¹(X)) = I(X)^T`.** The ideal of the preimage of `X ⊆ ℙⁿ` under the projective change
of coordinates `T` of `M` is the image of the ideal of `X`. -/
theorem vanishingIdeal_preimage_map_mulVecLin (X : Set (ℙ k (Fin (n + 1) → k))) :
    vanishingIdeal (map M.1.mulVecLin M.injective_mulVecLin ⁻¹' X) =
      linearSubstIdeal M (vanishingIdeal X) := by
  refine le_antisymm ?_ ?_
  · have h := (linearSubstIdeal_le_iff (M := M⁻¹)
      (I := vanishingIdeal (map M.1.mulVecLin M.injective_mulVecLin ⁻¹' X))
      (J := vanishingIdeal X))
    rw [inv_inv] at h
    refine h.1 ?_
    rw [← subset_zeroLocus_iff_le_vanishingIdeal, zeroLocus_linearSubstIdeal]
    intro P hP
    refine subset_zeroLocus_vanishingIdeal _ (show _ ∈ map _ _ ⁻¹' X from ?_)
    rw [Set.mem_preimage, map_map_inv_mulVecLin]
    exact hP
  · rw [← subset_zeroLocus_iff_le_vanishingIdeal, zeroLocus_linearSubstIdeal]
    exact Set.preimage_mono (subset_zeroLocus_vanishingIdeal X)

/-! ### Varieties under a change of coordinates -/

/-- **`V` is algebraic iff `V^T` is.** A set `V ⊆ ℙⁿ` is the zero locus of its ideal iff its
preimage `V^T = T⁻¹(V)` under the projective change of coordinates `T` of `M` is. -/
theorem zeroLocus_vanishingIdeal_preimage_map_mulVecLin_eq_iff (V : Set (ℙ k (Fin (n + 1) → k))) :
    zeroLocus (vanishingIdeal (map M.1.mulVecLin M.injective_mulVecLin ⁻¹' V) :
        Set (MvPolynomial (Fin (n + 1)) k)) = map M.1.mulVecLin M.injective_mulVecLin ⁻¹' V ↔
      zeroLocus (vanishingIdeal V : Set (MvPolynomial (Fin (n + 1)) k)) = V := by
  rw [vanishingIdeal_preimage_map_mulVecLin, zeroLocus_linearSubstIdeal]
  exact (bijective_map_mulVecLin M).2.preimage_injective.eq_iff

/-- **`V` is irreducible iff `V^T` is.** The ideal of `V ⊆ ℙⁿ` is prime iff the ideal of its
preimage `V^T = T⁻¹(V)` under the projective change of coordinates `T` of `M` is. -/
theorem isPrime_vanishingIdeal_preimage_map_mulVecLin_iff (V : Set (ℙ k (Fin (n + 1) → k))) :
    (vanishingIdeal (map M.1.mulVecLin M.injective_mulVecLin ⁻¹' V)).toIdeal.IsPrime ↔
      (vanishingIdeal V).toIdeal.IsPrime := by
  rw [vanishingIdeal_preimage_map_mulVecLin, isPrime_linearSubstIdeal_iff]

/-! ### The homogeneous coordinate ring -/

/-- **`Γ_h(V) ≅ Γ_h(V^T)`.** The change of coordinates `F ↦ F^T` induces an isomorphism of the
homogeneous coordinate rings `R ⧸ I ≅ R ⧸ I^T`; it preserves degrees
(`coordinateRingLinearSubstEquiv_mem_quotientGrading_iff`). -/
def coordinateRingLinearSubstEquiv :
    (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal) ≃ₐ[k]
      MvPolynomial (Fin (n + 1)) k ⧸ (linearSubstIdeal M I).toIdeal :=
  Ideal.quotientEquivAlg I.toIdeal (linearSubstIdeal M I).toIdeal (linearSubstAlgEquiv M)
    (by rw [linearSubstIdeal_toIdeal, Ideal.map, Ideal.map]; congr 2; ext f; simp)

@[simp]
theorem coordinateRingLinearSubstEquiv_mk (f : MvPolynomial (Fin (n + 1)) k) :
    coordinateRingLinearSubstEquiv M I (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (linearSubst M.1 f) := by
  simp [coordinateRingLinearSubstEquiv, Ideal.quotientEquivAlg_mk]

@[simp]
theorem coordinateRingLinearSubstEquiv_symm_mk (f : MvPolynomial (Fin (n + 1)) k) :
    (coordinateRingLinearSubstEquiv M I).symm (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (linearSubst (M⁻¹).1 f) := by
  simp [coordinateRingLinearSubstEquiv, Ideal.quotientEquivAlg_symm, Ideal.quotientEquivAlg_mk]

variable {M I} in
/-- The isomorphism `Γ_h(V) ≅ Γ_h(V^T)` preserves degrees. -/
theorem coordinateRingLinearSubstEquiv_mem_quotientGrading_iff
    {x : MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal} {d : ℕ} :
    coordinateRingLinearSubstEquiv M I x ∈ (linearSubstIdeal M I).quotientGrading d ↔
      x ∈ I.quotientGrading d := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨g, hg, hgx⟩ := (linearSubstIdeal M I).exists_isHomogeneous_mk_eq h
    rw [← (coordinateRingLinearSubstEquiv M I).symm_apply_apply x, ← hgx,
      coordinateRingLinearSubstEquiv_symm_mk]
    exact I.mk_mem_quotientGrading (hg.linearSubst _)
  · obtain ⟨f, hf, rfl⟩ := I.exists_isHomogeneous_mk_eq h
    rw [coordinateRingLinearSubstEquiv_mk]
    exact (linearSubstIdeal M I).mk_mem_quotientGrading (hf.linearSubst _)

/-- The isomorphism `Γ_h(V) ≅ Γ_h(V^T)` as a graded ring hom. -/
def coordinateRingLinearSubstGradedRingHom :
    I.quotientGrading →+*ᵍ (linearSubstIdeal M I).quotientGrading where
  toRingHom := (coordinateRingLinearSubstEquiv M I : _ →+* _)
  map_mem hx := coordinateRingLinearSubstEquiv_mem_quotientGrading_iff.2 hx

@[simp]
theorem coe_coordinateRingLinearSubstGradedRingHom :
    ⇑(coordinateRingLinearSubstGradedRingHom M I) = coordinateRingLinearSubstEquiv M I :=
  (rfl)

/-- The inverse of the isomorphism `Γ_h(V) ≅ Γ_h(V^T)`, as a graded ring hom. -/
def coordinateRingLinearSubstGradedRingHomSymm :
    (linearSubstIdeal M I).quotientGrading →+*ᵍ I.quotientGrading where
  toRingHom := ((coordinateRingLinearSubstEquiv M I).symm : _ →+* _)
  map_mem hx := coordinateRingLinearSubstEquiv_mem_quotientGrading_iff.1 <| by
    change coordinateRingLinearSubstEquiv M I ((coordinateRingLinearSubstEquiv M I).symm _) ∈ _
    rw [AlgEquiv.apply_symm_apply]
    exact hx

@[simp]
theorem coe_coordinateRingLinearSubstGradedRingHomSymm :
    ⇑(coordinateRingLinearSubstGradedRingHomSymm M I) =
      (coordinateRingLinearSubstEquiv M I).symm :=
  (rfl)

/-! ### The function field -/

variable [I.toIdeal.IsPrime]

/-- `Γ_h(V) ≅ Γ_h(V^T)` sends nonzero elements to nonzero elements. -/
theorem primeCompl_bot_le_comap_coordinateRingLinearSubstEquiv :
    (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)).primeCompl ≤
      (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ (linearSubstIdeal M I).toIdeal)).primeCompl.comap
        (coordinateRingLinearSubstGradedRingHom M I) := fun x hx h ↦
  hx (by simpa using h)

/-- The inverse of `Γ_h(V) ≅ Γ_h(V^T)` sends nonzero elements to nonzero elements. -/
theorem primeCompl_bot_le_comap_coordinateRingLinearSubstEquiv_symm :
    (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ (linearSubstIdeal M I).toIdeal)).primeCompl ≤
      (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)).primeCompl.comap
        (coordinateRingLinearSubstGradedRingHomSymm M I) := fun x hx h ↦
  hx (by simpa using h)

/-- **`k(V) ≅ k(V^T)`.** The change of coordinates `F ↦ F^T` induces an isomorphism of function
fields `k(V(I)) ≅ k(V(I^T))`, sending `f / g` to `f^T / g^T`
(`functionField.linearSubstEquiv_mk`). -/
def functionField.linearSubstEquiv : functionField I ≃ₐ[k] functionField (linearSubstIdeal M I) :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom
    (HomogeneousLocalization.map (coordinateRingLinearSubstGradedRingHom M I)
      (primeCompl_bot_le_comap_coordinateRingLinearSubstEquiv M I))
    (HomogeneousLocalization.map (coordinateRingLinearSubstGradedRingHomSymm M I)
      (primeCompl_bot_le_comap_coordinateRingLinearSubstEquiv_symm M I))
    (by
      rw [← HomogeneousLocalization.map_comp]
      have : (coordinateRingLinearSubstGradedRingHom M I).comp
          (coordinateRingLinearSubstGradedRingHomSymm M I) = GradedRingHom.id _ :=
        GradedRingHom.ext fun x ↦ by simp
      simp only [this, HomogeneousLocalization.map_id])
    (by
      rw [← HomogeneousLocalization.map_comp]
      have : (coordinateRingLinearSubstGradedRingHomSymm M I).comp
          (coordinateRingLinearSubstGradedRingHom M I) = GradedRingHom.id _ :=
        GradedRingHom.ext fun x ↦ by simp
      simp only [this, HomogeneousLocalization.map_id]))
    (HomogeneousLocalization.map_algebraMap _ (coordinateRingLinearSubstGradedRingHom M I)
      (fun a ↦ by simp) (primeCompl_bot_le_comap_coordinateRingLinearSubstEquiv M I))

variable {M I} in
/-- The isomorphism `k(V) ≅ k(V^T)` sends `f / g` to `f^T / g^T`. -/
theorem functionField.linearSubstEquiv_mk {d : ℕ} {f g : MvPolynomial (Fin (n + 1)) k}
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous d) (hgI : g ∉ I) :
    functionField.linearSubstEquiv M I (functionField.mk hf hg hgI) =
      functionField.mk (hf.linearSubst M.1) (hg.linearSubst M.1)
        (by rwa [linearSubst_mem_linearSubstIdeal_iff]) := by
  rw [functionField.mk_def, functionField.mk_def]
  change HomogeneousLocalization.map (coordinateRingLinearSubstGradedRingHom M I)
    (primeCompl_bot_le_comap_coordinateRingLinearSubstEquiv M I) (HomogeneousLocalization.mk _) = _
  rw [HomogeneousLocalization.map_mk]
  congr 1
  ext <;> simp


variable {M I} in
/-- The inverse of `k(V) ≅ k(V^T)` sends `f / g` to `f^(T⁻¹) / g^(T⁻¹)`. -/
theorem functionField.linearSubstEquiv_symm_mk {d : ℕ} {f g : MvPolynomial (Fin (n + 1)) k}
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous d) (hgI : g ∉ linearSubstIdeal M I) :
    (functionField.linearSubstEquiv M I).symm (functionField.mk hf hg hgI) =
      functionField.mk (hf.linearSubst (M⁻¹).1) (hg.linearSubst (M⁻¹).1)
        (by rwa [← linearSubstIdeal_inv_linearSubstIdeal M I,
          linearSubst_mem_linearSubstIdeal_iff]) := by
  rw [functionField.mk_def, functionField.mk_def]
  change HomogeneousLocalization.map (coordinateRingLinearSubstGradedRingHomSymm M I)
    (primeCompl_bot_le_comap_coordinateRingLinearSubstEquiv_symm M I)
      (HomogeneousLocalization.mk _) = _
  rw [HomogeneousLocalization.map_mk]
  congr 1
  ext <;> simp

/-! ### Local rings -/

variable {M I} {P : zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))}
  {Q : zeroLocus (linearSubstIdeal M I : Set (MvPolynomial (Fin (n + 1)) k))}

/-- **`𝒪_P(V) ≅ 𝒪_Q(V^T)` for `T(Q) = P`.** The isomorphism `k(V) ≅ k(V^T)` carries the local
ring of `V` at `P` onto the local ring of `V^T` at `Q`, when `T(Q) = P`. -/
theorem map_localSubring_linearSubstEquiv
    (hQP : map M.1.mulVecLin M.injective_mulVecLin Q.1 = P.1) :
    (localSubring I P).map (functionField.linearSubstEquiv M I : functionField I →+* _) =
      localSubring (linearSubstIdeal M I) Q := by
  refine LocalSubring.toSubring_injective (Subring.ext fun z ↦ ?_)
  rw [LocalSubring.map_toSubring, Subring.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨d, f, g, hf, hg, hgP, rfl⟩ := mem_localSubring_iff.1 hy
    refine mem_localSubring_iff.2 ⟨d, _, _, hf.linearSubst M.1, hg.linearSubst M.1, ?_, ?_⟩
    · rwa [Ne, eval_rep_linearSubst_eq_zero_iff M hg, hQP]
    · exact functionField.linearSubstEquiv_mk hf hg _
  · intro hz
    obtain ⟨d, f, g, hf, hg, hgQ, rfl⟩ := mem_localSubring_iff.1 hz
    have hgP : eval P.1.rep (linearSubst (M⁻¹).1 g) ≠ 0 := by
      rwa [Ne, eval_rep_linearSubst_eq_zero_iff M⁻¹ hg, ← hQP, map_inv_map_mulVecLin]
    refine ⟨_, mem_localSubring_iff.2
      ⟨d, _, _, hf.linearSubst (M⁻¹).1, hg.linearSubst _, hgP, rfl⟩, ?_⟩
    change functionField.linearSubstEquiv M I _ = _
    rw [functionField.linearSubstEquiv_mk, functionField.mk_eq_mk_iff, linearSubst_linearSubst_inv,
      linearSubst_linearSubst_inv, sub_self]
    exact zero_mem _

variable (M I) in
/-- The isomorphism `𝒪_P(V) ≅ 𝒪_Q(V^T)`, for `T(Q) = P`, induced by `k(V) ≅ k(V^T)`. -/
def localSubring.linearSubstEquiv (hQP : map M.1.mulVecLin M.injective_mulVecLin Q.1 = P.1) :
    (localSubring I P).toSubring ≃ₐ[k] (localSubring (linearSubstIdeal M I) Q).toSubring where
  toFun z := ⟨functionField.linearSubstEquiv M I z, by
    rw [← map_localSubring_linearSubstEquiv hQP, LocalSubring.map_toSubring]
    exact Subring.mem_map.2 ⟨_, z.2, rfl⟩⟩
  invFun z := ⟨(functionField.linearSubstEquiv M I).symm z, by
    have hz : (z : functionField (linearSubstIdeal M I)) ∈
        ((localSubring I P).map
          (functionField.linearSubstEquiv M I : functionField I →+* _)).toSubring := by
      rw [map_localSubring_linearSubstEquiv hQP]
      exact z.2
    obtain ⟨y, hy, hyz⟩ := Subring.mem_map.1 hz
    rw [← hyz]
    simpa using hy⟩
  left_inv z := Subtype.ext ((functionField.linearSubstEquiv M I).symm_apply_apply
    (z : functionField I))
  right_inv z := Subtype.ext ((functionField.linearSubstEquiv M I).apply_symm_apply
    (z : functionField (linearSubstIdeal M I)))
  map_mul' y z := Subtype.ext (map_mul (functionField.linearSubstEquiv M I)
    (y : functionField I) z)
  map_add' y z := Subtype.ext (map_add (functionField.linearSubstEquiv M I)
    (y : functionField I) z)
  commutes' a := Subtype.ext ((functionField.linearSubstEquiv M I).commutes a)

@[simp]
theorem coe_localSubring_linearSubstEquiv
    (hQP : map M.1.mulVecLin M.injective_mulVecLin Q.1 = P.1) (z : (localSubring I P).toSubring) :
    (localSubring.linearSubstEquiv M I hQP z : functionField (linearSubstIdeal M I)) =
      functionField.linearSubstEquiv M I z :=
  (rfl)

/-! ### The milestone -/

variable (I) in
/-- **Homogeneous coordinate ring, function field and local rings of a projective variety.**
Let `k` be a field, `R = k[X₀, …, Xₙ]` and `I` a homogeneous prime of `R`, with zero locus
`V = V(I) ⊆ ℙⁿ` and homogeneous coordinate ring `Γ_h(V) = R ⧸ I`, graded by `I.quotientGrading`;
a projective variety `V` has `I = I(V)`.

* (a) Every element of the function field `k(V)` is a fraction `f / g` of forms of the same
  degree with `g ∉ I`; `k(V)` embeds into the fraction field of `Γ_h(V)`, and if `V` is nonempty
  then `Γ_h(V)` is not contained in `k(V)`.
* (b) For `P ∈ V`, `𝒪_P(V) ⊆ k(V)` consists of the fractions `f / g` with `g(P) ≠ 0`; its
  maximal ideal of those with moreover `f(P) = 0`; the value of `f / g` at `P` is `f(v) / g(v)`
  for every set of homogeneous coordinates `v` of `P`.
* (c) The pole set of every `z ∈ k(V)` is the zero locus of a set of forms.
* (d) An invertible matrix `M` induces a bijection `T` of `ℙⁿ`. For `S ⊆ R`,
  `T⁻¹(V(S)) = V(S^T)`, with `F^T = linearSubst M F`, and `I(T⁻¹(X)) = I(X)^T` for `X ⊆ ℙⁿ`; a set
  is algebraic, resp. has a prime ideal, resp. is nonempty, iff its preimage `V^T` is. With
  `V(I^T) = T⁻¹(V)`, `F ↦ F^T` induces a degree-preserving isomorphism `Γ_h(V) ≅ Γ_h(V^T)`, an
  isomorphism `k(V) ≅ k(V^T)` sending `f / g` to `f^T / g^T`, and, for `T(Q) = P`, it carries
  `𝒪_P(V)` onto `𝒪_Q(V^T)`, so `𝒪_P(V) ≅ 𝒪_Q(V^T)`.

Milestone: *Homogeneous coordinate ring, function field and local rings of a projective
variety*. -/
theorem functionField_localSubring_and_linearSubstEquiv :
    -- (a)
    (∀ z : functionField I, ∃ (d : ℕ) (f g : MvPolynomial (Fin (n + 1)) k)
      (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous d) (hgI : g ∉ I),
        z = functionField.mk hf hg hgI) ∧
    Function.Injective (functionField.toFractionRing I) ∧
    ((zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))).Nonempty →
      ∃ a : MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal,
        algebraMap _ (FractionRing (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)) a ∉
          Set.range (functionField.toFractionRing I)) ∧
    -- (b)
    (∀ (P : zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))),
      (∀ z : functionField I, z ∈ (localSubring I P).toSubring ↔
        ∃ (d : ℕ) (f g : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
          (hg : g.IsHomogeneous d) (hgP : eval P.1.rep g ≠ 0),
          z = functionField.mk hf hg (notMem_of_eval_rep_ne_zero P.2 hg hgP)) ∧
      (∀ z : (localSubring I P).toSubring,
        z ∈ IsLocalRing.maximalIdeal (localSubring I P).toSubring ↔
          ∃ (d : ℕ) (f g : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
            (hg : g.IsHomogeneous d) (hgP : eval P.1.rep g ≠ 0), eval P.1.rep f = 0 ∧
            (z : functionField I) =
              functionField.mk hf hg (notMem_of_eval_rep_ne_zero P.2 hg hgP)) ∧
      ∀ (v : Fin (n + 1) → k) (hv : v ≠ 0), Projectivization.mk k v hv = P.1 →
        ∀ (d : ℕ) (f g : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
          (hg : g.IsHomogeneous d) (hgP : eval P.1.rep g ≠ 0),
          varietyLocalRing.evalAt I P (varietyLocalRing.mk hf hg hgP) = eval v f / eval v g) ∧
    -- (c)
    (∀ z : functionField I, ∃ S : Set (MvPolynomial (Fin (n + 1)) k),
      (∀ f ∈ S, ∃ d, f.IsHomogeneous d) ∧ poleSet z = zeroLocus S) ∧
    -- (d)
    ∀ N : GL (Fin (n + 1)) k,
      Function.Bijective (map N.1.mulVecLin N.injective_mulVecLin) ∧
      (∀ S : Set (MvPolynomial (Fin (n + 1)) k),
        zeroLocus (linearSubst N.1 '' S) =
          map N.1.mulVecLin N.injective_mulVecLin ⁻¹' zeroLocus S) ∧
      (∀ X : Set (ℙ k (Fin (n + 1) → k)),
        vanishingIdeal (map N.1.mulVecLin N.injective_mulVecLin ⁻¹' X) =
          linearSubstIdeal N (vanishingIdeal X)) ∧
      (∀ V : Set (ℙ k (Fin (n + 1) → k)),
        (zeroLocus (vanishingIdeal (map N.1.mulVecLin N.injective_mulVecLin ⁻¹' V) :
            Set (MvPolynomial (Fin (n + 1)) k)) = map N.1.mulVecLin N.injective_mulVecLin ⁻¹' V ↔
          zeroLocus (vanishingIdeal V : Set (MvPolynomial (Fin (n + 1)) k)) = V) ∧
        ((vanishingIdeal (map N.1.mulVecLin N.injective_mulVecLin ⁻¹' V)).toIdeal.IsPrime ↔
          (vanishingIdeal V).toIdeal.IsPrime) ∧
        ((map N.1.mulVecLin N.injective_mulVecLin ⁻¹' V).Nonempty ↔ V.Nonempty)) ∧
      zeroLocus (linearSubstIdeal N I : Set (MvPolynomial (Fin (n + 1)) k)) =
        map N.1.mulVecLin N.injective_mulVecLin ⁻¹'
          zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) ∧
      (∀ f : MvPolynomial (Fin (n + 1)) k, coordinateRingLinearSubstEquiv N I
        (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (linearSubst N.1 f)) ∧
      (∀ (x : MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal) (d : ℕ),
        coordinateRingLinearSubstEquiv N I x ∈ (linearSubstIdeal N I).quotientGrading d ↔
          x ∈ I.quotientGrading d) ∧
      (∀ (d : ℕ) (f g : MvPolynomial (Fin (n + 1)) k) (hf : f.IsHomogeneous d)
        (hg : g.IsHomogeneous d) (hgI : g ∉ I),
        functionField.linearSubstEquiv N I (functionField.mk hf hg hgI) =
          functionField.mk (hf.linearSubst N.1) (hg.linearSubst N.1)
            (by rwa [linearSubst_mem_linearSubstIdeal_iff])) ∧
      ∀ (P : zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)))
        (Q : zeroLocus (linearSubstIdeal N I : Set (MvPolynomial (Fin (n + 1)) k))),
        map N.1.mulVecLin N.injective_mulVecLin Q.1 = P.1 →
          (localSubring I P).map
              (functionField.linearSubstEquiv N I : functionField I →+* _) =
            localSubring (linearSubstIdeal N I) Q ∧
          Nonempty ((localSubring I P).toSubring ≃ₐ[k]
            (localSubring (linearSubstIdeal N I) Q).toSubring) :=
  ⟨functionField.exists_eq_mk, (functionField.toFractionRing I).injective,
    exists_algebraMap_notMem_range_toFractionRing,
    fun _ ↦ ⟨fun _ ↦ mem_localSubring_iff, fun _ ↦ mem_maximalIdeal_localSubring_iff,
      fun _ hv hvP _ _ _ hf hg hgP ↦ varietyLocalRing.evalAt_mk hv hvP hf hg hgP⟩,
    exists_poleSet_eq_zeroLocus,
    fun N ↦ ⟨bijective_map_mulVecLin N, zeroLocus_linearSubst N.1 N.injective_mulVecLin,
      vanishingIdeal_preimage_map_mulVecLin N,
      fun V ↦ ⟨zeroLocus_vanishingIdeal_preimage_map_mulVecLin_eq_iff N V,
        isPrime_vanishingIdeal_preimage_map_mulVecLin_iff N V,
        (bijective_map_mulVecLin N).2.nonempty_preimage⟩,
      zeroLocus_linearSubstIdeal N I, coordinateRingLinearSubstEquiv_mk N I,
      fun _ _ ↦ coordinateRingLinearSubstEquiv_mem_quotientGrading_iff,
      fun _ _ _ hf hg hgI ↦ functionField.linearSubstEquiv_mk hf hg hgI,
      fun _ _ hQP ↦ ⟨map_localSubring_linearSubstEquiv hQP,
        ⟨localSubring.linearSubstEquiv N I hQP⟩⟩⟩⟩

end PlaneCurves.ProjectiveSpace

end
