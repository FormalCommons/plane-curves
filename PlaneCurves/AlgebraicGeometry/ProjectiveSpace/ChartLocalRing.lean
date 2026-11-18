/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.AffineSpace.RationalFunction
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.FunctionField
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.ProjectiveClosure
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Dehomogenization

/-!
# Affine charts preserve function fields and local rings

Let `k` be a field, `I` a homogeneous prime of `R = k[X₀, …, Xₙ]` and `i` a coordinate with
`Xᵢ ∉ I`. Dehomogenizing at `Xᵢ` sends `I` to the ideal `J = I_*` of `k[Y₀, …, Yₙ₋₁]`, and
Tau Ceti's `HomogeneousIdeal.awayEquivDehomogenize` identifies the degree-zero part of
`(R ⧸ I)[1/xᵢ]` with `k[Y] ⧸ J`. This file deduces that `J` is prime and that the function
fields agree: `k(V) ≅ k(V_*)`, `f / g ↦ f_* / g_*`. For a zero `P` of `I` in the chart
`Xᵢ ≠ 0`, this isomorphism restricts to the local rings: `𝒪_P(V) ≅ 𝒪_{φᵢ(P)}(V_*)`, compatibly
with the values at `P` and `φᵢ(P)`, `φᵢ` the affine chart.

## Main definitions

* `PlaneCurves.ProjectiveSpace.awayToFunctionField I hi`: the inclusion of the chart ring
  `(R ⧸ I)_(xᵢ)` into `k(V)`.
* `PlaneCurves.ProjectiveSpace.functionField.chartEquiv i hi`: the isomorphism
  `k(V) ≃ₐ[k] k(V_*)`, for `V = V(I)` and `V_* = V(J)`.
* `PlaneCurves.ProjectiveSpace.varietyLocalRing.chartEquiv i P hP`: the isomorphism
  `𝒪_P(V) ≃ₐ[k] 𝒪_{φᵢ(P)}(V_*)`, for `P ∈ V` with `P ∈ Uᵢ`.

## Main results

* `PlaneCurves.ProjectiveSpace.eval_affineChart_dehomogenize`: `p_*(φᵢ(P)) = p(v) / vᵢᵈ`.
* `PlaneCurves.ProjectiveSpace.map_dehomogenize_le_vanishingIdeal`: `I_*` vanishes at `φᵢ(P)`.
* `PlaneCurves.ProjectiveSpace.isPrime_map_dehomogenize`: `J = I_*` is prime.
* `PlaneCurves.ProjectiveSpace.functionField.chartEquiv_mk`: `f / g ↦ f_* / g_*`.
* `PlaneCurves.ProjectiveSpace.varietyLocalRing.coe_chartEquiv`: the local isomorphism is the
  restriction of the function-field isomorphism.
* `PlaneCurves.ProjectiveSpace.varietyLocalRing.evalAt_chartEquiv`: it preserves values.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §4.3
-/

public section

open MvPolynomial Projectivization TauCeti HomogeneousLocalization
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PlaneCurves.ProjectiveSpace

variable {k : Type*} [Field k] {n : ℕ}

/-- The value of the dehomogenization `p_*` of a form `p` of degree `d` at the affine
coordinates `φᵢ(P)` of a point `P ∈ Uᵢ` is `p(v) / vᵢᵈ`, for `v` the representative of `P`. -/
theorem eval_affineChart_dehomogenize {i : Fin (n + 1)} {P : ℙ k (Fin (n + 1) → k)}
    (hP : P ∈ affineOpen i) {p : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hp : p.IsHomogeneous d) :
    eval (affineChart i P) (dehomogenize i p) = (P.rep i)⁻¹ ^ d * eval P.rep p := by
  conv_lhs => rw [← mk_rep P, affineChart_mk]
  exact eval_dehomogenize_div i hp _ ((mem_affineOpen_iff i P).1 hP)

/-- For a point `P ∈ Uᵢ` and a form `p`, `p_*` vanishes at `φᵢ(P)` iff `p` vanishes at `P`. -/
theorem eval_affineChart_dehomogenize_eq_zero_iff {i : Fin (n + 1)}
    {P : ℙ k (Fin (n + 1) → k)} (hP : P ∈ affineOpen i) {p : MvPolynomial (Fin (n + 1)) k}
    {d : ℕ} (hp : p.IsHomogeneous d) :
    eval (affineChart i P) (dehomogenize i p) = 0 ↔ eval P.rep p = 0 := by
  rw [eval_affineChart_dehomogenize hP hp, mul_eq_zero, or_iff_right]
  exact pow_ne_zero _ (inv_ne_zero ((mem_affineOpen_iff i P).1 hP))

section

variable {I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)} {i : Fin (n + 1)}
  (P : zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))) (hP : P.1 ∈ affineOpen i)
include hP

/-- A homogeneous ideal with a zero `P ∈ Uᵢ` does not contain `Xᵢ`. -/
theorem X_notMem_of_mem_affineOpen : X i ∉ I :=
  notMem_of_eval_rep_ne_zero P.2 (isHomogeneous_X k i)
    (by simpa using (mem_affineOpen_iff i P.1).1 hP)

/-- The dehomogenization `I_*` vanishes at the affine coordinates `φᵢ(P)` of a zero `P ∈ Uᵢ`
of `I`. -/
theorem map_dehomogenize_le_vanishingIdeal :
    I.toIdeal.map (dehomogenize i) ≤ MvPolynomial.vanishingIdeal k {affineChart i P.1} := by
  have h : (affineChart i).symm (affineChart i P.1) ∈
      zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) := by
    rw [(affineChart i).left_inv (by rwa [affineChart_source])]
    exact P.2
  rw [affineChart_symm_mem_zeroLocus_iff] at h
  intro f hf
  rw [mem_vanishingIdeal_singleton_iff]
  simpa using (MvPolynomial.mem_zeroLocus_iff.1 h) f hf

end

variable (I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)) [I.toIdeal.IsPrime]
  {i : Fin (n + 1)} (hi : X i ∉ I)

/-! ### The chart ring as a subring of the function field -/

include hi in
/-- For `Xᵢ ∉ I`, the class of `Xᵢ` in the domain `R ⧸ I` is nonzero. -/
theorem mk_X_mem_primeCompl_bot :
    Ideal.Quotient.mk I.toIdeal (X i) ∈
      (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)).primeCompl :=
  fun h ↦ hi (Ideal.Quotient.eq_zero_iff_mem.1 h)

/-- The inclusion of the chart ring `(R ⧸ I)_(xᵢ)`, the degree-zero part of `(R ⧸ I)[1/xᵢ]`, into
the function field `k(V)`. -/
noncomputable def awayToFunctionField :
    Away I.quotientGrading (Ideal.Quotient.mk I.toIdeal (X i)) →ₐ[k] functionField I where
  __ := mapId I.quotientGrading (Submonoid.powers_le.2 (mk_X_mem_primeCompl_bot I hi))
  commutes' _ := rfl

theorem awayToFunctionField_def : (awayToFunctionField I hi :
    Away I.quotientGrading (Ideal.Quotient.mk I.toIdeal (X i)) →+* functionField I) =
      mapId I.quotientGrading (Submonoid.powers_le.2 (mk_X_mem_primeCompl_bot I hi)) :=
  (rfl)

/-- The chart ring `(R ⧸ I)_(xᵢ)` is a subring of `k(V)`. -/
theorem awayToFunctionField_injective : Function.Injective (awayToFunctionField I hi) :=
  mapId_injective _ (Submonoid.powers_le.2 (mk_X_mem_primeCompl_bot I hi))
    (Ideal.primeCompl_le_nonZeroDivisors _)

variable {I hi} in
/-- The fraction `p / Xᵢᵐ` of the chart ring is `p / Xᵢᵐ` in `k(V)`. -/
theorem awayToFunctionField_mk {p : MvPolynomial (Fin (n + 1)) k} {m : ℕ}
    (hp : p.IsHomogeneous m) :
    awayToFunctionField I hi (Away.mk I.quotientGrading (I.mk_X_mem_quotientGrading i) m
      (Ideal.Quotient.mk I.toIdeal p) (by simpa using I.mk_mem_quotientGrading hp)) =
      functionField.mk hp (isHomogeneous_X_pow i m) (fun h ↦ hi
        ((‹I.toIdeal.IsPrime›).mem_of_pow_mem m h)) := by
  rw [ext_iff_val, functionField.mk_def, val_mk]
  change Localization.mk _ _ = Localization.mk _ _
  simp

/-- The inclusion `k[Y] ⧸ I_* ≅ (R ⧸ I)_(xᵢ) ⊆ k(V)`. -/
private noncomputable def chartRingToFunctionField :
    MvPolynomial (Fin n) k ⧸ I.toIdeal.map (dehomogenize i) →ₐ[k] functionField I :=
  (awayToFunctionField I hi).comp (I.awayEquivDehomogenize i).symm.toAlgHom

private theorem chartRingToFunctionField_apply
    (a : MvPolynomial (Fin n) k ⧸ I.toIdeal.map (dehomogenize i)) :
    chartRingToFunctionField I hi a =
      awayToFunctionField I hi ((I.awayEquivDehomogenize i).symm a) :=
  (rfl)

private theorem chartRingToFunctionField_injective :
    Function.Injective (chartRingToFunctionField I hi) := fun _ _ h ↦
  (I.awayEquivDehomogenize i).symm.injective (awayToFunctionField_injective I hi h)

include hi in
/-- The dehomogenization `I_*` of a homogeneous prime `I` with `Xᵢ ∉ I` is prime. -/
theorem isPrime_map_dehomogenize : (I.toIdeal.map (dehomogenize i)).IsPrime := by
  refine (Ideal.Quotient.isDomain_iff_prime _).1 ?_
  exact (chartRingToFunctionField_injective I hi).isDomain
    (chartRingToFunctionField I hi).toRingHom

variable {I} in
include hi in
/-- The dehomogenization of a form outside `I` lies outside `I_*`. -/
theorem dehomogenize_notMem_map {p : MvPolynomial (Fin (n + 1)) k} {m : ℕ}
    (hp : p.IsHomogeneous m) (hpI : p ∉ I) :
    dehomogenize i p ∉ I.toIdeal.map (dehomogenize i) := by
  intro h
  have h0 := congrArg (awayToFunctionField I hi) ((I.awayEquivDehomogenize i).injective
    (((I.awayEquivDehomogenize_mk i (by simpa using I.mk_mem_quotientGrading hp)).trans
      (Ideal.Quotient.eq_zero_iff_mem.2 h)).trans (map_zero _).symm))
  rw [map_zero, awayToFunctionField_mk hp] at h0
  exact functionField.mk_ne_zero hp _ _ hpI h0

/-! ### The function field -/

/-- Dehomogenization `R ⧸ I → k(V_*)`, `p ↦ p_*`. -/
private noncomputable def dehomogenizeToFunctionField :
    MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal →ₐ[k]
      AffineSpace.functionField (I.toIdeal.map (dehomogenize i)) :=
  (IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k ⧸ I.toIdeal.map (dehomogenize i)) _).comp
    (Ideal.quotientMapₐ _ (dehomogenize i) Ideal.le_comap_map)

omit [I.toIdeal.IsPrime] in
private theorem dehomogenizeToFunctionField_mk (p : MvPolynomial (Fin (n + 1)) k) :
    dehomogenizeToFunctionField I (i := i) (Ideal.Quotient.mk I.toIdeal p) =
      algebraMap _ _ (Ideal.Quotient.mk (I.toIdeal.map (dehomogenize i)) (dehomogenize i p)) :=
  (rfl)

include hi in
private theorem dehomogenizeToFunctionField_ne_zero ⦃m : ℕ⦄
    ⦃g : MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal⦄ (hg : g ∈ I.quotientGrading m)
    (hgI : g ∈ (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k ⧸ I.toIdeal)).primeCompl) :
    dehomogenizeToFunctionField I (i := i) g ≠ 0 := by
  have := isPrime_map_dehomogenize I hi
  obtain ⟨g, hg', rfl⟩ := I.exists_isHomogeneous_mk_eq hg
  rw [dehomogenizeToFunctionField_mk, Ne, IsFractionRing.to_map_eq_zero_iff,
    Ideal.Quotient.eq_zero_iff_mem]
  exact dehomogenize_notMem_map hi hg' fun h ↦ hgI (Ideal.Quotient.eq_zero_iff_mem.2 h)

include hi in
/-- The map `k(V) → k(V_*)`, `f / g ↦ f_* / g_*`. -/
private noncomputable def toChart :
    functionField I →ₐ[k] AffineSpace.functionField (I.toIdeal.map (dehomogenize i)) :=
  haveI := isPrime_map_dehomogenize I hi
  liftAlgHom I.quotientGrading (Ideal.primeCompl_le_nonZeroDivisors _)
    (dehomogenizeToFunctionField I) (dehomogenizeToFunctionField_ne_zero I hi)

/-- The map `k(V_*) → k(V)`, extending the inclusion of the chart ring. -/
private noncomputable def ofChart :
    AffineSpace.functionField (I.toIdeal.map (dehomogenize i)) →ₐ[k] functionField I :=
  haveI := isPrime_map_dehomogenize I hi
  IsFractionRing.liftAlgHom (K := AffineSpace.functionField (I.toIdeal.map (dehomogenize i)))
    (chartRingToFunctionField_injective I hi)

private theorem ofChart_algebraMap (a : MvPolynomial (Fin n) k ⧸ I.toIdeal.map (dehomogenize i)) :
    ofChart I hi (algebraMap _ _ a) = chartRingToFunctionField I hi a :=
  haveI := isPrime_map_dehomogenize I hi
  IsFractionRing.lift_algebraMap (chartRingToFunctionField_injective I hi) a

private theorem toChart_mk {d : ℕ} {f g : MvPolynomial (Fin (n + 1)) k} (hf : f.IsHomogeneous d)
    (hg : g.IsHomogeneous d) (hgI : g ∉ I) :
    haveI := isPrime_map_dehomogenize I hi
    toChart I hi (functionField.mk hf hg hgI) =
      algebraMap _ _ (Ideal.Quotient.mk (I.toIdeal.map (dehomogenize i)) (dehomogenize i f)) /
        algebraMap _ _ (Ideal.Quotient.mk (I.toIdeal.map (dehomogenize i)) (dehomogenize i g)) := by
  have := isPrime_map_dehomogenize I hi
  rw [toChart, functionField.mk_def, liftAlgHom_mk]
  rfl

private theorem ofChart_toChart (z : functionField I) : ofChart I hi (toChart I hi z) = z := by
  have := isPrime_map_dehomogenize I hi
  obtain ⟨d, f, g, hf, hg, hgI, rfl⟩ := functionField.exists_eq_mk z
  rw [toChart_mk, map_div₀, ofChart_algebraMap, ofChart_algebraMap, chartRingToFunctionField_apply,
    chartRingToFunctionField_apply,
    ← I.awayEquivDehomogenize_mk i (by simpa using I.mk_mem_quotientGrading hf),
    ← I.awayEquivDehomogenize_mk i (by simpa using I.mk_mem_quotientGrading hg),
    AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply, awayToFunctionField_mk hf,
    awayToFunctionField_mk hg, functionField.mk_div_mk hf hg _ hgI]

private theorem toChart_ofChart (z : AffineSpace.functionField (I.toIdeal.map (dehomogenize i))) :
    toChart I hi (ofChart I hi z) = z := by
  have := isPrime_map_dehomogenize I hi
  suffices ((toChart I hi).comp (ofChart I hi) : _ →+* _) = RingHom.id _ from
    congr($this z)
  refine IsLocalization.ringHom_ext
    (nonZeroDivisors (MvPolynomial (Fin n) k ⧸ I.toIdeal.map (dehomogenize i)))
    (RingHom.ext fun a ↦ ?_)
  obtain ⟨z, rfl⟩ := (I.awayEquivDehomogenize i).surjective a
  obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective I.quotientGrading (I.mk_X_mem_quotientGrading i) z
  obtain ⟨p, hp, rfl⟩ := I.exists_isHomogeneous_mk_eq (by simpa using ha)
  change toChart I hi (ofChart I hi (algebraMap _ _ _)) = algebraMap _ _ _
  rw [ofChart_algebraMap, chartRingToFunctionField_apply, AlgEquiv.symm_apply_apply,
    awayToFunctionField_mk hp, toChart_mk, HomogeneousIdeal.awayEquivDehomogenize_mk]
  simp

variable {I} (i) in
/-- **Affine charts preserve function fields.** For a homogeneous prime `I` with `Xᵢ ∉ I`, the
function field `k(V)` of `V = V(I)` is the function field `k(V_*)` of the dehomogenization
`I_*`: the isomorphism sends `f / g` to `f_* / g_*` (`chartEquiv_mk`). -/
noncomputable def functionField.chartEquiv :
    functionField I ≃ₐ[k] AffineSpace.functionField (I.toIdeal.map (dehomogenize i)) :=
  AlgEquiv.ofAlgHom (toChart I hi) (ofChart I hi) (AlgHom.ext (toChart_ofChart I hi))
    (AlgHom.ext (ofChart_toChart I hi))

variable {I}

/-- The chart isomorphism sends `f / g` to `f_* / g_*`. -/
@[simp]
theorem functionField.chartEquiv_mk {d : ℕ} {f g : MvPolynomial (Fin (n + 1)) k}
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous d) (hgI : g ∉ I) :
    haveI := isPrime_map_dehomogenize I hi
    functionField.chartEquiv i hi (functionField.mk hf hg hgI) =
      algebraMap _ _ (Ideal.Quotient.mk (I.toIdeal.map (dehomogenize i)) (dehomogenize i f)) /
        algebraMap _ _ (Ideal.Quotient.mk (I.toIdeal.map (dehomogenize i)) (dehomogenize i g)) :=
  toChart_mk I hi hf hg hgI

/-- The inverse of the chart isomorphism sends the class of a polynomial `p_*`, for a form `p` of
degree `m`, to `p / Xᵢᵐ`. -/
@[simp]
theorem functionField.chartEquiv_symm_algebraMap_mk_dehomogenize {m : ℕ}
    {p : MvPolynomial (Fin (n + 1)) k} (hp : p.IsHomogeneous m) :
    (functionField.chartEquiv i hi).symm (algebraMap _ _
      (Ideal.Quotient.mk (I.toIdeal.map (dehomogenize i)) (dehomogenize i p))) =
      functionField.mk hp (isHomogeneous_X_pow i m) (fun h ↦ hi
        ((‹I.toIdeal.IsPrime›).mem_of_pow_mem m h)) := by
  change ofChart I hi _ = _
  rw [ofChart_algebraMap, chartRingToFunctionField_apply,
    ← I.awayEquivDehomogenize_mk i (by simpa using I.mk_mem_quotientGrading hp),
    AlgEquiv.symm_apply_apply, awayToFunctionField_mk hp]

/-- The inverse of the chart isomorphism sends the coordinate `Yⱼ` to `X_{i.succAbove j} / Xᵢ`. -/
theorem functionField.chartEquiv_symm_algebraMap_mk_X (j : Fin n) :
    (functionField.chartEquiv i hi).symm (algebraMap _ _
      (Ideal.Quotient.mk (I.toIdeal.map (dehomogenize i)) (X j))) =
      functionField.mk (isHomogeneous_X k (i.succAbove j)) (isHomogeneous_X k i) hi := by
  have h := functionField.chartEquiv_symm_algebraMap_mk_dehomogenize hi
    (isHomogeneous_X k (i.succAbove j))
  simp only [dehomogenize_X, Fin.insertNth_apply_succAbove, pow_one] at h
  exact h

/-! ### The local rings -/

section LocalRing

variable (P : zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))) (hP : P.1 ∈ affineOpen i)
include hP

/-- The isomorphism `k(V) ≅ k(V_*)` maps `𝒪_P(V)` onto `𝒪_{φᵢ(P)}(V_*)`. -/
theorem map_localSubring_chartEquiv :
    haveI := isPrime_map_dehomogenize I (X_notMem_of_mem_affineOpen P hP)
    (localSubring I P).toSubring.map
        (functionField.chartEquiv i (X_notMem_of_mem_affineOpen P hP)).toRingEquiv.toRingHom =
      (AffineSpace.localSubring (affineChart i P.1)
        (map_dehomogenize_le_vanishingIdeal P hP)).toSubring := by
  have hi := X_notMem_of_mem_affineOpen P hP
  have := isPrime_map_dehomogenize I hi
  ext z
  rw [Subring.mem_map, AffineSpace.mem_localSubring_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨d, f, g, hf, hg, hgP, rfl⟩ := mem_localSubring_iff.1 hy
    refine ⟨dehomogenize i f, dehomogenize i g, ?_, functionField.chartEquiv_mk hi hf hg _⟩
    exact (eval_affineChart_dehomogenize_eq_zero_iff hP hg).not.2 hgP
  · rintro ⟨a, b, hb, rfl⟩
    set N := max a.totalDegree b.totalDegree
    have hb' : dehomogenize i (homogenize i N b) = b := dehomogenize_homogenize (le_max_right _ _)
    have ha' : dehomogenize i (homogenize i N a) = a := dehomogenize_homogenize (le_max_left _ _)
    have hGP : eval P.1.rep (homogenize i N b) ≠ 0 := fun h ↦ hb (by
      rwa [← hb', eval_affineChart_dehomogenize_eq_zero_iff hP (isHomogeneous_homogenize i N b)])
    refine ⟨_, mem_localSubring_iff.2 ⟨N, _, _, isHomogeneous_homogenize i N a,
      isHomogeneous_homogenize i N b, hGP, rfl⟩, ?_⟩
    simp only [RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe,
      functionField.chartEquiv_mk, ha', hb']

variable (i) in
/-- **Affine charts preserve local rings.** For a zero `P` of a homogeneous prime `I` in the
chart `Uᵢ`, the local ring `𝒪_P(V)` of `V = V(I)` is the local ring `𝒪_{φᵢ(P)}(V_*)` of the
dehomogenization at the affine coordinates of `P`: the restriction of
`functionField.chartEquiv` (`coe_chartEquiv`), sending `f / g` to `f_* / g_*`. -/
noncomputable def varietyLocalRing.chartEquiv :
    haveI := isPrime_map_dehomogenize I (X_notMem_of_mem_affineOpen P hP)
    varietyLocalRing I P ≃ₐ[k] (AffineSpace.localSubring (affineChart i P.1)
      (map_dehomogenize_le_vanishingIdeal P hP)).toSubring :=
  haveI := isPrime_map_dehomogenize I (X_notMem_of_mem_affineOpen P hP)
  AlgEquiv.ofRingEquiv (f := ((localSubringEquiv I P).toRingEquiv.trans
      ((functionField.chartEquiv i (X_notMem_of_mem_affineOpen P hP)).toRingEquiv.subringMap
        (s := (localSubring I P).toSubring))).trans
      (RingEquiv.subringCongr (map_localSubring_chartEquiv P hP)))
    fun c ↦ Subtype.ext (by
      change functionField.chartEquiv i (X_notMem_of_mem_affineOpen P hP)
        ((localSubringEquiv I P) (algebraMap k _ c) : functionField I) = _
      rw [AlgEquiv.commutes, coe_algebraMap_localSubring, AlgEquiv.commutes]
      exact IsScalarTower.algebraMap_apply k _ _ c)

/-- The isomorphism `𝒪_P(V) ≅ 𝒪_{φᵢ(P)}(V_*)` is the restriction of `k(V) ≅ k(V_*)`. -/
@[simp]
theorem varietyLocalRing.coe_chartEquiv (z : varietyLocalRing I P) :
    haveI := isPrime_map_dehomogenize I (X_notMem_of_mem_affineOpen P hP)
    (varietyLocalRing.chartEquiv i P hP z :
        AffineSpace.functionField (I.toIdeal.map (dehomogenize i))) =
      functionField.chartEquiv i (X_notMem_of_mem_affineOpen P hP)
        (varietyLocalRing.toFunctionField I P z) := by
  change functionField.chartEquiv i (X_notMem_of_mem_affineOpen P hP)
    (localSubringEquiv I P z : functionField I) = _
  rw [coe_localSubringEquiv]

/-- The isomorphism `𝒪_P(V) ≅ 𝒪_{φᵢ(P)}(V_*)` sends `f / g` to `f_* / g_*`. -/
theorem varietyLocalRing.chartEquiv_mk {d : ℕ} {f g : MvPolynomial (Fin (n + 1)) k}
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous d) (hgP : eval P.1.rep g ≠ 0) :
    haveI := isPrime_map_dehomogenize I (X_notMem_of_mem_affineOpen P hP)
    (varietyLocalRing.chartEquiv i P hP (varietyLocalRing.mk hf hg hgP) :
        AffineSpace.functionField (I.toIdeal.map (dehomogenize i))) =
      algebraMap _ _ (Ideal.Quotient.mk (I.toIdeal.map (dehomogenize i)) (dehomogenize i f)) /
        algebraMap _ _ (Ideal.Quotient.mk (I.toIdeal.map (dehomogenize i)) (dehomogenize i g)) := by
  rw [varietyLocalRing.coe_chartEquiv, varietyLocalRing.toFunctionField_mk,
    functionField.chartEquiv_mk]

/-- The isomorphism `𝒪_P(V) ≅ 𝒪_{φᵢ(P)}(V_*)` preserves values: the value of its image at
`φᵢ(P)` is the value at `P`. -/
@[simp]
theorem varietyLocalRing.evalAt_chartEquiv (z : varietyLocalRing I P) :
    haveI := isPrime_map_dehomogenize I (X_notMem_of_mem_affineOpen P hP)
    AffineSpace.evalAt (affineChart i P.1) (map_dehomogenize_le_vanishingIdeal P hP)
        (varietyLocalRing.chartEquiv i P hP z) = varietyLocalRing.evalAt I P z := by
  have := isPrime_map_dehomogenize I (X_notMem_of_mem_affineOpen P hP)
  have hr : P.1.rep i ≠ 0 := (mem_affineOpen_iff i P.1).1 hP
  obtain ⟨d, f, g, hf, hg, hgP, rfl⟩ := varietyLocalRing.exists_eq_mk z
  have hgP' := (eval_affineChart_dehomogenize_eq_zero_iff hP hg).not.2 hgP
  rw [AffineSpace.evalAt_eq_div _ _ hgP' (varietyLocalRing.chartEquiv_mk P hP hf hg hgP),
    varietyLocalRing.evalAt_mk_rep, eval_affineChart_dehomogenize hP hf,
    eval_affineChart_dehomogenize hP hg,
    mul_div_mul_left _ _ (pow_ne_zero _ (inv_ne_zero hr))]

end LocalRing

end PlaneCurves.ProjectiveSpace

end
