/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.OrdinaryMultiplePoint
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Tangent
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Birational

/-!
# Singularities of the proper transform under the standard quadratic transformation

Off the fundamental triangle `xyz = 0`, the standard quadratic transformation
`Q : [x : y : z] ↦ [yz : xz : xy]` is, in the affine chart `z = 1`, the inversion
`(x, y) ↦ (x⁻¹, y⁻¹)`: indeed `[yz : xz : xy] = [x⁻¹ : y⁻¹ : 1]` for `z = 1`. The inversion is an
involution of the localization `k[x, y][1/(xy)]`, and for a form `F` of degree `n` it sends the
dehomogenization `F_*` of `F` to a unit times the dehomogenization `F'_*` of the proper transform
`F'`: `F^Q(x, y, 1) = F(y, x, xy) = (xy)ⁿ F(x⁻¹, y⁻¹, 1)`. So the local ring of `F` at a point `P`
off the triangle is isomorphic to the local ring of `F'` at `Q(P)`, and `F` and `F'` have the same
multiplicity there, and the same ordinariness. This is Fulton's step (7)(2)(a).

## Main definitions

* `PlaneCurves.Projective.chartInversion`: the inversion `x ↦ x⁻¹, y ↦ y⁻¹` of
  `R[x, y][1/(xy)]`, an involution.
* `PlaneCurves.Projective.localRingEquivQuadraticMap`: for a point `P` off the fundamental
  triangle, the isomorphism `𝒪_P(F) ≅ 𝒪_{Q(P)}(F')` of the local rings in the chart `z = 1`.

## Main results

* `PlaneCurves.Projective.dehomogenize_quadraticTransform`: `F^Q(x, y, 1) = F(y, x, xy)`.
* `PlaneCurves.Projective.algebraMap_dehomogenize_quadraticTransform`: in `k[x, y][1/(xy)]`,
  `F^Q(x, y, 1) = (xy)ⁿ F(x⁻¹, y⁻¹, 1)` for a form `F` of degree `n`.
* `PlaneCurves.Projective.exists_chartInversion_algebraMap_dehomogenize_eq`: the inversion sends
  `F_*` to a unit times `F'_*`.
* `PlaneCurves.Projective.affineChart_quadraticMap`: in the chart `z = 1`, the point map is the
  inversion `(a, b) ↦ (a⁻¹, b⁻¹)` off the triangle.
* `PlaneCurves.Projective.mult_properTransform_quadraticMap`: `m_{Q(P)}(F') = m_P(F)` for `P`
  off the fundamental triangle.
* `PlaneCurves.Projective.isOrdinaryMultiplePoint_properTransform_quadraticMap_iff`: `Q(P)` is
  an ordinary multiple point of `F'` iff `P` is one of `F`, for `P` off the fundamental triangle.

These hold for every form `F`; that no exceptional line is a component of `F` is not needed.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.4
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial hiding zeroLocus zeroLocus_anti_mono vanishingIdeal mem_vanishingIdeal_iff
open Projectivization TauCeti PlaneCurves.ProjectiveSpace PlaneCurves.AffineSpace Ideal
open scoped LinearAlgebra.Projectivization

/-- The polynomial `xy` of `R[x, y]`. -/
local notation "xy[" R "]" => (X 0 * X 1 : MvPolynomial (Fin 2) R)
/-- The localization `R[x, y][1/(xy)]`. -/
local notation "𝓛[" R "]" => Localization.Away xy[R]
/-- The map `R[x, y] → R[x, y][1/(xy)]`. -/
local notation "toL[" R "]" => algebraMap (MvPolynomial (Fin 2) R) 𝓛[R]
/-- The inverse `(xy)⁻¹` in `R[x, y][1/(xy)]`. -/
local notation "w[" R "]" => IsLocalization.Away.invSelf (S := 𝓛[R]) xy[R]

/-! ### The inversion of `R[x, y][1/(xy)]` -/

section Inversion

variable {R : Type*} [CommRing R]

/-- The images `y / (xy)` and `x / (xy)` of `x` and `y` under the inversion. -/
private noncomputable def invVec : Fin 2 → 𝓛[R] :=
  ![toL[R] (X 1) * w[R], toL[R] (X 0) * w[R]]

private theorem mul_invSelf' :
    toL[R] (X 0) * toL[R] (X 1) * w[R] = 1 := by
  rw [← map_mul]
  exact IsLocalization.Away.mul_invSelf _

private theorem aeval_invVec_X_mul_X :
    aeval (invVec (R := R)) xy[R] = w[R] := by
  have h := mul_invSelf' (R := R)
  simp only [map_mul, aeval_X, invVec, Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination w[R] * h

private noncomputable def chartInversionHom :
    𝓛[R] →ₐ[R] 𝓛[R] :=
  IsLocalization.Away.liftAlgHom xy[R] (f := aeval invVec) <| by
    rw [aeval_invVec_X_mul_X]
    exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf _)

private theorem chartInversionHom_algebraMap (f : MvPolynomial (Fin 2) R) :
    chartInversionHom (toL[R] f) = aeval invVec f := by
  simp [chartInversionHom]

private theorem chartInversionHom_invSelf :
    chartInversionHom w[R] = toL[R] xy[R] := by
  have h1 := congrArg chartInversionHom
    (IsLocalization.Away.mul_invSelf (S := 𝓛[R]) xy[R])
  rw [map_mul, map_one, chartInversionHom_algebraMap, aeval_invVec_X_mul_X] at h1
  have h2 := IsLocalization.Away.mul_invSelf (S := 𝓛[R]) xy[R]
  linear_combination toL[R] xy[R] * h1 - chartInversionHom w[R] * h2

private theorem chartInversionHom_comp :
    (chartInversionHom (R := R)).comp chartInversionHom = AlgHom.id _ _ := by
  ext i
  change chartInversionHom (chartInversionHom (toL[R] (X i))) = toL[R] (X i)
  have h := mul_invSelf' (R := R)
  fin_cases i
  · simp [chartInversionHom_algebraMap, invVec, chartInversionHom_invSelf]
    linear_combination toL[R] (X 0) * h
  · simp [chartInversionHom_algebraMap, invVec, chartInversionHom_invSelf]
    linear_combination toL[R] (X 1) * h

/-- The inversion `x ↦ x⁻¹, y ↦ y⁻¹` of `R[x, y][1/(xy)]`, an involution
(`chartInversion_chartInversion`). In the affine chart `z = 1` of `ℙ²`, it is the standard
quadratic transformation off the fundamental triangle. -/
noncomputable def chartInversion :
    𝓛[R] ≃ₐ[R] 𝓛[R] :=
  AlgEquiv.ofAlgHom chartInversionHom chartInversionHom chartInversionHom_comp
    chartInversionHom_comp

/-- The inversion is the `R`-algebra map sending `x` to `y / (xy)` and `y` to `x / (xy)`. -/
theorem chartInversion_algebraMap (f : MvPolynomial (Fin 2) R) :
    chartInversion (toL[R] f) =
      aeval ![toL[R] (X 1) * w[R], toL[R] (X 0) * w[R]] f :=
  chartInversionHom_algebraMap f

@[simp]
theorem chartInversion_algebraMap_X_zero :
    chartInversion (toL[R] (X 0 : MvPolynomial (Fin 2) R)) =
      toL[R] (X 1) * w[R] := by
  simp [chartInversion_algebraMap]

@[simp]
theorem chartInversion_algebraMap_X_one :
    chartInversion (toL[R] (X 1 : MvPolynomial (Fin 2) R)) =
      toL[R] (X 0) * w[R] := by
  simp [chartInversion_algebraMap]

/-- The inversion sends `xy` to `(xy)⁻¹`. -/
@[simp]
theorem chartInversion_algebraMap_X_mul_X :
    chartInversion (toL[R] xy[R]) = w[R] :=
  (chartInversion_algebraMap _).trans aeval_invVec_X_mul_X

/-- The inversion sends `(xy)⁻¹` to `xy`. -/
@[simp]
theorem chartInversion_invSelf :
    chartInversion w[R] = toL[R] xy[R] :=
  chartInversionHom_invSelf

/-- The inversion is an involution. -/
@[simp]
theorem chartInversion_chartInversion (a : 𝓛[R]) :
    chartInversion (chartInversion a) = a :=
  congr($chartInversionHom_comp a)

@[simp]
theorem chartInversion_symm :
    (chartInversion (R := R)).symm = chartInversion :=
  AlgEquiv.ext fun a ↦ by
    rw [AlgEquiv.symm_apply_eq, chartInversion_chartInversion]

end Inversion

/-- The inversion respects values: if `q = p⁻¹` coordinatewise, with `p` off the axes, then
`(ι a)(q) = a(p)` for every `a ∈ k[x, y][1/(xy)]`. -/
theorem awayLift_comp_chartInversion {k : Type*} [Field k] {p q : Fin 2 → k}
    (hp : eval p (X 0 * X 1) ≠ 0) (hq : eval q (X 0 * X 1) ≠ 0) (hpq : ∀ i, p i * q i = 1) :
    (Localization.awayLift (eval q) (X 0 * X 1) (isUnit_iff_ne_zero.2 hq)).comp
        (chartInversion (R := k) : 𝓛[k] →+* 𝓛[k]) =
      Localization.awayLift (eval p) (X 0 * X 1) (isUnit_iff_ne_zero.2 hp) := by
  have hinv : Localization.awayLift (eval q) (X 0 * X 1) (isUnit_iff_ne_zero.2 hq)
      w[k] = (q 0 * q 1)⁻¹ := by
    have h := congrArg (Localization.awayLift (eval q) (X 0 * X 1) (isUnit_iff_ne_zero.2 hq))
      (IsLocalization.Away.mul_invSelf (S := 𝓛[k]) xy[k])
    rw [map_mul, map_one, IsLocalization.Away.lift_eq] at h
    exact eq_inv_of_mul_eq_one_right (by simpa using h)
  have h0 := hpq 0
  have h1 := hpq 1
  refine IsLocalization.ringHom_ext (Submonoid.powers xy[k]) <|
    MvPolynomial.ringHom_ext (fun r ↦ ?_) fun i ↦ ?_
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe]
    rw [show toL[k] (C r) = algebraMap k 𝓛[k] r from (IsScalarTower.algebraMap_apply k _ _ r).symm,
      AlgEquiv.commutes, IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 2) k),
      IsLocalization.Away.lift_eq]
    simp
  · have hq0 : q 0 ≠ 0 := right_ne_zero_of_mul_eq_one h0
    have hq1 : q 1 ≠ 0 := right_ne_zero_of_mul_eq_one h1
    fin_cases i
    · simp [IsLocalization.Away.lift_eq, hinv]
      field_simp
      linear_combination -h0
    · simp [IsLocalization.Away.lift_eq, hinv]
      field_simp
      linear_combination -h1

/-! ### The quadratic transformation in the chart `z = 1` -/

section Chart

variable {R : Type*} [CommRing R]

/-- In the chart `z = 1`, the quadratic transform is `F^Q(x, y, 1) = F(y, x, xy)`. -/
theorem dehomogenize_quadraticTransform (F : MvPolynomial (Fin 3) R) :
    dehomogenize 2 (quadraticTransform F) = aeval ![X 1, X 0, X 0 * X 1] F := by
  rw [← AlgHom.comp_apply]
  congr 1
  ext i
  fin_cases i <;> simp [Fin.insertNth_apply_below]

/-- In `R[x, y][1/(xy)]`, `F^Q(x, y, 1) = (xy)ⁿ F(x⁻¹, y⁻¹, 1)` for a form `F` of degree `n`, where
`x ↦ x⁻¹, y ↦ y⁻¹` is the inversion `chartInversion`. -/
theorem algebraMap_dehomogenize_quadraticTransform {F : MvPolynomial (Fin 3) R} {n : ℕ}
    (hF : F.IsHomogeneous n) :
    toL[R] (dehomogenize 2 (quadraticTransform F)) =
      toL[R] xy[R] ^ n * chartInversion (toL[R] (dehomogenize 2 F)) := by
  let φ : MvPolynomial (Fin 3) R →ₐ[R] 𝓛[R] :=
    (IsScalarTower.toAlgHom R (MvPolynomial (Fin 2) R) 𝓛[R]).comp
      ((dehomogenize 2).comp quadraticTransform)
  let ψ : MvPolynomial (Fin 3) R →ₐ[R] 𝓛[R] :=
    (chartInversion (R := R) : 𝓛[R] →ₐ[R] 𝓛[R]).comp
      ((IsScalarTower.toAlgHom R (MvPolynomial (Fin 2) R) 𝓛[R]).comp (dehomogenize 2))
  have h := mul_invSelf' (R := R)
  have key : (fun i ↦ φ (X i)) = fun i ↦ toL[R] xy[R] * ψ (X i) := by
    funext i
    fin_cases i
    · simp [φ, ψ, Fin.insertNth_apply_below]
      linear_combination (-(toL[R] (X 1))) * h
    · simp [φ, ψ, Fin.insertNth_apply_below]
      linear_combination (-(toL[R] (X 0))) * h
    · simp [φ, ψ, Fin.insertNth_apply_below]
  have hφ := congr($(aeval_unique φ) F)
  have hψ := congr($(aeval_unique ψ) F)
  simp only [Function.comp_def] at hφ hψ
  change φ F = _ * ψ F
  rw [hφ, key, hF.aeval_mul_left, ← hψ]

end Chart

section Field

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {n : ℕ}

/-- The inversion sends the dehomogenization `F_*` of a form at `z` to a unit times the
dehomogenization `F'_*` of its proper transform: `F(x⁻¹, y⁻¹, 1) = (xy)⁻ⁿ x^r₀ y^r₁ F'(x, y, 1)`,
by Fulton's (1). -/
theorem exists_chartInversion_algebraMap_dehomogenize_eq (hF : F.IsHomogeneous n) :
    ∃ u : (𝓛[k])ˣ,
      chartInversion (toL[k] (dehomogenize 2 F)) =
        (u : 𝓛[k]) * toL[k] (dehomogenize 2 (properTransform F)) := by
  set w : 𝓛[k] := w[k]
  have h := algebraMap_dehomogenize_quadraticTransform hF
  rw [quadraticTransform_eq hF] at h
  simp only [map_mul, map_pow, dehomogenize_X] at h
  rw [show (Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin 2) k) 2 1 X 0) = X 0 from rfl,
    show (Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin 2) k) 2 1 X 1) = X 1 from rfl] at h
  simp only [Fin.isValue, Fin.insertNth_apply_same, one_pow, mul_one, map_one] at h
  have hw : toL[k] xy[k] * w = 1 := IsLocalization.Away.mul_invSelf _
  have hn : (toL[k] (X 0) * toL[k] (X 1)) ^ n * w ^ n = 1 := by
    rw [← mul_pow, ← map_mul, hw, one_pow]
  have h0 : IsUnit (toL[k] (X 0)) :=
    IsLocalization.Away.isUnit_of_dvd xy[k] (dvd_mul_right (X 0) (X 1))
  have h1 : IsUnit (toL[k] (X 1)) :=
    IsLocalization.Away.isUnit_of_dvd xy[k] (dvd_mul_left (X 1) (X 0))
  have hu : IsUnit (w ^ n * (toL[k] (X 0) ^ (mult F (fundamentalPoint 0)).toNat *
      toL[k] (X 1) ^ (mult F (fundamentalPoint 1)).toNat)) :=
    ((IsUnit.of_mul_eq_one_right _ hw).pow n).mul ((h0.pow _).mul (h1.pow _))
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec]
  linear_combination (-(w ^ n)) * h - chartInversion (toL[k] (dehomogenize 2 F)) * hn

variable {P : ℙ k (Fin 3 → k)}

/-- The chart coordinates `(a, b)` at `z = 1` of a point off the fundamental triangle satisfy
`ab ≠ 0`. -/
theorem eval_affineChart_two_X_mul_X_ne_zero (hP : P ∉ fundamentalTriangle) :
    eval (affineChart 2 P) (X 0 * X 1) ≠ 0 := by
  induction P using Projectivization.ind with | h v hv =>
  have h : ∀ i, v i ≠ 0 := by simpa [mk_mem_fundamentalTriangle_iff] using hP
  simp [affineChart_mk, h, Fin.succAbove]

/-- In the chart `z = 1`, the point map is the inversion `(a, b) ↦ (a⁻¹, b⁻¹)` off the fundamental
triangle: `[a : b : 1] ↦ [b : a : ab] = [a⁻¹ : b⁻¹ : 1]`. -/
theorem affineChart_quadraticMap (hP : P ∉ fundamentalTriangle) (i : Fin 2) :
    affineChart 2 (quadraticMap P) i = (affineChart 2 P i)⁻¹ := by
  induction P using Projectivization.ind with | h v hv =>
  have h : ∀ i, v i ≠ 0 := by simpa [mk_mem_fundamentalTriangle_iff] using hP
  have hw : ![v 1 * v 2, v 0 * v 2, v 0 * v 1] ≠ 0 := fun h0 ↦ by
    simpa [h] using congrFun h0 0
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  rw [quadraticMap_mk v hv hw, affineChart_mk, affineChart_mk]
  fin_cases i <;> simp [Fin.succAbove] <;> field_simp

theorem affineChart_mul_affineChart_quadraticMap (hP : P ∉ fundamentalTriangle) (i : Fin 2) :
    affineChart 2 P i * affineChart 2 (quadraticMap P) i = 1 := by
  rw [affineChart_quadraticMap hP]
  refine mul_inv_cancel₀ fun h ↦ eval_affineChart_two_X_mul_X_ne_zero hP ?_
  fin_cases i <;> simp_all

/-- **The local rings off the fundamental triangle.** For a form `F` and a point `P` off the
fundamental triangle, the inversion `chartInversion` induces an isomorphism of the local rings
`𝒪_P(F) ≅ 𝒪_{Q(P)}(F')` in the chart `z = 1`, where `F'` is the proper transform and `Q` the
quadratic point map. -/
noncomputable def localRingEquivQuadraticMap (hF : F.IsHomogeneous n)
    (hP : P ∉ fundamentalTriangle) :
    (localRing k (affineChart 2 P) ⧸
        span {(algebraMap _ (localRing k (affineChart 2 P)) (dehomogenize 2 F))}) ≃ₐ[k]
      (localRing k (affineChart 2 (quadraticMap P)) ⧸
        span {(algebraMap _ (localRing k (affineChart 2 (quadraticMap P)))
          (dehomogenize 2 (properTransform F)))}) :=
  quotientEquivOfAway chartInversion (eval_affineChart_two_X_mul_X_ne_zero hP)
    (eval_affineChart_two_X_mul_X_ne_zero
      (bijOn_quadraticMap_compl_fundamentalTriangle.mapsTo hP))
    (awayLift_comp_chartInversion (eval_affineChart_two_X_mul_X_ne_zero hP)
      (eval_affineChart_two_X_mul_X_ne_zero
        (bijOn_quadraticMap_compl_fundamentalTriangle.mapsTo hP))
      (affineChart_mul_affineChart_quadraticMap hP))
    (exists_chartInversion_algebraMap_dehomogenize_eq hF).choose
    (exists_chartInversion_algebraMap_dehomogenize_eq hF).choose_spec

/-- The isomorphism of local rings off the triangle is induced by the inversion of
`k[x, y][1/(xy)]`. -/
theorem localRingEquivQuadraticMap_mk (hF : F.IsHomogeneous n) (hP : P ∉ fundamentalTriangle)
    (a : localRing k (affineChart 2 P)) :
    localRingEquivQuadraticMap hF hP (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (localRingEquivOfAway chartInversion
        (eval_affineChart_two_X_mul_X_ne_zero hP)
        (eval_affineChart_two_X_mul_X_ne_zero
          (bijOn_quadraticMap_compl_fundamentalTriangle.mapsTo hP))
        (awayLift_comp_chartInversion (eval_affineChart_two_X_mul_X_ne_zero hP)
          (eval_affineChart_two_X_mul_X_ne_zero
            (bijOn_quadraticMap_compl_fundamentalTriangle.mapsTo hP))
          (affineChart_mul_affineChart_quadraticMap hP)) a) :=
  quotientEquivOfAway_mk _ _ _ _ _ _ a

private theorem eval_dehomogenize_eq_zero (hF : F.IsHomogeneous n) (hP : P ∈ affineOpen 2)
    (hPF : P ∈ zeroLocus {F}) : eval (affineChart 2 P) (dehomogenize 2 F) = 0 :=
  (eval_affineChart_dehomogenize_eq_zero_iff hP hF).2 <| by
    rw [mem_zeroLocus_iff_eval_rep (by simpa using ⟨n, hF⟩)] at hPF; exact hPF F rfl

/-- **Fulton's (7)(2)(a), multiplicities.** Off the fundamental triangle, the quadratic
transformation preserves multiplicities: `m_{Q(P)}(F') = m_P(F)` for every form `F`. -/
theorem mult_properTransform_quadraticMap (hF : F.IsHomogeneous n)
    (hP : P ∉ fundamentalTriangle) :
    mult (properTransform F) (quadraticMap P) = mult F P := by
  have hP' := bijOn_quadraticMap_compl_fundamentalTriangle.mapsTo hP
  by_cases hPF : P ∈ zeroLocus {F}
  · have hPF' := (quadraticMap_mem_zeroLocus_properTransform_iff hF hP).2 hPF
    rw [mult_eq_orderAt_dehomogenize hF.properTransform
        (mem_affineOpen_of_notMem_fundamentalTriangle hP' 2),
      mult_eq_orderAt_dehomogenize hF (mem_affineOpen_of_notMem_fundamentalTriangle hP 2)]
    exact (Affine.orderAt_eq_of_ringEquiv
      (eval_dehomogenize_eq_zero hF (mem_affineOpen_of_notMem_fundamentalTriangle hP 2) hPF)
      (eval_dehomogenize_eq_zero hF.properTransform
        (mem_affineOpen_of_notMem_fundamentalTriangle hP' 2) hPF')
      (localRingEquivQuadraticMap hF hP).toRingEquiv).symm
  · rw [(mult_eq_zero_iff hF).2 hPF, mult_eq_zero_iff hF.properTransform,
      quadraticMap_mem_zeroLocus_properTransform_iff hF hP]
    exact hPF

/-- **Fulton's (7)(2)(a), ordinary multiple points.** Over an algebraically closed field, off the
fundamental triangle, `Q(P)` is an ordinary multiple point of the proper transform `F'` exactly
when `P` is one of `F`, for every form `F`. -/
theorem isOrdinaryMultiplePoint_properTransform_quadraticMap_iff [IsAlgClosed k]
    (hF : F.IsHomogeneous n) (hP : P ∉ fundamentalTriangle) :
    IsOrdinaryMultiplePoint (properTransform F) (quadraticMap P) ↔
      IsOrdinaryMultiplePoint F P := by
  have hP' := bijOn_quadraticMap_compl_fundamentalTriangle.mapsTo hP
  by_cases hPF : P ∈ zeroLocus {F}
  · have hPF' := (quadraticMap_mem_zeroLocus_properTransform_iff hF hP).2 hPF
    rw [isOrdinaryMultiplePoint_iff_affine hF.properTransform
        (mem_affineOpen_of_notMem_fundamentalTriangle hP' 2),
      isOrdinaryMultiplePoint_iff_affine hF (mem_affineOpen_of_notMem_fundamentalTriangle hP 2)]
    exact (Affine.isOrdinaryMultiplePoint_iff_of_ringEquiv
      (eval_dehomogenize_eq_zero hF (mem_affineOpen_of_notMem_fundamentalTriangle hP 2) hPF)
      (eval_dehomogenize_eq_zero hF.properTransform
        (mem_affineOpen_of_notMem_fundamentalTriangle hP' 2) hPF')
      (localRingEquivQuadraticMap hF hP).toRingEquiv).symm
  · have h0 : mult F P = 0 := (mult_eq_zero_iff hF).2 hPF
    have h0' : mult (properTransform F) (quadraticMap P) = 0 := by
      rw [mult_properTransform_quadraticMap hF hP, h0]
    refine iff_of_false (fun h ↦ ?_) fun h ↦ ?_
    · have := isMultiplePoint_def.1 (isOrdinaryMultiplePoint_def.1 h).1
      rw [h0'] at this
      exact absurd this (by decide)
    · have := isMultiplePoint_def.1 (isOrdinaryMultiplePoint_def.1 h).1
      rw [h0] at this
      exact absurd this (by decide)

end Field

end PlaneCurves.Projective

end
