/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.Blowup.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.OrdinaryMultiplePoint
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Tangent
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Birational
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Singularities.Basic

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

Near the centre `P = [0 : 0 : 1]`, for a curve in excellent position, the quadratic
transformation is the blow-up of `P` (Fulton's step (5)): in the chart `y = 1`, with coordinates
`(x, z)`, `F'(x, 1, xz) = x^(n - r) g(z, x)` for `g` the strict transform of `F(x, y, 1)` under the
blow-up of the origin and `r = m_P(F)`. So the blow-up chart `(x, z) ↦ (x, xz)` identifies the
local ring of `F'` at a point over the centre `[α : 1 : 0]` with that of `g` at `(0, α)`, and the
results of the blow-up apply: Fulton's step (7)(2)(c).

## Main definitions

* `PlaneCurves.Projective.chartInversion`: the inversion `x ↦ x⁻¹, y ↦ y⁻¹` of
  `R[x, y][1/(xy)]`, an involution.
* `PlaneCurves.Projective.localRingEquivQuadraticMap`: for a point `P` off the fundamental
  triangle, the isomorphism `𝒪_P(F) ≅ 𝒪_{Q(P)}(F')` of the local rings in the chart `z = 1`.
* `PlaneCurves.Projective.IsExcellentPosition.localRingEquivPointsOverCentre`: for `α ≠ 0`, the
  isomorphism of the local ring of `F'` at `[α : 1 : 0]`, in the chart `y = 1`, with that of `g` at
  `(0, α)`.

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

At the points over the centre, for a curve in excellent position with `r = m_P(F)`:

* `PlaneCurves.Projective.IsExcellentPosition.dehomogenize_properTransform_blowup`:
  `F'(x, 1, xz) = x^(n - r) g(z, x)`.
* `PlaneCurves.Projective.IsExcellentPosition.mem_pointsOverCentre_iff_eval_blowupStrictTransform`:
  the points over the centre are the `[α : 1 : 0]` with `g(0, α) = 0`.
* `IsExcellentPosition.mult_properTransform_mk_eq_orderAt_blowupStrictTransform` (in the namespace
  `PlaneCurves.Projective`): `m_{[α:1:0]}(F') = m_{(0, α)}(g)`;
  `PlaneCurves.Projective.IsExcellentPosition.intersectionNumber_properTransform_X_two_mk`:
  `I([α : 1 : 0], F' ∩ Z) = I((0, α), g ∩ X)`.
* `PlaneCurves.Projective.mult_le_intersectionNumber_of_mem_pointsOverCentre`:
  `m_Q(F') ≤ I(Q, F' ∩ Z)` at a point `Q` over the centre, for every form `F`.
* `PlaneCurves.Projective.IsExcellentPosition.finsum_intersectionNumber_pointsOverCentre`: these
  intersection numbers add up to `r`.
* `PlaneCurves.Projective.IsExcellentPosition.isSimplePoint_of_mem_pointsOverCentre`: if `r ≤ 1` or
  `P` is an ordinary multiple point, the points over the centre are simple points of `F'`.

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

/-! ### The points over the centre: the blow-up chart

In the chart `y = 1`, with coordinates `(x, z)`, the points over the centre `[α : 1 : 0]` are the
points `(α, 0)`, `α ≠ 0`. For a form `F` of degree `n` in excellent position, with
`f = F(x, y, 1)` and `r = m_{[0:0:1]}(F)`, Fulton's identity `F'(x, 1, xz) = x^(n - r) g(z, x)`,
with `g` the strict transform of `f` under the blow-up of the origin, shows that the blow-up
chart `(x, z) ↦ (x, xz)`, followed by the swap of the two variables, identifies the local ring of
`C'` at `(α, 0)` with that of `g` at `(0, α)`: near the centre, the quadratic transformation is the
blow-up. This is Fulton's step (5), and gives (7) (2) (c). -/

section PointsOverCentre

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {n : ℕ} {α : k}

namespace IsExcellentPosition

/-- **The quadratic transform near the centre, through the blow-up** (Fulton's step (5)). For a
form `F` of degree `n` in excellent position, `F'(x, 1, xz) = x^(n - r) g(z, x)`, where `F'` is
the proper transform, `r = m_{[0:0:1]}(F)` and `g` is the strict transform of `F(x, y, 1)` under
the blow-up of the origin. -/
theorem dehomogenize_properTransform_blowup (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) :
    aeval ![X 0, X 0 * X 1] (dehomogenize 1 (properTransform F)) =
      X 0 ^ (n - (mult F (fundamentalPoint 2)).toNat) *
        rename (Equiv.swap 0 1) (Affine.blowupStrictTransform (dehomogenize 2 F)) := by
  set r := (mult F (fundamentalPoint 2)).toNat
  have hr : r = ((dehomogenize 2 F).orderAt 0).toNat := by
    rw [← mult_fundamentalPoint_eq_orderAt hF]
  have hrn : r ≤ n := ENat.toNat_le_of_le_natCast (mult_le_degree hF h.ne_zero _)
  have hX : (Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin 2) k) 1 1 X 2) = X 1 := rfl
  let φ : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 2) k :=
    (aeval ![X 0, X 0 * X 1]).comp (dehomogenize 1)
  have e1 : φ.comp quadraticTransform =
      aeval fun i ↦ X 0 * (![X 1, X 0 * X 1, 1] i : MvPolynomial (Fin 2) k) := by
    ext i
    fin_cases i <;> simp [φ, quadraticTransform_def, Fin.insertNth_apply_below, hX]
  have e2 : ((rename (Equiv.swap (0 : Fin 2) 1)).comp (aeval ![X 0, X 0 * X 1])).comp
      (dehomogenize 2) = aeval ![X 1, X 0 * X 1, (1 : MvPolynomial (Fin 2) k)] := by
    ext i
    fin_cases i <;> simp [Fin.insertNth_apply_below, mul_comm]
  have h1 : φ (quadraticTransform F) = X 0 ^ n *
      rename (Equiv.swap 0 1) (aeval ![X 0, X 0 * X 1] (dehomogenize 2 F)) := by
    rw [← AlgHom.comp_apply, e1, hF.aeval_mul_left, ← e2]
    rfl
  have h2 := congrArg φ (h.quadraticTransform_eq hF)
  rw [h1, map_mul, map_pow, ← Affine.X_pow_mul_blowupStrictTransform, ← hr, map_mul, map_pow,
    rename_X] at h2
  have hX2 : φ (X 2) = X 0 * X 1 := by simp [φ, hX]
  rw [hX2] at h2
  refine mul_left_cancel₀ (pow_ne_zero r (mul_ne_zero (X_ne_zero (0 : Fin 2)) (X_ne_zero 1))) ?_
  change (X 0 * X 1) ^ r * φ _ = _
  rw [← h2]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hrn
  simp only [Nat.add_sub_cancel_left, Equiv.swap_apply_left]
  ring

/-- The values at the points of the exceptional line: `F'(α, 1, 0) = α^(n - r) g(0, α)`, with `g`
the strict transform of `F(x, y, 1)` under the blow-up of the origin and `r = m_{[0:0:1]}(F)`. -/
theorem eval_dehomogenize_properTransform (h : IsExcellentPosition F) (hF : F.IsHomogeneous n)
    (α : k) :
    eval ![α, 0] (dehomogenize 1 (properTransform F)) =
      α ^ (n - (mult F (fundamentalPoint 2)).toNat) *
        eval ![0, α] (Affine.blowupStrictTransform (dehomogenize 2 F)) := by
  have h' := congrArg (eval ![α, 0]) (h.dehomogenize_properTransform_blowup hF)
  have e1 : eval ![α, 0] (aeval ![X 0, X 0 * X 1] (dehomogenize 1 (properTransform F))) =
      eval ![α, 0] (dehomogenize 1 (properTransform F)) := by
    rw [← coe_aeval_eq_eval]
    change aeval _ (aeval _ _) = aeval _ _
    rw [← AlgHom.comp_apply, comp_aeval]
    congr 2
    ext i : 1
    fin_cases i <;> simp
  have e2 : (![α, 0] ∘ Equiv.swap (0 : Fin 2) 1) = ![0, α] := by
    ext i : 1
    fin_cases i <;> simp
  rwa [e1, eval_mul, eval_pow, eval_X, eval_rename, e2] at h'

end IsExcellentPosition

/-- The localization `k[x, z][1/x]`. -/
local notation "𝓛₀[" k "]" => Localization.Away (X 0 : MvPolynomial (Fin 2) k)
/-- The localization `k[x, z][1/z]`. -/
local notation "𝓛₁[" k "]" => Localization.Away (X 1 : MvPolynomial (Fin 2) k)

/-- The swap of the two variables, `k[x, z][1/x] ≅ k[x, z][1/z]`. -/
private noncomputable def swapAway : 𝓛₀[k] ≃ₐ[k] 𝓛₁[k] :=
  IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers (X 0)) (T := Submonoid.powers (X 1))
    _ _ (renameEquiv k (Equiv.swap (0 : Fin 2) 1)) (by simp [Submonoid.map_powers])

/-- The blow-up chart followed by the swap of the variables. -/
private noncomputable def overCentreAway : 𝓛₀[k] ≃ₐ[k] 𝓛₁[k] :=
  (Affine.blowupChartEquiv k).trans swapAway

private theorem overCentreAway_algebraMap (p : MvPolynomial (Fin 2) k) :
    overCentreAway (algebraMap (MvPolynomial (Fin 2) k) 𝓛₀[k] p) =
      algebraMap (MvPolynomial (Fin 2) k) 𝓛₁[k]
        (rename (Equiv.swap 0 1) (aeval ![X 0, X 0 * X 1] p)) := by
  rw [overCentreAway, AlgEquiv.trans_apply, Affine.blowupChartEquiv_algebraMap, swapAway,
    IsLocalization.algEquivOfAlgEquiv_eq]
  rfl

private theorem awayLift_comp_overCentreAway (hα : α ≠ 0) :
    (Localization.awayLift (eval ![0, α]) (X 1 : MvPolynomial (Fin 2) k)
        (isUnit_iff_ne_zero.2 (by simpa using hα))).comp
        ((overCentreAway (k := k)) : 𝓛₀[k] →+* 𝓛₁[k]) =
      Localization.awayLift (eval ![α, 0]) (X 0 : MvPolynomial (Fin 2) k)
        (isUnit_iff_ne_zero.2 (by simpa using hα)) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (X 0 : MvPolynomial (Fin 2) k)) <|
    RingHom.ext fun p ↦ ?_
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, overCentreAway_algebraMap,
    Localization.awayLift, IsLocalization.Away.lift_eq, eval_rename]
  rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
  change aeval (![0, α] ∘ Equiv.swap 0 1) (aeval ![X 0, X 0 * X 1] p) = aeval ![α, 0] p
  rw [← AlgHom.comp_apply, comp_aeval]
  congr 2
  ext i : 1
  fin_cases i <;> simp

private theorem overCentreAway_dehomogenize_properTransform (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) :
    overCentreAway (algebraMap _ 𝓛₀[k] (dehomogenize 1 (properTransform F))) =
      ((IsLocalization.Away.algebraMap_isUnit (S := 𝓛₁[k]) (X 1 : MvPolynomial (Fin 2) k)).pow
        (n - (mult F (fundamentalPoint 2)).toNat)).unit *
        algebraMap _ 𝓛₁[k] (Affine.blowupStrictTransform (dehomogenize 2 F)) := by
  rw [overCentreAway_algebraMap, h.dehomogenize_properTransform_blowup hF, map_mul, map_pow,
    rename_X, rename_rename, Equiv.swap_apply_left, IsUnit.unit_spec, map_mul, map_pow]
  rw [show (⇑(Equiv.swap (0 : Fin 2) 1) ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) = id from
    funext (Equiv.swap_apply_self 0 1), rename_id_apply]

private theorem eval_X_zero_vec_ne_zero (hα : α ≠ 0) :
    eval ![α, 0] (X 0 : MvPolynomial (Fin 2) k) ≠ 0 := by simpa using hα

private theorem eval_X_one_vec_ne_zero (hα : α ≠ 0) :
    eval ![0, α] (X 1 : MvPolynomial (Fin 2) k) ≠ 0 := by simpa using hα

namespace IsExcellentPosition

/-- **Near the centre the quadratic transformation is the blow-up.** For a curve in excellent
position and `α ≠ 0`, the local ring of `C'` at the point over the centre `[α : 1 : 0]`, which is
`(α, 0)` in the chart `y = 1`, is isomorphic to the local ring at `(0, α)` of the strict transform
`g` of the blow-up of `F(x, y, 1)` at the origin. -/
noncomputable def localRingEquivPointsOverCentre (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) (hα : α ≠ 0) :
    (localRing k ![α, 0] ⧸
        span {algebraMap _ (localRing k ![α, 0]) (dehomogenize 1 (properTransform F))}) ≃ₐ[k]
      (localRing k ![0, α] ⧸ span {(algebraMap _ (localRing k ![0, α])
        (Affine.blowupStrictTransform (dehomogenize 2 F)))}) :=
  quotientEquivOfAway overCentreAway (eval_X_zero_vec_ne_zero hα) (eval_X_one_vec_ne_zero hα)
    (awayLift_comp_overCentreAway hα) _ (overCentreAway_dehomogenize_properTransform h hF)

end IsExcellentPosition

private theorem mk_vec_one_zero_mem_affineOpen (α : k) :
    mk k ![α, 1, 0] (by simp) ∈ affineOpen 1 :=
  (mk_mem_affineOpen_iff 1 _ _).2 (by simp)

private theorem affineChart_mk_vec_one_zero (α : k) :
    affineChart 1 (mk k ![α, 1, 0] (by simp)) = ![α, 0] := by
  rw [affineChart_mk]
  ext j : 1
  fin_cases j <;> simp [Fin.succAbove]

namespace IsExcellentPosition

/-- At a point `[α : 1 : 0]`, `α ≠ 0`, of the exceptional line `V(Z)`, the intersection number of
`C'` with `V(Z)` is that of the strict transform `g` of the blow-up of `F(x, y, 1)` at the origin
with the exceptional line `x = 0` at `(0, α)`. -/
theorem intersectionNumber_properTransform_X_two_mk (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) (hα : α ≠ 0) :
    intersectionNumber (mk k ![α, 1, 0] (by simp)) (properTransform F) (X 2) =
      Affine.intersectionNumber ![0, α] (Affine.blowupStrictTransform (dehomogenize 2 F))
        (X 0) := by
  rw [intersectionNumber_eq_affine (h.isHomogeneous_properTransform hF) (isHomogeneous_X k 2)
    (mk_vec_one_zero_mem_affineOpen α), affineChart_mk_vec_one_zero, dehomogenize_X,
    show (Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin 2) k) 1 1 X 2) = X 1 from rfl,
    Affine.intersectionNumber_def, Affine.intersectionNumber_def]
  set E := localRingEquivOfAway overCentreAway (eval_X_zero_vec_ne_zero hα)
    (eval_X_one_vec_ne_zero hα) (awayLift_comp_overCentreAway hα)
  refine (Ideal.length_quotient_span_pair_eq_of_ringEquiv E.toRingEquiv ?_ ?_).symm
  · rw [AlgEquiv.coe_toRingEquiv, localRingEquivOfAway_algebraMap,
      overCentreAway_dehomogenize_properTransform h hF, map_mul, IsUnit.unit_spec, map_pow,
      localRing.ofAway_algebraMap, localRing.ofAway_algebraMap]
    exact associated_unit_mul_left _ _
      ((localRing.isUnit_algebraMap_iff.2 (eval_X_one_vec_ne_zero hα)).pow _)
  · rw [AlgEquiv.coe_toRingEquiv, localRingEquivOfAway_algebraMap,
      overCentreAway_algebraMap]
    simp only [aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero, map_mul, rename_X,
      Equiv.swap_apply_left, Equiv.swap_apply_right, localRing.ofAway_algebraMap]
    exact associated_unit_mul_left _ _
      (localRing.isUnit_algebraMap_iff.2 (eval_X_one_vec_ne_zero hα))

/-- **The multiplicity at a point over the centre.** For a curve in excellent position and
`α ≠ 0`, the multiplicity of `C'` at `[α : 1 : 0]` is the multiplicity at `(0, α)` of the strict
transform `g` of the blow-up of `F(x, y, 1)` at the origin. -/
theorem mult_properTransform_mk_eq_orderAt_blowupStrictTransform (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) (hα : α ≠ 0) :
    mult (properTransform F) (mk k ![α, 1, 0] (by simp)) =
      (Affine.blowupStrictTransform (dehomogenize 2 F)).orderAt ![0, α] := by
  rw [mult_eq_orderAt_dehomogenize (h.isHomogeneous_properTransform hF)
    (mk_vec_one_zero_mem_affineOpen α), affineChart_mk_vec_one_zero]
  have he := h.eval_dehomogenize_properTransform hF α
  by_cases hg : eval ![0, α] (Affine.blowupStrictTransform (dehomogenize 2 F)) = 0
  · rw [hg, mul_zero] at he
    exact Affine.orderAt_eq_of_ringEquiv he hg
      (h.localRingEquivPointsOverCentre hF hα).toRingEquiv
  · rw [orderAt_eq_zero_iff.2 hg, orderAt_eq_zero_iff.2]
    rw [he]
    exact mul_ne_zero (pow_ne_zero _ hα) hg

/-- In excellent position, neither `x` nor `y` is tangent at the origin to `F(x, y, 1)`: this is
good position at `[0 : 0 : 1]`. -/
theorem not_isTangentAt_dehomogenize_X (h : IsExcellentPosition F) (hF : F.IsHomogeneous n)
    (i : Fin 2) : ¬ Affine.IsTangentAt (dehomogenize 2 F) 0 (X i) := fun hT ↦
  isGoodPosition_def.1 h.isGoodPosition 2 (Fin.succAbove 2 i) (Fin.succAbove_ne 2 i).symm
    ((isTangentAt_fundamentalPoint_two_iff_dvd_leadingFormAt hF i).2
      (Affine.isTangentAt_def.1 hT).2.2)

private theorem ne_zero_of_eval_blowupStrictTransform_eq_zero (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) {α : k}
    (h0 : eval ![0, α] (Affine.blowupStrictTransform (dehomogenize 2 F)) = 0) : α ≠ 0 := by
  rintro rfl
  refine h.not_isTangentAt_dehomogenize_X hF 1 ?_
  simpa using (Affine.eval_zero_blowupStrictTransform_eq_zero_iff
    (dehomogenize_ne_zero_of_isHomogeneous 2 hF h.ne_zero) 0).1 h0

/-- **The points over the centre through the blow-up.** For a curve in excellent position, the
points over the centre are the points `[α : 1 : 0]` for the points `(0, α)` of the strict
transform `g` of the blow-up of `F(x, y, 1)` at the origin on the exceptional line `x = 0`. -/
theorem mem_pointsOverCentre_iff_eval_blowupStrictTransform (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) {Q : ℙ k (Fin 3 → k)} :
    Q ∈ pointsOverCentre F ↔ ∃ α : k, Q = mk k ![α, 1, 0] (by simp) ∧
      eval ![0, α] (Affine.blowupStrictTransform (dehomogenize 2 F)) = 0 := by
  rw [h.mem_pointsOverCentre_iff hF]
  simp_rw [← Affine.eval_zero_blowupStrictTransform]
  exact ⟨fun ⟨α, _, hQ, h0⟩ ↦ ⟨α, hQ, h0⟩, fun ⟨α, hQ, h0⟩ ↦
    ⟨α, h.ne_zero_of_eval_blowupStrictTransform_eq_zero hF h0, hQ, h0⟩⟩

end IsExcellentPosition

/-- **A point over the centre has multiplicity at most its intersection number with the
exceptional line**: `m_Q(F') ≤ I(Q, F' ∩ Z)` for `Q` over the centre. -/
theorem mult_le_intersectionNumber_of_mem_pointsOverCentre (hF : F.IsHomogeneous n)
    {Q : ℙ k (Fin 3 → k)} (hQ : Q ∈ pointsOverCentre F) :
    mult (properTransform F) Q ≤ intersectionNumber Q (properTransform F) (X 2) := by
  have hQ' : Q ∈ zeroLocus {properTransform F, X 2} := by
    rw [pointsOverCentre_def] at hQ
    exact hQ.1
  have h2 : eval Q.rep (X 2 : MvPolynomial (Fin 3) k) = 0 :=
    (mem_zeroLocus_iff_eval_rep (by simpa using ⟨⟨_, hF.properTransform⟩,
      ⟨1, isHomogeneous_X k 2⟩⟩)).1 hQ' _ (by simp)
  simpa [mult_eq_one_of_isHomogeneous_one (isHomogeneous_X k 2) (X_ne_zero 2) h2] using
    mul_mult_le_intersectionNumber hF.properTransform (isHomogeneous_X k 2) (P := Q)

namespace IsExcellentPosition

/-- **The points over the centre count the multiplicity of the centre.** For a curve in excellent
position over an algebraically closed field, the intersection numbers of `C'` with the
exceptional line `V(Z)` at the points over the centre add up to `r = m_P(F)`,
`P = [0 : 0 : 1]`. -/
theorem finsum_intersectionNumber_pointsOverCentre [IsAlgClosed k] (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) :
    ∑ᶠ Q ∈ pointsOverCentre F, intersectionNumber Q (properTransform F) (X 2) =
      mult F (fundamentalPoint 2) := by
  classical
  set f := dehomogenize 2 F
  have hf : f ≠ 0 := dehomogenize_ne_zero_of_isHomogeneous 2 hF h.ne_zero
  have hfib := Affine.eval_zero_blowupStrictTransform_eq_zero_iff hf
  obtain ⟨A, hA, -⟩ :=
    Affine.exists_finset_eval_zero_blowupStrictTransform hf (h.not_isTangentAt_dehomogenize_X hF 0)
  have hA0 (α : k) (hα : α ∈ A) : α ≠ 0 :=
    h.ne_zero_of_eval_blowupStrictTransform_eq_zero hF ((hA α).1 hα)
  have himage : pointsOverCentre F = (fun α : k ↦ mk k ![α, 1, 0] (by simp)) '' ↑A := by
    ext Q
    simp only [h.mem_pointsOverCentre_iff_eval_blowupStrictTransform hF, Set.mem_image,
      Finset.mem_coe, hA]
    exact ⟨fun ⟨α, hQ, h0⟩ ↦ ⟨α, h0, hQ.symm⟩, fun ⟨α, h0, hQ⟩ ↦ ⟨α, hQ.symm, h0⟩⟩
  have hinj : Set.InjOn (fun α : k ↦ mk k ![α, 1, 0] (by simp)) ↑A := by
    intro α _ β _ hαβ
    obtain ⟨a, ha⟩ := (mk_eq_mk_iff' _ _ _ _ _).1 hαβ
    have h1 := congrFun ha 1
    have h0 := congrFun ha 0
    simp only [Pi.smul_apply, Matrix.cons_val_one, Matrix.cons_val_zero, smul_eq_mul,
      mul_one] at h0 h1
    rw [← h0, h1, one_mul]
  rw [himage, finsum_mem_image hinj, finsum_mem_coe_finset,
    Finset.sum_congr rfl fun α hα ↦ (h.intersectionNumber_properTransform_X_two_mk hF
      (hA0 α hα)).trans (Affine.intersectionNumber_blowupStrictTransform_X_zero hf α),
    ← Nat.cast_sum, ← Finset.sum_image (f := fun L ↦ Affine.tangentMultiplicity f 0 L)
      fun α _ β _ h ↦ X_one_sub_C_mul_X_zero_injective h,
    mult_fundamentalPoint_eq_orderAt hF]
  refine Affine.sum_tangentMultiplicity ?_ ?_ ?_ hf
  · simp only [Finset.mem_image]
    rintro _ ⟨α, hα, rfl⟩
    exact (hfib α).1 ((hA α).1 hα)
  · simp only [Finset.coe_image, Set.Pairwise, Set.mem_image, Finset.mem_coe]
    rintro _ ⟨α, -, rfl⟩ _ ⟨β, -, rfl⟩ hne hαβ
    exact hne (by rw [associated_X_one_sub_C_mul_X_zero_iff.1 hαβ])
  · intro L hL
    obtain ⟨α, hα⟩ := hL.exists_associated_X_one_sub_C_mul_X_zero
      (h.not_isTangentAt_dehomogenize_X hF 0)
    refine ⟨_, Finset.mem_image_of_mem _ ((hA α).2 ((hfib α).2 ?_)), hα⟩
    exact Affine.isTangentAt_def.2 ⟨isHomogeneous_X_one_sub_C_mul_X_zero α,
      X_one_sub_C_mul_X_zero_ne_zero α, hα.symm.dvd.trans hL.dvd⟩

/-- **The points over an ordinary centre are simple.** For a curve in excellent position whose
centre `P = [0 : 0 : 1]` is a point of multiplicity at most one or an ordinary multiple point,
the points over the centre are simple points of `C'`. -/
theorem isSimplePoint_of_mem_pointsOverCentre (h : IsExcellentPosition F) (hF : F.IsHomogeneous n)
    (hP : mult F (fundamentalPoint 2) ≤ 1 ∨ IsOrdinaryMultiplePoint F (fundamentalPoint 2))
    {Q : ℙ k (Fin 3 → k)} (hQ : Q ∈ pointsOverCentre F) :
    IsSimplePoint (properTransform F) Q := by
  obtain ⟨α, rfl, h0⟩ := (h.mem_pointsOverCentre_iff_eval_blowupStrictTransform hF).1 hQ
  have hf : dehomogenize 2 F ≠ 0 := dehomogenize_ne_zero_of_isHomogeneous 2 hF h.ne_zero
  have hT := (Affine.eval_zero_blowupStrictTransform_eq_zero_iff hf α).1 h0
  rw [isSimplePoint_def, h.mult_properTransform_mk_eq_orderAt_blowupStrictTransform hF
    (h.ne_zero_of_eval_blowupStrictTransform_eq_zero hF h0)]
  rcases hP with hle | hord
  · refine le_antisymm ?_ (Order.one_le_iff_pos.2 (orderAt_pos_iff.2 h0))
    calc _ ≤ (Affine.tangentMultiplicity (dehomogenize 2 F) 0 (X 1 - C α * X 0) : ℕ∞) :=
          Affine.orderAt_blowupStrictTransform_le_tangentMultiplicity hf α
      _ ≤ (dehomogenize 2 F).orderAt 0 := Affine.tangentMultiplicity_le_orderAt hf
          (isHomogeneous_X_one_sub_C_mul_X_zero α) (X_one_sub_C_mul_X_zero_ne_zero α)
      _ ≤ 1 := by rwa [← mult_fundamentalPoint_eq_orderAt hF]
  · rw [isOrdinaryMultiplePoint_iff_affine hF (fundamentalPoint_mem_affineOpen_iff.2 rfl),
      affineChart_fundamentalPoint] at hord
    exact Affine.isSimplePoint_iff_orderAt_eq_one.1 (hord.isSimplePoint_blowupStrictTransform hT).1

end IsExcellentPosition

end PointsOverCentre

end PlaneCurves.Projective

end
