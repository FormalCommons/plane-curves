/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.RingTheory.MvPolynomial.LeadingForm
public import TauCeti.Algebra.Field.Fin.Tuple
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization

/-!
# The order and leading form of a form at a point and in an affine chart

For a form `F` in `n + 1` variables, the order of vanishing `F.orderAt v` at a vector `v`
(Tau Ceti's `MvPolynomial.orderAt`) depends only on the line through `v`, and it is the order of
vanishing of the dehomogenization `F(X₀, …, 1, …, Xₙ)` at the corresponding affine point. This is
the chart-free description of the multiplicity of a projective hypersurface at a point. Likewise
the leading form of `F` at `v` is, up to a unit, independent of `v` on its line, and it is the
leading form of the dehomogenization written in the coordinates `X (i.succAbove j) - aⱼ Xᵢ`.

## Main results

* `MvPolynomial.IsHomogeneous.orderAt_smul`: `F.orderAt (c • v) = F.orderAt v` for a unit `c`.
* `MvPolynomial.IsHomogeneous.orderAt_dehomogenize`: the order of `dehomogenize i F` at `a` is
  the order of `F` at `Fin.insertNth i 1 a`.
* `MvPolynomial.IsHomogeneous.orderAt_eq_orderAt_dehomogenize`: over a field, for `v i ≠ 0`, the
  order of `F` at `v` is the order of `dehomogenize i F` at the ratios `v j / v i`.
* `MvPolynomial.IsHomogeneous.associated_leadingFormAt_smul`: over a domain, the leading forms
  of `F` at `c • v` and at `v` are associated, for a unit `c`.
* `MvPolynomial.IsHomogeneous.leadingFormAt_insertNth`: the leading form of `F` at
  `Fin.insertNth i 1 a` is the leading form of `dehomogenize i F` at `a`, with `Yⱼ` replaced by
  `X (i.succAbove j) - aⱼ Xᵢ`.

## Implementation notes

The chart comparison uses the polynomial map `φ(t, y) = t • Fin.insertNth i 1 y`: on a form `F`
of degree `d` it gives `F(φ) = Xᵢ ^ d * F_(i)`, and its Jacobian matrix at every point with
`t = 1` is invertible, so Problem 3.8 of Fulton (`MvPolynomial.orderAt_aeval_eq_of_isUnit_det`)
applies. For leading forms, the linear change of variables along that Jacobian matrix is inverted
by `X (i.succAbove j) ↦ X (i.succAbove j) - aⱼ Xᵢ`, `Xᵢ ↦ Xᵢ`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.1
-/

public section

namespace MvPolynomial

open TauCeti Matrix

variable {R : Type*} [CommRing R] {σ : Type*} {n d : ℕ} {F : MvPolynomial σ R}

/-- A form of degree `d` vanishes to the same order at `c • v` as at `v`, for a unit `c`. -/
theorem IsHomogeneous.orderAt_smul [Finite σ] (hF : F.IsHomogeneous d) {c : R} (hc : IsUnit c)
    (v : σ → R) : F.orderAt (c • v) = F.orderAt v := by
  classical
  have := Fintype.ofFinite σ
  have hM : IsUnit (c • (1 : Matrix σ σ R)).det := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact hc.pow _
  have hv : (c • (1 : Matrix σ σ R)) *ᵥ v = c • v := by rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [← hv, ← orderAt_linearSubst hM, hF.linearSubst_smul,
    linearSubst_one, AlgHom.id_apply, smul_eq_C_mul]
  exact orderAt_eq_of_associated
    ((associated_isUnit_mul_left_iff ((hc.pow d).map C)).2 (Associated.refl F)) v

/-- The polynomial map `(t, y) ↦ t • Fin.insertNth i 1 y`, in coordinates `Xᵢ = t` and
`X (i.succAbove j) = yⱼ`. -/
private noncomputable def coneChart (R : Type*) [CommRing R] (i : Fin (n + 1)) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) R :=
  (X i : MvPolynomial (Fin (n + 1)) R) •
    Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin (n + 1)) R) i 1 fun j ↦ X (i.succAbove j)

private theorem aeval_coneChart {F : MvPolynomial (Fin (n + 1)) R} (hF : F.IsHomogeneous d)
    (i : Fin (n + 1)) :
    aeval (coneChart R i) F = X i ^ d * rename i.succAbove (dehomogenize i F) := by
  have hF' := hF.map (algebraMap R (MvPolynomial (Fin (n + 1)) R))
  rw [aeval_def, ← eval_map, coneChart, hF'.eval_smul, eval_map, ← aeval_def,
    ← AlgHom.comp_apply]
  congr 1
  refine congrArg (· F) (algHom_ext (A := MvPolynomial (Fin (n + 1)) R) fun j ↦ ?_)
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) j <;> simp

private theorem eval_coneChart (i : Fin (n + 1)) (a : Fin n → R) :
    (fun j ↦ eval (Fin.insertNth (α := fun _ ↦ R) i 1 a) (coneChart R i j)) =
      Fin.insertNth (α := fun _ ↦ R) i 1 a := by
  ext j
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) j <;> simp [coneChart]

/-- The Jacobian matrix of `coneChart i` at a point with `Xᵢ = 1` is invertible: it is
`1 + N` with `N` supported in column `i` off the diagonal, so `N * N = 0`. -/
private theorem isUnit_det_jacobian_coneChart (i : Fin (n + 1)) (a : Fin n → R) :
    IsUnit (Matrix.of fun r c ↦ eval (Fin.insertNth (α := fun _ ↦ R) i 1 a)
      (pderiv c (coneChart R i r))).det := by
  set b := Fin.insertNth (α := fun _ ↦ R) i 1 a
  let N : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Matrix.of fun r c ↦
    if c = i ∧ r ≠ i then b r else 0
  have hJ : (Matrix.of fun r c ↦ eval b (pderiv c (coneChart R i r))) = 1 + N := by
    ext r c
    refine Fin.succAboveCases i ?_ (fun r ↦ ?_) r
    · simp [coneChart, N, b, Matrix.one_apply, pderiv_X, Pi.single_apply, eq_comm]
    · have hr : i.succAbove r ≠ i := Fin.succAbove_ne i r
      by_cases hc : c = i
      · subst hc
        simp [coneChart, N, b, pderiv_X, Pi.single_apply, hr]
      · simp [coneChart, N, b, Matrix.one_apply, pderiv_X, Pi.single_apply, Ne.symm hc, eq_comm]
  have hN : N * N = 0 := by
    ext r c
    simp only [Matrix.mul_apply, N, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun s _ ↦ ?_
    by_cases hs : s = i <;> simp [hs]
  refine hJ ▸ Matrix.isUnit_det_of_left_inverse (B := 1 - N) ?_
  rw [sub_mul, mul_add, mul_add, hN]
  simp

/-- The linear change of variables along the Jacobian matrix of `coneChart i` at
`Fin.insertNth i 1 a` fixes `Xᵢ` and sends `X (i.succAbove j)` to `X (i.succAbove j) + aⱼ Xᵢ`. -/
private theorem linearSubst_jacobian_coneChart_X (i : Fin (n + 1)) (a : Fin n → R)
    (r : Fin (n + 1)) :
    linearSubst (Matrix.of fun r c ↦ eval (Fin.insertNth (α := fun _ ↦ R) i 1 a)
      (pderiv c (coneChart R i r))) (X r) =
      Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin (n + 1)) R) i (X i)
        (fun j ↦ X (i.succAbove j) + C (a j) * X i) r := by
  rw [linearSubst_X, Fin.sum_univ_succAbove _ i]
  refine Fin.succAboveCases i ?_ (fun r ↦ ?_) r
  · simp [coneChart, pderiv_X, Pi.single_apply]
  · simp only [Matrix.of_apply, coneChart, Pi.smul_apply, Fin.insertNth_apply_succAbove,
      smul_eq_mul, Derivation.leibniz, pderiv_X, Pi.single_apply, map_add, map_mul, eval_X,
      Fin.insertNth_apply_same, Fin.succAbove_ne, (Fin.succAbove_right_injective (p := i)).eq_iff]
    simp [add_comm]

/-- **The leading form of a form in an affine chart.** For a form `F` over a domain, the leading
form of `F` at the point `Fin.insertNth i 1 a` of the chart `Xᵢ = 1` is the leading form of the
dehomogenization `F_(i)` at `a`, with `Yⱼ` replaced by `X (i.succAbove j) - aⱼ Xᵢ`. -/
theorem IsHomogeneous.leadingFormAt_insertNth [IsDomain R] {F : MvPolynomial (Fin (n + 1)) R}
    (hF : F.IsHomogeneous d) (i : Fin (n + 1)) (a : Fin n → R) :
    F.leadingFormAt (Fin.insertNth (α := fun _ ↦ R) i 1 a) =
      MvPolynomial.aeval (fun j ↦ X (i.succAbove j) - C (a j) * X i)
        ((dehomogenize i F).leadingFormAt a) := by
  have h := leadingFormAt_aeval_of_isUnit_det (p := F) (isUnit_det_jacobian_coneChart (R := R) i a)
  rw [eval_coneChart, aeval_coneChart hF, leadingFormAt_mul,
    leadingFormAt_of_eval_ne_zero (by simp), leadingFormAt_rename Fin.succAbove_right_injective,
    Fin.insertNth_comp_succAbove] at h
  set Φ : MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R :=
    MvPolynomial.aeval (Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin (n + 1)) R) i (X i)
      fun j ↦ X (i.succAbove j) - C (a j) * X i)
  have hΦ : Φ.comp (MvPolynomial.linearSubst (Matrix.of fun r c ↦
      eval (Fin.insertNth (α := fun _ ↦ R) i 1 a) (pderiv c (coneChart R i r)))) =
      AlgHom.id R _ := by
    refine algHom_ext fun r ↦ ?_
    rw [AlgHom.comp_apply, linearSubst_jacobian_coneChart_X]
    refine Fin.succAboveCases i ?_ (fun r ↦ ?_) r <;> simp [Φ]
  have := congrArg Φ h
  rw [← AlgHom.comp_apply, hΦ, AlgHom.id_apply] at this
  rw [← this]
  simp [Φ, aeval_rename, Function.comp_def]

/-- Over a domain, the leading form of a form at `c • v` is associated to its leading form at
`v`, for a unit `c`: the two differ by a power of `c`. -/
theorem IsHomogeneous.associated_leadingFormAt_smul [Finite σ] [IsDomain R]
    (hF : F.IsHomogeneous d) {c : R} (hc : IsUnit c) (v : σ → R) :
    Associated (F.leadingFormAt (c • v)) (F.leadingFormAt v) := by
  classical
  have := Fintype.ofFinite σ
  have hM : IsUnit (c • (1 : Matrix σ σ R)).det := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact hc.pow _
  have hv : (c • (1 : Matrix σ σ R)) *ᵥ v = c • v := by rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  have h := leadingFormAt_linearSubst hM F v
  rw [hv, hF.linearSubst_smul, linearSubst_one, AlgHom.id_apply, leadingFormAt_smul,
    (isHomogeneous_leadingFormAt F (c • v)).linearSubst_smul, linearSubst_one,
    AlgHom.id_apply] at h
  have hu : ∀ (m : ℕ) (x : MvPolynomial σ R), Associated (c ^ m • x) x := fun m x ↦ by
    rw [smul_eq_C_mul]
    exact (associated_isUnit_mul_left_iff ((hc.pow m).map C)).2 (Associated.refl x)
  exact (hu _ _).symm.trans (h ▸ hu _ _)

/-- **The order of a form in an affine chart.** For a form `F` in `n + 1` variables, the order of
the dehomogenization `F(X₀, …, 1, …, Xₙ)` (`1` in position `i`) at `a` is the order of `F` at the
point `Fin.insertNth i 1 a` of the affine chart `Xᵢ = 1`. -/
theorem IsHomogeneous.orderAt_dehomogenize [IsDomain R] {F : MvPolynomial (Fin (n + 1)) R}
    (hF : F.IsHomogeneous d) (i : Fin (n + 1)) (a : Fin n → R) :
    (dehomogenize i F).orderAt a = F.orderAt (Fin.insertNth (α := fun _ ↦ R) i 1 a) := by
  rcases eq_or_ne F 0 with rfl | hF0
  · simp
  have h := orderAt_aeval_eq_of_isUnit_det hF0 (isUnit_det_jacobian_coneChart (R := R) i a)
  rw [eval_coneChart, aeval_coneChart hF, orderAt_mul,
    orderAt_rename Fin.succAbove_right_injective, orderAt_eq_zero_iff.2 (by simp), zero_add] at h
  simpa using h

/-- **The order of a form in an affine chart**, over a field: if `v i ≠ 0`, the order of `F` at
`v` is the order of the dehomogenization of `F` in the variable `i` at the affine point with
coordinates `v j / v i`. -/
theorem IsHomogeneous.orderAt_eq_orderAt_dehomogenize {k : Type*} [Field k]
    {F : MvPolynomial (Fin (n + 1)) k} (hF : F.IsHomogeneous d) {v : Fin (n + 1) → k}
    {i : Fin (n + 1)} (hi : v i ≠ 0) :
    F.orderAt v = (dehomogenize i F).orderAt fun j ↦ v (i.succAbove j) / v i := by
  rw [hF.orderAt_dehomogenize, Fin.insertNth_one_div_eq_inv_smul i v hi,
    hF.orderAt_smul (isUnit_iff_ne_zero.2 (inv_ne_zero hi))]

end MvPolynomial

end
