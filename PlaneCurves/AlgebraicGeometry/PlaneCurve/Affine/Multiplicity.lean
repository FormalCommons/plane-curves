/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.RingTheory.MvPolynomial.LeadingForm
public import TauCeti.RingTheory.MvPolynomial.LocalOrder

/-!
# Simple and multiple points of affine plane curves

An affine plane curve is a nonzero `F : MvPolynomial (Fin 2) k`, and its multiplicity
`m_P(F)` at a point `P` is Tau Ceti's `MvPolynomial.orderAt F P`. A point `P` of `F` is
*simple* if some partial derivative of `F` does not vanish at `P`, and *multiple* if
`m_P(F) ≥ 2`.

## Main definitions

* `PlaneCurves.Affine.IsSimplePoint F P`: `F(P) = 0` and `F_X(P) ≠ 0` or `F_Y(P) ≠ 0`.
* `PlaneCurves.Affine.IsMultiplePoint F P`: `2 ≤ m_P(F)`.

## Main results

* `PlaneCurves.Affine.isSimplePoint_iff_orderAt_eq_one`: `P` is simple exactly when
  `m_P(F) = 1`; `PlaneCurves.Affine.isSimplePoint_of_totalDegree_eq_one`: a line through `P`
  is smooth at `P`.
* `PlaneCurves.Affine.isMultiplePoint_iff_eval_pderiv`: `P` is multiple exactly when `F` and
  both partial derivatives vanish at `P`;
  `PlaneCurves.Affine.IsMultiplePoint.not_associated_X_sub_C`: then `F` is not the line
  `Xᵢ = Pᵢ`.
* `PlaneCurves.Affine.isSimplePoint_mul_iff`: `P` is simple on `FG` exactly when it is simple
  on one factor and not on the other.
* `PlaneCurves.Affine.isSimplePoint_prod_pow_iff`: `P` is simple on `∏ᵢ Fᵢ ^ eᵢ` exactly when
  it is simple on one `Fᵢ`, with `eᵢ = 1`, and lies on no other factor.
* `PlaneCurves.Affine.isSimplePoint_taylor_iff`,
  `PlaneCurves.Affine.isSimplePoint_linearSubst_iff`: invariance under translations and
  invertible linear changes of coordinates.
* `PlaneCurves.Affine.orderAt_affine_change`: an affine change of coordinates `T` with
  `T(Q) = P` preserves the multiplicity and carries the leading form at `P` to the leading form
  at `Q`.
* `PlaneCurves.Affine.multiplicity_simple_points`: the multiplicity of an affine plane curve and
  its simple points, as in §3.1 of Fulton.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.1
-/

public section

namespace PlaneCurves.Affine

open MvPolynomial

variable {R : Type*}

section CommSemiring

variable [CommSemiring R] {F G : MvPolynomial (Fin 2) R} {P : Fin 2 → R}

/-- A point `P` is a *simple point* of the plane curve `F` if `F(P) = 0` and one of the partial
derivatives `F_X`, `F_Y` does not vanish at `P`. -/
def IsSimplePoint (F : MvPolynomial (Fin 2) R) (P : Fin 2 → R) : Prop :=
  eval P F = 0 ∧ ∃ i, eval P (pderiv i F) ≠ 0

theorem isSimplePoint_def :
    IsSimplePoint F P ↔ eval P F = 0 ∧ ∃ i, eval P (pderiv i F) ≠ 0 :=
  Iff.rfl

/-- A point `P` is a *multiple point* (a singular point) of the plane curve `F` if `F` has
multiplicity at least two at `P`. -/
def IsMultiplePoint (F : MvPolynomial (Fin 2) R) (P : Fin 2 → R) : Prop :=
  2 ≤ F.orderAt P

theorem isMultiplePoint_def : IsMultiplePoint F P ↔ 2 ≤ F.orderAt P :=
  Iff.rfl

/-- A point is simple exactly when the multiplicity there is one. -/
theorem isSimplePoint_iff_orderAt_eq_one : IsSimplePoint F P ↔ F.orderAt P = 1 :=
  orderAt_eq_one_iff.symm

theorem IsSimplePoint.eval_eq_zero (h : IsSimplePoint F P) : eval P F = 0 :=
  h.1

theorem IsSimplePoint.ne_zero (h : IsSimplePoint F P) : F ≠ 0 := by
  rintro rfl
  simp [isSimplePoint_iff_orderAt_eq_one] at h

/-- A point of a curve is multiple exactly when it is not simple. -/
theorem isMultiplePoint_iff_not_isSimplePoint :
    IsMultiplePoint F P ↔ eval P F = 0 ∧ ¬IsSimplePoint F P := by
  rw [isMultiplePoint_def, isSimplePoint_iff_orderAt_eq_one, ← orderAt_pos_iff]
  generalize F.orderAt P = m
  cases m using ENat.recTopCoe with
  | top => simp
  | coe m =>
    norm_cast
    omega

/-- A point is multiple exactly when `F` and both its partial derivatives vanish there. -/
theorem isMultiplePoint_iff_eval_pderiv :
    IsMultiplePoint F P ↔ eval P F = 0 ∧ ∀ i, eval P (pderiv i F) = 0 := by
  rw [isMultiplePoint_iff_not_isSimplePoint, isSimplePoint_def]
  grind

theorem IsMultiplePoint.eval_eq_zero (h : IsMultiplePoint F P) : eval P F = 0 :=
  (isMultiplePoint_iff_eval_pderiv.1 h).1

theorem IsMultiplePoint.not_isSimplePoint (h : IsMultiplePoint F P) : ¬IsSimplePoint F P :=
  (isMultiplePoint_iff_not_isSimplePoint.1 h).2

/-- Every point of the zero polynomial is multiple. -/
@[simp]
theorem isMultiplePoint_zero (P : Fin 2 → R) : IsMultiplePoint 0 P := by
  simp [isMultiplePoint_def]

/-- Associated polynomials have the same simple points. -/
theorem isSimplePoint_iff_of_associated (h : Associated F G) :
    IsSimplePoint F P ↔ IsSimplePoint G P := by
  simp only [isSimplePoint_iff_orderAt_eq_one, orderAt_eq_of_associated h]

/-- Associated polynomials have the same multiple points. -/
theorem isMultiplePoint_iff_of_associated (h : Associated F G) :
    IsMultiplePoint F P ↔ IsMultiplePoint G P := by
  simp only [isMultiplePoint_def, orderAt_eq_of_associated h]

/-- A Taylor shift moves the simple points: `P` is simple on `F(X + a)` exactly when `P + a`
is simple on `F`. -/
@[simp]
theorem isSimplePoint_taylor_iff (a : Fin 2 → R) :
    IsSimplePoint (taylor a F) P ↔ IsSimplePoint F (P + a) := by
  simp only [isSimplePoint_iff_orderAt_eq_one, orderAt_taylor]

/-- A Taylor shift moves the multiple points: `P` is multiple on `F(X + a)` exactly when
`P + a` is multiple on `F`. -/
@[simp]
theorem isMultiplePoint_taylor_iff (a : Fin 2 → R) :
    IsMultiplePoint (taylor a F) P ↔ IsMultiplePoint F (P + a) := by
  simp only [isMultiplePoint_def, orderAt_taylor]

end CommSemiring

section CommRing

variable [CommRing R] {F G : MvPolynomial (Fin 2) R} {P : Fin 2 → R}

/-- An invertible linear change of coordinates moves the simple points: `P` is simple on
`F(M X)` exactly when `M P` is simple on `F`. -/
theorem isSimplePoint_linearSubst_iff {M : Matrix (Fin 2) (Fin 2) R} (hM : IsUnit M.det) :
    IsSimplePoint (linearSubst M F) P ↔ IsSimplePoint F (M.mulVec P) := by
  simp only [isSimplePoint_iff_orderAt_eq_one, orderAt_linearSubst hM]

/-- An invertible linear change of coordinates moves the multiple points: `P` is multiple on
`F(M X)` exactly when `M P` is multiple on `F`. -/
theorem isMultiplePoint_linearSubst_iff {M : Matrix (Fin 2) (Fin 2) R} (hM : IsUnit M.det) :
    IsMultiplePoint (linearSubst M F) P ↔ IsMultiplePoint F (M.mulVec P) := by
  simp only [isMultiplePoint_def, orderAt_linearSubst hM]

/-- An affine change of coordinates `T(x) = M x + c`, with `M` invertible and `T(Q) = P`,
preserves multiplicities: `F^T = F(M X + c)` has order at `Q` the order of `F` at `P`, and its
leading form at `Q` is the leading form of `F` at `P` after the linear change of variables
along `M`, so that the linear part of `T` carries the tangent lines of `F^T` at `Q` to those of
`F` at `P`. -/
theorem orderAt_affine_change {M : Matrix (Fin 2) (Fin 2) R} (hM : IsUnit M.det)
    (c : Fin 2 → R) {Q : Fin 2 → R} (hQ : M.mulVec Q + c = P) (F : MvPolynomial (Fin 2) R) :
    (linearSubst M (taylor c F)).orderAt Q = F.orderAt P ∧
      (linearSubst M (taylor c F)).leadingFormAt Q = linearSubst M (F.leadingFormAt P) := by
  subst hQ
  rw [orderAt_linearSubst hM, orderAt_taylor, leadingFormAt_linearSubst hM, leadingFormAt_taylor]
  exact ⟨rfl, rfl⟩

/-- At a simple point, the leading form is the differential `F_X(P) X + F_Y(P) Y`, so the
tangent line at `P` is `F_X(P) (X - a) + F_Y(P) (Y - b)`. -/
theorem IsSimplePoint.leadingFormAt_eq (h : IsSimplePoint F P) :
    F.leadingFormAt P = ∑ i, eval P (pderiv i F) • X i :=
  leadingFormAt_eq_sum_pderiv (isSimplePoint_iff_orderAt_eq_one.1 h)

/-- At a multiple point `P`, the curve `F` is not, up to a unit, the line `Xᵢ = Pᵢ`, which has
multiplicity one at `P`. -/
theorem IsMultiplePoint.not_associated_X_sub_C [Nontrivial R] (h : IsMultiplePoint F P)
    (i : Fin 2) : ¬Associated F (X i - C (P i)) := fun ha ↦ by
  have h2 := isMultiplePoint_def.1 h
  rw [orderAt_eq_of_associated ha, orderAt_X_sub_C] at h2
  exact absurd h2 (by norm_num)

variable [NoZeroDivisors R]

/-- A point is simple on `FG` exactly when it is simple on one factor and does not lie on the
other. -/
theorem isSimplePoint_mul_iff :
    IsSimplePoint (F * G) P ↔
      IsSimplePoint F P ∧ eval P G ≠ 0 ∨ eval P F ≠ 0 ∧ IsSimplePoint G P := by
  simp only [isSimplePoint_iff_orderAt_eq_one, orderAt_mul_eq_one_iff, orderAt_eq_zero_iff]

/-- A point is simple on `c • F`, for `c ≠ 0`, exactly when it is simple on `F`. -/
@[simp]
theorem isSimplePoint_smul_iff {c : R} (hc : c ≠ 0) :
    IsSimplePoint (c • F) P ↔ IsSimplePoint F P := by
  rw [smul_eq_C_mul, isSimplePoint_mul_iff]
  simp [hc, isSimplePoint_iff_orderAt_eq_one, orderAt_C_of_ne_zero hc]

/-- A point is multiple on `c • F`, for `c ≠ 0`, exactly when it is multiple on `F`. -/
@[simp]
theorem isMultiplePoint_smul_iff {c : R} (hc : c ≠ 0) :
    IsMultiplePoint (c • F) P ↔ IsMultiplePoint F P := by
  rw [isMultiplePoint_def, isMultiplePoint_def, smul_eq_C_mul, orderAt_mul,
    orderAt_C_of_ne_zero hc, zero_add]

/-- A point is simple on `F ^ n` exactly when `n = 1` and it is simple on `F`. -/
theorem isSimplePoint_pow_iff [Nontrivial R] {n : ℕ} :
    IsSimplePoint (F ^ n) P ↔ n = 1 ∧ IsSimplePoint F P := by
  simp only [isSimplePoint_iff_orderAt_eq_one, orderAt_pow]
  generalize F.orderAt P = m
  cases m using ENat.recTopCoe with
  | top => rcases n with _ | n <;> simp
  | coe m =>
    rw [nsmul_eq_mul]
    norm_cast
    exact mul_eq_one

/-- A point is simple on a product `∏ᵢ Fᵢ ^ eᵢ` exactly when it is simple on one `Fᵢ` with
`eᵢ = 1` and lies on no other factor `Fⱼ ^ eⱼ`. -/
theorem isSimplePoint_prod_pow_iff [Nontrivial R] {ι : Type*} (s : Finset ι)
    (F : ι → MvPolynomial (Fin 2) R) (e : ι → ℕ) :
    IsSimplePoint (∏ i ∈ s, F i ^ e i) P ↔
      ∃ i ∈ s, e i = 1 ∧ IsSimplePoint (F i) P ∧ ∀ j ∈ s, j ≠ i → eval P (F j ^ e j) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [isSimplePoint_iff_orderAt_eq_one, orderAt_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, isSimplePoint_mul_iff, ih, isSimplePoint_pow_iff, map_prod,
      Finset.prod_ne_zero_iff]
    constructor
    · rintro (⟨⟨he, hs⟩, h⟩ | ⟨h, i, hi, he, hs, h'⟩)
      · exact ⟨a, Finset.mem_insert_self a s, he, hs, fun j hj hja ↦
          h j ((Finset.mem_insert.1 hj).resolve_left hja)⟩
      · refine ⟨i, Finset.mem_insert_of_mem hi, he, hs, fun j hj hji ↦ ?_⟩
        rcases Finset.mem_insert.1 hj with rfl | hj
        · exact h
        · exact h' j hj hji
    · rintro ⟨i, hi, he, hs, h⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact Or.inl ⟨⟨he, hs⟩, fun j hj ↦ h j (Finset.mem_insert_of_mem hj)
          fun hji ↦ ha (hji ▸ hj)⟩
      · exact Or.inr ⟨h a (Finset.mem_insert_self a s) fun hai ↦ ha (hai ▸ hi), i, hi, he, hs,
          fun j hj ↦ h j (Finset.mem_insert_of_mem hj)⟩

end CommRing

section Field

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 2) k} {P : Fin 2 → k}

/-- A polynomial with total degree one vanishing at `P`, such as a line `aX + bY + c` through
`P`, is smooth at `P`. -/
theorem isSimplePoint_of_totalDegree_eq_one (hF : F.totalDegree = 1) (hP : eval P F = 0) :
    IsSimplePoint F P := by
  have hF0 : F ≠ 0 := by rintro rfl; simp at hF
  rw [isSimplePoint_iff_orderAt_eq_one]
  refine le_antisymm (by simpa [hF] using orderAt_le_totalDegree hF0 P) ?_
  exact Order.one_le_iff_pos.2 (orderAt_pos_iff.2 hP)

/-- **Multiplicity and simple points of an affine plane curve.** Let `F` be a nonzero plane
curve over a field `k` and `P` a point, and write `m_P(F)` for the order of `F` at `P`.

1. `m_P(F) > 0` exactly when `F(P) = 0`; `m_P(λ F) = m_P(F)` for `λ ≠ 0`; `m_P(F) ≤ deg F`.
2. A point `P` of `F` is simple exactly when `m_P(F) = 1`, and then the leading form of `F` at
   `P` is `F_X(P) X + F_Y(P) Y`.
3. `F ∈ I_P ^ n` exactly when `n ≤ m_P(F)`, with `I_P = (X - a, Y - b)`; an affine change of
   coordinates `T(x) = M x + c` with `T(Q) = P` preserves the multiplicity and carries leading
   forms (hence tangent lines) along `M`; and for a polynomial map `T = g` with `T(Q) = P`,
   `m_Q(F^T) ≥ m_P(F)`, with equality when the Jacobian matrix of `T` at `Q` is invertible
   (Problem 3.8).

Milestone: *Multiplicity and simple points of an affine plane curve*. -/
theorem multiplicity_simple_points (hF : F ≠ 0) :
    (0 < F.orderAt P ↔ eval P F = 0) ∧
    (∀ c : k, c ≠ 0 → (c • F).orderAt P = F.orderAt P) ∧
    F.orderAt P ≤ F.totalDegree ∧
    (eval P F = 0 → (IsSimplePoint F P ↔ F.orderAt P = 1)) ∧
    (IsSimplePoint F P → F.leadingFormAt P = ∑ i, eval P (pderiv i F) • X i) ∧
    (∀ n : ℕ, F ∈ vanishingIdeal k {P} ^ n ↔ (n : ℕ∞) ≤ F.orderAt P) ∧
    (∀ (M : Matrix (Fin 2) (Fin 2) k) (c Q : Fin 2 → k), IsUnit M.det → M.mulVec Q + c = P →
      (linearSubst M (taylor c F)).orderAt Q = F.orderAt P ∧
      (linearSubst M (taylor c F)).leadingFormAt Q = linearSubst M (F.leadingFormAt P)) ∧
    (∀ (g : Fin 2 → MvPolynomial (Fin 2) k) (Q : Fin 2 → k), (fun i ↦ eval Q (g i)) = P →
      F.orderAt P ≤ (aeval g F).orderAt Q ∧
      (IsUnit (Matrix.of fun i j ↦ eval Q (pderiv j (g i))).det →
        (aeval g F).orderAt Q = F.orderAt P)) := by
  refine ⟨orderAt_pos_iff, fun c hc ↦ ?_, orderAt_le_totalDegree hF P,
    fun _ ↦ isSimplePoint_iff_orderAt_eq_one, IsSimplePoint.leadingFormAt_eq,
    mem_pow_vanishingIdeal_singleton_iff F P, fun M c Q hM hQ ↦ orderAt_affine_change hM c hQ F,
    fun g Q hQ ↦ ⟨hQ ▸ orderAt_le_orderAt_aeval g Q F, fun hg ↦ ?_⟩⟩
  · rw [smul_eq_C_mul, orderAt_mul, orderAt_C_of_ne_zero hc, zero_add]
  · rw [orderAt_aeval_eq_of_isUnit_det hF hg, hQ]

/- The parabola `Y = X²` is smooth at the origin. -/
example : IsSimplePoint (X 1 - X 0 ^ 2 : MvPolynomial (Fin 2) k) 0 :=
  ⟨by simp, 1, by simp [pderiv_X]⟩

/- The node `XY = 0` has a multiple point at the origin. -/
example : IsMultiplePoint (X 0 * X 1 : MvPolynomial (Fin 2) k) 0 := by
  rw [isMultiplePoint_iff_eval_pderiv]
  refine ⟨by simp, fun i ↦ ?_⟩
  fin_cases i <;> simp [pderiv_X]

/- The converse of Problem 3.8 fails: for `T = (X², Y)` and `F = Y - X²`, the Jacobian matrix of
`T` at the origin is singular, but `m_0(F^T) = m_0(F) = 1`. -/
example :
    ¬IsUnit (Matrix.of fun i j ↦
      eval 0 (pderiv j ((![X 0 ^ 2, X 1] : Fin 2 → MvPolynomial (Fin 2) k) i))).det ∧
      (aeval ![X 0 ^ 2, X 1] (X 1 - X 0 ^ 2 : MvPolynomial (Fin 2) k)).orderAt (0 : Fin 2 → k) =
        (X 1 - X 0 ^ 2 : MvPolynomial (Fin 2) k).orderAt (0 : Fin 2 → k) := by
  refine ⟨by simp [Matrix.det_fin_two, pderiv_X], ?_⟩
  rw [orderAt_eq_one_of_eval_pderiv_ne_zero (i := 1) (by simp) (by simp [pderiv_X]),
    orderAt_eq_one_of_eval_pderiv_ne_zero (i := 1) (by simp) (by simp [pderiv_X])]

end Field

end PlaneCurves.Affine

end
