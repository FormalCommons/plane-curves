/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.Multiplicity
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Multiplicity
public import TauCeti.RingTheory.MvPolynomial.CommonZero

/-!
# Simple and singular points of projective plane curves

A point `P` of `ℙ²` is a *simple point* of the projective plane curve `F` if `m_P(F) = 1`, and a
*multiple* (singular) point if `m_P(F) ≥ 2`. In homogeneous coordinates `P = [v]`, `P` is
multiple exactly when `F` and its three partial derivatives vanish at `v` (Fulton, Problem 5.1),
in every characteristic. At a simple point the tangent line is
`F_X(v) X + F_Y(v) Y + F_Z(v) Z` (Problem 5.4). A curve is *nonsingular* if all its points are
simple; over an algebraically closed field such a curve is irreducible (§5.3, via Tau Ceti's
`TauCeti.irreducible_of_isHomogeneous`).

## Main definitions

* `PlaneCurves.Projective.IsSimplePoint F P`: `m_P(F) = 1`.
* `PlaneCurves.Projective.IsMultiplePoint F P`: `2 ≤ m_P(F)`.
* `PlaneCurves.Projective.IsNonsingular F`: every nonzero `v` with `F(v) = 0` has a partial
  derivative of `F` nonzero at `v`.
* `PlaneCurves.Projective.tangentLine F v`: the linear form `∑ᵢ F_{Xᵢ}(v) Xᵢ`.

## Main results

* `PlaneCurves.Projective.isMultiplePoint_iff_eval_pderiv`: `[v]` is a multiple point of a
  form `F` exactly when `F(v) = F_X(v) = F_Y(v) = F_Z(v) = 0` (Problem 5.1).
* `PlaneCurves.Projective.isSimplePoint_iff_affine`: in an affine chart, simple points are the
  simple points of the dehomogenization.
* `PlaneCurves.Projective.isNonsingular_iff_forall_isSimplePoint`: a form is nonsingular exactly
  when every point of its zero locus is simple.
* `PlaneCurves.Projective.isNonsingular_linearSubst_iff`: nonsingularity is invariant under an
  invertible change of coordinates.
* `PlaneCurves.Projective.IsNonsingular.irreducible`: a nonsingular form of positive degree over
  an algebraically closed field is irreducible.
* `PlaneCurves.Projective.IsSimplePoint.tangentLine_ne_zero`,
  `PlaneCurves.Projective.eval_tangentLine_self`,
  `PlaneCurves.Projective.dehomogenize_tangentLine`: at a simple point the tangent line is a
  nonzero linear form vanishing at the point, whose dehomogenization in a chart is the affine
  tangent line (Problem 5.4).

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.1, §5.3, Problems 5.1, 5.4
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {P : ℙ k (Fin 3 → k)} {d : ℕ}

/-! ### Simple and multiple points -/

/-- A point `P` is a *simple point* of the projective plane curve `F` if `m_P(F) = 1`. -/
def IsSimplePoint (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k)) : Prop :=
  mult F P = 1

theorem isSimplePoint_def : IsSimplePoint F P ↔ mult F P = 1 :=
  Iff.rfl

/-- A point `P` is a *multiple point* (a singular point) of the projective plane curve `F` if
`m_P(F) ≥ 2`. -/
def IsMultiplePoint (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k)) : Prop :=
  2 ≤ mult F P

theorem isMultiplePoint_def : IsMultiplePoint F P ↔ 2 ≤ mult F P :=
  Iff.rfl

/-- `P` is simple exactly when `F` vanishes at `P.rep` and some partial derivative does not. -/
theorem isSimplePoint_iff_eval_rep :
    IsSimplePoint F P ↔ eval P.rep F = 0 ∧ ∃ i, eval P.rep (pderiv i F) ≠ 0 := by
  rw [isSimplePoint_def, mult_def, orderAt_eq_one_iff]

/-- For a form `F`, `[v]` is simple exactly when `F(v) = 0` and some `F_{Xᵢ}(v) ≠ 0`. -/
theorem isSimplePoint_mk_iff (hF : F.IsHomogeneous d) (v : Fin 3 → k) (hv : v ≠ 0) :
    IsSimplePoint F (mk k v hv) ↔ eval v F = 0 ∧ ∃ i, eval v (pderiv i F) ≠ 0 := by
  rw [isSimplePoint_def, mult_mk hF, orderAt_eq_one_iff]

/-- A point is multiple exactly when `F` vanishes at `P.rep` and `P` is not simple. -/
theorem isMultiplePoint_iff_not_isSimplePoint :
    IsMultiplePoint F P ↔ eval P.rep F = 0 ∧ ¬IsSimplePoint F P := by
  rw [isMultiplePoint_def, mult_def, two_le_orderAt_iff, isSimplePoint_iff_eval_rep]
  grind

/-- `P` is multiple exactly when `F` and all its partial derivatives vanish at `P.rep`. -/
theorem isMultiplePoint_iff_eval_rep :
    IsMultiplePoint F P ↔ eval P.rep F = 0 ∧ ∀ i, eval P.rep (pderiv i F) = 0 := by
  rw [isMultiplePoint_def, mult_def, two_le_orderAt_iff]

/-- **Problem 5.1.** For a form `F`, the point `[v]` is a multiple point exactly when
`F(v) = F_X(v) = F_Y(v) = F_Z(v) = 0`. This holds in every characteristic; the condition
`F(v) = 0` cannot be dropped when the characteristic divides the degree (see the example
below). -/
theorem isMultiplePoint_iff_eval_pderiv (hF : F.IsHomogeneous d) (v : Fin 3 → k)
    (hv : v ≠ 0) :
    IsMultiplePoint F (mk k v hv) ↔ eval v F = 0 ∧ ∀ i, eval v (pderiv i F) = 0 := by
  rw [isMultiplePoint_def, mult_mk hF, two_le_orderAt_iff]

/- The condition `F(v) = 0` in `isMultiplePoint_iff_eval_pderiv` is needed: in characteristic
two all partial derivatives of `X²` vanish identically, but `[1 : 0 : 0]` is not on the curve. -/
example {K : Type*} [Field K] [CharP K 2] :
    (∀ i, eval ![1, 0, 0] (pderiv i (X 0 ^ 2 : MvPolynomial (Fin 3) K)) = 0) ∧
    ¬IsMultiplePoint (X 0 ^ 2 : MvPolynomial (Fin 3) K) (mk K ![1, 0, 0] (by simp)) := by
  refine ⟨fun i ↦ ?_, fun h ↦ ?_⟩
  · have h2 : (2 : MvPolynomial (Fin 3) K) = 0 := by
      exact_mod_cast CharP.cast_eq_zero (MvPolynomial (Fin 3) K) 2
    simp [pderiv_X, h2]
  · have := ((isMultiplePoint_iff_eval_pderiv ((isHomogeneous_X K 0).pow 2) _ _).1 h).1
    simp at this

theorem IsSimplePoint.eval_rep_eq_zero (h : IsSimplePoint F P) : eval P.rep F = 0 :=
  (isSimplePoint_iff_eval_rep.1 h).1

theorem IsSimplePoint.ne_zero (h : IsSimplePoint F P) : F ≠ 0 := by
  rintro rfl
  simp [isSimplePoint_def] at h

/-- A simple point of a form lies on the curve. -/
theorem IsSimplePoint.mem_zeroLocus (hF : F.IsHomogeneous d) (h : IsSimplePoint F P) :
    P ∈ zeroLocus {F} :=
  (mult_pos_iff hF).1 (by rw [isSimplePoint_def.1 h]; exact zero_lt_one)

theorem IsMultiplePoint.not_isSimplePoint (h : IsMultiplePoint F P) : ¬IsSimplePoint F P :=
  (isMultiplePoint_iff_not_isSimplePoint.1 h).2

/-- A point of a form's curve is either simple or multiple. -/
theorem isSimplePoint_or_isMultiplePoint (hF : F.IsHomogeneous d) (hP : P ∈ zeroLocus {F}) :
    IsSimplePoint F P ∨ IsMultiplePoint F P := by
  rw [isMultiplePoint_iff_not_isSimplePoint, ← mult_pos_iff_eval_rep, mult_pos_iff hF]
  tauto

/-- Every point is a multiple point of the zero polynomial. -/
@[simp]
theorem isMultiplePoint_zero (P : ℙ k (Fin 3 → k)) : IsMultiplePoint 0 P := by
  simp [isMultiplePoint_def]

/-- Simple points do not change when `F` is multiplied by a nonzero scalar. -/
@[simp]
theorem isSimplePoint_smul_iff {c : k} (hc : c ≠ 0) :
    IsSimplePoint (c • F) P ↔ IsSimplePoint F P := by
  rw [isSimplePoint_def, isSimplePoint_def, mult_smul hc]

/-- Multiple points do not change when `F` is multiplied by a nonzero scalar. -/
@[simp]
theorem isMultiplePoint_smul_iff {c : k} (hc : c ≠ 0) :
    IsMultiplePoint (c • F) P ↔ IsMultiplePoint F P := by
  rw [isMultiplePoint_def, isMultiplePoint_def, mult_smul hc]

/-- A projective change of coordinates moves the simple points: `Q` is simple on `F(M X)`
exactly when `[M v]` is simple on `F`, for `Q = [v]`. -/
theorem isSimplePoint_linearSubst_iff (hF : F.IsHomogeneous d) {M : Matrix (Fin 3) (Fin 3) k}
    (hM : Function.Injective M.mulVecLin) (Q : ℙ k (Fin 3 → k)) :
    IsSimplePoint (linearSubst M F) Q ↔ IsSimplePoint F (map M.mulVecLin hM Q) := by
  rw [isSimplePoint_def, isSimplePoint_def, mult_linearSubst hF hM]

/-- A projective change of coordinates moves the multiple points. -/
theorem isMultiplePoint_linearSubst_iff (hF : F.IsHomogeneous d) {M : Matrix (Fin 3) (Fin 3) k}
    (hM : Function.Injective M.mulVecLin) (Q : ℙ k (Fin 3 → k)) :
    IsMultiplePoint (linearSubst M F) Q ↔ IsMultiplePoint F (map M.mulVecLin hM Q) := by
  rw [isMultiplePoint_def, isMultiplePoint_def, mult_linearSubst hF hM]

/-- In an affine chart `Xᵢ ≠ 0` containing `P`, `P` is a simple point of the form `F` exactly
when its chart point is a simple point of the affine curve `F_(i)`. -/
theorem isSimplePoint_iff_affine (hF : F.IsHomogeneous d) {i : Fin 3} (hP : P ∈ affineOpen i) :
    IsSimplePoint F P ↔ Affine.IsSimplePoint (dehomogenize i F) (affineChart i P) := by
  rw [isSimplePoint_def, Affine.isSimplePoint_iff_orderAt_eq_one,
    mult_eq_orderAt_dehomogenize hF hP]

/-- In an affine chart `Xᵢ ≠ 0` containing `P`, `P` is a multiple point of the form `F` exactly
when its chart point is a multiple point of the affine curve `F_(i)`. -/
theorem isMultiplePoint_iff_affine (hF : F.IsHomogeneous d) {i : Fin 3}
    (hP : P ∈ affineOpen i) :
    IsMultiplePoint F P ↔ Affine.IsMultiplePoint (dehomogenize i F) (affineChart i P) := by
  rw [isMultiplePoint_def, Affine.isMultiplePoint_def, mult_eq_orderAt_dehomogenize hF hP]

/- The node `XY` has a multiple point at `[0 : 0 : 1]`. -/
example : IsMultiplePoint (X 0 * X 1 : MvPolynomial (Fin 3) k) (mk k ![0, 0, 1] (by simp)) := by
  rw [isMultiplePoint_iff_eval_pderiv ((isHomogeneous_X k 0).mul (isHomogeneous_X k 1))]
  refine ⟨by simp, fun i ↦ ?_⟩
  fin_cases i <;> simp [pderiv_X]

/-! ### Nonsingular curves -/

/-- A projective plane curve `F` is *nonsingular* if at every nonzero `v` with `F(v) = 0` some
partial derivative of `F` is nonzero. For a form this says that every point of the curve is
simple (`isNonsingular_iff_forall_isSimplePoint`), and it is the hypothesis of Tau Ceti's
`TauCeti.irreducible_of_isHomogeneous` with `K = k`. -/
def IsNonsingular (F : MvPolynomial (Fin 3) k) : Prop :=
  ∀ v : Fin 3 → k, v ≠ 0 → eval v F = 0 → ∃ i, eval v (pderiv i F) ≠ 0

theorem isNonsingular_def :
    IsNonsingular F ↔ ∀ v : Fin 3 → k, v ≠ 0 → eval v F = 0 → ∃ i, eval v (pderiv i F) ≠ 0 :=
  Iff.rfl

/-- A form is nonsingular exactly when every point of its curve is a simple point. -/
theorem isNonsingular_iff_forall_isSimplePoint (hF : F.IsHomogeneous d) :
    IsNonsingular F ↔ ∀ P ∈ zeroLocus {F}, IsSimplePoint F P := by
  have hS : ∀ f ∈ ({F} : Set (MvPolynomial (Fin 3) k)), ∃ d, f.IsHomogeneous d := by
    simpa using ⟨d, hF⟩
  refine ⟨fun h P hP ↦ ?_, fun h v hv hFv ↦ ?_⟩
  · induction P using Projectivization.ind with | h v hv =>
    have hFv : eval v F = 0 := by simpa using (mk_mem_zeroLocus_iff hS v hv).1 hP
    exact (isSimplePoint_mk_iff hF v hv).2 ⟨hFv, h v hv hFv⟩
  · exact ((isSimplePoint_mk_iff hF v hv).1 (h _ ((mk_mem_zeroLocus_iff hS v hv).2
      (by simpa using hFv)))).2

/-- **Nonsingular projective plane curves are irreducible.** Over an algebraically closed field
`k`, a nonsingular form `F` of degree `d ≥ 1`, that is one whose points are all simple
(`isNonsingular_iff_forall_isSimplePoint`), is irreducible; in particular it has no multiple
component.

Milestone: *Nonsingular projective plane curves are irreducible*. -/
theorem IsNonsingular.irreducible [IsAlgClosed k] (hF : F.IsHomogeneous d) (hd : d ≠ 0)
    (h : IsNonsingular F) : Irreducible F :=
  irreducible_of_isHomogeneous (K := k) (n := 2) le_rfl hF hd (by simpa [coe_aeval_eq_eval])

/-- An invertible change of coordinates preserves nonsingularity. -/
theorem isNonsingular_linearSubst_iff {M : Matrix (Fin 3) (Fin 3) k}
    (hM : Function.Injective M.mulVecLin) :
    IsNonsingular (linearSubst M F) ↔ IsNonsingular F := by
  have hdet : IsUnit M.det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]; exact hM
  have key : ∀ {N : Matrix (Fin 3) (Fin 3) k} {G : MvPolynomial (Fin 3) k}, N.det ≠ 0 →
      IsNonsingular G → IsNonsingular (linearSubst N G) := fun hN hG ↦ by
    rw [isNonsingular_def] at hG ⊢
    intro v hv hv0
    simpa [coe_aeval_eq_eval] using exists_aeval_pderiv_linearSubst_ne_zero (K := k) hN
      (by simpa [coe_aeval_eq_eval] using hG) hv (by simpa [coe_aeval_eq_eval] using hv0)
  refine ⟨fun h ↦ ?_, key hdet.ne_zero⟩
  have := key (N := M⁻¹) (by simpa [Matrix.det_nonsing_inv] using hdet.ne_zero) h
  rwa [linearSubst_nonsing_inv_linearSubst hdet] at this

/- A line is nonsingular. -/
example : IsNonsingular (X 0 : MvPolynomial (Fin 3) k) :=
  fun _ _ _ ↦ ⟨0, by simp [pderiv_X]⟩

/- The node `XY` is singular. -/
example : ¬IsNonsingular (X 0 * X 1 : MvPolynomial (Fin 3) k) := by
  intro h
  obtain ⟨i, hi⟩ := h ![0, 0, 1] (by simp) (by simp)
  fin_cases i <;> simp [pderiv_X] at hi

/-! ### The tangent line at a simple point -/

/-- The *tangent line* of `F` at `v`: the linear form `∑ᵢ F_{Xᵢ}(v) Xᵢ`. At a simple point
`[v]` of a form `F` it is a nonzero linear form vanishing at `[v]`
(`IsSimplePoint.tangentLine_ne_zero`, `eval_tangentLine_self`), whose dehomogenization in a
chart is the affine tangent line (`dehomogenize_tangentLine`). -/
noncomputable def tangentLine (F : MvPolynomial (Fin 3) k) (v : Fin 3 → k) :
    MvPolynomial (Fin 3) k :=
  ∑ i, C (eval v (pderiv i F)) * X i

theorem tangentLine_def (F : MvPolynomial (Fin 3) k) (v : Fin 3 → k) :
    tangentLine F v = ∑ i, C (eval v (pderiv i F)) * X i :=
  (rfl)

/-- The tangent line is a linear form. -/
theorem isHomogeneous_tangentLine (F : MvPolynomial (Fin 3) k) (v : Fin 3 → k) :
    (tangentLine F v).IsHomogeneous 1 := by
  rw [tangentLine_def]
  exact IsHomogeneous.sum _ _ _ fun i _ ↦ by
    simpa using (isHomogeneous_C _ _).mul (isHomogeneous_X k i)

@[simp]
theorem eval_tangentLine (F : MvPolynomial (Fin 3) k) (v w : Fin 3 → k) :
    eval w (tangentLine F v) = ∑ i, eval v (pderiv i F) * w i := by
  simp [tangentLine_def]

@[simp]
theorem pderiv_tangentLine (F : MvPolynomial (Fin 3) k) (v : Fin 3 → k) (j : Fin 3) :
    pderiv j (tangentLine F v) = C (eval v (pderiv j F)) := by
  simp [tangentLine_def, pderiv_X, Pi.single_apply]

/-- By Euler's identity, the tangent line of a form at a zero `v` vanishes at `v`. -/
theorem eval_tangentLine_self (hF : F.IsHomogeneous d) {v : Fin 3 → k} (h : eval v F = 0) :
    eval v (tangentLine F v) = 0 := by
  have he := congrArg (eval v) hF.sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, map_nsmul, h, smul_zero] at he
  simpa [mul_comm] using he

/-- At a simple point `[v]`, the tangent line `∑ᵢ F_{Xᵢ}(v) Xᵢ` is nonzero. -/
theorem IsSimplePoint.tangentLine_ne_zero (hF : F.IsHomogeneous d) {v : Fin 3 → k} {hv : v ≠ 0}
    (h : IsSimplePoint F (mk k v hv)) : tangentLine F v ≠ 0 := by
  obtain ⟨i, hi⟩ := ((isSimplePoint_mk_iff hF v hv).1 h).2
  intro h0
  have := congrArg (pderiv i) h0
  rw [pderiv_tangentLine, map_zero, C_eq_zero] at this
  exact hi this

/-- **The tangent line in a chart.** If `v = (a with 1 inserted at i)` is a zero of the form `F`,
then the dehomogenization of the tangent line at `v` is the affine tangent line
`∑ⱼ (∂F_(i)/∂Xⱼ)(a) (Xⱼ - aⱼ)` of the affine curve `F_(i)` at `a`. -/
theorem dehomogenize_tangentLine (hF : F.IsHomogeneous d) (i : Fin 3) (a : Fin 2 → k)
    (h : eval (i.insertNth 1 a) F = 0) :
    dehomogenize i (tangentLine F (i.insertNth 1 a)) =
      ∑ j, C (eval a (pderiv j (dehomogenize i F))) * (X j - C (a j)) := by
  have he := eval_pderiv_add_sum_dehomogenize i hF a (by rwa [eval_dehomogenize])
  rw [tangentLine_def, map_sum, Fin.sum_univ_succAbove _ i]
  simp only [map_mul, algHom_C, dehomogenize_X, Fin.insertNth_apply_same, mul_one,
    Fin.insertNth_apply_succAbove, mul_sub, Finset.sum_sub_distrib, pderiv_dehomogenize,
    eval_dehomogenize, algebraMap_eq] at he ⊢
  rw [← eq_neg_iff_add_eq_zero] at he
  rw [he, map_neg, map_sum]
  simp only [← map_mul, mul_comm (a _)]
  ring

/-- At a simple point, the tangent line in a chart, centred at the chart point, is the leading
form of the dehomogenization: the tangent line of the affine curve. -/
theorem IsSimplePoint.taylor_dehomogenize_tangentLine (hF : F.IsHomogeneous d) (i : Fin 3)
    (a : Fin 2 → k) (h : IsSimplePoint F (mk k (i.insertNth 1 a) (Fin.insertNth_one_ne_zero i a))) :
    taylor a (dehomogenize i (tangentLine F (i.insertNth 1 a))) =
      (dehomogenize i F).leadingFormAt a := by
  have hP : mk k (i.insertNth 1 a) (Fin.insertNth_one_ne_zero i a) ∈ affineOpen i := by
    rw [mk_mem_affineOpen_iff]
    simp
  have ha : affineChart i (mk k (i.insertNth 1 a) (Fin.insertNth_one_ne_zero i a)) = a := by
    rw [← affineChart_symm_apply]
    exact (affineChart i).right_inv (by simp)
  have hs := (isSimplePoint_iff_affine hF hP).1 h
  rw [ha] at hs
  rw [dehomogenize_tangentLine hF i a ((isSimplePoint_mk_iff hF _ _).1 h).1,
    hs.leadingFormAt_eq]
  simp [taylor_X, smul_eq_C_mul]

end PlaneCurves.Projective

end
