/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.Tangent
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Singular
public import PlaneCurves.RingTheory.MvPolynomial.LinearForm

/-!
# Tangent lines of projective plane curves

Let `F` be a form in `X, Y, Z` and `P = [v]` a point of `ℙ²`. The *leading form* of `F` at `P`
is the lowest-degree nonzero homogeneous component of `F(v + W)`, a form of degree `m_P(F)` in
`W = (W₀, W₁, W₂)`; up to a nonzero scalar it does not depend on `v`. The tangent lines of `F`
at `P` are its linear factors that vanish at `P`, counted with their multiplicity, and `P` is an
*ordinary* multiple point if it is multiple and the leading form is squarefree.

In an affine chart `Xᵢ ≠ 0` containing `P`, with chart coordinates `a`, the leading form is the
leading form of the dehomogenization `F_(i)` at `a`, with `Yⱼ` replaced by the linear form
`X (i.succAbove j) - aⱼ Xᵢ` (`associated_leadingForm_affine`). So these notions are those of the
affine curve `F_(i)` at `a` (§3.1 of Fulton), the projective line `L = 0` corresponding to the
affine tangent `L_(i)(Y + a) = 0`: this is how Fulton defines them in §5.1.

## Main definitions

* `PlaneCurves.Projective.leadingForm F P`: the leading form of `F` at `P.rep`.
* `PlaneCurves.Projective.IsTangentAt F P L`: `L` is a nonzero linear form vanishing at `P` and
  dividing the leading form of `F` at `P`.
* `PlaneCurves.Projective.tangentMultiplicity F P L`: the multiplicity of `L` in the leading
  form.
* `PlaneCurves.Projective.IsOrdinaryMultiplePoint F P`: `P` is a multiple point of `F` with a
  squarefree leading form.

## Main results

* `PlaneCurves.Projective.associated_leadingForm_affine`: the leading form in an affine chart.
* `PlaneCurves.Projective.isTangentAt_iff_affine`,
  `PlaneCurves.Projective.tangentMultiplicity_eq_affine`,
  `PlaneCurves.Projective.isOrdinaryMultiplePoint_iff_affine`: tangent lines, their
  multiplicities and ordinary multiple points are those of the dehomogenization in any chart.
* `PlaneCurves.Projective.isTangentAt_aeval_chart_iff`,
  `PlaneCurves.Projective.exists_isTangentAt_iff_affine`: conversely, every tangent of the
  dehomogenization comes from a tangent of `F`, so common tangents correspond.
* `PlaneCurves.Projective.leadingForm_linearSubst`,
  `PlaneCurves.Projective.isTangentAt_linearSubst_iff`: leading forms and tangent lines under an
  invertible linear change of coordinates.
* `PlaneCurves.Projective.IsSimplePoint.isTangentAt_tangentLine`: at a simple point the line
  `F_X(v) X + F_Y(v) Y + F_Z(v) Z` is tangent, and
  `PlaneCurves.Projective.IsSimplePoint.associated_tangentLine_of_isTangentAt`: it is the only
  tangent there, up to a scalar.
* `PlaneCurves.Projective.mult_eq_and_isTangentAt_iff_of_eq_sum`: Problem 5.5 of Fulton, the
  multiplicity and the tangent lines at `[0 : 1 : 0]` of `F = ∑ᵢ Fᵢ(X, Z) Y^{d-i}`.
* `PlaneCurves.Projective.mult_sub_one_le_mult_pderiv`: Problem 5.6 of Fulton,
  `m_P(∂F/∂Xᵢ) ≥ m_P(F) - 1`, in every characteristic.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.1, §5.1, Problems 5.5, 5.6
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F L : MvPolynomial (Fin 3) k} {P : ℙ k (Fin 3 → k)} {d : ℕ}

/-! ### The leading form at a point -/

/-- The *leading form* of `F` at `P`: the lowest-degree nonzero homogeneous component of
`F(v + W)` for `v = P.rep`, a form of degree `m_P(F)`. For a form `F` it is, up to a nonzero
scalar, the leading form at any set of homogeneous coordinates of `P`
(`associated_leadingForm_mk`), and in an affine chart the leading form of the dehomogenization
(`associated_leadingForm_affine`). -/
noncomputable def leadingForm (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k)) :
    MvPolynomial (Fin 3) k :=
  F.leadingFormAt P.rep

theorem leadingForm_def (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k)) :
    leadingForm F P = F.leadingFormAt P.rep :=
  (rfl)

/-- The leading form at `P` is a form of degree `m_P(F)`. -/
theorem isHomogeneous_leadingForm (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k)) :
    (leadingForm F P).IsHomogeneous (mult F P).toNat := by
  rw [leadingForm_def, mult_def]
  exact isHomogeneous_leadingFormAt F P.rep

@[simp]
theorem leadingForm_eq_zero_iff : leadingForm F P = 0 ↔ F = 0 :=
  leadingFormAt_eq_zero_iff

/-- For a form, the leading form at `P` is associated to the leading form at any set of
homogeneous coordinates of `P`. -/
theorem associated_leadingForm_mk (hF : F.IsHomogeneous d) (v : Fin 3 → k) (hv : v ≠ 0) :
    Associated (leadingForm F (mk k v hv)) (F.leadingFormAt v) := by
  obtain ⟨c, hc⟩ := exists_smul_eq_mk_rep k v hv
  rw [leadingForm_def, ← hc, Units.smul_def]
  exact hF.associated_leadingFormAt_smul c.isUnit v

/-- A point of the chart `Xᵢ ≠ 0` is the class of `Fin.insertNth i 1 a`, where `a` are its chart
coordinates. -/
private theorem eq_mk_insertNth_affineChart {i : Fin 3} (hP : P ∈ affineOpen i) :
    P = mk k (Fin.insertNth (α := fun _ ↦ k) i 1 (affineChart i P))
      (Fin.insertNth_one_ne_zero i _) := by
  rw [← affineChart_symm_apply]
  exact ((affineChart i).left_inv (by rwa [affineChart_source])).symm

/-- **The leading form in an affine chart.** If `P` lies in the chart `Xᵢ ≠ 0`, with chart
coordinates `a`, the leading form of a form `F` at `P` is, up to a nonzero scalar, the leading
form of the dehomogenization `F_(i)` at `a`, with `Yⱼ` replaced by `X (i.succAbove j) - aⱼ Xᵢ`. -/
theorem associated_leadingForm_affine (hF : F.IsHomogeneous d) {i : Fin 3}
    (hP : P ∈ affineOpen i) :
    Associated (leadingForm F P)
      (aeval (fun j ↦ X (i.succAbove j) - C (affineChart i P j) * X i)
        ((dehomogenize i F).leadingFormAt (affineChart i P))) := by
  rw [← hF.leadingFormAt_insertNth]
  conv_lhs => rw [eq_mk_insertNth_affineChart hP]
  exact associated_leadingForm_mk hF _ _

/-! ### Linear forms in an affine chart -/

section Chart

variable (i : Fin 3) (a : Fin 2 → k)

/-- Setting `Xᵢ = 0` undoes the substitution `Yⱼ ↦ X (i.succAbove j) - aⱼ Xᵢ`. -/
private theorem aeval_insertNth_zero_aeval (p : MvPolynomial (Fin 2) k) :
    aeval (Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin 2) k) i 0 X)
      (aeval (fun j ↦ X (i.succAbove j) - C (a j) * X i) p) = p := by
  have h : (aeval (Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin 2) k) i 0 X)).comp
      (aeval fun j ↦ X (i.succAbove j) - C (a j) * X i) = AlgHom.id k _ :=
    algHom_ext fun j ↦ by simp
  exact DFunLike.congr_fun h p

private theorem aeval_chart_injective :
    Function.Injective (aeval (R := k) fun j ↦ X (i.succAbove j) - C (a j) * X i) :=
  Function.LeftInverse.injective (aeval_insertNth_zero_aeval i a)

private theorem aeval_chart_dvd_iff {p q : MvPolynomial (Fin 2) k} :
    aeval (fun j ↦ X (i.succAbove j) - C (a j) * X i) p ∣
      aeval (fun j ↦ X (i.succAbove j) - C (a j) * X i) q ↔ p ∣ q := by
  refine ⟨fun h ↦ ?_, map_dvd _⟩
  simpa only [aeval_insertNth_zero_aeval] using
    map_dvd (aeval (Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin 2) k) i 0 X)) h

private theorem multiplicity_aeval_chart (p q : MvPolynomial (Fin 2) k) :
    multiplicity (aeval (fun j ↦ X (i.succAbove j) - C (a j) * X i) p)
      (aeval (fun j ↦ X (i.succAbove j) - C (a j) * X i) q) = multiplicity p q :=
  multiplicity_eq_of_emultiplicity_eq <| emultiplicity_eq_emultiplicity_iff.2 fun n ↦ by
    rw [← map_pow, aeval_chart_dvd_iff]

private theorem isHomogeneous_insertNth_zero_X (j : Fin 3) :
    (Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin 2) k) i 0 X j).IsHomogeneous 1 := by
  refine Fin.succAboveCases i ?_ (fun j ↦ ?_) j
  · simpa using isHomogeneous_zero (Fin 2) k 1
  · simpa using isHomogeneous_X k j

private theorem isHomogeneous_chart (j : Fin 2) :
    (X (i.succAbove j) - C (a j) * X i : MvPolynomial (Fin 3) k).IsHomogeneous 1 :=
  (isHomogeneous_X k _).sub (isHomogeneous_C_mul_X (a j) i)

/-- On forms, the substitution `Yⱼ ↦ X (i.succAbove j) - aⱼ Xᵢ` preserves and reflects
squarefreeness. -/
private theorem squarefree_aeval_chart_iff {q : MvPolynomial (Fin 2) k} {m : ℕ}
    (hq : q.IsHomogeneous m) :
    Squarefree (aeval (fun j ↦ X (i.succAbove j) - C (a j) * X i) q) ↔ Squarefree q := by
  set φ : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 3) k :=
    aeval fun j ↦ X (i.succAbove j) - C (a j) * X i
  set ψ : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 2) k :=
    aeval (Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin 2) k) i 0 X)
  have hψφ (p : MvPolynomial (Fin 2) k) : ψ (φ p) = p := aeval_insertNth_zero_aeval i a p
  refine ⟨fun h x hx ↦ ?_, fun h x ⟨y, hy⟩ ↦ ?_⟩
  · have := h (φ x) (by simpa only [map_mul] using map_dvd φ hx)
    simpa only [hψφ] using this.map ψ
  have hφq : (φ q).IsHomogeneous m := by
    simpa only [one_mul] using hq.aeval _ (isHomogeneous_chart i a)
  have hφq0 : φ q ≠ 0 := (map_ne_zero_iff _ (aeval_chart_injective i a)).2 h.ne_zero
  rw [hy] at hφq hφq0
  have hx : x.IsHomogeneous x.totalDegree :=
    (hφq.of_mul_left (right_ne_zero_of_mul hφq0)).of_mul_left
      (right_ne_zero_of_mul (left_ne_zero_of_mul hφq0))
  have hu : IsUnit (ψ x) := h (ψ x) ⟨ψ y, by rw [← map_mul, ← map_mul, ← hy, hψφ]⟩
  have hψx : (ψ x).IsHomogeneous x.totalDegree := by
    simpa only [one_mul] using hx.aeval _ (isHomogeneous_insertNth_zero_X i)
  obtain ⟨r, -, hr⟩ := isUnit_iff_eq_C_of_isReduced.1 hu
  have hdeg : x.totalDegree = 0 := by
    rw [← hψx.totalDegree hu.ne_zero, hr, totalDegree_C]
  rw [totalDegree_eq_zero_iff_eq_C] at hdeg
  rw [hdeg] at hφq0 ⊢
  exact (isUnit_iff_ne_zero.2
    (C_eq_zero.not.1 (left_ne_zero_of_mul (left_ne_zero_of_mul hφq0)))).map C

/-- A linear form `L` vanishing at `Fin.insertNth i 1 a` is recovered from its affine part
`L_(i)(Y + a)` by the substitution `Yⱼ ↦ X (i.succAbove j) - aⱼ Xᵢ`. -/
private theorem aeval_chart_taylor_dehomogenize (hL : L.IsHomogeneous 1)
    (hLa : eval (Fin.insertNth (α := fun _ ↦ k) i 1 a) L = 0) :
    aeval (fun j ↦ X (i.succAbove j) - C (a j) * X i) (taylor a (dehomogenize i L)) = L := by
  obtain ⟨c, rfl⟩ : ∃ c : Fin 3 → k, L = ∑ r, C (c r) * X r := ⟨_, hL.eq_sum_C_mul_X⟩
  rw [eval_sum_C_mul_X, dotProduct, Fin.sum_univ_succAbove _ i, Fin.sum_univ_two] at hLa
  simp only [map_sum, map_mul, algHom_C, algebraMap_eq, dehomogenize_X]
  rw [Fin.sum_univ_succAbove _ i, Fin.sum_univ_succAbove _ i, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, map_one, taylor_X,
    map_add, aeval_X, aeval_C, algebraMap_eq] at hLa ⊢
  have h' := congrArg (C (σ := Fin 3)) hLa
  simp only [mul_one, map_add, map_mul, map_zero] at h'
  linear_combination (1 - X i) * h'

/-- The affine part `L_(i)(Y + a)` of a linear form is linear. -/
theorem isHomogeneous_taylor_dehomogenize (hL : L.IsHomogeneous 1)
    (hLa : eval (Fin.insertNth (α := fun _ ↦ k) i 1 a) L = 0) :
    (taylor a (dehomogenize i L)).IsHomogeneous 1 := by
  rw [← aeval_insertNth_zero_aeval i a (taylor a (dehomogenize i L)),
    aeval_chart_taylor_dehomogenize i a hL hLa]
  simpa only [one_mul] using hL.aeval _ (isHomogeneous_insertNth_zero_X i)

/-- The substitution `Yⱼ ↦ X (i.succAbove j) - aⱼ Xᵢ` followed by dehomogenization at `Xᵢ` and
the Taylor shift to `a` is the identity: every polynomial `p` is the affine part, centred at
`a`, of `p(X (i.succAbove j) - aⱼ Xᵢ)`. -/
theorem taylor_dehomogenize_aeval_chart (p : MvPolynomial (Fin 2) k) :
    taylor a (dehomogenize i (aeval (fun j ↦ X (i.succAbove j) - C (a j) * X i) p)) = p := by
  have h : (taylor a).comp ((dehomogenize i).comp
      (aeval fun j ↦ X (i.succAbove j) - C (a j) * X i)) = AlgHom.id k _ :=
    algHom_ext fun j ↦ by simp [dehomogenize_X, taylor_X]
  exact DFunLike.congr_fun h p

end Chart

/-! ### Tangent lines and ordinary multiple points -/

/-- The nonzero linear form `L` is *tangent* to the plane curve `F` at `P` if it vanishes at `P`
and divides the leading form of `F` at `P`; the tangent line is `L = 0`. -/
def IsTangentAt (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k)) (L : MvPolynomial (Fin 3) k) :
    Prop :=
  L.IsHomogeneous 1 ∧ L ≠ 0 ∧ eval P.rep L = 0 ∧ L ∣ leadingForm F P

theorem isTangentAt_def :
    IsTangentAt F P L ↔
      L.IsHomogeneous 1 ∧ L ≠ 0 ∧ eval P.rep L = 0 ∧ L ∣ leadingForm F P :=
  Iff.rfl

/-- The multiplicity of the linear form `L` as a tangent of `F` at `P`: its multiplicity as a
factor of the leading form of `F` at `P`. -/
noncomputable def tangentMultiplicity (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k))
    (L : MvPolynomial (Fin 3) k) : ℕ :=
  multiplicity L (leadingForm F P)

theorem tangentMultiplicity_def :
    tangentMultiplicity F P L = multiplicity L (leadingForm F P) :=
  (rfl)

/-- `P` is an *ordinary multiple point* of `F` if it is a multiple point and the leading form of
`F` at `P` is squarefree: over an algebraically closed field, `F` has `m_P(F)` distinct tangents
at `P`. -/
def IsOrdinaryMultiplePoint (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k)) : Prop :=
  IsMultiplePoint F P ∧ Squarefree (leadingForm F P)

theorem isOrdinaryMultiplePoint_def :
    IsOrdinaryMultiplePoint F P ↔ IsMultiplePoint F P ∧ Squarefree (leadingForm F P) :=
  Iff.rfl

/-- A curve with a tangent at `P` passes through `P`. -/
theorem IsTangentAt.eval_rep_eq_zero (h : IsTangentAt F P L) : eval P.rep F = 0 := by
  by_contra hP
  rw [isTangentAt_def, leadingForm_def, leadingFormAt_of_eval_ne_zero hP] at h
  exact (irreducible_of_isHomogeneous_one h.1 h.2.1).not_isUnit
    (isUnit_of_dvd_unit h.2.2.2 ((isUnit_iff_ne_zero.2 hP).map C))

/-- Rescaling a curve by a nonzero constant does not change its tangent lines. -/
theorem isTangentAt_smul_iff {c : k} (hc : c ≠ 0) :
    IsTangentAt (c • F) P L ↔ IsTangentAt F P L := by
  rw [isTangentAt_def, isTangentAt_def, leadingForm_def, leadingForm_def, leadingFormAt_smul,
    smul_eq_C_mul, (hc.isUnit.map C).dvd_mul_left]

/-- A form vanishes at `P.rep` exactly when it vanishes at the point `Fin.insertNth i 1 a` of the
chart `Xᵢ = 1` corresponding to `P`. -/
private theorem eval_rep_eq_zero_iff_affine (hL : L.IsHomogeneous d) {i : Fin 3}
    (hP : P ∈ affineOpen i) :
    eval P.rep L = 0 ↔ eval (Fin.insertNth (α := fun _ ↦ k) i 1 (affineChart i P)) L = 0 := by
  conv_lhs => rw [eq_mk_insertNth_affineChart hP]
  exact hL.eval_rep_mk_eq_zero_iff _

/-- **Tangent lines in an affine chart.** If `P` lies in the chart `Xᵢ ≠ 0`, with chart
coordinates `a`, a linear form `L` vanishing at `P` is tangent to the form `F` at `P` exactly
when its affine part `L_(i)(Y + a)` is tangent to the dehomogenization `F_(i)` at `a`. -/
theorem isTangentAt_iff_affine (hF : F.IsHomogeneous d) {i : Fin 3} (hP : P ∈ affineOpen i)
    (hL : L.IsHomogeneous 1) (hLP : eval P.rep L = 0) :
    IsTangentAt F P L ↔ Affine.IsTangentAt (dehomogenize i F) (affineChart i P)
      (taylor (affineChart i P) (dehomogenize i L)) := by
  have hLa := (eval_rep_eq_zero_iff_affine hL hP).1 hLP
  have hφ := aeval_chart_taylor_dehomogenize i (affineChart i P) hL hLa
  rw [isTangentAt_def, Affine.isTangentAt_def,
    (associated_leadingForm_affine hF hP).dvd_iff_dvd_right,
    ← aeval_chart_dvd_iff i (affineChart i P), hφ]
  refine ⟨fun ⟨_, hL0, _, h⟩ ↦ ⟨isHomogeneous_taylor_dehomogenize i _ hL hLa, ?_, h⟩,
    fun ⟨_, hL0, h⟩ ↦ ⟨hL, ?_, hLP, h⟩⟩
  · rintro h0
    rw [h0, map_zero] at hφ
    exact hL0 hφ.symm
  · rintro rfl
    simp at hL0

/-- **Affine tangent lines give projective ones.** If `P` lies in the chart `Xᵢ ≠ 0`, with
chart coordinates `a`, a linear form `L'` in `Y₀, Y₁` is tangent to the dehomogenization `F_(i)`
at `a` exactly when the linear form `L'(X (i.succAbove j) - aⱼ Xᵢ)` is tangent to `F` at `P`.
With `isTangentAt_iff_affine`, the tangents of `F` at `P` and of `F_(i)` at `a` correspond. -/
theorem isTangentAt_aeval_chart_iff (hF : F.IsHomogeneous d) {i : Fin 3}
    (hP : P ∈ affineOpen i) {L' : MvPolynomial (Fin 2) k} (hL' : L'.IsHomogeneous 1) :
    IsTangentAt F P (aeval (fun j ↦ X (i.succAbove j) - C (affineChart i P j) * X i) L') ↔
      Affine.IsTangentAt (dehomogenize i F) (affineChart i P) L' := by
  set a := affineChart i P
  have hL : (aeval (fun j ↦ X (i.succAbove j) - C (a j) * X i) L').IsHomogeneous 1 := by
    simpa only [one_mul] using hL'.aeval _ (isHomogeneous_chart i a)
  have hLP : eval P.rep (aeval (fun j ↦ X (i.succAbove j) - C (a j) * X i) L') = 0 := by
    rw [eval_rep_eq_zero_iff_affine hL hP]
    obtain ⟨c, hc⟩ : ∃ c : Fin 2 → k, L' = ∑ r, C (c r) * X r := ⟨_, hL'.eq_sum_C_mul_X⟩
    simp [hc, a]
  rw [isTangentAt_iff_affine hF hP hL hLP, taylor_dehomogenize_aeval_chart]

/-- **Common tangents in an affine chart.** If `P` lies in the chart `Xᵢ ≠ 0`, the forms `F` and
`G` have a common tangent at `P` exactly when their dehomogenizations `F_(i)` and `G_(i)` have a
common tangent at the chart point of `P`. -/
theorem exists_isTangentAt_iff_affine {G : MvPolynomial (Fin 3) k} {e : ℕ}
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e) {i : Fin 3} (hP : P ∈ affineOpen i) :
    (∃ L, IsTangentAt F P L ∧ IsTangentAt G P L) ↔
      ∃ L, Affine.IsTangentAt (dehomogenize i F) (affineChart i P) L ∧
        Affine.IsTangentAt (dehomogenize i G) (affineChart i P) L := by
  refine ⟨fun ⟨L, hLF, hLG⟩ ↦ ⟨_, (isTangentAt_iff_affine hF hP hLF.1 hLF.2.2.1).1 hLF,
    (isTangentAt_iff_affine hG hP hLG.1 hLG.2.2.1).1 hLG⟩, fun ⟨L, hLF, hLG⟩ ↦ ⟨_,
    (isTangentAt_aeval_chart_iff hF hP hLF.isHomogeneous).2 hLF,
    (isTangentAt_aeval_chart_iff hG hP hLF.isHomogeneous).2 hLG⟩⟩

/-- **Tangent multiplicities in an affine chart.** If `P` lies in the chart `Xᵢ ≠ 0`, with chart
coordinates `a`, the multiplicity of a linear form `L` vanishing at `P` as a tangent of the form
`F` at `P` is the multiplicity of its affine part `L_(i)(Y + a)` as a tangent of `F_(i)` at
`a`. -/
theorem tangentMultiplicity_eq_affine (hF : F.IsHomogeneous d) {i : Fin 3}
    (hP : P ∈ affineOpen i) (hL : L.IsHomogeneous 1) (hLP : eval P.rep L = 0) :
    tangentMultiplicity F P L = Affine.tangentMultiplicity (dehomogenize i F) (affineChart i P)
      (taylor (affineChart i P) (dehomogenize i L)) := by
  have hLa := (eval_rep_eq_zero_iff_affine hL hP).1 hLP
  rw [tangentMultiplicity_def, Affine.tangentMultiplicity_def,
    multiplicity_eq_of_associated_right (associated_leadingForm_affine hF hP),
    ← multiplicity_aeval_chart i (affineChart i P),
    aeval_chart_taylor_dehomogenize i (affineChart i P) hL hLa]

/-- **Ordinary multiple points in an affine chart.** A point `P` in the chart `Xᵢ ≠ 0` is an
ordinary multiple point of the form `F` exactly when its chart point is an ordinary multiple
point of the dehomogenization `F_(i)`. -/
theorem isOrdinaryMultiplePoint_iff_affine (hF : F.IsHomogeneous d) {i : Fin 3}
    (hP : P ∈ affineOpen i) :
    IsOrdinaryMultiplePoint F P ↔
      Affine.IsOrdinaryMultiplePoint (dehomogenize i F) (affineChart i P) := by
  rw [isOrdinaryMultiplePoint_def, Affine.isOrdinaryMultiplePoint_def,
    isMultiplePoint_iff_affine hF hP, (associated_leadingForm_affine hF hP).squarefree_iff,
    squarefree_aeval_chart_iff i _ (isHomogeneous_leadingFormAt _ _)]

/-- At a simple point `P = [v]`, the line `F_X(v) X + F_Y(v) Y + F_Z(v) Z` is tangent to the
form `F`. -/
theorem IsSimplePoint.isTangentAt_tangentLine (hF : F.IsHomogeneous d) (h : IsSimplePoint F P) :
    IsTangentAt F P (tangentLine F P.rep) := by
  have h' : IsSimplePoint F (mk k P.rep P.rep_ne_zero) := by rwa [mk_rep]
  refine ⟨isHomogeneous_tangentLine F _, h'.tangentLine_ne_zero hF,
    eval_tangentLine_self hF h.eval_rep_eq_zero, ?_⟩
  rw [leadingForm_def, leadingFormAt_eq_sum_pderiv (by rwa [isSimplePoint_def, mult_def] at h),
    tangentLine_def]
  simp only [smul_eq_C_mul, dvd_refl]

/-- At a simple point `P = [v]`, every tangent of the form `F` is, up to a nonzero scalar, the
line `F_X(v) X + F_Y(v) Y + F_Z(v) Z`: a simple point has exactly one tangent line. -/
theorem IsSimplePoint.associated_tangentLine_of_isTangentAt (hF : F.IsHomogeneous d)
    (h : IsSimplePoint F P) (hL : IsTangentAt F P L) : Associated L (tangentLine F P.rep) := by
  have hT := h.isTangentAt_tangentLine hF
  have hlead : leadingForm F P = tangentLine F P.rep := by
    rw [leadingForm_def, leadingFormAt_eq_sum_pderiv (by rwa [isSimplePoint_def, mult_def] at h),
      tangentLine_def]
    simp only [smul_eq_C_mul]
  exact (irreducible_of_isHomogeneous_one hL.1 hL.2.1).associated_of_dvd
    (irreducible_of_isHomogeneous_one hT.1 hT.2.1) (hlead ▸ hL.2.2.2)

/-! ### Linear changes of coordinates -/

/-- **The leading form under a change of coordinates.** For an invertible matrix `M`, the leading
form of `F(MX)` at `Q` is, up to a nonzero scalar, the leading form of `F` at `MQ` with the
variables changed along `M`. -/
theorem leadingForm_linearSubst (hF : F.IsHomogeneous d) {M : Matrix (Fin 3) (Fin 3) k}
    (hM : Function.Injective M.mulVecLin) (Q : ℙ k (Fin 3 → k)) :
    Associated (leadingForm (linearSubst M F) Q)
      (linearSubst M (leadingForm F (Projectivization.map M.mulVecLin hM Q))) := by
  have hdet : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).1 (Matrix.mulVec_injective_iff_isUnit.1 hM)
  conv_rhs => rw [← Q.mk_rep, map_mk]
  rw [leadingForm_def, leadingFormAt_linearSubst hdet]
  exact ((associated_leadingForm_mk hF _ _).map (linearSubst M)).symm

/-- **Tangent lines under a change of coordinates.** For an invertible matrix `M`, the line
`L(MX) = 0` is tangent to `F(MX)` at `Q` exactly when `L = 0` is tangent to `F` at `MQ`. -/
theorem isTangentAt_linearSubst_iff (hF : F.IsHomogeneous d) {M : Matrix (Fin 3) (Fin 3) k}
    (hM : Function.Injective M.mulVecLin) (Q : ℙ k (Fin 3 → k)) :
    IsTangentAt (linearSubst M F) Q (linearSubst M L) ↔
      IsTangentAt F (Projectivization.map M.mulVecLin hM Q) L := by
  have hdet : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).1 (Matrix.mulVec_injective_iff_isUnit.1 hM)
  have hinv := linearSubst_nonsing_inv_linearSubst hdet
  have hhom : (linearSubst M L).IsHomogeneous 1 ↔ L.IsHomogeneous 1 :=
    ⟨fun h ↦ hinv L ▸ h.linearSubst M⁻¹, fun h ↦ h.linearSubst M⟩
  have hdvd {p q : MvPolynomial (Fin 3) k} : linearSubst M p ∣ linearSubst M q ↔ p ∣ q :=
    ⟨fun h ↦ by simpa only [hinv] using map_dvd (linearSubst M⁻¹) h, map_dvd _⟩
  rw [isTangentAt_def, isTangentAt_def, hhom,
    (leadingForm_linearSubst hF hM Q).dvd_iff_dvd_right, hdvd,
    map_ne_zero_iff _ (linearSubst_injective hdet)]
  refine and_congr_right fun hL ↦ and_congr_right fun _ ↦ and_congr_left fun _ ↦ ?_
  conv_rhs => rw [← Q.mk_rep, map_mk]
  rw [eval_linearSubst, hL.eval_rep_mk_eq_zero_iff, Matrix.mulVecLin_apply]

/-! ### Problems 5.5 and 5.6 -/

/-- If `f = ∑ᵢ Gᵢ` with `Gᵢ` a form of degree `i`, `Gᵢ = 0` for `i < m` and `Gₘ ≠ 0`, then `f`
has order `m` at the origin, with leading form `Gₘ`. -/
private theorem orderAt_zero_and_leadingFormAt_zero_of_eq_sum {f : MvPolynomial (Fin 2) k}
    {G : ℕ → MvPolynomial (Fin 2) k} (hG : ∀ i, (G i).IsHomogeneous i) {m : ℕ} (hmd : m ≤ d)
    (hf : f = ∑ i ∈ Finset.range (d + 1), G i) (hlt : ∀ i < m, G i = 0) (hm : G m ≠ 0) :
    f.orderAt 0 = m ∧ f.leadingFormAt 0 = G m := by
  have hc (n : ℕ) : homogeneousComponent n f = if n ≤ d then G n else 0 := by
    have h1 (x : ℕ) : homogeneousComponent n (G x) = if n = x then G x else 0 :=
      homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 (hG x))
    simp only [hf, map_sum, h1, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]
  have hle : (m : ℕ∞) ≤ f.orderAt 0 := by
    refine le_orderAt_iff.2 fun e he ↦ ?_
    have h := coeff_homogeneousComponent (φ := f) (n := e.degree) e
    simp only [↓reduceIte] at h
    rw [taylor_zero, ← h, hc]
    split_ifs
    · simp [hlt _ (by exact_mod_cast he)]
    · simp
  have hord : f.orderAt 0 = m := orderAt_eq_of_homogeneousComponent_ne_zero hle
    (by simpa [hc, hmd] using hm)
  refine ⟨hord, ?_⟩
  rw [leadingFormAt_def, hord, ENat.toNat_natCast, taylor_zero, hc]
  simp [hmd]

/-- **Problem 5.5 of Fulton.** Let `F = ∑ᵢ Fᵢ(X, Z) Y^{d-i}`, with `Fᵢ` a binary form of degree
`i` (in the variables `X = X₀`, `Z = X₂`), and let `m ≤ d` be least with `Fₘ ≠ 0`. Then the
multiplicity of `F` at `P = [0 : 1 : 0]` is `m`, the leading form of `F` at `P` is `Fₘ` up to a
nonzero scalar, and the tangent lines of `F` at `P` are the linear factors of `Fₘ`, with the
same multiplicities. -/
theorem mult_eq_and_isTangentAt_iff_of_eq_sum {G : ℕ → MvPolynomial (Fin 2) k}
    (hG : ∀ i, (G i).IsHomogeneous i)
    (hF : F = ∑ i ∈ Finset.range (d + 1), rename (Fin.succAbove 1) (G i) * X 1 ^ (d - i))
    {m : ℕ} (hmd : m ≤ d) (hlt : ∀ i < m, G i = 0) (hm : G m ≠ 0) :
    mult F (mk k ![0, 1, 0] (by simp)) = m ∧
      Associated (leadingForm F (mk k ![0, 1, 0] (by simp))) (rename (Fin.succAbove 1) (G m)) ∧
      (∀ L : MvPolynomial (Fin 2) k,
        IsTangentAt F (mk k ![0, 1, 0] (by simp)) (rename (Fin.succAbove 1) L) ↔
          L.IsHomogeneous 1 ∧ L ≠ 0 ∧ L ∣ G m) ∧
      ∀ L : MvPolynomial (Fin 2) k,
        tangentMultiplicity F (mk k ![0, 1, 0] (by simp)) (rename (Fin.succAbove 1) L) =
          multiplicity L (G m) := by
  have hv : (![0, 1, 0] : Fin 3 → k) = Fin.insertNth (α := fun _ ↦ k) 1 1 0 := by
    ext j
    fin_cases j <;> rfl
  have hFh : F.IsHomogeneous d := by
    rw [hF]
    refine IsHomogeneous.sum _ _ _ fun i hi ↦ ?_
    have h := ((hG i).rename_isHomogeneous (f := Fin.succAbove 1)).mul
      (isHomogeneous_X_pow (R := k) (1 : Fin 3) (d - i))
    rwa [Nat.add_sub_cancel' (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))] at h
  have hdeh : dehomogenize 1 F = ∑ i ∈ Finset.range (d + 1), G i := by
    simp [hF, dehomogenize_rename_succAbove, dehomogenize_X]
  obtain ⟨hord, hlf⟩ := orderAt_zero_and_leadingFormAt_zero_of_eq_sum hG hmd hdeh hlt hm
  have hren : (aeval fun j ↦ X ((1 : Fin 3).succAbove j) - C ((0 : Fin 2 → k) j) * X 1 :
      MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 3) k) = rename (Fin.succAbove 1) :=
    algHom_ext fun j ↦ by simp
  have hassoc : Associated (leadingForm F (mk k ![0, 1, 0] (by simp)))
      (rename (Fin.succAbove 1) (G m)) := by
    have := associated_leadingForm_mk hFh ![0, 1, 0] (by simp)
    have hlf' : F.leadingFormAt ![0, 1, 0] = rename (Fin.succAbove 1) (G m) := by
      rw [hv, hFh.leadingFormAt_insertNth, hlf, hren]
    rwa [hlf'] at this
  refine ⟨?_, hassoc, fun L ↦ ?_, fun L ↦ ?_⟩
  · rw [mult_mk hFh, hv, ← hFh.orderAt_dehomogenize, hord]
  · rw [isTangentAt_def, IsHomogeneous.rename_isHomogeneous_iff Fin.succAbove_right_injective,
      map_ne_zero_iff _ (rename_injective _ Fin.succAbove_right_injective),
      hassoc.dvd_iff_dvd_right, ← hren, aeval_chart_dvd_iff]
    refine ⟨fun ⟨h1, h2, _, h3⟩ ↦ ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, ?_, h3⟩⟩
    rw [hren, h1.rename_isHomogeneous.eval_rep_mk_eq_zero_iff _, hv, eval_rename,
      Fin.insertNth_comp_succAbove, eval_zero]
    exact h1.coeff_eq_zero (by simp)
  · rw [tangentMultiplicity_def, multiplicity_eq_of_associated_right hassoc, ← hren,
      multiplicity_aeval_chart]

/- The curve `XZ = 0` has an ordinary double point at `[0 : 1 : 0]`, where its two tangents are
`X = 0` and `Z = 0`. -/
example :
    IsOrdinaryMultiplePoint (X 0 * X 2 : MvPolynomial (Fin 3) k) (mk k ![0, 1, 0] (by simp)) := by
  obtain ⟨hmult, hassoc, -⟩ := mult_eq_and_isTangentAt_iff_of_eq_sum
    (F := (X 0 * X 2 : MvPolynomial (Fin 3) k)) (d := 2)
    (G := fun i ↦ if i = 2 then (X 0 * X 1 : MvPolynomial (Fin 2) k) else 0) (m := 2)
    (fun i ↦ by
      split_ifs with h
      · subst h
        exact (isHomogeneous_X k 0).mul (isHomogeneous_X k 1)
      · exact isHomogeneous_zero _ _ _)
    (by simp [Finset.sum_range_succ]) le_rfl (fun i hi ↦ by simp; omega)
    (by simp [X_ne_zero])
  refine ⟨by rw [isMultiplePoint_def, hmult]; rfl, hassoc.squarefree_iff.2 ?_⟩
  simp only [↓reduceIte, map_mul, rename_X]
  refine squarefree_mul_iff.2 ⟨(prime_X.irreducible).isRelPrime_iff_not_dvd.2 ?_,
    prime_X.irreducible.squarefree, prime_X.irreducible.squarefree⟩
  rw [X_dvd_X]
  decide

/-- **Problem 5.6 of Fulton.** A partial derivative lowers the multiplicity by at most one:
`m_P(∂F/∂Xᵢ) ≥ m_P(F) - 1` for every `i` and every point `P`, in every characteristic (with
`m_P(0) = ⊤`). -/
theorem mult_sub_one_le_mult_pderiv (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k))
    (i : Fin 3) : mult F P - 1 ≤ mult (pderiv i F) P := by
  rw [mult_def, mult_def]
  exact orderAt_sub_one_le_orderAt_pderiv F P.rep i

end PlaneCurves.Projective

end
