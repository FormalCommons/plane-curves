/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.ZeroLocus
public import PlaneCurves.RingTheory.MvPolynomial.OrderAtDehomogenize

/-!
# Multiplicity of a projective plane curve at a point

A projective plane curve is a nonzero form `F : MvPolynomial (Fin 3) k`, and a point `P` of
`ℙ²` is `ℙ k (Fin 3 → k)`. The multiplicity `m_P(F)` is the order of vanishing of `F` at a set
of homogeneous coordinates of `P` (Tau Ceti's `MvPolynomial.orderAt`, in all three variables).
For a form it does not depend on the homogeneous coordinates, and in every standard affine chart
containing `P` it is the multiplicity of the affine curve `F_(i)` at the point of the chart: this
is Fulton's definition.

## Main definitions

* `PlaneCurves.Projective.mult F P`: the multiplicity `m_P(F)`, the order of `F` at `P.rep`.

## Main results

* `PlaneCurves.Projective.mult_mk`: `m_P(F)` is the order of `F` at any set of homogeneous
  coordinates of `P`.
* `PlaneCurves.Projective.mult_eq_orderAt_dehomogenize`: `m_P(F)` is the multiplicity of the
  dehomogenization `F_(i)` at the chart point of `P`, for every chart containing `P`.
* `PlaneCurves.Projective.mult_smul`, `PlaneCurves.Projective.mult_linearSubst`: invariance under
  scalars and projective changes of coordinates.
* `PlaneCurves.Projective.mult_eq_zero_iff`, `PlaneCurves.Projective.mult_mul`,
  `PlaneCurves.Projective.mult_prod_pow`, `PlaneCurves.Projective.mult_le_degree`.
* `PlaneCurves.Projective.mult_eq_orderAt_dehomogenize_and_properties`: the multiplicity of a
  projective plane curve at a point, as in §5.1 of Fulton.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.1
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F G : MvPolynomial (Fin 3) k} {P : ℙ k (Fin 3 → k)} {d : ℕ}

/-- The multiplicity `m_P(F)` of a plane curve `F` at a point `P` of `ℙ²`: the order of
vanishing of `F` at the homogeneous coordinates `P.rep`. For a form it is the order at any set of
homogeneous coordinates (`mult_mk`), and the multiplicity of the dehomogenization in any affine
chart containing `P` (`mult_eq_orderAt_dehomogenize`). It is `⊤` only for `F = 0`. -/
noncomputable def mult (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k)) : ℕ∞ :=
  F.orderAt P.rep

theorem mult_def (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k)) :
    mult F P = F.orderAt P.rep :=
  (rfl)

/-- The multiplicity of a form is its order at any set of homogeneous coordinates of the
point. -/
theorem mult_mk (hF : F.IsHomogeneous d) (v : Fin 3 → k) (hv : v ≠ 0) :
    mult F (mk k v hv) = F.orderAt v := by
  obtain ⟨c, hc⟩ := exists_smul_eq_mk_rep k v hv
  rw [mult_def, ← hc, Units.smul_def, hF.orderAt_smul c.isUnit]

/-- **The multiplicity in an affine chart.** For a form `F` and a point `P` in the standard
affine open `Xᵢ ≠ 0`, `m_P(F)` is the multiplicity of the dehomogenization `F_(i)` at the chart
coordinates of `P`. -/
theorem mult_eq_orderAt_dehomogenize (hF : F.IsHomogeneous d) {i : Fin 3}
    (hP : P ∈ affineOpen i) :
    mult F P = (dehomogenize i F).orderAt (affineChart i P) := by
  induction P using Projectivization.ind with | h v hv =>
  rw [mult_mk hF, affineChart_mk,
    hF.orderAt_eq_orderAt_dehomogenize ((mk_mem_affineOpen_iff i v hv).1 hP)]

@[simp]
theorem mult_zero (P : ℙ k (Fin 3 → k)) : mult 0 P = ⊤ :=
  orderAt_zero _

@[simp]
theorem mult_eq_top_iff : mult F P = ⊤ ↔ F = 0 :=
  orderAt_eq_top_iff

/-- A curve passes through a point exactly when its multiplicity there is positive; this is
tested at the representative `P.rep`. -/
theorem mult_pos_iff_eval_rep : 0 < mult F P ↔ eval P.rep F = 0 :=
  orderAt_pos_iff

/-- The multiplicity of a form at `P` is zero exactly when `P` is not on the curve. -/
theorem mult_eq_zero_iff (hF : F.IsHomogeneous d) : mult F P = 0 ↔ P ∉ zeroLocus {F} := by
  rw [mult_def, orderAt_eq_zero_iff, mem_zeroLocus_iff_eval_rep (by simpa using ⟨d, hF⟩)]
  simp

/-- The multiplicity of a form at `P` is positive exactly when `P` is on the curve. -/
theorem mult_pos_iff (hF : F.IsHomogeneous d) : 0 < mult F P ↔ P ∈ zeroLocus {F} := by
  rw [pos_iff_ne_zero, Ne, mult_eq_zero_iff hF, not_not]

/-- `m_P(cF) = m_P(F)` for `c ≠ 0`. -/
@[simp]
theorem mult_smul {c : k} (hc : c ≠ 0) (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k)) :
    mult (c • F) P = mult F P := by
  rw [mult_def, mult_def, smul_eq_C_mul, orderAt_mul, orderAt_C_of_ne_zero hc, zero_add]

/-- Multiplicities add over products: `m_P(FG) = m_P(F) + m_P(G)`. -/
theorem mult_mul (F G : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k)) :
    mult (F * G) P = mult F P + mult G P :=
  orderAt_mul _ _ _

theorem mult_pow (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k)) (e : ℕ) :
    mult (F ^ e) P = e • mult F P :=
  orderAt_pow _ _ _

/-- `m_P(∏ Fᵢ ^ eᵢ) = ∑ eᵢ m_P(Fᵢ)`. -/
theorem mult_prod_pow {ι : Type*} (s : Finset ι) (F : ι → MvPolynomial (Fin 3) k) (e : ι → ℕ)
    (P : ℙ k (Fin 3 → k)) : mult (∏ i ∈ s, F i ^ e i) P = ∑ i ∈ s, e i • mult (F i) P := by
  simp only [mult_def, orderAt_prod, orderAt_pow]

/-- The multiplicity of a nonzero form at a point is at most its degree. -/
theorem mult_le_degree (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) (P : ℙ k (Fin 3 → k)) :
    mult F P ≤ d := by
  rw [mult_def, ← hF.totalDegree hF0]
  exact orderAt_le_totalDegree hF0 _

/-- **Change of coordinates.** For a form `F` and an invertible matrix `M`, the multiplicity of
`F^M = F(M X)` at `Q` is the multiplicity of `F` at the image `[M v]` of `Q = [v]`. -/
theorem mult_linearSubst (hF : F.IsHomogeneous d) {M : Matrix (Fin 3) (Fin 3) k}
    (hM : Function.Injective M.mulVecLin) (Q : ℙ k (Fin 3 → k)) :
    mult (linearSubst M F) Q = mult F (Projectivization.map M.mulVecLin hM Q) := by
  have hdet : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).1 (Matrix.mulVec_injective_iff_isUnit.1 hM)
  conv_rhs => rw [← Q.mk_rep, map_mk]
  rw [mult_mk hF, mult_def, orderAt_linearSubst hdet, Matrix.mulVecLin_apply]

/-- **Multiplicity of a projective plane curve at a point.** Let `F` be a nonzero form of degree
`d` over a field `k` and `P` a point of `ℙ²`.

1. For every set of homogeneous coordinates `v` of `P`, `m_P(F)` is the order of `F` at `v`; for
   every standard affine chart `Xᵢ ≠ 0` containing `P`, it is the multiplicity of the
   dehomogenization `F_(i)` at the chart point of `P`. So the chart multiplicity depends neither
   on the chart nor on the coordinates.
2. `m_P(cF) = m_P(F)` for `c ≠ 0`, and `m_Q(F^T) = m_{T(Q)}(F)` for a projective change of
   coordinates `T`.
3. `m_P(F) = 0` exactly when `P ∉ V(F)`.
4. `m_P(FG) = m_P(F) + m_P(G)`, and `m_P(∏ Fᵢ ^ eᵢ) = ∑ eᵢ m_P(Fᵢ)`.
5. `m_P(F) ≤ d`.

Milestone: *Multiplicity of a projective plane curve at a point*. -/
theorem mult_eq_orderAt_dehomogenize_and_properties (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) :
    (∀ (v : Fin 3 → k) (hv : v ≠ 0), mk k v hv = P → F.orderAt v = mult F P) ∧
    (∀ i : Fin 3, P ∈ affineOpen i →
      (dehomogenize i F).orderAt (affineChart i P) = mult F P) ∧
    (∀ c : k, c ≠ 0 → mult (c • F) P = mult F P) ∧
    (∀ (M : Matrix (Fin 3) (Fin 3) k) (hM : Function.Injective M.mulVecLin)
      (Q : ℙ k (Fin 3 → k)), mult (linearSubst M F) Q = mult F (map M.mulVecLin hM Q)) ∧
    (mult F P = 0 ↔ P ∉ zeroLocus {F}) ∧
    (∀ G, mult (F * G) P = mult F P + mult G P) ∧
    (∀ {ι : Type*} (s : Finset ι) (G : ι → MvPolynomial (Fin 3) k) (e : ι → ℕ),
      mult (∏ i ∈ s, G i ^ e i) P = ∑ i ∈ s, e i • mult (G i) P) ∧
    mult F P ≤ d :=
  ⟨fun v hv hP ↦ hP ▸ (mult_mk hF v hv).symm,
    fun _ hP ↦ (mult_eq_orderAt_dehomogenize hF hP).symm, fun _ hc ↦ mult_smul hc F P,
    fun _ hM Q ↦ mult_linearSubst hF hM Q, mult_eq_zero_iff hF, fun G ↦ mult_mul F G P,
    fun s G e ↦ mult_prod_pow s G e P, mult_le_degree hF hF0 P⟩

/- The node `XY = 0`, homogenized to `XY`, has multiplicity two at `[0 : 0 : 1]`, computed in the
chart `Z ≠ 0`, where it is the affine node at the origin. -/
example : mult (X 0 * X 1 : MvPolynomial (Fin 3) k) (mk k ![0, 0, 1] (by simp)) = 2 := by
  rw [mult_mk ((isHomogeneous_X k 0).mul (isHomogeneous_X k 1)), orderAt_mul,
    orderAt_eq_one_of_eval_pderiv_ne_zero (i := 0) (by simp) (by simp [pderiv_X]),
    orderAt_eq_one_of_eval_pderiv_ne_zero (i := 1) (by simp) (by simp [pderiv_X])]
  rfl

end PlaneCurves.Projective

end
