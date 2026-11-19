/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Projectivization.Constructions
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.ZMod.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Tangent
public import PlaneCurves.RingTheory.MvPolynomial.PDeriv
public import PlaneCurves.RingTheory.MvPolynomial.PolarDerivative

/-!
# Terrible points of a projective plane curve

Following Appendix A of Fulton, a point `P = [v]` of `ℙ²` is *terrible* for a plane curve `F`
of degree `n` if infinitely many lines through `P` meet `F` in fewer than `n - m_P(F)` points
other than `P`. We use the algebraic characterization as the definition: `P` is terrible when
`n ≥ 2` and the polar derivative `D_v F = v₀ F_X + v₁ F_Y + v₂ F_Z` is zero, that is, when the
tangent line at every simple point of `F` passes through `P`.

Terrible points only occur in positive characteristic. If `F` is an irreducible form of degree
`n` over an algebraically closed field and `P = [v]` is terrible with `r = m_P(F)`, then `r < n`
and `(n - r) · 1 = 0` in `k`: this is the contrapositive of the nonvanishing theorem
`MvPolynomial.IsHomogeneous.polarDerivative_ne_zero` for the polar derivative. Over a perfect
field an irreducible form has at most one terrible point: if `D_v F = D_w F = 0` for independent
`v` and `w`, then after a change of coordinates `F_Y = F_Z = 0`, and Euler's identity
`X F_X = n F` makes `F` either divisible by `X` or have all its partial derivatives zero.

## Main definitions

* `PlaneCurves.Projective.IsTerriblePoint F v`: `2 ≤ deg F` and `D_v F = 0`.

## Main results

* `PlaneCurves.Projective.isTerriblePoint_smul_left_iff`,
  `PlaneCurves.Projective.isTerriblePoint_smul_right_iff`,
  `PlaneCurves.Projective.isTerriblePoint_linearSubst_iff`: invariance under scalars and linear
  changes of coordinates.
* `PlaneCurves.Projective.IsTerriblePoint.natCast_sub_eq_zero`,
  `PlaneCurves.Projective.IsTerriblePoint.mult_lt`,
  `PlaneCurves.Projective.IsTerriblePoint.mult_lt_and_natCast_sub_eq_zero`: at a terrible point
  `P` of an irreducible curve over an algebraically closed field, `m_P(F) < n` and
  `(n - m_P(F)) · 1 = 0`.
* `PlaneCurves.Projective.not_isTerriblePoint`: in characteristic zero no point is terrible.
* `PlaneCurves.Projective.IsTerriblePoint.mk_eq_mk`: over a perfect field an irreducible form has
  at most one terrible point.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], Appendix A, §5.4 (Problem 5.26)
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {v w : Fin 3 → k} {n : ℕ}

/-- The point `[v]` is *terrible* for the plane curve `F` if `F` has degree at least two and the
polar derivative `D_v F = ∑ᵢ vᵢ ∂F/∂Xᵢ` is zero: the tangent line at every simple point of `F`
passes through `[v]`. Such points exist only in positive characteristic. The degree condition
excludes lines, for which `D_v F = F(v)` vanishes at every point of the line. -/
def IsTerriblePoint (F : MvPolynomial (Fin 3) k) (v : Fin 3 → k) : Prop :=
  2 ≤ F.totalDegree ∧ polarDerivative v F = 0

theorem isTerriblePoint_def :
    IsTerriblePoint F v ↔ 2 ≤ F.totalDegree ∧ polarDerivative v F = 0 :=
  Iff.rfl

theorem IsTerriblePoint.two_le_totalDegree (h : IsTerriblePoint F v) : 2 ≤ F.totalDegree :=
  h.1

theorem IsTerriblePoint.polarDerivative_eq_zero (h : IsTerriblePoint F v) :
    polarDerivative v F = 0 :=
  h.2

/-- A curve of degree at most one, such as a line, has no terrible points. -/
theorem not_isTerriblePoint_of_totalDegree_le_one (h : F.totalDegree ≤ 1) :
    ¬IsTerriblePoint F v :=
  fun h' ↦ by have := h'.two_le_totalDegree; omega

/-- Being terrible depends only on the point `[v]`, not on its homogeneous coordinates. -/
@[simp]
theorem isTerriblePoint_smul_left_iff {c : k} (hc : c ≠ 0) :
    IsTerriblePoint F (c • v) ↔ IsTerriblePoint F v := by
  simp [isTerriblePoint_def, polarDerivative_smul_left, hc]

/-- Rescaling a curve by a nonzero constant does not change its terrible points. -/
@[simp]
theorem isTerriblePoint_smul_right_iff {c : k} (hc : c ≠ 0) :
    IsTerriblePoint (c • F) v ↔ IsTerriblePoint F v := by
  have hdeg : (c • F).totalDegree = F.totalDegree := by
    rcases eq_or_ne F 0 with rfl | hF
    · simp
    rw [smul_eq_C_mul, totalDegree_mul_of_isDomain (C_ne_zero.2 hc) hF, totalDegree_C, zero_add]
  rw [isTerriblePoint_def, isTerriblePoint_def, polarDerivative_smul_right, smul_eq_zero,
    or_iff_right hc, hdeg]

/-- **Change of coordinates.** For an invertible matrix `M`, `[v]` is terrible for
`F^M = F(M X)` exactly when its image `[M v]` is terrible for `F`. -/
theorem isTerriblePoint_linearSubst_iff {M : Matrix (Fin 3) (Fin 3) k} (hM : IsUnit M.det) :
    IsTerriblePoint (linearSubst M F) v ↔ IsTerriblePoint F (M.mulVec v) := by
  rw [isTerriblePoint_def, isTerriblePoint_def, totalDegree_linearSubst hM,
    polarDerivative_linearSubst, map_eq_zero_iff _ (linearSubst_injective hM)]

/-- In characteristic `2`, `[1 : 0 : 0]` is a terrible point of the conic `X² + YZ`: every
tangent line of the conic passes through it. -/
example :
    IsTerriblePoint (X 0 ^ 2 + X 1 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) (Pi.single 0 1) := by
  have hH : (X 0 ^ 2 + X 1 * X 2 : MvPolynomial (Fin 3) (ZMod 2)).IsHomogeneous 2 :=
    (isHomogeneous_X_pow 0 2).add ((isHomogeneous_X _ 1).mul (isHomogeneous_X _ 2))
  have h0 : (X 0 ^ 2 + X 1 * X 2 : MvPolynomial (Fin 3) (ZMod 2)) ≠ 0 := by
    intro h
    simpa using congrArg (eval ![1, 0, 0]) h
  refine ⟨(hH.totalDegree h0).ge, ?_⟩
  rw [polarDerivative_eq_sum_C_mul]
  simp only [Fin.isValue, Pi.single_apply, MonoidWithZeroHom.map_ite_one_zero, map_add,
    Derivation.leibniz_pow, Nat.add_one_sub_one, pow_one, pderiv_X, smul_eq_mul, mul_ite, mul_one,
    mul_zero, smul_ite, nsmul_eq_mul, Nat.cast_ofNat, Derivation.leibniz, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fin.reduceEq, one_ne_zero,
    add_zero, mul_eq_zero, X_ne_zero, or_false]
  exact CharTwo.two_eq_zero

/-! ### Terrible points and the characteristic -/

/-- At a terrible point `P = [v]` of a form `F` of degree `n`, with `r = m_P(F)`, the integer
`n - r` is zero in `k`: otherwise the polar derivative `D_v F` would be nonzero. -/
theorem IsTerriblePoint.natCast_sub_eq_zero (hF : F.IsHomogeneous n) (hv : v ≠ 0)
    (h : IsTerriblePoint F v) {r : ℕ} (hr : mult F (mk k v hv) = r) : ((n - r : ℕ) : k) = 0 := by
  by_contra hnr
  rw [mult_mk hF] at hr
  exact hF.polarDerivative_ne_zero hr hnr h.polarDerivative_eq_zero

/-- Over an algebraically closed field, the multiplicity of an irreducible curve of degree `n` at
a terrible point is less than `n`. -/
theorem IsTerriblePoint.mult_lt [IsAlgClosed k] (hF : F.IsHomogeneous n) (hirr : Irreducible F)
    (h : IsTerriblePoint F v) (P : ℙ k (Fin 3 → k)) : mult F P < n :=
  mult_lt_of_irreducible hF hirr (hF.totalDegree hirr.ne_zero ▸ h.two_le_totalDegree) P

/-- **Terrible points and the characteristic.** Let `F` be an irreducible form of degree `n` over
an algebraically closed field `k`, and `P = [v]` a terrible point of `F` with `r = m_P(F)`. Then
`r < n` and `(n - r) · 1 = 0` in `k`: so `k` has characteristic `p > 0` and `p ∣ n - r`.
Algebraic closure is needed for `r < n`: over `ℝ`, `[0 : 1 : 0]` is a terrible point of
multiplicity `2` of the irreducible conic `X² + Z²`. -/
theorem IsTerriblePoint.mult_lt_and_natCast_sub_eq_zero [IsAlgClosed k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) (hv : v ≠ 0) (h : IsTerriblePoint F v) {r : ℕ}
    (hr : mult F (mk k v hv) = r) : r < n ∧ ((n - r : ℕ) : k) = 0 :=
  ⟨by exact_mod_cast hr ▸ h.mult_lt hF hirr (mk k v hv), h.natCast_sub_eq_zero hF hv hr⟩

/-- In characteristic zero, an irreducible curve over an algebraically closed field has no
terrible points. -/
theorem not_isTerriblePoint [IsAlgClosed k] [CharZero k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) (hv : v ≠ 0) : ¬IsTerriblePoint F v := by
  intro h
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.1 (mult_eq_top_iff.not.2 hirr.ne_zero :
    mult F (mk k v hv) ≠ ⊤)
  obtain ⟨hrn, hnr⟩ := h.mult_lt_and_natCast_sub_eq_zero hF hirr hv hr.symm
  rw [Nat.cast_eq_zero] at hnr
  omega

/-! ### At most one terrible point -/

/-- The polar derivative in the direction of a standard basis vector is the partial
derivative. -/
private theorem polarDerivative_single (i : Fin 3) (G : MvPolynomial (Fin 3) k) :
    polarDerivative (Pi.single i 1) G = pderiv i G := by
  simp [polarDerivative_def, Pi.single_apply]

/-- If an irreducible form `G` of degree `n ≥ 2` over a perfect field has `∂G/∂X₁ = ∂G/∂X₂ = 0`,
then Euler's identity `X₀ ∂G/∂X₀ = n G` gives a contradiction: either `n = 0` in `k` and all
partial derivatives of `G` vanish, or `X₀` divides `G`. -/
private theorem false_of_pderiv_one_eq_zero_of_pderiv_two_eq_zero [PerfectField k]
    {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous n) (hirr : Irreducible G) (hn : 2 ≤ n)
    (h₁ : pderiv 1 G = 0) (h₂ : pderiv 2 G = 0) : False := by
  have heuler := hG.sum_X_mul_pderiv
  simp only [Fin.sum_univ_three, h₁, h₂, mul_zero, add_zero, nsmul_eq_mul] at heuler
  rw [← map_natCast C] at heuler
  by_cases hn0 : (n : k) = 0
  · rw [hn0, map_zero, zero_mul, mul_eq_zero, or_iff_right (X_ne_zero 0)] at heuler
    obtain ⟨i, hi⟩ := hirr.exists_pderiv_ne_zero
    fin_cases i <;> simp_all
  · have hdvd : X 0 ∣ G := ⟨C (n : k)⁻¹ * pderiv 0 G, by
      rw [← mul_left_comm, heuler, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hn0, map_one, one_mul]⟩
    have hassoc := (irreducible_of_isHomogeneous_one (isHomogeneous_X k 0) (X_ne_zero 0))
      |>.associated_of_dvd hirr hdvd
    have hle := totalDegree_le_of_dvd_of_isDomain hassoc.symm.dvd (X_ne_zero 0)
    rw [hG.totalDegree hirr.ne_zero, totalDegree_X] at hle
    omega

/-- **At most one terrible point.** Over a perfect field, an irreducible form has at most one
terrible point: if `[v]` and `[w]` are terrible, they are equal. The field must be perfect:
over `𝔽_p(t)` every point is terrible for the irreducible form `X^p - t Y^p`, all of whose
partial derivatives vanish. -/
theorem IsTerriblePoint.mk_eq_mk [PerfectField k] (hF : F.IsHomogeneous n) (hirr : Irreducible F)
    (hv : v ≠ 0) (hw : w ≠ 0) (h₁ : IsTerriblePoint F v) (h₂ : IsTerriblePoint F w) :
    mk k v hv = mk k w hw := by
  rw [mk_eq_mk_iff_crossProduct_eq_zero]
  by_contra hc
  obtain ⟨j, hj⟩ : ∃ j, crossProduct v w j ≠ 0 := by
    by_contra! h
    exact hc (funext h)
  -- The columns of `M` are `e_j`, `v` and `w`; its determinant is the `j`-th coordinate of
  -- `v × w`.
  set M : Matrix (Fin 3) (Fin 3) k := (Matrix.of ![Pi.single j 1, v, w]).transpose
  have hdet : IsUnit M.det := by
    rw [Matrix.det_transpose, isUnit_iff_ne_zero]
    change Matrix.det ![Pi.single j 1, v, w] ≠ 0
    rwa [← triple_product_eq_det, single_dotProduct, one_mul]
  have hcol (i : Fin 3) :
      pderiv i (linearSubst M F) =
        linearSubst M (polarDerivative (![Pi.single j 1, v, w] i) F) := by
    rw [← polarDerivative_single, polarDerivative_linearSubst, Matrix.mulVec_single_one]
    rfl
  have hn : 2 ≤ n := hF.totalDegree hirr.ne_zero ▸ h₁.two_le_totalDegree
  exact false_of_pderiv_one_eq_zero_of_pderiv_two_eq_zero (hF.linearSubst M)
    ((irreducible_linearSubst_iff hdet).2 hirr) hn
    (by rw [hcol 1]; simp [h₁.polarDerivative_eq_zero])
    (by rw [hcol 2]; simp [h₂.polarDerivative_eq_zero])

end PlaneCurves.Projective

end
