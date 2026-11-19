/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.Line
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Bezout.Corollaries
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Hessian.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.IntersectionNumber.Properties
public import PlaneCurves.LinearAlgebra.Matrix.GeneralLinearGroup

/-!
# Flexes of projective plane curves

Let `F` be a form in `X, Y, Z` over a field `k` and `P` a simple point of the curve `F = 0`, with
tangent line `T = F_X(P) X + F_Y(P) Y + F_Z(P) Z`. Then `I(P, F ∩ T) ≥ 2`; `P` is a *flex* of
`F` if `I(P, F ∩ T) ≥ 3`, and an *ordinary flex* if `I(P, F ∩ T) = 3` ([Fulton2008],
Problem 3.12 and §5.3). A line component of `F` through `P` makes `I(P, F ∩ T) = ⊤`, so `P` is
then a flex, as in Fulton.

Since a simple point has only one tangent line up to a nonzero scalar, the definitions do not
depend on the tangent line chosen (`isFlex_iff_of_isTangentAt`), nor on the representative of
`P`, and they are invariant under nonzero scalars and projective changes of coordinates.

**The Hessian criterion** (Problem 5.23). Let `F` have degree `n` and `H = det (Fᵢⱼ)` be its
Hessian determinant. For `P` on `F = 0`, `H(P) = 0` iff `P` is a flex or a multiple point,
when `2 (n - 1) ≠ 0` in `k`; and `I(P, H ∩ F) = 1` iff `P` is an ordinary flex, when
`6 (n - 1) ≠ 0`. A simple point and its tangent are moved to `[0 : 0 : 1]` and `Y = 0`; in the
chart `Z = 1`, `H ≡ -(n - 1)² g` modulo `f` for `g = f_y² f_xx + f_x² f_yy - 2 f_x f_y f_xy`
(`MvPolynomial.IsHomogeneous.dehomogenize_det_hessian_add_mem_span`), and `g(0)`, `g_x(0)` are
`2` and `6` times the coefficients of `x²` and `x³` in `f`.

## Main definitions

* `PlaneCurves.Projective.IsFlex F P`: `P` is a simple point of `F` with `I(P, F ∩ T) ≥ 3` for
  the tangent line `T` at `P`.
* `PlaneCurves.Projective.IsOrdinaryFlex F P`: `P` is a simple point of `F` with
  `I(P, F ∩ T) = 3`.

## Main results

* `PlaneCurves.Projective.isFlex_iff_of_isTangentAt`,
  `PlaneCurves.Projective.isOrdinaryFlex_iff_of_isTangentAt`: any tangent line at `P` may be used.
* `PlaneCurves.Projective.isFlex_linearSubst_iff`,
  `PlaneCurves.Projective.isOrdinaryFlex_linearSubst_iff`: invariance under projective changes
  of coordinates.
* `PlaneCurves.Projective.isOrdinaryFlex_X_one_mul_X_two_sq_sub_X_zero_pow_three`: `[0 : 0 : 1]`
  is an ordinary flex of `Y Z² - X³`.
* `PlaneCurves.Projective.IsMultiplePoint.eval_det_hessian_eq_zero`: the Hessian vanishes at
  multiple points.
* `PlaneCurves.Projective.eval_det_hessian_eq_zero_iff`: `H(P) = 0` iff `P` is a flex or a
  multiple point.
* `PlaneCurves.Projective.intersectionNumber_det_hessian_eq_one_iff`: `I(P, H ∩ F) = 1` iff `P`
  is an ordinary flex.
* `PlaneCurves.Projective.IsNonsingular.exists_isFlex`: a nonsingular curve of degree `n ≥ 3`
  has a flex, when `2 (n - 1) ≠ 0`.
* `PlaneCurves.Projective.IsFlex.isOrdinaryFlex_of_irreducible`: flexes of an irreducible cubic
  are ordinary.
* `PlaneCurves.Projective.IsNonsingular.ncard_setOf_isFlex`: a nonsingular cubic has exactly
  nine flexes, when `6 ≠ 0`.
* `PlaneCurves.Projective.isFlex_det_hessian_spec`: the Hessian criterion and the nine flexes
  of a nonsingular cubic together.

## References

* [W. Fulton, *Algebraic Curves: An Introduction to Algebraic Geometry*][Fulton2008],
  Problem 3.12, §5.3, Problem 5.23
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F L : MvPolynomial (Fin 3) k} {P : ℙ k (Fin 3 → k)} {d : ℕ}

/-- `P` is a *flex* of the plane curve `F` if it is a simple point of `F` and the tangent line
`T` at `P` meets `F` there with intersection number `I(P, F ∩ T) ≥ 3`. -/
def IsFlex (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k)) : Prop :=
  IsSimplePoint F P ∧ 3 ≤ intersectionNumber P F (tangentLine F P.rep)

theorem isFlex_def :
    IsFlex F P ↔ IsSimplePoint F P ∧ 3 ≤ intersectionNumber P F (tangentLine F P.rep) :=
  (Iff.rfl)

/-- `P` is an *ordinary flex* of the plane curve `F` if it is a simple point of `F` and the
tangent line `T` at `P` meets `F` there with intersection number `I(P, F ∩ T) = 3`. -/
def IsOrdinaryFlex (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k)) : Prop :=
  IsSimplePoint F P ∧ intersectionNumber P F (tangentLine F P.rep) = 3

theorem isOrdinaryFlex_def :
    IsOrdinaryFlex F P ↔ IsSimplePoint F P ∧ intersectionNumber P F (tangentLine F P.rep) = 3 :=
  (Iff.rfl)

theorem IsFlex.isSimplePoint (h : IsFlex F P) : IsSimplePoint F P :=
  h.1

theorem IsOrdinaryFlex.isSimplePoint (h : IsOrdinaryFlex F P) : IsSimplePoint F P :=
  h.1

/-- An ordinary flex is a flex. -/
theorem IsOrdinaryFlex.isFlex (h : IsOrdinaryFlex F P) : IsFlex F P :=
  ⟨h.1, h.2.ge⟩

/-! ### Independence of the tangent line -/

/-- At a simple point, the intersection number of `F` with a tangent line `L` is that with the
tangent line `F_X(P) X + F_Y(P) Y + F_Z(P) Z`. -/
theorem IsSimplePoint.intersectionNumber_eq_of_isTangentAt (hF : F.IsHomogeneous d)
    (h : IsSimplePoint F P) (hL : IsTangentAt F P L) :
    intersectionNumber P F L = intersectionNumber P F (tangentLine F P.rep) :=
  intersectionNumber_congr_right_of_associated
    (h.associated_tangentLine_of_isTangentAt hF hL)

/-- A simple point `P` is a flex iff `I(P, F ∩ L) ≥ 3` for some, equivalently every, tangent
line `L` at `P`. -/
theorem isFlex_iff_of_isTangentAt (hF : F.IsHomogeneous d) (h : IsSimplePoint F P)
    (hL : IsTangentAt F P L) : IsFlex F P ↔ 3 ≤ intersectionNumber P F L := by
  rw [isFlex_def, h.intersectionNumber_eq_of_isTangentAt hF hL, and_iff_right h]

/-- A simple point `P` is an ordinary flex iff `I(P, F ∩ L) = 3` for some, equivalently every,
tangent line `L` at `P`. -/
theorem isOrdinaryFlex_iff_of_isTangentAt (hF : F.IsHomogeneous d) (h : IsSimplePoint F P)
    (hL : IsTangentAt F P L) : IsOrdinaryFlex F P ↔ intersectionNumber P F L = 3 := by
  rw [isOrdinaryFlex_def, h.intersectionNumber_eq_of_isTangentAt hF hL, and_iff_right h]

/-- A simple point `P` is a flex iff some tangent line meets `F` at `P` with multiplicity at
least three. -/
theorem isFlex_iff_exists_isTangentAt (hF : F.IsHomogeneous d) :
    IsFlex F P ↔ IsSimplePoint F P ∧ ∃ L, IsTangentAt F P L ∧ 3 ≤ intersectionNumber P F L := by
  refine ⟨fun h ↦ ⟨h.1, _, h.1.isTangentAt_tangentLine hF, h.2⟩, fun ⟨h, L, hL, hI⟩ ↦ ?_⟩
  exact (isFlex_iff_of_isTangentAt hF h hL).2 hI

/-! ### Scalars and changes of coordinates -/

/-- Flexes do not change when `F` is multiplied by a nonzero scalar. -/
@[simp]
theorem isFlex_smul_iff {c : k} (hc : c ≠ 0) : IsFlex (c • F) P ↔ IsFlex F P := by
  rw [isFlex_def, isFlex_def, isSimplePoint_smul_iff hc, tangentLine_smul,
    intersectionNumber_smul_left hc, intersectionNumber_smul_right hc]

/-- Ordinary flexes do not change when `F` is multiplied by a nonzero scalar. -/
@[simp]
theorem isOrdinaryFlex_smul_iff {c : k} (hc : c ≠ 0) :
    IsOrdinaryFlex (c • F) P ↔ IsOrdinaryFlex F P := by
  rw [isOrdinaryFlex_def, isOrdinaryFlex_def, isSimplePoint_smul_iff hc, tangentLine_smul,
    intersectionNumber_smul_left hc, intersectionNumber_smul_right hc]

/-- Flexes do not change when `F` is multiplied by a nonzero constant polynomial. -/
theorem isFlex_C_mul_iff {c : k} (hc : c ≠ 0) :
    IsFlex (C c * F) P ↔ IsFlex F P := by
  rw [← smul_eq_C_mul, isFlex_smul_iff hc]

/-- Ordinary flexes do not change when `F` is multiplied by a nonzero constant polynomial. -/
theorem isOrdinaryFlex_C_mul_iff {c : k} (hc : c ≠ 0) :
    IsOrdinaryFlex (C c * F) P ↔ IsOrdinaryFlex F P := by
  rw [← smul_eq_C_mul, isOrdinaryFlex_smul_iff hc]

/-- The intersection numbers with the tangent line at a simple point under a projective change
of coordinates: for `T` the tangent line of `F` at `MQ`, `T(MX)` is tangent to `F(MX)` at `Q`,
and meets it there as `T` meets `F` at `MQ`. -/
private theorem isSimplePoint_linearSubst_aux (hF : F.IsHomogeneous d) (M : GL (Fin 3) k)
    (Q : ℙ k (Fin 3 → k))
    (h : IsSimplePoint F (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) Q)) :
    IsTangentAt (linearSubst M.1 F) Q (linearSubst M.1
      (tangentLine F (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) Q).rep)) ∧
    intersectionNumber Q (linearSubst M.1 F) (linearSubst M.1
      (tangentLine F (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) Q).rep)) =
      intersectionNumber (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) Q) F
        (tangentLine F (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) Q).rep) :=
  ⟨(isTangentAt_linearSubst_iff hF _ Q).2 (h.isTangentAt_tangentLine hF),
    intersectionNumber_linearSubst hF (isHomogeneous_tangentLine _ _) M Q⟩

/-- **Flexes under a change of coordinates.** For a form `F`, an invertible matrix `M` with
projective change of coordinates `T`, and `F^T = F(M X)`, `Q` is a flex of `F^T` iff `T(Q)` is a
flex of `F`. -/
theorem isFlex_linearSubst_iff (hF : F.IsHomogeneous d) (M : GL (Fin 3) k)
    (Q : ℙ k (Fin 3 → k)) :
    IsFlex (linearSubst M.1 F) Q ↔
      IsFlex F (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) Q) := by
  have hs := isSimplePoint_linearSubst_iff hF (Matrix.mulVec_injective_of_isUnit M.isUnit) Q
  by_cases h : IsSimplePoint F (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) Q)
  · obtain ⟨hT, hI⟩ := isSimplePoint_linearSubst_aux hF M Q h
    rw [isFlex_iff_of_isTangentAt (hF.linearSubst _) (hs.2 h) hT, hI,
      isFlex_iff_of_isTangentAt hF h (h.isTangentAt_tangentLine hF)]
  · exact iff_of_false (fun h' ↦ h (hs.1 h'.1)) fun h' ↦ h h'.1

/-- **Ordinary flexes under a change of coordinates.** `Q` is an ordinary flex of `F(M X)` iff
`T(Q)` is an ordinary flex of `F`, for `T` the projective change of coordinates of `M`. -/
theorem isOrdinaryFlex_linearSubst_iff (hF : F.IsHomogeneous d) (M : GL (Fin 3) k)
    (Q : ℙ k (Fin 3 → k)) :
    IsOrdinaryFlex (linearSubst M.1 F) Q ↔
      IsOrdinaryFlex F (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) Q) := by
  have hs := isSimplePoint_linearSubst_iff hF (Matrix.mulVec_injective_of_isUnit M.isUnit) Q
  by_cases h : IsSimplePoint F (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) Q)
  · obtain ⟨hT, hI⟩ := isSimplePoint_linearSubst_aux hF M Q h
    rw [isOrdinaryFlex_iff_of_isTangentAt (hF.linearSubst _) (hs.2 h) hT, hI,
      isOrdinaryFlex_iff_of_isTangentAt hF h (h.isTangentAt_tangentLine hF)]
  · exact iff_of_false (fun h' ↦ h (hs.1 h'.1)) fun h' ↦ h h'.1

/-! ### An example -/

/-- `[0 : 0 : 1]` is an ordinary flex of the cubic `Y Z² - X³`: in the chart
`Z = 1` it is `y - x³`, with tangent `y = 0` at the origin, met with intersection number three. -/
theorem isOrdinaryFlex_X_one_mul_X_two_sq_sub_X_zero_pow_three :
    IsOrdinaryFlex (X 1 * X 2 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 3) k)
      (mk k ![0, 0, 1] (by simp)) := by
  set F : MvPolynomial (Fin 3) k := X 1 * X 2 ^ 2 - X 0 ^ 3
  set P : ℙ k (Fin 3 → k) := mk k ![0, 0, 1] (by simp)
  have hF : F.IsHomogeneous 3 :=
    (((isHomogeneous_X k 1).mul ((isHomogeneous_X k 2).pow 2))).sub ((isHomogeneous_X k 0).pow 3)
  have hS : IsSimplePoint F P := by
    rw [isSimplePoint_mk_iff hF]
    refine ⟨by simp [F], 1, ?_⟩
    simp [F, pderiv_X]
  have hX0 : (X 0 : MvPolynomial (Fin 3) k).IsHomogeneous 1 := isHomogeneous_X k 0
  have hX1 : (X 1 : MvPolynomial (Fin 3) k).IsHomogeneous 1 := isHomogeneous_X k 1
  have hP2 : P ∈ affineOpen 2 := by simp [P]
  have h01 : intersectionNumber P (X 1) (X 0) = 1 := by
    have ha : affineChart 2 P = 0 := by
      funext j
      fin_cases j <;> simp [P, Fin.succAbove, Fin.lt_def]
    rw [intersectionNumber_eq_affine hX1 hX0 hP2, ha, Affine.intersectionNumber_comm]
    simpa [Fin.insertNth_apply_below (show (1 : Fin 3) < 2 by decide)] using
      Affine.intersectionNumber_X_sub_C_X_sub_C (0 : Fin 2 → k)
  have hI : intersectionNumber P F (X 1) = 3 := by
    have hF' : F = (-1 : k) • (X 0 ^ 2 * X 0) + X 2 ^ 2 * X 1 := by
      simp only [F, neg_smul, one_smul]
      ring
    rw [intersectionNumber_comm, hF', intersectionNumber_add_mul,
      intersectionNumber_smul_right (by simp),
      intersectionNumber_mul_right hX1 (hX0.pow 2) hX0, pow_two,
      intersectionNumber_mul_right hX1 hX0 hX0, h01]
    rfl
  have hT : IsTangentAt F P (X 1) := by
    rw [isTangentAt_iff_mult_lt_intersectionNumber hF hS.ne_zero hX1 (X_ne_zero 1)]
    · rw [hI, isSimplePoint_def.1 hS]
      decide
    · rw [hX1.eval_rep_mk_eq_zero_iff]
      simp
  exact (isOrdinaryFlex_iff_of_isTangentAt hF hS hT).2 hI

end PlaneCurves.Projective

/-! ### The local computation in the chart `Z = 1`

Let `f ∈ k[x, y]` with `f(0) = 0`, `f_x(0) = 0` and `f_y(0) = 1`: the origin is a simple point of
`f` with tangent `y = 0`. With `g = f_y² f_xx + f_x² f_yy - 2 f_x f_y f_xy`, the polynomial that
the Hessian is congruent to modulo `f` (`MvPolynomial.IsHomogeneous.dehomogenize_det_hessian`),
`g(0) = 2a` and `g_x(0) = 6b`, for `a` and `b` the coefficients of `x²` and `x³` in `f`. -/

namespace PlaneCurves.Affine

open MvPolynomial

variable {k : Type*} [Field k] {f : MvPolynomial (Fin 2) k}

private theorem eval_zero_eq_coeff (p : MvPolynomial (Fin 2) k) :
    eval 0 p = p.coeff (Finsupp.single 0 0) := by
  simp [eval_zero, constantCoeff_eq]

private theorem eval_zero_pderiv_zero (p : MvPolynomial (Fin 2) k) :
    eval 0 (pderiv 0 p) = p.coeff (Finsupp.single 0 1) := by
  simp [eval_zero, constantCoeff_eq, coeff_pderiv]

/-- `f_xx(0) = 2a`. -/
private theorem eval_zero_pderiv_pderiv (p : MvPolynomial (Fin 2) k) :
    eval 0 (pderiv 0 (pderiv 0 p)) = 2 * p.coeff (Finsupp.single 0 2) := by
  simp [eval_zero, constantCoeff_eq, coeff_pderiv, ← Finsupp.single_add]
  ring

/-- `f_xxx(0) = 6b`. -/
private theorem eval_zero_pderiv_pderiv_pderiv (p : MvPolynomial (Fin 2) k) :
    eval 0 (pderiv 0 (pderiv 0 (pderiv 0 p))) = 6 * p.coeff (Finsupp.single 0 3) := by
  simp [eval_zero, constantCoeff_eq, coeff_pderiv, ← Finsupp.single_add]
  ring

/-- `g(0) = 2a`. -/
private theorem eval_zero_g (hfx : eval 0 (pderiv 0 f) = 0) (hfy : eval 0 (pderiv 1 f) = 1) :
    eval 0 (pderiv 1 f ^ 2 * pderiv 0 (pderiv 0 f) + pderiv 0 f ^ 2 * pderiv 1 (pderiv 1 f) -
      2 * pderiv 0 f * pderiv 1 f * pderiv 0 (pderiv 1 f)) = 2 * f.coeff (Finsupp.single 0 2) := by
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, hfx, hfy, eval_zero_pderiv_pderiv]
  ring

/-- `g_x(0) = 6b`. -/
private theorem eval_zero_pderiv_g (hfx : eval 0 (pderiv 0 f) = 0) (hfy : eval 0 (pderiv 1 f) = 1) :
    eval 0 (pderiv 0 (pderiv 1 f ^ 2 * pderiv 0 (pderiv 0 f) +
      pderiv 0 f ^ 2 * pderiv 1 (pderiv 1 f) -
      2 * pderiv 0 f * pderiv 1 f * pderiv 0 (pderiv 1 f))) =
        6 * f.coeff (Finsupp.single 0 3) := by
  have h2 : pderiv 0 (2 : MvPolynomial (Fin 2) k) = 0 := by
    simpa using (pderiv 0 : Derivation k (MvPolynomial (Fin 2) k) _).map_natCast 2
  simp only [map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, h2,
    map_mul, map_pow, map_ofNat, nsmul_eq_mul, map_natCast, map_zero, hfx, hfy,
    eval_zero_pderiv_pderiv_pderiv]
  ring

/-- A linear form `a X + b Y` associated with `Y` has `a = 0`. -/
private theorem eq_zero_of_associated_X_one {a b : k}
    (h : Associated (X 1 : MvPolynomial (Fin 2) k) (a • X 0 + b • X 1)) :
    a = 0 := by
  obtain ⟨u, hu⟩ := h
  have := congrArg (fun p : MvPolynomial (Fin 2) k ↦ p.coeff (Finsupp.single 0 1)) hu
  rw [mul_comm, coeff_mul_X'] at this
  simpa [coeff_X, Finsupp.single_eq_single_iff] using this.symm

/-- `I(0, g ∩ f) = 1` iff `a = 0` and `b ≠ 0`, when `2` and `6` are invertible. -/
private theorem intersectionNumber_g_eq_one_iff (h2 : (2 : k) ≠ 0) (h6 : (6 : k) ≠ 0)
    (hf0 : eval 0 f = 0) (hfx : eval 0 (pderiv 0 f) = 0) (hfy : eval 0 (pderiv 1 f) = 1) :
    intersectionNumber 0 (pderiv 1 f ^ 2 * pderiv 0 (pderiv 0 f) +
      pderiv 0 f ^ 2 * pderiv 1 (pderiv 1 f) -
      2 * pderiv 0 f * pderiv 1 f * pderiv 0 (pderiv 1 f)) f = 1 ↔
      f.coeff (Finsupp.single 0 2) = 0 ∧ f.coeff (Finsupp.single 0 3) ≠ 0 := by
  set g := pderiv 1 f ^ 2 * pderiv 0 (pderiv 0 f) + pderiv 0 f ^ 2 * pderiv 1 (pderiv 1 f) -
      2 * pderiv 0 f * pderiv 1 f * pderiv 0 (pderiv 1 f)
  have hg0 : eval 0 g = 2 * f.coeff (Finsupp.single 0 2) := eval_zero_g hfx hfy
  have hgx : eval 0 (pderiv 0 g) = 6 * f.coeff (Finsupp.single 0 3) := eval_zero_pderiv_g hfx hfy
  have hfs : IsSimplePoint f 0 := isSimplePoint_def.2 ⟨hf0, 1, by rw [hfy]; exact one_ne_zero⟩
  have hlf : f.leadingFormAt 0 = X 1 := by
    rw [hfs.leadingFormAt_eq, Fin.sum_univ_two, hfx, hfy, zero_smul, zero_add, one_smul]
  rw [intersectionNumber_eq_one_iff]
  constructor
  · rintro ⟨hgs, -, hna⟩
    have hc2 : f.coeff (Finsupp.single 0 2) = 0 := by
      have := hgs.eval_eq_zero
      rw [hg0] at this
      exact (mul_eq_zero.1 this).resolve_left h2
    refine ⟨hc2, fun hc3 ↦ hna ?_⟩
    have hgy : eval 0 (pderiv 1 g) ≠ 0 := by
      obtain ⟨-, i, hi⟩ := isSimplePoint_def.1 hgs
      fin_cases i
      · simp only [Fin.zero_eta] at hi
        rw [hgx, hc3, mul_zero] at hi
        exact absurd rfl hi
      · exact hi
    rw [hgs.leadingFormAt_eq, hlf, Fin.sum_univ_two, hgx, hc3, mul_zero, zero_smul, zero_add,
      smul_eq_C_mul]
    exact associated_unit_mul_left _ _ ((Ne.isUnit hgy).map C)
  · rintro ⟨hc2, hc3⟩
    have hgs : IsSimplePoint g 0 :=
      isSimplePoint_def.2 ⟨by rw [hg0, hc2, mul_zero], 0, by rw [hgx]; exact mul_ne_zero h6 hc3⟩
    refine ⟨hgs, hfs, fun h ↦ ?_⟩
    rw [hgs.leadingFormAt_eq, hlf, Fin.sum_univ_two, hgx] at h
    exact mul_ne_zero h6 hc3 (eq_zero_of_associated_X_one h.symm)

end PlaneCurves.Affine

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization Matrix

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {P : ℙ k (Fin 3 → k)} {n : ℕ}

/-! ### The Hessian criterion -/

/-- **The Hessian vanishes at multiple points.** If `P` is a multiple point of a form `F`, the
Hessian determinant `H = det (Fᵢⱼ)` of `F` vanishes at `P`. -/
theorem IsMultiplePoint.eval_det_hessian_eq_zero (hF : F.IsHomogeneous n)
    (h : IsMultiplePoint F P) : eval P.rep (TauCeti.hessian pderiv F).det = 0 := by
  have hz := (isMultiplePoint_iff_eval_rep.1 h).2
  rw [RingHom.map_det]
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨P.rep, P.rep_ne_zero, ?_⟩
  funext i
  have := congrArg (eval P.rep) (congrFun hF.hessian_mulVec_X i)
  simpa [Matrix.mulVec, dotProduct, hz] using this

private theorem eval_dehomogenize_two (p : MvPolynomial (Fin 3) k) :
    eval 0 (dehomogenize 2 p) = eval (Pi.single 2 1) p := by
  rw [eval_dehomogenize]
  rw [show (Fin.insertNth 2 1 0 : Fin 3 → k) = Pi.single 2 1 by
    funext j; fin_cases j <;> simp [Fin.insertNth_apply_below]]

private theorem eval_pderiv_dehomogenize_two (p : MvPolynomial (Fin 3) k) (j : Fin 2) :
    eval 0 (pderiv j (dehomogenize 2 p)) = eval (Pi.single 2 1) (pderiv j.castSucc p) := by
  rw [pderiv_dehomogenize, eval_dehomogenize_two, show (2 : Fin 3) = Fin.last 2 from rfl,
    Fin.succAbove_last]

private theorem affineChart_two_mk :
    affineChart 2 (mk k (Pi.single 2 1 : Fin 3 → k) (by simp)) = 0 := by
  funext j
  fin_cases j <;> simp [Fin.succAbove, Fin.lt_def]

/-- The chart `Z = 1` after moving a simple point `P` of `F` to `[0 : 0 : 1]` and its tangent to
`Y = 0` by some `M`: with `f = F(M X)(x, y, 1)`, the origin is a simple point of `f` with
`f_x(0) = 0`, `f_y(0) = 1`, and the intersection numbers of `F` with its tangent and with its
Hessian `H` at `P`, and the vanishing of `H` at `P`, are read off in the chart. -/
private theorem chart_data (hF : F.IsHomogeneous n) (h : IsSimplePoint F P) :
    ∃ M : GL (Fin 3) k,
      eval 0 (dehomogenize 2 (linearSubst M.1 F)) = 0 ∧
      eval 0 (pderiv 0 (dehomogenize 2 (linearSubst M.1 F))) = 0 ∧
      eval 0 (pderiv 1 (dehomogenize 2 (linearSubst M.1 F))) = 1 ∧
      intersectionNumber P F (tangentLine F P.rep) =
        Affine.intersectionNumber 0 (X 1) (dehomogenize 2 (linearSubst M.1 F)) ∧
      (eval P.rep (TauCeti.hessian pderiv F).det = 0 ↔
        eval 0 (dehomogenize 2 (TauCeti.hessian pderiv (linearSubst M.1 F)).det) = 0) ∧
      intersectionNumber P (TauCeti.hessian pderiv F).det F =
        Affine.intersectionNumber 0
          (dehomogenize 2 (TauCeti.hessian pderiv (linearSubst M.1 F)).det)
          (dehomogenize 2 (linearSubst M.1 F)) := by
  set t : Fin 3 → k := fun i ↦ eval P.rep (pderiv i F)
  have ht : t ≠ 0 := by
    obtain ⟨-, i, hi⟩ := isSimplePoint_iff_eval_rep.1 h
    exact fun h0 ↦ hi (congrFun h0 i)
  have htp : t ⬝ᵥ P.rep = 0 := by
    simpa [dotProduct] using eval_tangentLine_self hF h.eval_rep_eq_zero
  obtain ⟨M, hMp, hMt⟩ :=
    Matrix.exists_mulVec_single_eq_and_vecMul_eq_single ht P.rep_ne_zero htp
  set e : Fin 3 → k := Pi.single 2 1
  have he : e ≠ 0 := by simp [e]
  set Q := mk k e he
  have hQP : map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) Q = P := by
    erw [map_mk]
    simp only [Matrix.mulVecLin_apply, hMp]
    exact P.mk_rep
  have hQ : Q ∈ affineOpen 2 := by simp [Q, e]
  have hF' := hF.linearSubst M.1
  have hdet : M.1.det ^ 2 ≠ 0 :=
    pow_ne_zero _ ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit).ne_zero
  have hd (j : Fin 3) :
      eval e (pderiv j (linearSubst M.1 F)) = (Pi.single 1 1 : Fin 3 → k) j := by
    rw [← hMt]
    simp [pderiv_linearSubst, eval_linearSubst, hMp, Matrix.vecMul, dotProduct, mul_comm, t]
  have hT : linearSubst M.1 (tangentLine F P.rep) = X 1 := by
    have : linearSubst M.1 (tangentLine F P.rep) = ∑ j, C ((t ᵥ* M.1) j) * X j := by
      simp only [tangentLine_def, map_mul, linearSubst_X, Matrix.vecMul, dotProduct,
        Fin.sum_univ_three, map_add, map_mul, algHom_C, t]
      simp only [algebraMap_eq]
      ring
    rw [this, hMt]
    simp [Fin.sum_univ_three]
  refine ⟨M, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eval_dehomogenize_two, eval_linearSubst, hMp]
    exact h.eval_rep_eq_zero
  · rw [eval_pderiv_dehomogenize_two]
    simpa using hd 0
  · rw [eval_pderiv_dehomogenize_two]
    simpa using hd 1
  · calc intersectionNumber P F (tangentLine F P.rep)
        = intersectionNumber (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) Q)
            F (tangentLine F P.rep) := by rw [hQP]
      _ = intersectionNumber Q (linearSubst M.1 F) (X 1) := by
        rw [← hT, intersectionNumber_linearSubst hF (isHomogeneous_tangentLine _ _)]
      _ = _ := by
        rw [intersectionNumber_eq_affine hF' (isHomogeneous_X k 1) hQ, affineChart_two_mk,
          Affine.intersectionNumber_comm]
        simp [dehomogenize_X, Fin.insertNth_apply_below]
  · rw [eval_dehomogenize_two, eval_det_hessian_linearSubst, hMp, mul_eq_zero,
      or_iff_right hdet]
  · calc intersectionNumber P (TauCeti.hessian pderiv F).det F
        = intersectionNumber (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) Q)
            (TauCeti.hessian pderiv F).det F := by rw [hQP]
      _ = intersectionNumber Q (TauCeti.hessian pderiv (linearSubst M.1 F)).det
            (linearSubst M.1 F) := by
        rw [det_hessian_linearSubst, ← smul_eq_C_mul, intersectionNumber_smul_left hdet,
          intersectionNumber_linearSubst hF.det_hessian hF]
      _ = _ := by
        rw [intersectionNumber_eq_affine hF'.det_hessian hF' hQ, affineChart_two_mk]

/-- In the chart `Z = 1`, at the origin of a simple point with tangent `y = 0`, the Hessian
of a form `F` of degree `n` is `-(n - 1)² g(0) = -2 (n - 1)² a`, for `a` the coefficient of `x²`
in `f = F(x, y, 1)`. -/
private theorem eval_zero_dehomogenize_det_hessian (hF : F.IsHomogeneous n)
    (hf0 : eval 0 (dehomogenize 2 F) = 0) (hfx : eval 0 (pderiv 0 (dehomogenize 2 F)) = 0)
    (hfy : eval 0 (pderiv 1 (dehomogenize 2 F)) = 1) :
    eval 0 (dehomogenize 2 (TauCeti.hessian pderiv F).det) =
      -(((n - 1 : ℕ) : k) ^ 2 * (2 * (dehomogenize 2 F).coeff (Finsupp.single 0 2))) := by
  rw [hF.dehomogenize_det_hessian]
  set f := dehomogenize 2 F
  have hg := Affine.eval_zero_g hfx hfy
  generalize pderiv 1 f ^ 2 * pderiv 0 (pderiv 0 f) + pderiv 0 f ^ 2 * pderiv 1 (pderiv 1 f) -
    2 * pderiv 0 f * pderiv 1 f * pderiv 0 (pderiv 1 f) = g at hg ⊢
  simp only [map_sub, map_mul, map_pow, map_natCast, hf0, hg, mul_zero, zero_mul, zero_sub]

/-- **Hessian criterion for flexes** ([Fulton2008], Problem 5.23). Let `F` be a form of degree
`n`, `H` its Hessian determinant and `P` a point of the curve `F = 0`. If `2 (n - 1) ≠ 0` in
`k`, then `H(P) = 0` iff `P` is a flex or a multiple point of `F`. -/
theorem eval_det_hessian_eq_zero_iff (hF : F.IsHomogeneous n)
    (hP : P ∈ zeroLocus {F}) (h : (2 * (n - 1) : k) ≠ 0) :
    eval P.rep (TauCeti.hessian pderiv F).det = 0 ↔ IsFlex F P ∨ IsMultiplePoint F P := by
  rcases isSimplePoint_or_isMultiplePoint hF hP with hs | hm
  · obtain ⟨M, hf0, hfx, hfy, hT, hH, -⟩ := chart_data hF hs
    rw [← Nat.cast_pred (Nat.pos_of_ne_zero (hs.degree_ne_zero hF))] at h
    have h2 : (2 : k) ≠ 0 := left_ne_zero_of_mul h
    have hn : ((n - 1 : ℕ) : k) ≠ 0 := right_ne_zero_of_mul h
    rw [isFlex_def, hT, hH, eval_zero_dehomogenize_det_hessian (hF.linearSubst M.1) hf0 hfx hfy,
      neg_eq_zero, mul_eq_zero, or_iff_right (pow_ne_zero _ hn), mul_eq_zero, or_iff_right h2,
      and_iff_right hs, or_iff_left fun hm ↦ hm.not_isSimplePoint hs,
      show (3 : ℕ∞) = ((3 : ℕ) : ℕ∞) from rfl, Affine.le_intersectionNumber_X_one_iff]
    rw [Affine.eval_zero_eq_coeff] at hf0
    rw [Affine.eval_zero_pderiv_zero] at hfx
    refine ⟨fun h2 d hd ↦ ?_, fun h ↦ h 2 (by norm_num)⟩
    interval_cases d <;> assumption
  · exact iff_of_true (hm.eval_det_hessian_eq_zero hF) (Or.inr hm)

/-- **Hessian criterion for ordinary flexes** ([Fulton2008], Problem 5.23). Let `F` be a form of
degree `n`, `H` its Hessian determinant and `P` a point of the curve `F = 0`. If
`6 (n - 1) ≠ 0` in `k`, then `I(P, H ∩ F) = 1` iff `P` is an ordinary flex of `F`. -/
theorem intersectionNumber_det_hessian_eq_one_iff (hF : F.IsHomogeneous n)
    (hP : P ∈ zeroLocus {F}) (h : (6 * (n - 1) : k) ≠ 0) :
    intersectionNumber P (TauCeti.hessian pderiv F).det F = 1 ↔ IsOrdinaryFlex F P := by
  rcases isSimplePoint_or_isMultiplePoint hF hP with hs | hm
  · obtain ⟨M, hf0, hfx, hfy, hT, -, hI⟩ := chart_data hF hs
    rw [← Nat.cast_pred (Nat.pos_of_ne_zero (hs.degree_ne_zero hF))] at h
    have h6 : (6 : k) ≠ 0 := left_ne_zero_of_mul h
    have h2 : (2 : k) ≠ 0 := fun h2 ↦
      h6 (by rw [show (6 : k) = 2 * 3 by norm_num, h2, zero_mul])
    have hn : ((n - 1 : ℕ) : k) ≠ 0 := right_ne_zero_of_mul h
    have hmem := (hF.linearSubst M.1).dehomogenize_det_hessian_add_mem_span
    rw [← map_natCast C, ← map_pow] at hmem
    rw [isOrdinaryFlex_def, and_iff_right hs, hT, hI,
      Affine.intersectionNumber_eq_of_add_C_mul_mem_span (pow_ne_zero 2 hn) hmem,
      Affine.intersectionNumber_g_eq_one_iff h2 h6 hf0 hfx hfy]
    rw [Affine.eval_zero_eq_coeff] at hf0
    rw [Affine.eval_zero_pderiv_zero] at hfx
    have h34 (I : ℕ∞) :
        I = 3 ↔ ((3 : ℕ) : ℕ∞) ≤ I ∧ ¬((4 : ℕ) : ℕ∞) ≤ I := by
      refine ⟨by rintro rfl; norm_num, fun ⟨h3, h4⟩ ↦ le_antisymm ?_ h3⟩
      rw [not_le] at h4
      exact Order.le_of_lt_add_one h4
    rw [h34, Affine.le_intersectionNumber_X_one_iff, Affine.le_intersectionNumber_X_one_iff]
    refine ⟨fun ⟨hc2, hc3⟩ ↦ ⟨fun d hd ↦ ?_, fun h4 ↦ hc3 (h4 3 (by norm_num))⟩,
      fun ⟨h3, h4⟩ ↦ ⟨h3 2 (by norm_num), fun hc3 ↦ h4 fun d hd ↦ ?_⟩⟩
    · interval_cases d <;> assumption
    · interval_cases d
      exacts [h3 0 (by norm_num), h3 1 (by norm_num), h3 2 (by norm_num), hc3]
  · refine iff_of_false (fun h1 ↦ ?_) fun h' ↦ hm.not_isSimplePoint h'.isSimplePoint
    have hH : 1 ≤ mult (TauCeti.hessian pderiv F).det P :=
      Order.one_le_iff_pos.2 (mult_pos_iff_eval_rep.2 (hm.eval_det_hessian_eq_zero hF))
    have := (mul_le_mul' hH (isMultiplePoint_def.1 hm)).trans
      (mul_mult_le_intersectionNumber hF.det_hessian hF)
    rw [h1] at this
    norm_num at this

/-! ### Flexes of nonsingular curves and the nine flexes of a cubic -/

section IsAlgClosed

variable [IsAlgClosed k]

/-- **Nonsingular curves have flexes** ([Fulton2008], Corollary of Problem 5.23). Over an
algebraically closed field, a nonsingular plane curve `F` of degree `n ≥ 3` has a flex, when
`2 (n - 1) ≠ 0` in `k`: the Hessian `H`, of degree `3 (n - 2) > 0`, meets `F`, and a common
zero is a flex since `F` has no multiple points. -/
theorem IsNonsingular.exists_isFlex (hF : F.IsHomogeneous n) (h : IsNonsingular F)
    (hn : 3 ≤ n) (hchar : (2 * (n - 1) : k) ≠ 0) : ∃ P, IsFlex F P := by
  classical
  set H := (TauCeti.hessian pderiv F).det
  have hH : H.IsHomogeneous (3 * (n - 2)) := by simpa using hF.det_hessian
  have hS : ∀ f ∈ (({F, H} : Finset (MvPolynomial (Fin 3) k)) : Set (MvPolynomial (Fin 3) k)),
      ∃ d ≠ 0, f.IsHomogeneous d := by
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    exact ⟨⟨n, by omega, hF⟩, ⟨_, by omega, hH⟩⟩
  obtain ⟨P, hP⟩ := zeroLocus_nonempty_of_card_le (n := 2) Finset.card_le_two hS
  rw [mem_zeroLocus_iff_eval_rep fun f hf ↦ (hS f hf).imp fun _ ↦ And.right] at hP
  have hPF : P ∈ zeroLocus {F} :=
    (mem_zeroLocus_iff_eval_rep (by simpa using ⟨n, hF⟩)).2 (by simpa using hP F (by simp))
  rcases (eval_det_hessian_eq_zero_iff hF hPF hchar).1 (hP H (by simp)) with hfl | hm
  · exact ⟨P, hfl⟩
  · exact absurd ((isNonsingular_iff_forall_isSimplePoint hF).1 h P hPF) hm.not_isSimplePoint

/-- A simple point `P` of a plane curve `F` of degree `n` whose tangent line `T` at `P` is not a
component of `F` has `I(P, F ∩ T) ≤ n`. -/
theorem IsSimplePoint.intersectionNumber_tangentLine_le (hF : F.IsHomogeneous n)
    (h : IsSimplePoint F P) (hT : ¬tangentLine F P.rep ∣ F) :
    intersectionNumber P F (tangentLine F P.rep) ≤ n := by
  have hT0 : tangentLine F P.rep ≠ 0 := by
    have hs := h
    rw [← P.mk_rep] at hs
    exact hs.tangentLine_ne_zero hF
  have hrel : IsRelPrime F (tangentLine F P.rep) :=
    ((irreducible_of_isHomogeneous_one (isHomogeneous_tangentLine F _) hT0).isRelPrime_iff_not_dvd
      |>.2 hT).symm
  simpa using sum_intersectionNumber_le_mul hF (isHomogeneous_tangentLine F _) hrel {P}

/-- **Flexes of an irreducible cubic are ordinary.** A line meets an irreducible cubic in three
points counted with multiplicity, so the tangent line at a flex meets it there exactly three
times. -/
theorem IsFlex.isOrdinaryFlex_of_irreducible (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (h : IsFlex F P) : IsOrdinaryFlex F P := by
  refine ⟨h.1, le_antisymm (h.1.intersectionNumber_tangentLine_le hF fun hT ↦ ?_) h.2⟩
  have hT0 : tangentLine F P.rep ≠ 0 := fun h0 ↦ by
    rw [h0, zero_dvd_iff] at hT
    exact hirr.ne_zero hT
  have hTirr := irreducible_of_isHomogeneous_one (isHomogeneous_tangentLine F P.rep) hT0
  have := totalDegree_le_of_dvd_of_isDomain (hTirr.associated_of_dvd hirr hT).symm.dvd hT0
  rw [hF.totalDegree hirr.ne_zero, (isHomogeneous_tangentLine F _).totalDegree hT0] at this
  omega

/-- On a nonsingular cubic, every flex is ordinary. -/
theorem IsNonsingular.isOrdinaryFlex_of_isFlex (hF : F.IsHomogeneous 3) (h : IsNonsingular F)
    (hP : IsFlex F P) : IsOrdinaryFlex F P :=
  hP.isOrdinaryFlex_of_irreducible hF (h.irreducible hF (by norm_num))

omit [IsAlgClosed k] in
/-- If `6 ≠ 0` in `k`, the characteristic conditions of the Hessian criterion hold for cubics. -/
private theorem ne_zero_of_six_ne_zero (h6 : (6 : k) ≠ 0) :
    (2 * ((3 : ℕ) - 1) : k) ≠ 0 ∧ (6 * ((3 : ℕ) - 1) : k) ≠ 0 := by
  have h2 : (2 : k) ≠ 0 := fun h2 ↦ h6 (by rw [show (6 : k) = 2 * 3 by norm_num, h2, zero_mul])
  rw [show (2 * ((3 : ℕ) - 1) : k) = 2 * 2 by norm_num,
    show (6 * ((3 : ℕ) - 1) : k) = 6 * 2 by norm_num]
  exact ⟨mul_ne_zero h2 h2, mul_ne_zero h6 h2⟩

open Classical in
/-- On a nonsingular cubic, when `6 ≠ 0` in `k`, the Hessian `H` meets `F` exactly at the flexes,
each with intersection number one: `I(P, H ∩ F)` is `1` at a flex and `0` elsewhere. -/
theorem IsNonsingular.intersectionNumber_det_hessian_eq (hF : F.IsHomogeneous 3)
    (h : IsNonsingular F) (h6 : (6 : k) ≠ 0) (P : ℙ k (Fin 3 → k)) :
    intersectionNumber P (TauCeti.hessian pderiv F).det F = if IsFlex F P then 1 else 0 := by
  obtain ⟨h2, h12⟩ := ne_zero_of_six_ne_zero h6
  have hH := (hF.det_hessian (σ := Fin 3))
  by_cases hPF : P ∈ zeroLocus {F}
  · split_ifs with hfl
    · exact (intersectionNumber_det_hessian_eq_one_iff hF hPF h12).2
        (h.isOrdinaryFlex_of_isFlex hF hfl)
    · refine (intersectionNumber_eq_zero_iff hH hF).2 (Or.inl fun h0 ↦ ?_)
      rcases (eval_det_hessian_eq_zero_iff hF hPF h2).1 h0 with hfl' | hm
      · exact hfl hfl'
      · exact hm.not_isSimplePoint ((isNonsingular_iff_forall_isSimplePoint hF).1 h P hPF)
  · have hfl : ¬IsFlex F P := fun hfl ↦ hPF (hfl.isSimplePoint.mem_zeroLocus hF)
    simp only [hfl, ↓reduceIte]
    refine (intersectionNumber_eq_zero_iff hH hF).2 (Or.inr fun h0 ↦ hPF ?_)
    exact (mem_zeroLocus_iff_eval_rep (by simpa using ⟨3, hF⟩)).2 (by simpa using h0)

/-- On a nonsingular cubic, when `6 ≠ 0` in `k`, the curve and its Hessian are relatively prime:
otherwise `I(P, H ∩ F) = ⊤` at every point, in particular at a flex. -/
theorem IsNonsingular.isRelPrime_det_hessian (hF : F.IsHomogeneous 3) (h : IsNonsingular F)
    (h6 : (6 : k) ≠ 0) : IsRelPrime (TauCeti.hessian pderiv F).det F := by
  have hirr := h.irreducible hF (by norm_num)
  refine (hirr.isRelPrime_iff_not_dvd.2 fun hd ↦ ?_).symm
  obtain ⟨P, hP⟩ := h.exists_isFlex hF le_rfl (ne_zero_of_six_ne_zero h6).1
  have h1 := h.intersectionNumber_det_hessian_eq hF h6 P
  simp only [hP, ↓reduceIte] at h1
  refine (intersectionNumber_ne_top_iff (hF.det_hessian (σ := Fin 3)) hF).1 (by simp [h1]) F
    hirr hd dvd_rfl hP.isSimplePoint.eval_rep_eq_zero

/-- **The nine flexes of a nonsingular cubic** ([Fulton2008], Corollary of Problem 5.23). Over
an algebraically closed field with `6 ≠ 0`, a nonsingular cubic has exactly nine flexes: by
Bézout's theorem its Hessian, a cubic prime to it, meets it in nine points counted with
multiplicity, and these are the flexes, each counted once. -/
theorem IsNonsingular.ncard_setOf_isFlex (hF : F.IsHomogeneous 3) (h : IsNonsingular F)
    (h6 : (6 : k) ≠ 0) : {P | IsFlex F P}.ncard = 9 := by
  classical
  have hH := (hF.det_hessian (σ := Fin 3))
  have hrel := h.isRelPrime_det_hessian hF h6
  have hsum := finsum_intersectionNumber_eq_mul hH hF hrel
  have hfin := finite_support_intersectionNumber hH hF hrel
  have hsupp : (Function.support fun P ↦ intersectionNumber P (TauCeti.hessian pderiv F).det F)
      = {P | IsFlex F P} := by
    ext P
    simp [h.intersectionNumber_det_hessian_eq hF h6 P]
  rw [hsupp] at hfin
  rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ (by rw [hsupp]; simp),
    Finset.sum_congr rfl (g := fun _ ↦ (1 : ℕ∞)) fun P hP ↦
      (h.intersectionNumber_det_hessian_eq hF h6 P).trans
        (by simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hP; simp [hP])] at hsum
  rw [Set.ncard_eq_toFinset_card _ hfin]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Fintype.card_fin] at hsum
  exact_mod_cast hsum

end IsAlgClosed

/-- **Hessian criterion for flexes and the nine flexes of a nonsingular cubic** ([Fulton2008],
Problem 5.23 and its Corollary). Let `k` be algebraically closed, `F` a form of degree `n` and
`H = det (Fᵢⱼ)` its Hessian determinant.

1. If `2 (n - 1) ≠ 0` in `k`, a point `P` of `F = 0` has `H(P) = 0` iff it is a flex or a
   multiple point of `F`.
2. If `6 (n - 1) ≠ 0` in `k`, a point `P` of `F = 0` has `I(P, H ∩ F) = 1` iff it is an
   ordinary flex of `F`.
3. If `F` is nonsingular, `n ≥ 3` and `2 (n - 1) ≠ 0` in `k`, then `F` has a flex.
4. If `F` is a nonsingular cubic and `6 ≠ 0` in `k`, every flex of `F` is ordinary, and `F` has
   exactly nine flexes.

Milestone: *Hessian criterion for flexes and the nine flexes of a nonsingular cubic*. -/
theorem isFlex_det_hessian_spec [IsAlgClosed k] (hF : F.IsHomogeneous n) :
    (∀ P ∈ zeroLocus {F}, (2 * (n - 1) : k) ≠ 0 →
      (eval P.rep (TauCeti.hessian pderiv F).det = 0 ↔ IsFlex F P ∨ IsMultiplePoint F P)) ∧
    (∀ P ∈ zeroLocus {F}, (6 * (n - 1) : k) ≠ 0 →
      (intersectionNumber P (TauCeti.hessian pderiv F).det F = 1 ↔ IsOrdinaryFlex F P)) ∧
    (IsNonsingular F → 3 ≤ n → (2 * (n - 1) : k) ≠ 0 → ∃ P, IsFlex F P) ∧
    (IsNonsingular F → n = 3 → (6 : k) ≠ 0 →
      (∀ P, IsFlex F P → IsOrdinaryFlex F P) ∧ {P | IsFlex F P}.ncard = 9) := by
  refine ⟨fun P hP h ↦ eval_det_hessian_eq_zero_iff hF hP h,
    fun P hP h ↦ intersectionNumber_det_hessian_eq_one_iff hF hP h,
    fun h hn hchar ↦ h.exists_isFlex hF hn hchar, ?_⟩
  rintro h rfl h6
  exact ⟨fun P hP ↦ h.isOrdinaryFlex_of_isFlex hF hP, h.ncard_setOf_isFlex hF h6⟩

end PlaneCurves.Projective

end
