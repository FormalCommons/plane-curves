/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.IntersectionNumber.Properties

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

end
