/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Hessian.Flex
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.VariableChange

/-!
# Weierstrass form of a plane cubic at a flex

Let `F` be an irreducible cubic form over a field `k` and `O` a flex of `F`. Then a projective
change of coordinates sends `[0 : 1 : 0]` to `O` and the tangent line at `O` to `Z = 0`, and
carries `F` to a nonzero multiple of a Weierstrass cubic
`Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³)` (Mathlib's
`WeierstrassCurve.Projective.polynomial`). This holds in every characteristic; if `2 ≠ 0` in
`k`, completing the square makes `a₁ = a₃ = 0` ([Fulton2008], Problem 5.24 (a)).

The proof moves `O` to `[0 : 0 : 1]` and its tangent to `Y = 0`, as for the Hessian criterion.
There the cubic has no `Z³` and no `XZ²` term, and its `YZ²` term can be taken to be `1`. On the
tangent `Y = 0` it is `X²(aX + bZ)`, which meets `Y = 0` at `[0 : 0 : 1]` only twice unless
`b = 0`; and `a ≠ 0`, since otherwise `Y` divides the cubic. Exchanging `Y` and `Z` and scaling
`Y` makes the `Y²Z` and `X³` coefficients opposite, with no square or cube roots needed.

Changes of coordinates are Tau Ceti's `MvPolynomial.linearSubst M`, `F ↦ F(M X)`, along a matrix
`M` with `M.mulVecLin` injective, as in the rest of the library.

## Main results

* `MvPolynomial.IsHomogeneous.eq_of_fin_three_three`: a cubic form in three variables is the sum
  of its ten monomials.
* `PlaneCurves.Projective.tangentLine_weierstrassCurve_polynomial`: the tangent line of a
  Weierstrass cubic at `[0 : 1 : 0]` is `Z = 0`.
* `PlaneCurves.Projective.IsFlex.exists_linearSubst_eq_smul_polynomial`: an irreducible cubic is
  in Weierstrass form after moving a flex to `[0 : 1 : 0]`.
* `PlaneCurves.Projective.IsFlex.exists_linearSubst_eq_smul_polynomial_of_two_ne_zero`: the same
  with `a₁ = a₃ = 0`, when `2 ≠ 0`.

## References

* [W. Fulton, *Algebraic Curves: An Introduction to Algebraic Geometry*][Fulton2008],
  Problem 5.24
-/

public section

namespace MvPolynomial

variable {k : Type*} [CommSemiring k]

/-- A form of degree three in three variables is the sum of its ten monomials
`X³, Y³, Z³, X²Y, X²Z, XY², Y²Z, XZ², YZ², XYZ` with their coefficients. -/
theorem IsHomogeneous.eq_of_fin_three_three {F : MvPolynomial (Fin 3) k}
    (hF : F.IsHomogeneous 3) :
    F = C (F.coeff (Finsupp.single 0 3)) * X 0 ^ 3 + C (F.coeff (Finsupp.single 1 3)) * X 1 ^ 3 +
      C (F.coeff (Finsupp.single 2 3)) * X 2 ^ 3 +
      C (F.coeff (Finsupp.single 0 2 + Finsupp.single 1 1)) * (X 0 ^ 2 * X 1) +
      C (F.coeff (Finsupp.single 0 2 + Finsupp.single 2 1)) * (X 0 ^ 2 * X 2) +
      C (F.coeff (Finsupp.single 0 1 + Finsupp.single 1 2)) * (X 0 * X 1 ^ 2) +
      C (F.coeff (Finsupp.single 1 2 + Finsupp.single 2 1)) * (X 1 ^ 2 * X 2) +
      C (F.coeff (Finsupp.single 0 1 + Finsupp.single 2 2)) * (X 0 * X 2 ^ 2) +
      C (F.coeff (Finsupp.single 1 1 + Finsupp.single 2 2)) * (X 1 * X 2 ^ 2) +
      C (F.coeff (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1)) *
        (X 0 * X 1 * X 2) := by
  ext n
  simp only [X_pow_eq_monomial]
  simp only [X, monomial_mul_monomial, C_mul_monomial, AddMonoidAlgebra.coeff_add, Finsupp.coe_add,
    Pi.add_apply, coeff_monomial, mul_one]
  by_cases h : n.degree = 3
  · have e : n = Finsupp.single 0 (n 0) + Finsupp.single 1 (n 1) + Finsupp.single 2 (n 2) := by
      ext i; fin_cases i <;> simp
    have hs : n 0 + n 1 + n 2 = 3 := by
      simpa [Finsupp.degree_eq_sum, Fin.sum_univ_three] using h
    generalize n 0 = a, n 1 = b, n 2 = c at e hs
    subst e
    have : a ≤ 3 := by omega
    have : b ≤ 3 := by omega
    have : c ≤ 3 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> simp at hs <;>
      simp [Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply]
  · have : F.coeff n = 0 := by
      by_contra h'
      exact h (by rw [Finsupp.degree_eq_weight_one]; exact hF h')
    rw [this]
    have hm : ∀ m : Fin 3 →₀ ℕ, m.degree = 3 → m ≠ n := fun m hm e ↦ h (e ▸ hm)
    simp [hm, Finsupp.degree_single]

end MvPolynomial
namespace PlaneCurves.Projective

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization Matrix

variable {k : Type*} [Field k]

/-- The tangent line of the Weierstrass cubic `Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³)`
at its point at infinity `[0 : 1 : 0]` is the line at infinity `Z = 0`. -/
theorem tangentLine_weierstrassCurve_polynomial (W : WeierstrassCurve k) :
    tangentLine W.toProjective.polynomial ![0, 1, 0] = X 2 := by
  simp [tangentLine_def, Fin.sum_univ_three, WeierstrassCurve.Projective.polynomial]

/-- The point `[0 : 0 : 1]` lies on `X` and `Y` with intersection number one. -/
private theorem intersectionNumber_X_one_X_zero :
    intersectionNumber (mk k ![0, 0, 1] (by simp)) (X 1 : MvPolynomial (Fin 3) k) (X 0) = 1 := by
  have hP2 : (mk k ![0, 0, 1] (by simp) : ℙ k (Fin 3 → k)) ∈ affineOpen 2 := by simp
  have ha : affineChart 2 (mk k ![0, 0, 1] (by simp) : ℙ k (Fin 3 → k)) = 0 := by
    funext j
    fin_cases j <;> simp [Fin.succAbove, Fin.lt_def]
  rw [intersectionNumber_eq_affine (isHomogeneous_X k 1) (isHomogeneous_X k 0) hP2, ha,
    Affine.intersectionNumber_comm]
  simpa [Fin.insertNth_apply_below (show (1 : Fin 3) < 2 by decide)] using
    Affine.intersectionNumber_X_sub_C_X_sub_C (0 : Fin 2 → k)

variable {F : MvPolynomial (Fin 3) k} {O : ℙ k (Fin 3 → k)}

/-- A flex `O` of a form `F` and its tangent line are moved to `[0 : 0 : 1]` and `Y = 0` by a
change of coordinates `M`; there `F(M X)` has no `Z³` and `XZ²` term, and its `YZ²` term is
`1`. -/
private theorem exists_flex_standard (hF : F.IsHomogeneous 3) (hO : IsFlex F O) :
    ∃ M : GL (Fin 3) k, M.1 *ᵥ ![0, 0, 1] = O.rep ∧
      eval ![0, 0, 1] (linearSubst M.1 F) = 0 ∧
      (∀ j, eval ![0, 0, 1] (pderiv j (linearSubst M.1 F)) = (Pi.single 1 1 : Fin 3 → k) j) ∧
      3 ≤ intersectionNumber (mk k ![0, 0, 1] (by simp)) (X 1) (linearSubst M.1 F) := by
  set t : Fin 3 → k := fun i ↦ eval O.rep (pderiv i F)
  have ht : t ≠ 0 := by
    obtain ⟨-, i, hi⟩ := isSimplePoint_iff_eval_rep.1 hO.isSimplePoint
    exact fun h0 ↦ hi (congrFun h0 i)
  have htp : t ⬝ᵥ O.rep = 0 := by
    simpa [dotProduct] using eval_tangentLine_self hF hO.isSimplePoint.eval_rep_eq_zero
  obtain ⟨M, hMp, hMt⟩ :=
    Matrix.exists_mulVec_single_eq_and_vecMul_eq_single ht O.rep_ne_zero htp
  have he : (Pi.single 2 1 : Fin 3 → k) = ![0, 0, 1] := by
    funext i; fin_cases i <;> simp
  rw [he] at hMp
  have hQO : map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit)
      (mk k ![0, 0, 1] (by simp)) = O := by
    erw [map_mk]
    simp only [Matrix.mulVecLin_apply, hMp]
    exact O.mk_rep
  have hT : linearSubst M.1 (tangentLine F O.rep) = X 1 := by
    have : linearSubst M.1 (tangentLine F O.rep) = ∑ j, C ((t ᵥ* M.1) j) * X j := by
      simp only [tangentLine_def, map_mul, linearSubst_X, Matrix.vecMul, dotProduct,
        Fin.sum_univ_three, map_add, map_mul, algHom_C, t]
      simp only [algebraMap_eq]
      ring
    rw [this, hMt]
    simp [Fin.sum_univ_three]
  refine ⟨M, hMp, ?_, fun j ↦ ?_, ?_⟩
  · rw [eval_linearSubst, hMp]
    exact hO.isSimplePoint.eval_rep_eq_zero
  · rw [← hMt]
    simp [pderiv_linearSubst, eval_linearSubst, hMp, Matrix.vecMul, dotProduct, mul_comm, t]
  · rw [intersectionNumber_comm, ← hT,
      intersectionNumber_linearSubst hF (isHomogeneous_tangentLine _ _), hQO]
    exact (isFlex_def.1 hO).2

/-- A product of two polynomials that vanish at the origin is not irreducible. -/
private theorem not_irreducible_mul {p q : MvPolynomial (Fin 3) k} (hp : eval 0 p = 0)
    (hq : eval 0 q = 0) : ¬Irreducible (p * q) := fun h ↦ by
  rcases h.isUnit_or_isUnit rfl with h | h
  · exact (h.map (eval 0)).ne_zero hp
  · exact (h.map (eval 0)).ne_zero hq

/-- An irreducible cubic `H` with a flex at `[0 : 0 : 1]` with tangent `Y = 0`, normalized as by
`exists_flex_standard`, is `a X³ + b Y³ + c X²Y + d XY² + e Y²Z + YZ² + g XYZ` with `a ≠ 0`. -/
private theorem exists_coeff_of_flex {H : MvPolynomial (Fin 3) k} (hH : H.IsHomogeneous 3)
    (hi : Irreducible H) (h0 : eval ![0, 0, 1] H = 0)
    (hd : ∀ j, eval ![0, 0, 1] (pderiv j H) = (Pi.single 1 1 : Fin 3 → k) j)
    (hI : 3 ≤ intersectionNumber (mk k ![0, 0, 1] (by simp)) (X 1) H) :
    ∃ a b c d e g : k, a ≠ 0 ∧
      H = C a * X 0 ^ 3 + C b * X 1 ^ 3 + C c * (X 0 ^ 2 * X 1) + C d * (X 0 * X 1 ^ 2) +
        C e * (X 1 ^ 2 * X 2) + X 1 * X 2 ^ 2 + C g * (X 0 * X 1 * X 2) := by
  have hH := hH.eq_of_fin_three_three
  generalize H.coeff (Finsupp.single 0 3) = a300, H.coeff (Finsupp.single 1 3) = a030,
    H.coeff (Finsupp.single 2 3) = a003,
    H.coeff (Finsupp.single 0 2 + Finsupp.single 1 1) = a210,
    H.coeff (Finsupp.single 0 2 + Finsupp.single 2 1) = a201,
    H.coeff (Finsupp.single 0 1 + Finsupp.single 1 2) = a120,
    H.coeff (Finsupp.single 1 2 + Finsupp.single 2 1) = a021,
    H.coeff (Finsupp.single 0 1 + Finsupp.single 2 2) = a102,
    H.coeff (Finsupp.single 1 1 + Finsupp.single 2 2) = a012,
    H.coeff (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1) = a111 at hH
  subst hH
  have h003 : a003 = 0 := by simpa using h0
  have h102 : a102 = 0 := by simpa [pderiv_X] using hd 0
  have h012 : a012 = 1 := by simpa [pderiv_X] using hd 1
  subst h003 h102 h012
  have hX0 : (X 0 : MvPolynomial (Fin 3) k).IsHomogeneous 1 := isHomogeneous_X k 0
  have hX1 : (X 1 : MvPolynomial (Fin 3) k).IsHomogeneous 1 := isHomogeneous_X k 1
  have h201 : a201 = 0 := by
    by_contra h201
    have hL : (C a300 * X 0 + C a201 * X 2 : MvPolynomial (Fin 3) k).IsHomogeneous 1 :=
      ((isHomogeneous_C_mul_X _ _)).add (isHomogeneous_C_mul_X _ _)
    have : 3 ≤ intersectionNumber (mk k ![0, 0, 1] (by simp)) (X 1)
        (X 0 ^ 2 * (C a300 * X 0 + C a201 * X 2) + (C a030 * X 1 ^ 2 + C a210 * X 0 ^ 2 +
          C a120 * (X 0 * X 1) + C a021 * (X 1 * X 2) + X 2 ^ 2 + C a111 * (X 0 * X 2)) * X 1) := by
      convert hI using 2
      simp only [map_zero, zero_mul, add_zero, map_one, one_mul]
      ring
    rw [intersectionNumber_add_mul,
      intersectionNumber_mul_right_of_eval_ne_zero hX1 (hX0.pow 2) hL
        (by rw [Ne, hL.eval_rep_mk_eq_zero_iff]; simpa using h201), pow_two,
      intersectionNumber_mul_right hX1 hX0 hX0,
      intersectionNumber_X_one_X_zero] at this
    exact absurd this (by decide)
  subst h201
  refine ⟨a300, a030, a210, a120, a021, a111, fun h300 ↦ ?_, by simp⟩
  subst h300
  refine not_irreducible_mul (p := X 1) (q := C a030 * X 1 ^ 2 + C a210 * X 0 ^ 2 +
    C a120 * (X 0 * X 1) + C a021 * (X 1 * X 2) + X 2 ^ 2 + C a111 * (X 0 * X 2))
    (by simp) (by simp) ?_
  convert hi using 1
  simp
  ring

/-- **Weierstrass form of a cubic at a flex.** Let `F` be an irreducible cubic form over a field
`k` and `O` a flex of `F`. Then a projective change of coordinates `T` sends `[0 : 1 : 0]` to `O`
and carries `F` to a nonzero multiple of a Weierstrass cubic
`Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³)`; the tangent line at `O` becomes the line
at infinity `Z = 0`. This holds in every characteristic, and `k` need not be algebraically
closed. -/
theorem IsFlex.exists_linearSubst_eq_smul_polynomial (hF : F.IsHomogeneous 3)
    (hirr : Irreducible F) (hO : IsFlex F O) :
    ∃ (T : Matrix (Fin 3) (Fin 3) k) (c : k) (W : WeierstrassCurve k),
      Function.Injective T.mulVecLin ∧ c ≠ 0 ∧ T *ᵥ ![0, 1, 0] = O.rep ∧
      linearSubst T F = c • W.toProjective.polynomial ∧
      tangentLine (linearSubst T F) ![0, 1, 0] = c • X 2 := by
  obtain ⟨M, hMO, h0, hd, hI⟩ := exists_flex_standard hF hO
  have hi : Irreducible (linearSubst M.1 F) :=
    (irreducible_linearSubst_iff ((Matrix.isUnit_iff_isUnit_det _).1 M.isUnit)).2 hirr
  obtain ⟨a, b, c, d, e, g, ha, hH⟩ := exists_coeff_of_flex (hF.linearSubst M.1) hi h0 hd hI
  set N : Matrix (Fin 3) (Fin 3) k := !![1, 0, 0; 0, 0, -a; 0, 1, 0]
  have hN : Function.Injective N.mulVecLin :=
    Matrix.mulVecLin_injective_iff_isUnit_det.2 <| Ne.isUnit (by simp [N, Matrix.det_fin_three, ha])
  have hTF : linearSubst (M.1 * N) F = (-a) • (⟨g, -c, -e * a, d * a, -b * a ^ 2⟩ :
      WeierstrassCurve k).toProjective.polynomial := by
    rw [linearSubst_mul_apply, hH]
    simp [N, WeierstrassCurve.Projective.polynomial, linearSubst_X, Fin.sum_univ_three,
      smul_eq_C_mul]
    ring
  refine ⟨M.1 * N, -a, _, Matrix.mulVecLin_mul_injective
    (Matrix.mulVec_injective_of_isUnit M.isUnit) hN, neg_ne_zero.2 ha, ?_, hTF, ?_⟩
  · rw [← Matrix.mulVec_mulVec, ← hMO]
    congr 1
    funext i
    fin_cases i <;> simp [N]
  · rw [hTF, tangentLine_smul, tangentLine_weierstrassCurve_polynomial]

/-- **Weierstrass form of a cubic at a flex, away from characteristic two** ([Fulton2008],
Problem 5.24 (a)). Let `F` be an irreducible cubic form over a field `k` with `2 ≠ 0`, and `O` a
flex of `F`. Then a projective change of coordinates `T` sends `[0 : 1 : 0]` to `O` and carries
`F` to a nonzero multiple of `Y²Z - (X³ + a₂X²Z + a₄XZ² + a₆Z³)`, a Weierstrass cubic with
`a₁ = a₃ = 0`; the tangent line at `O` becomes `Z = 0`. -/
theorem IsFlex.exists_linearSubst_eq_smul_polynomial_of_two_ne_zero (h2 : (2 : k) ≠ 0)
    (hF : F.IsHomogeneous 3) (hirr : Irreducible F) (hO : IsFlex F O) :
    ∃ (T : Matrix (Fin 3) (Fin 3) k) (c : k) (W : WeierstrassCurve k),
      Function.Injective T.mulVecLin ∧ c ≠ 0 ∧ T *ᵥ ![0, 1, 0] = O.rep ∧
      linearSubst T F = c • W.toProjective.polynomial ∧ W.a₁ = 0 ∧ W.a₃ = 0 ∧
      tangentLine (linearSubst T F) ![0, 1, 0] = c • X 2 := by
  obtain ⟨T, c, W, hT, hc, hTO, hTF, -⟩ := hO.exists_linearSubst_eq_smul_polynomial hF hirr
  -- Complete the square in `Y`: `y ↦ y - (a₁ x + a₃) / 2`.
  set V : WeierstrassCurve.VariableChange k := ⟨1, 0, -W.a₁ / 2, -W.a₃ / 2⟩
  have hV : Function.Injective V.toMatrix.mulVecLin :=
    Matrix.mulVecLin_injective_iff_isUnit_det.2 <| Ne.isUnit <| by
      simp [V, WeierstrassCurve.VariableChange.toMatrix_def, Matrix.det_fin_three]
  have hVF : linearSubst (T * V.toMatrix) F = c • (V • W).toProjective.polynomial := by
    rw [linearSubst_mul_apply, hTF, map_smul,
      WeierstrassCurve.Projective.linearSubst_polynomial]
    simp [V]
  refine ⟨T * V.toMatrix, c, V • W, Matrix.mulVecLin_mul_injective hT hV, hc, ?_, hVF, ?_, ?_,
    by rw [hVF, tangentLine_smul, tangentLine_weierstrassCurve_polynomial]⟩
  · rw [← Matrix.mulVec_mulVec, ← hTO]
    congr 1
    funext i
    fin_cases i <;> simp [V, WeierstrassCurve.VariableChange.toMatrix_def]
  · simp [V, WeierstrassCurve.variableChange_a₁]
    field_simp
    ring
  · simp [V, WeierstrassCurve.variableChange_a₃]
    field_simp
    ring

end PlaneCurves.Projective

end
