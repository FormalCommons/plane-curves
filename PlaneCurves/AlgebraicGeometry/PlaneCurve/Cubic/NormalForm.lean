/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Hessian.Flex
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.MultiplePoints
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Tangent
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.LinearSubvariety
public import PlaneCurves.RingTheory.MvPolynomial.Homogenize.Factorization
public import PlaneCurves.RingTheory.MvPolynomial.Irreducible
public import PlaneCurves.RingTheory.MvPolynomial.LinearSubst
public import TauCeti.AlgebraicGeometry.EllipticCurve.Legendre
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.VariableChange

/-!
# Normal forms of irreducible cubics

This file describes an irreducible plane cubic `F` near its special points: its multiple point,
if it has one, and its flexes.

## Singular points

Over an algebraically closed field, in every characteristic, `F` has at most one multiple point
(`eq_of_isMultiplePoint_of_degree_three`), by the bound on the multiple points, and it is a
double point (`mult_eq_two_of_degree_three`) (Problem 5.13 of Fulton). A double point is a
*node*, an ordinary double point with two distinct tangents, or a *cusp*, with a single tangent
of multiplicity `2` (`isOrdinaryMultiplePoint_or_exists_tangentMultiplicity_eq_two`).

## Weierstrass form at a flex

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

## Legendre form of a nonsingular cubic

Over an algebraically closed field with `2 ≠ 0`, a nonsingular cubic has a flex, by the Hessian,
and at a flex its Weierstrass form is `Y²Z = (X - e₁Z)(X - e₂Z)(X - e₃Z)`. The roots `eᵢ` are
distinct, since a double root `e` makes `[e : 0 : 1]` a singular point. Tau Ceti's change of
variables to the Legendre form (`WeierstrassCurve.exists_variableChange_smul_eq_freyCurve_one`)
and a scaling then carry the cubic to `Y²Z = X(X - Z)(X - λZ)` with `λ ≠ 0, 1` (Problem 5.24 (b),
there in characteristic zero).

Changes of coordinates are Tau Ceti's `MvPolynomial.linearSubst M`, `F ↦ F(M X)`, along a matrix
`M` with `M.mulVecLin` injective, as in the rest of the library.

## Normal forms of the cuspidal and the nodal cubic

In characteristic zero a singular irreducible cubic is projectively equivalent to the cuspidal
cubic `Y²Z = X³` or to the nodal cubic `Y²Z = X²(X + Z)` (Problems 5.10 and 5.11). The proof
moves the multiple point to `[0 : 1 : 0]`, so that the cubic is `Y q(X, Z) + r(X, Z)` with `q`
the leading form there; a change of coordinates in `X, Z` makes `X` divide `q`. At a node `q`
is then `X` times a second, independent linear form, which becomes `Z`; substitutions
`Y ↦ Y + αX + βZ` and a rescaling of `X` and `Z`, which takes cube roots, bring the cubic to
`XYZ + X³ + Z³` and a fixed change of coordinates to `Y²Z = X²(X + Z)`. At a cusp `q = aX²`, and
the substitution `Z ↦ Z - (f / 3g) X` removes the `XZ²` term of `r = dX³ + eX²Z + fXZ² + gZ³`,
which needs `3 ≠ 0`.

## Main results

All in the namespace `PlaneCurves.Projective`, unless named in full.

* `MvPolynomial.IsHomogeneous.eq_of_fin_three_three`: a cubic form in three variables is the sum
  of its ten monomials.
* `WeierstrassCurve.Projective.tangentLine_polynomial_zero`: the tangent line of a
  Weierstrass cubic at `[0 : 1 : 0]` is `Z = 0`.
* `IsFlex.exists_linearSubst_eq_smul_polynomial`: an irreducible cubic is
  in Weierstrass form after moving a flex to `[0 : 1 : 0]`.
* `IsFlex.exists_linearSubst_eq_smul_polynomial_of_two_ne_zero`: the same
  with `a₁ = a₃ = 0`, when `2 ≠ 0`.
* `isOrdinaryMultiplePoint_or_exists_tangentMultiplicity_eq_two_of_degree_three`:
  a multiple point of an irreducible cubic is a node or a cusp.
* `isNonsingular_or_exists_isMultiplePoint_iff_of_degree_three`: an
  irreducible cubic is nonsingular, or it has exactly one multiple point, a double point that is a
  node or a cusp.
* `exists_linearSubst_eq_X_sq_mul_X_sub_X_pow_three`: in characteristic zero, an irreducible
  cubic with a cusp is carried to `Y²Z = X³` by a change of coordinates (Problem 5.10).
* `exists_linearSubst_eq_X_sq_mul_X_sub_X_sq_mul_X_add_X`: in characteristic zero, an
  irreducible cubic with a node is carried to `Y²Z = X²(X + Z)` (Problem 5.11).
* `IsNonsingular.exists_linearSubst_eq_legendre`: over an algebraically closed field with
  `2 ≠ 0`, a nonsingular cubic is carried to `Y²Z = X(X - Z)(X - λZ)`, `λ ≠ 0, 1`, by a change
  of coordinates (Problem 5.24 (b)).
* `WeierstrassCurve.toProjective_polynomial_eq_prod`: the Weierstrass cubic
  `Y²Z = (X - e₁Z)(X - e₂Z)(X - e₃Z)` from the roots of its `2`-division polynomial.
* `MvPolynomial.irreducible_X_sq_mul_X_sub_X_pow_three`,
  `isMultiplePoint_X_sq_mul_X_sub_X_pow_three`, `isTangentAt_X_sq_mul_X_sub_X_pow_three`,
  `tangentMultiplicity_X_sq_mul_X_sub_X_pow_three`: `Y²Z = X³` is irreducible, with a cusp at
  `[0 : 0 : 1]`.
* `MvPolynomial.irreducible_X_sq_mul_X_sub_X_sq_mul_X_add_X`,
  `isOrdinaryMultiplePoint_X_sq_mul_X_sub_X_sq_mul_X_add_X`: `Y²Z = X²(X + Z)` is irreducible,
  with a node at `[0 : 0 : 1]` when `2 ≠ 0`.

## References

* [W. Fulton, *Algebraic Curves: An Introduction to Algebraic Geometry*][Fulton2008],
  Problems 5.10, 5.11, 5.13 and 5.24
-/

public section

namespace MvPolynomial

section CommSemiring

variable {k : Type*} [CommSemiring k]

/-- A form of degree three in three variables is the sum of its ten monomials
`X³, Y³, Z³, X²Y, X²Z, XY², Y²Z, XZ², YZ², XYZ`, with their coefficients. -/
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

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The cuspidal cubic `Y²Z = X³` is irreducible, over any domain. -/
theorem irreducible_X_sq_mul_X_sub_X_pow_three :
    Irreducible (X 1 ^ 2 * X 2 - X 0 ^ 3 : MvPolynomial (Fin 3) R) := by
  have h : linearSubst !![-1, 0, 0; 0, 1, 0; 0, 0, 1] (X 0 ^ 3 + X 1 ^ (3 - 1) * X 2) =
      (X 1 ^ 2 * X 2 - X 0 ^ 3 : MvPolynomial (Fin 3) R) := by
    simp [linearSubst_X, Fin.sum_univ_three]
    ring
  rw [← h, irreducible_linearSubst_iff (by simp [Matrix.det_fin_three])]
  exact irreducible_X_pow_add_X_pow_mul_X three_ne_zero

/-- The nodal cubic `Y²Z = X²(X + Z)` is irreducible, over any domain: it is not divisible by `X`,
and in the chart `X = 1` it is `z (y² - 1) - 1`, of degree one in `z`. -/
theorem irreducible_X_sq_mul_X_sub_X_sq_mul_X_add_X :
    Irreducible (X 1 ^ 2 * X 2 - X 0 ^ 2 * (X 0 + X 2) : MvPolynomial (Fin 3) R) := by
  have hX (j : Fin 3) : (X j : MvPolynomial (Fin 3) R).IsHomogeneous 1 := isHomogeneous_X R j
  have hN : (X 1 ^ 2 * X 2 - X 0 ^ 2 * (X 0 + X 2) : MvPolynomial (Fin 3) R).IsHomogeneous 3 :=
    (((hX 1).pow 2).mul (hX 2)).sub (((hX 0).pow 2).mul ((hX 0).add (hX 2)))
  have hX0 : ¬X 0 ∣ (X 1 ^ 2 * X 2 - X 0 ^ 2 * (X 0 + X 2) : MvPolynomial (Fin 3) R) := by
    rintro ⟨G, hG⟩
    have := congrArg (eval ![0, 1, 1]) hG
    simp at this
  rw [← irreducible_dehomogenize_iff hN hX0]
  -- In the chart `X = 1` the curve is `z (y² - 1) - 1`, of degree one in `z`.
  have hp : Irreducible (X 0 * (X 1 ^ 2 - 1) - 1 : MvPolynomial (Fin 2) R) := by
    have h : finSuccEquiv R 1 (X 0 * (X 1 ^ 2 - 1) - 1) =
        Polynomial.C (X 0 ^ 2 - 1) * Polynomial.X + Polynomial.C (-1) := by
      have h1 : finSuccEquiv R 1 (X 1) = Polynomial.C (X 0) := finSuccEquiv_X_succ (j := 0)
      simp [finSuccEquiv_X_zero, h1]
      ring
    rw [← MulEquiv.irreducible_iff (finSuccEquiv R 1), h]
    refine Polynomial.irreducible_C_mul_X_add_C (fun h ↦ ?_) (isUnit_one.neg.isRelPrime_right)
    simpa using congrArg (eval 0) h
  convert (MulEquiv.irreducible_iff (renameEquiv R (Equiv.swap (0 : Fin 2) 1))).2 hp using 1
  have h2 : Fin.cons (α := fun _ ↦ MvPolynomial (Fin 2) R) 1 X 2 = X 1 := rfl
  simp [Fin.insertNth, h2]
  ring

end CommRing

end MvPolynomial

namespace WeierstrassCurve.Projective

open MvPolynomial

variable {k : Type*} [Field k]

/-- The tangent line of the Weierstrass cubic `Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³)`
at its point at infinity `[0 : 1 : 0]` is the line at infinity `Z = 0`. -/
theorem tangentLine_polynomial_zero (W : WeierstrassCurve.Projective k) :
    PlaneCurves.Projective.tangentLine W.polynomial ![0, 1, 0] = X 2 := by
  simp [PlaneCurves.Projective.tangentLine_def, Fin.sum_univ_three, polynomial]

end WeierstrassCurve.Projective

namespace WeierstrassCurve

open MvPolynomial

variable {k : Type*} [Field k] {W : WeierstrassCurve k}

/-- Let `W` be a Weierstrass curve `y² = x³ + a₂x² + a₄x + a₆`, with `a₁ = a₃ = 0`, over a field
with `2 ≠ 0`. If its `2`-division polynomial is `4 (x - e₁) (x - e₂) (x - e₃)`, then its
homogeneous Weierstrass polynomial is `Y²Z - (X - e₁Z) (X - e₂Z) (X - e₃Z)`. -/
theorem toProjective_polynomial_eq_prod (h2 : (2 : k) ≠ 0) (h1 : W.a₁ = 0) (h3 : W.a₃ = 0)
    {e₁ e₂ e₃ : k} (h : W.twoTorsionPolynomial.toPoly = Polynomial.C 4 *
      (Polynomial.X - Polynomial.C e₁) * (Polynomial.X - Polynomial.C e₂) *
        (Polynomial.X - Polynomial.C e₃)) :
    W.toProjective.polynomial =
      X 1 ^ 2 * X 2 - (X 0 - C e₁ * X 2) * (X 0 - C e₂ * X 2) * (X 0 - C e₃ * X 2) := by
  have h4 : (4 : k) ≠ 0 := by
    rw [show (4 : k) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  rw [Cubic.C_mul_prod_X_sub_C_eq, Cubic.toPoly_injective, twoTorsionPolynomial] at h
  simp only [Cubic.mk.injEq, true_and, b₂, b₄, b₆, h1, h3] at h
  obtain ⟨hb₂, hb₄, hb₆⟩ := h
  have ha₂ : W.a₂ = -(e₁ + e₂ + e₃) := mul_left_cancel₀ h4 (by linear_combination hb₂)
  have ha₄ : W.a₄ = e₁ * e₂ + e₁ * e₃ + e₂ * e₃ := mul_left_cancel₀ h4 (by linear_combination hb₄)
  have ha₆ : W.a₆ = -(e₁ * e₂ * e₃) := mul_left_cancel₀ h4 (by linear_combination hb₆)
  simp only [Projective.polynomial, h1, h3, ha₂, ha₄, ha₆, map_neg, map_add, map_mul, map_zero]
  ring

end WeierstrassCurve

namespace PlaneCurves.Projective

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization Matrix

variable {k : Type*} [Field k]

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
  refine not_irreducible_mul_of_eval_eq_zero (x := (0 : Fin 3 → k)) (p := X 1)
    (q := C a030 * X 1 ^ 2 + C a210 * X 0 ^ 2 + C a120 * (X 0 * X 1) +
      C a021 * (X 1 * X 2) + X 2 ^ 2 + C a111 * (X 0 * X 2))
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
  · rw [hTF, tangentLine_smul, WeierstrassCurve.Projective.tangentLine_polynomial_zero]

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
    by rw [hVF, tangentLine_smul, WeierstrassCurve.Projective.tangentLine_polynomial_zero]⟩
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

/-- The cubic `Y²Z - (X - eZ)² L` is singular at `[e : 0 : 1]`, for every form `L`. -/
theorem not_isNonsingular_X_sq_mul_X_sub_X_sub_C_mul_X_sq_mul (e : k)
    (L : MvPolynomial (Fin 3) k) :
    ¬IsNonsingular (X 1 ^ 2 * X 2 - (X 0 - C e * X 2) ^ 2 * L) := by
  intro h
  obtain ⟨i, hi⟩ := isNonsingular_def.1 h ![e, 0, 1] (by simp) (by simp)
  fin_cases i <;> simp [pderiv_X, Derivation.leibniz, Derivation.leibniz_pow] at hi

section IsAlgClosed

variable [IsAlgClosed k]

/-- A multiple point `P` of an irreducible cubic `F` is a *node*, an ordinary double point, or a
*cusp*: `F` has a single tangent `L` at `P`, of multiplicity `2`. -/
theorem isOrdinaryMultiplePoint_or_exists_tangentMultiplicity_eq_two_of_degree_three
    (hF : F.IsHomogeneous 3) (hirr : Irreducible F) {P : ℙ k (Fin 3 → k)}
    (hP : IsMultiplePoint F P) :
    IsOrdinaryMultiplePoint F P ∨ ∃ L, IsTangentAt F P L ∧ tangentMultiplicity F P L = 2 :=
  isOrdinaryMultiplePoint_or_exists_tangentMultiplicity_eq_two hF
    (mult_eq_two_of_degree_three hF hirr hP)

/-- **Singular points of an irreducible cubic.** An irreducible plane cubic `F` over an
algebraically closed field is nonsingular, or it has exactly one multiple point `P`; then `P` is a
double point, and it is a node (an ordinary double point) or a cusp (a single tangent `L`, of
multiplicity `2`). -/
theorem isNonsingular_or_exists_isMultiplePoint_iff_of_degree_three (hF : F.IsHomogeneous 3)
    (hirr : Irreducible F) :
    IsNonsingular F ∨ ∃ P : ℙ k (Fin 3 → k), (∀ Q, IsMultiplePoint F Q ↔ Q = P) ∧
      mult F P = 2 ∧
        (IsOrdinaryMultiplePoint F P ∨ ∃ L, IsTangentAt F P L ∧ tangentMultiplicity F P L = 2) := by
  refine or_iff_not_imp_left.2 fun hns ↦ ?_
  obtain ⟨P, hPF, hPs⟩ : ∃ P ∈ zeroLocus {F}, ¬IsSimplePoint F P := by
    simpa [isNonsingular_iff_forall_isSimplePoint hF] using hns
  have hP := (isSimplePoint_or_isMultiplePoint hF hPF).resolve_left hPs
  refine ⟨P, fun Q ↦ ⟨fun hQ ↦ eq_of_isMultiplePoint_of_degree_three hF hirr hQ hP,
    fun h ↦ h ▸ hP⟩, mult_eq_two_of_degree_three hF hirr hP,
    isOrdinaryMultiplePoint_or_exists_tangentMultiplicity_eq_two_of_degree_three hF hirr hP⟩

/-! ### Normal forms of the cuspidal and the nodal cubic -/

/-- The cubic `Y (a X² + b XZ + c Z²) + d X³ + e X²Z + f XZ² + g Z³`: a cubic with a multiple
point at `[0 : 1 : 0]` (when it vanishes there to order at least two). -/
private noncomputable def shape (a b c d e f g : k) : MvPolynomial (Fin 3) k :=
  X 1 * (C a * X 0 ^ 2 + C b * (X 0 * X 2) + C c * X 2 ^ 2) +
    (C d * X 0 ^ 3 + C e * (X 0 ^ 2 * X 2) + C f * (X 0 * X 2 ^ 2) + C g * X 2 ^ 3)

/-- A change of coordinates fixing `[0 : 1 : 0]` removes the `YZ²` term of a cubic
`Y (a X² + b XZ + c Z²) + d X³ + e X²Z + f XZ² + g Z³`. -/
private theorem exists_linearSubst_shape_eq (a b c d e f g : k) :
    ∃ M : Matrix (Fin 3) (Fin 3) k, Function.Injective M.mulVecLin ∧
      M *ᵥ ![0, 1, 0] = ![0, 1, 0] ∧
        ∃ a' b' d' e' f' g' : k,
          linearSubst M (shape a b c d e f g) = shape a' b' 0 d' e' f' g' := by
  by_cases ha : a = 0
  · refine ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0],
      Matrix.mulVecLin_injective_iff_isUnit_det.2 <| Ne.isUnit (by simp [Matrix.det_fin_three]),
      by ext i; fin_cases i <;> simp, c, b, g, f, e, d, MvPolynomial.funext fun x ↦ ?_⟩
    simp [shape, Fin.sum_univ_three, ha]
    ring
  · obtain ⟨t, ht⟩ := IsAlgClosed.exists_root (Polynomial.C a * Polynomial.X ^ 2 +
      Polynomial.C b * Polynomial.X + Polynomial.C c) (by rw [Polynomial.degree_quadratic ha]; simp)
    have ht : a * t ^ 2 + b * t + c = 0 := by simpa using ht
    refine ⟨!![1, 0, t; 0, 1, 0; 0, 0, 1],
      Matrix.mulVecLin_injective_iff_isUnit_det.2 <| Ne.isUnit (by simp [Matrix.det_fin_three]),
      by ext i; fin_cases i <;> simp, a, 2 * a * t + b, d, 3 * d * t + e,
      3 * d * t ^ 2 + 2 * e * t + f, d * t ^ 3 + e * t ^ 2 + f * t + g,
      MvPolynomial.funext fun x ↦ ?_⟩
    simp [shape, Fin.sum_univ_three]
    linear_combination x 1 * x 2 ^ 2 * ht

/-- A cubic with a multiple point `P` is carried, by a change of coordinates taking
`[0 : 1 : 0]` to `P`, to a cubic `Y (a X² + b XZ) + d X³ + e X²Z + f XZ² + g Z³`. -/
private theorem exists_linearSubst_eq_shape (hF : F.IsHomogeneous 3) {P : ℙ k (Fin 3 → k)}
    (hP : IsMultiplePoint F P) :
    ∃ (M : Matrix (Fin 3) (Fin 3) k) (hM : Function.Injective M.mulVecLin),
      map M.mulVecLin hM (mk k ![0, 1, 0] (by simp)) = P ∧
        ∃ a b d e f g : k, linearSubst M F = shape a b 0 d e f g := by
  obtain ⟨M, hM, hMP⟩ := exists_mulVecLin_map_eq (n := 2) (mk k ![0, 1, 0] (by simp)) P
  set G := linearSubst M F with hGdef
  have hG : G.IsHomogeneous 3 := hF.linearSubst M
  obtain ⟨h0, h1⟩ := (isMultiplePoint_iff_eval_pderiv hG _ _).1
    ((isMultiplePoint_linearSubst_iff hF hM _).2 (hMP ▸ hP))
  have he := hG.eq_of_fin_three_three
  have c1 : G.coeff (Finsupp.single 1 3) = 0 := by
    rw [he] at h0; simpa using h0
  have c2 : G.coeff (Finsupp.single 0 1 + Finsupp.single 1 2) = 0 := by
    have h := h1 0; rw [he] at h; simpa [pderiv_X] using h
  have c3 : G.coeff (Finsupp.single 1 2 + Finsupp.single 2 1) = 0 := by
    have h := h1 2; rw [he] at h; simpa [pderiv_X] using h
  have hGs : G = shape (G.coeff (Finsupp.single 0 2 + Finsupp.single 1 1))
      (G.coeff (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1))
      (G.coeff (Finsupp.single 1 1 + Finsupp.single 2 2)) (G.coeff (Finsupp.single 0 3))
      (G.coeff (Finsupp.single 0 2 + Finsupp.single 2 1))
      (G.coeff (Finsupp.single 0 1 + Finsupp.single 2 2)) (G.coeff (Finsupp.single 2 3)) := by
    conv_lhs => rw [he]
    rw [c1, c2, c3, shape]
    simp only [map_zero, zero_mul, add_zero]
    ring
  obtain ⟨N, hN, hNv, a, b, d, e, f, g, hNG⟩ := exists_linearSubst_shape_eq
    (G.coeff (Finsupp.single 0 2 + Finsupp.single 1 1))
    (G.coeff (Finsupp.single 0 1 + Finsupp.single 1 1 + Finsupp.single 2 1))
    (G.coeff (Finsupp.single 1 1 + Finsupp.single 2 2)) (G.coeff (Finsupp.single 0 3))
    (G.coeff (Finsupp.single 0 2 + Finsupp.single 2 1))
    (G.coeff (Finsupp.single 0 1 + Finsupp.single 2 2)) (G.coeff (Finsupp.single 2 3))
  refine ⟨M * N, Matrix.mulVecLin_mul_injective hM hN, ?_, a, b, d, e, f, g,
    by rw [linearSubst_mul_apply, ← hGdef]; exact (congrArg (linearSubst N) hGs).trans hNG⟩
  rw [← hMP, map_mk, map_mk]
  congr 1
  rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, hNv]

omit [IsAlgClosed k] in
/-- The cubic `Y (a X² + b XZ) + d X³ + e X²Z + f XZ² + g Z³` as a sum `∑ᵢ Gᵢ(X, Z) Y^{3-i}`
of binary forms of degree `i`, as in `mult_eq_and_isTangentAt_iff_of_eq_sum`. -/
private theorem shape_eq_sum (a b d e f g : k) :
    shape a b 0 d e f g = ∑ i ∈ Finset.range (3 + 1), rename (Fin.succAbove 1)
      ((fun i : ℕ ↦ if i = 2 then C a * X 0 ^ 2 + C b * (X 0 * X 1) else if i = 3 then
        C d * X 0 ^ 3 + C e * (X 0 ^ 2 * X 1) + C f * (X 0 * X 1 ^ 2) + C g * X 1 ^ 3 else 0) i) *
        X 1 ^ (3 - i) := by
  simp [shape, Finset.sum_range_succ]
  ring

omit [IsAlgClosed k] in
/-- The pieces `Gᵢ` of `shape_eq_sum` are binary forms of degree `i`. -/
private theorem isHomogeneous_shape_piece (a b d e f g : k) (i : ℕ) :
    ((fun i : ℕ ↦ if i = 2 then C a * X 0 ^ 2 + C b * (X 0 * X 1) else if i = 3 then
        C d * X 0 ^ 3 + C e * (X 0 ^ 2 * X 1) + C f * (X 0 * X 1 ^ 2) + C g * X 1 ^ 3 else 0) i :
      MvPolynomial (Fin 2) k).IsHomogeneous i := by
  have hX (j : Fin 2) : (X j : MvPolynomial (Fin 2) k).IsHomogeneous 1 := isHomogeneous_X k j
  dsimp only
  split_ifs with h2 h3
  · subst h2
    exact (((isHomogeneous_C _ a).mul ((hX 0).pow 2)).add
      ((isHomogeneous_C _ b).mul ((hX 0).mul (hX 1))))
  · subst h3
    refine ((((isHomogeneous_C _ d).mul ((hX 0).pow 3)).add ((isHomogeneous_C _ e).mul
      (((hX 0).pow 2).mul (hX 1)))).add ((isHomogeneous_C _ f).mul
      ((hX 0).mul ((hX 1).pow 2)))).add ((isHomogeneous_C _ g).mul ((hX 1).pow 3))
  · exact isHomogeneous_zero _ _ _

omit [IsAlgClosed k] in
/-- The point `[0 : 1 : 0]` is a double point of `Y (a X² + b XZ) + d X³ + e X²Z + f XZ² + g Z³`
for `(a, b) ≠ (0, 0)`, with leading form `a X² + b XZ`. -/
private theorem mult_and_leadingForm_shape {a b d e f g : k} (hab : a ≠ 0 ∨ b ≠ 0) :
    mult (shape a b 0 d e f g) (mk k ![0, 1, 0] (by simp)) = 2 ∧
      Associated (leadingForm (shape a b 0 d e f g) (mk k ![0, 1, 0] (by simp)))
        (C a * X 0 ^ 2 + C b * (X 0 * X 2)) := by
  have hq : (C a * X 0 ^ 2 + C b * (X 0 * X 1) : MvPolynomial (Fin 2) k) ≠ 0 := by
    intro h
    have h1 : a = 0 := by simpa using congrArg (eval ![1, 0]) h
    have h2 : a + b = 0 := by simpa using congrArg (eval ![1, 1]) h
    rcases hab with hab | hab
    · exact hab h1
    · exact hab (by linear_combination h2 - h1)
  obtain ⟨h1, h2, -⟩ := mult_eq_and_isTangentAt_iff_of_eq_sum
    (isHomogeneous_shape_piece a b d e f g)
    (shape_eq_sum a b d e f g) (m := 2) (by norm_num) (fun i hi ↦ by interval_cases i <;> simp)
    (by simpa using hq)
  exact ⟨h1, by simpa using h2⟩

omit [IsAlgClosed k] in
/-- If `a = b = 0`, the point `[0 : 1 : 0]` is a triple point of
`Y (a X² + b XZ) + d X³ + e X²Z + f XZ² + g Z³`, unless that form is zero. -/
private theorem mult_shape_zero {d e f g : k} (h : shape 0 0 0 d e f g ≠ 0) :
    mult (shape 0 0 0 d e f g) (mk k ![0, 1, 0] (by simp)) = 3 := by
  refine (mult_eq_and_isTangentAt_iff_of_eq_sum (isHomogeneous_shape_piece 0 0 d e f g)
    (shape_eq_sum 0 0 d e f g) (m := 3) le_rfl (fun i hi ↦ by interval_cases i <;> simp)
    (fun h0 ↦ h ?_)).1
  have := congrArg (rename (Fin.succAbove (1 : Fin 3))) h0
  simpa [shape] using this

omit [IsAlgClosed k] in
/-- The binary quadratic form `a X² + b XZ ≠ 0` is squarefree exactly when `b ≠ 0`. -/
private theorem squarefree_C_mul_X_sq_add_iff {a b : k} (hab : a ≠ 0 ∨ b ≠ 0) :
    Squarefree (C a * X 0 ^ 2 + C b * (X 0 * X 2) : MvPolynomial (Fin 3) k) ↔ b ≠ 0 := by
  refine ⟨fun h hb ↦ ?_, fun hb ↦ ?_⟩
  · subst hb
    refine (prime_X : Prime (X 0 : MvPolynomial (Fin 3) k)).not_isUnit ?_
    exact h (X 0) ⟨C a, by simp; ring⟩
  · have hL : (C a * X 0 + C b * X 2 : MvPolynomial (Fin 3) k).IsHomogeneous 1 :=
      (isHomogeneous_C_mul_X _ _).add (isHomogeneous_C_mul_X _ _)
    have hL0 : (C a * X 0 + C b * X 2 : MvPolynomial (Fin 3) k) ≠ 0 := fun h ↦ hb <| by
      simpa using congrArg (eval ![0, 0, 1]) h
    have hndvd : ¬X 0 ∣ (C a * X 0 + C b * X 2 : MvPolynomial (Fin 3) k) := fun ⟨p, hp⟩ ↦ hb <| by
      simpa using congrArg (eval ![0, 0, 1]) hp
    have : (C a * X 0 ^ 2 + C b * (X 0 * X 2) : MvPolynomial (Fin 3) k) =
        X 0 * (C a * X 0 + C b * X 2) := by ring
    rw [this, squarefree_mul_iff]
    exact ⟨prime_X.irreducible.isRelPrime_iff_not_dvd.2 hndvd, prime_X.irreducible.squarefree,
      (irreducible_of_isHomogeneous_one hL hL0).squarefree⟩
/-- A change of coordinates fixing the line `X = 0` turns
`Y (a X² + b XZ) + d X³ + e X²Z + f XZ² + g Z³`, for `b ≠ 0`, into
`XYZ + d' X³ + e' X²Z + f' XZ² + g' Z³`. -/
private theorem exists_linearSubst_shape_eq_of_ne_zero {a b d e f g : k} (hb : b ≠ 0) :
    ∃ M : Matrix (Fin 3) (Fin 3) k, Function.Injective M.mulVecLin ∧
      ∃ d' e' f' g' : k, linearSubst M (shape a b 0 d e f g) = X 0 * X 1 * X 2 +
        (C d' * X 0 ^ 3 + C e' * (X 0 ^ 2 * X 2) + C f' * (X 0 * X 2 ^ 2) + C g' * X 2 ^ 3) := by
  obtain ⟨u, hu⟩ : ∃ u, b * u = 1 := ⟨b⁻¹, mul_inv_cancel₀ hb⟩
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  refine ⟨!![1, 0, 0; 0, 1, 0; -a * u, 0, u],
    Matrix.mulVecLin_injective_iff_isUnit_det.2 <| Ne.isUnit (by simp [Matrix.det_fin_three, hu0]),
    d - e * u * a + f * u ^ 2 * a ^ 2 - g * u ^ 3 * a ^ 3,
    e * u - 2 * f * u ^ 2 * a + 3 * g * u ^ 3 * a ^ 2, f * u ^ 2 - 3 * g * u ^ 3 * a, g * u ^ 3,
    MvPolynomial.funext fun x ↦ ?_⟩
  simp [shape, Fin.sum_univ_three]
  linear_combination x 1 * x 0 * (x 2 - a * x 0) * hu

section CharZero

variable [CharZero k]

/-- An irreducible cubic `Y aX² + d X³ + e X²Z + f XZ² + g Z³`, `a ≠ 0`, is carried to
`Y²Z = X³` by a change of coordinates, in characteristic zero. -/
private theorem exists_linearSubst_shape_eq_X_sq_mul_X_sub_X_pow_three {a d e f g : k}
    (ha : a ≠ 0) (h : Irreducible (shape a 0 0 d e f g)) :
    ∃ M : Matrix (Fin 3) (Fin 3) k, Function.Injective M.mulVecLin ∧
      linearSubst M (shape a 0 0 d e f g) = X 1 ^ 2 * X 2 - X 0 ^ 3 := by
  have hg : g ≠ 0 := by
    rintro rfl
    refine not_irreducible_mul_of_eval_eq_zero (x := (0 : Fin 3 → k)) (p := X 0)
      (q := C a * X 0 * X 1 + C d * X 0 ^ 2 + C e * (X 0 * X 2) + C f * X 2 ^ 2)
      (by simp) (by simp) ?_
    convert h using 1
    simp [shape]; ring
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq g⁻¹ three_pos
  have hμ' : g * μ ^ 3 = 1 := by rw [hμ]; field_simp
  have hμ0 : μ ≠ 0 := by rintro rfl; simp at hμ'
  obtain ⟨l, hl⟩ : ∃ l, f + 3 * g * l = 0 := ⟨-f / (3 * g), by field_simp; ring⟩
  set d' := d + e * l + f * l ^ 2 + g * l ^ 3
  set e' := e + 2 * f * l + 3 * g * l ^ 2
  refine ⟨!![0, 1, 0; e' * μ / a, -d' / a, 1 / a; -μ, l, 0],
    Matrix.mulVecLin_injective_iff_isUnit_det.2 <| Ne.isUnit (by
      simp [Matrix.det_fin_three, ha, hμ0]), MvPolynomial.funext fun x ↦ ?_⟩
  simp [shape, Fin.sum_univ_three]
  field_simp
  linear_combination (x 1 * μ ^ 2 * x 0 ^ 2) * hl - x 0 ^ 3 * hμ'

/-- An irreducible cubic `XYZ + d X³ + e X²Z + f XZ² + g Z³` is carried to `Y²Z = X²(X + Z)` by a
change of coordinates, in characteristic zero. -/
private theorem exists_linearSubst_X_mul_X_mul_X_add_eq {d e f g : k}
    (h : Irreducible (X 0 * X 1 * X 2 + (C d * X 0 ^ 3 + C e * (X 0 ^ 2 * X 2) +
      C f * (X 0 * X 2 ^ 2) + C g * X 2 ^ 3) : MvPolynomial (Fin 3) k)) :
    ∃ M : Matrix (Fin 3) (Fin 3) k, Function.Injective M.mulVecLin ∧
      linearSubst M (X 0 * X 1 * X 2 + (C d * X 0 ^ 3 + C e * (X 0 ^ 2 * X 2) +
        C f * (X 0 * X 2 ^ 2) + C g * X 2 ^ 3)) = X 1 ^ 2 * X 2 - X 0 ^ 2 * (X 0 + X 2) := by
  have hd : d ≠ 0 := by
    rintro rfl
    refine not_irreducible_mul_of_eval_eq_zero (x := (0 : Fin 3 → k)) (p := X 2)
      (q := X 0 * X 1 + C e * X 0 ^ 2 + C f * (X 0 * X 2) + C g * X 2 ^ 2)
      (by simp) (by simp) ?_
    convert h using 1
    simp; ring
  have hg : g ≠ 0 := by
    rintro rfl
    refine not_irreducible_mul_of_eval_eq_zero (x := (0 : Fin 3 → k)) (p := X 0)
      (q := X 1 * X 2 + C d * X 0 ^ 2 + C e * (X 0 * X 2) + C f * X 2 ^ 2)
      (by simp) (by simp) ?_
    convert h using 1
    simp; ring
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq d⁻¹ three_pos
  have hα' : α ^ 3 * d = 1 := by rw [hα]; field_simp
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq g⁻¹ three_pos
  have hβ' : β ^ 3 * g = 1 := by rw [hβ]; field_simp
  have hα0 : α ≠ 0 := by rintro rfl; simp at hα'
  have hβ0 : β ≠ 0 := by rintro rfl; simp at hβ'
  -- `c = 1 / (αβ)`, written without division
  set c := α ^ 2 * β ^ 2 * d * g
  refine ⟨!![-α / 2, α / 2, 0; -3 * c + e * α / 2 + f * β / 2, -e * α / 2 + f * β / 2, -4 * c;
      -β / 2, -β / 2, 0],
    Matrix.mulVecLin_injective_iff_isUnit_det.2 <| Ne.isUnit (by
      simp [Matrix.det_fin_three, c]; ring_nf; simp [hα0, hβ0, hd, hg]),
    MvPolynomial.funext fun x ↦ ?_⟩
  simp [Fin.sum_univ_three, c]
  -- with `s = (y - x) / 2`, `t = -(y + x) / 2` and `ρ = -4z - 3x`, the cubic is `stρ + s³ + t³`
  linear_combination
    ((x 1 - x 0) / 2 * (-(x 1 + x 0) / 2) * (-4 * x 2 - 3 * x 0) * β ^ 3 * g +
      ((x 1 - x 0) / 2) ^ 3) * hα' +
    ((x 1 - x 0) / 2 * (-(x 1 + x 0) / 2) * (-4 * x 2 - 3 * x 0) + (-(x 1 + x 0) / 2) ^ 3) * hβ'

/-- An irreducible cubic with a multiple point `P` is carried, by a change of coordinates taking
`[0 : 1 : 0]` to `P`, to a cubic `Y (a X² + b XZ) + d X³ + e X²Z + f XZ² + g Z³` with
`(a, b) ≠ (0, 0)`; then `P` is a node exactly when `b ≠ 0`. -/
private theorem exists_linearSubst_eq_shape_and_iff (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    {P : ℙ k (Fin 3 → k)} (hP : IsMultiplePoint F P) :
    ∃ M : Matrix (Fin 3) (Fin 3) k, Function.Injective M.mulVecLin ∧
      ∃ a b d e f g : k, linearSubst M F = shape a b 0 d e f g ∧ (a ≠ 0 ∨ b ≠ 0) ∧
        (IsOrdinaryMultiplePoint F P ↔ b ≠ 0) := by
  obtain ⟨M, hM, hMQ, a, b, d, e, f, g, hMF⟩ := exists_linearSubst_eq_shape hF hP
  have hirrG : Irreducible (shape a b 0 d e f g) := hMF ▸
    (irreducible_linearSubst_iff (Matrix.isUnit_det_of_mulVecLin_injective hM)).2 hirr
  have hmult : mult (shape a b 0 d e f g) (mk k ![0, 1, 0] (by simp)) = 2 := by
    rw [← hMF, mult_linearSubst hF hM, hMQ]
    exact mult_eq_two_of_degree_three hF hirr hP
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra! h
    obtain ⟨rfl, rfl⟩ := h
    rw [mult_shape_zero hirrG.ne_zero] at hmult
    norm_num at hmult
  refine ⟨M, hM, a, b, d, e, f, g, hMF, hab, ?_⟩
  rw [← hMQ, ← isOrdinaryMultiplePoint_linearSubst_iff hF hM, hMF, isOrdinaryMultiplePoint_def,
    isMultiplePoint_def, hmult, (mult_and_leadingForm_shape hab).2.squarefree_iff,
    squarefree_C_mul_X_sq_add_iff hab]
  simp

/-- **Normal form of the nodal cubic.** Over an algebraically closed field of characteristic
zero, an irreducible cubic `F` with a node `P` (an ordinary double point) is projectively
equivalent to `Y²Z = X²(X + Z)`: some invertible change of coordinates carries `F` to
`Y²Z - X²(X + Z)` exactly (Fulton, Problem 5.11). -/
theorem exists_linearSubst_eq_X_sq_mul_X_sub_X_sq_mul_X_add_X (hF : F.IsHomogeneous 3)
    (hirr : Irreducible F) {P : ℙ k (Fin 3 → k)} (hP : IsOrdinaryMultiplePoint F P) :
    ∃ M : Matrix (Fin 3) (Fin 3) k, Function.Injective M.mulVecLin ∧
      linearSubst M F = X 1 ^ 2 * X 2 - X 0 ^ 2 * (X 0 + X 2) := by
  obtain ⟨M, hM, a, b, d, e, f, g, hMF, -, hiff⟩ :=
    exists_linearSubst_eq_shape_and_iff hF hirr (isOrdinaryMultiplePoint_def.1 hP).1
  obtain ⟨N, hN, d', e', f', g', hNG⟩ := exists_linearSubst_shape_eq_of_ne_zero (a := a)
    (d := d) (e := e) (f := f) (g := g) (hiff.1 hP)
  have hirrN := (irreducible_linearSubst_iff (Matrix.isUnit_det_of_mulVecLin_injective
    (Matrix.mulVecLin_mul_injective hM hN))).2 hirr
  rw [linearSubst_mul_apply, hMF, hNG] at hirrN
  obtain ⟨R, hR, hRG⟩ := exists_linearSubst_X_mul_X_mul_X_add_eq hirrN
  exact ⟨M * N * R, Matrix.mulVecLin_mul_injective (Matrix.mulVecLin_mul_injective hM hN) hR,
    by rw [linearSubst_mul_apply, linearSubst_mul_apply, hMF, hNG, hRG]⟩

/-- An irreducible cubic `F` over an algebraically closed field of characteristic zero, with a
double point `P` that is not a node, is carried to `Y²Z = X³` by a change of coordinates. -/
theorem exists_linearSubst_eq_X_sq_mul_X_sub_X_pow_three_of_not_isOrdinaryMultiplePoint
    (hF : F.IsHomogeneous 3) (hirr : Irreducible F) {P : ℙ k (Fin 3 → k)}
    (hP : IsMultiplePoint F P) (hnode : ¬IsOrdinaryMultiplePoint F P) :
    ∃ M : Matrix (Fin 3) (Fin 3) k, Function.Injective M.mulVecLin ∧
      linearSubst M F = X 1 ^ 2 * X 2 - X 0 ^ 3 := by
  obtain ⟨M, hM, a, b, d, e, f, g, hMF, hab, hiff⟩ :=
    exists_linearSubst_eq_shape_and_iff hF hirr hP
  have hb : b = 0 := by simpa [hiff] using hnode
  subst hb
  have hirrG : Irreducible (shape a 0 0 d e f g) := hMF ▸
    (irreducible_linearSubst_iff (Matrix.isUnit_det_of_mulVecLin_injective hM)).2 hirr
  obtain ⟨N, hN, hNG⟩ := exists_linearSubst_shape_eq_X_sq_mul_X_sub_X_pow_three
    (hab.resolve_right (by simp)) hirrG
  exact ⟨M * N, Matrix.mulVecLin_mul_injective hM hN, by rw [linearSubst_mul_apply, hMF, hNG]⟩

/-- **Normal form of the cuspidal cubic.** Over an algebraically closed field of characteristic
zero, an irreducible cubic `F` with a cusp `P` (a double point with a single tangent `L`, of
multiplicity `2`) is projectively equivalent to `Y²Z = X³`: some invertible change of coordinates
carries `F` to `Y²Z - X³` exactly (Fulton, Problem 5.10). -/
theorem exists_linearSubst_eq_X_sq_mul_X_sub_X_pow_three (hF : F.IsHomogeneous 3)
    (hirr : Irreducible F) {P : ℙ k (Fin 3 → k)} (hP : IsMultiplePoint F P)
    {L : MvPolynomial (Fin 3) k} (hL : IsTangentAt F P L) (hLm : tangentMultiplicity F P L = 2) :
    ∃ M : Matrix (Fin 3) (Fin 3) k, Function.Injective M.mulVecLin ∧
      linearSubst M F = X 1 ^ 2 * X 2 - X 0 ^ 3 := by
  refine exists_linearSubst_eq_X_sq_mul_X_sub_X_pow_three_of_not_isOrdinaryMultiplePoint hF hirr hP
    fun h ↦ ?_
  obtain ⟨hL1, hL0, -⟩ := isTangentAt_def.1 hL
  refine (irreducible_of_isHomogeneous_one hL1 hL0).not_isUnit
    ((isOrdinaryMultiplePoint_def.1 h).2 L ?_)
  have := pow_multiplicity_dvd L (leadingForm F P)
  rwa [← tangentMultiplicity_def, hLm, pow_two] at this

end CharZero

/-! ### The cuspidal and the nodal cubic -/

omit [IsAlgClosed k] in
/-- `Y (a X² + b XZ + c Z²) + d X³ + e X²Z + f XZ² + g Z³` is a form of degree three. -/
private theorem isHomogeneous_shape (a b c d e f g : k) :
    (shape a b c d e f g).IsHomogeneous 3 := by
  have hX (j : Fin 3) : (X j : MvPolynomial (Fin 3) k).IsHomogeneous 1 := isHomogeneous_X k j
  have hC (r : k) : (C r : MvPolynomial (Fin 3) k).IsHomogeneous 0 := isHomogeneous_C _ r
  exact (hX 1).mul ((((hC a).mul ((hX 0).pow 2)).add ((hC b).mul ((hX 0).mul (hX 2)))).add
    ((hC c).mul ((hX 2).pow 2))) |>.add <|
    ((((hC d).mul ((hX 0).pow 3)).add ((hC e).mul (((hX 0).pow 2).mul (hX 2)))).add
      ((hC f).mul ((hX 0).mul ((hX 2).pow 2)))).add ((hC g).mul ((hX 2).pow 3))

omit [IsAlgClosed k] in
/-- A matrix `M` with `M (0, 0, 1) = (0, 1, 0)` carries `[0 : 0 : 1]` to `[0 : 1 : 0]`. -/
private theorem map_mk_eq_of_mulVec_eq {M : Matrix (Fin 3) (Fin 3) k}
    (hM : Function.Injective M.mulVecLin) (h : M *ᵥ ![0, 0, 1] = ![0, 1, 0]) :
    map M.mulVecLin hM (mk k ![0, 0, 1] (by simp)) = mk k ![0, 1, 0] (by simp) := by
  rw [map_mk]
  congr 1

omit [IsAlgClosed k] in
/-- The cuspidal cubic `Y²Z = X³` is `Y X² - Z³` after a permutation of the coordinates taking
`[0 : 0 : 1]` to `[0 : 1 : 0]`. -/
private theorem linearSubst_shape_eq_X_sq_mul_X_sub_X_pow_three :
    linearSubst !![0, 1, 0; 0, 0, 1; 1, 0, 0] (shape (1 : k) 0 0 0 0 0 (-1)) =
      X 1 ^ 2 * X 2 - X 0 ^ 3 := by
  simp [shape, linearSubst_X, Fin.sum_univ_three]
  ring

omit [IsAlgClosed k] in
/-- The leading form of the cuspidal cubic `Y²Z = X³` at `[0 : 0 : 1]` is `Y²`, up to a
scalar. -/
theorem associated_leadingForm_X_sq_mul_X_sub_X_pow_three :
    Associated (leadingForm (X 1 ^ 2 * X 2 - X 0 ^ 3 : MvPolynomial (Fin 3) k)
      (mk k ![0, 0, 1] (by simp))) (X 1 ^ 2) := by
  have hM : Function.Injective
      (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) k).mulVecLin :=
    Matrix.mulVecLin_injective_iff_isUnit_det.2 <| Ne.isUnit (by simp [Matrix.det_fin_three])
  rw [← linearSubst_shape_eq_X_sq_mul_X_sub_X_pow_three]
  refine (leadingForm_linearSubst (isHomogeneous_shape _ _ _ _ _ _ _) hM _).trans ?_
  rw [map_mk_eq_of_mulVec_eq hM (by ext i; fin_cases i <;> simp)]
  convert ((mult_and_leadingForm_shape (a := (1 : k)) (b := 0) (d := 0) (e := 0) (f := 0) (g := -1)
    (Or.inl one_ne_zero)).2.map
    (linearSubst !![0, 1, 0; 0, 0, 1; 1, 0, 0])) using 1
  simp [linearSubst_X, Fin.sum_univ_three]
omit [IsAlgClosed k] in
/-- The cuspidal cubic `Y²Z = X³` has a double point at `[0 : 0 : 1]`. -/
theorem mult_X_sq_mul_X_sub_X_pow_three :
    mult (X 1 ^ 2 * X 2 - X 0 ^ 3 : MvPolynomial (Fin 3) k) (mk k ![0, 0, 1] (by simp)) = 2 := by
  have hM : Function.Injective
      (!![0, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) k).mulVecLin :=
    Matrix.mulVecLin_injective_iff_isUnit_det.2 <| Ne.isUnit (by simp [Matrix.det_fin_three])
  rw [← linearSubst_shape_eq_X_sq_mul_X_sub_X_pow_three,
    mult_linearSubst (isHomogeneous_shape _ _ _ _ _ _ _) hM,
    map_mk_eq_of_mulVec_eq hM (by ext i; fin_cases i <;> simp)]
  exact (mult_and_leadingForm_shape (Or.inl one_ne_zero)).1

omit [IsAlgClosed k] in
/-- The point `[0 : 0 : 1]` is a multiple point of the cuspidal cubic `Y²Z = X³`. -/
theorem isMultiplePoint_X_sq_mul_X_sub_X_pow_three :
    IsMultiplePoint (X 1 ^ 2 * X 2 - X 0 ^ 3 : MvPolynomial (Fin 3) k)
      (mk k ![0, 0, 1] (by simp)) := by
  rw [isMultiplePoint_def, mult_X_sq_mul_X_sub_X_pow_three]

omit [IsAlgClosed k] in
/-- The line `Y = 0` is tangent to the cuspidal cubic `Y²Z = X³` at `[0 : 0 : 1]`. -/
theorem isTangentAt_X_sq_mul_X_sub_X_pow_three :
    IsTangentAt (X 1 ^ 2 * X 2 - X 0 ^ 3 : MvPolynomial (Fin 3) k) (mk k ![0, 0, 1] (by simp))
      (X 1) := by
  refine isTangentAt_def.2 ⟨isHomogeneous_X k 1, X_ne_zero _, ?_,
    associated_leadingForm_X_sq_mul_X_sub_X_pow_three.dvd_iff_dvd_right.2
      (dvd_pow_self _ two_ne_zero)⟩
  rw [(isHomogeneous_X k 1).eval_rep_mk_eq_zero_iff]
  simp

omit [IsAlgClosed k] in
/-- The cuspidal cubic `Y²Z = X³` has a cusp at `[0 : 0 : 1]`: its tangent `Y = 0` there has
multiplicity `2`. -/
theorem tangentMultiplicity_X_sq_mul_X_sub_X_pow_three :
    tangentMultiplicity (X 1 ^ 2 * X 2 - X 0 ^ 3 : MvPolynomial (Fin 3) k)
      (mk k ![0, 0, 1] (by simp)) (X 1) = 2 := by
  rw [tangentMultiplicity_def,
    multiplicity_eq_of_associated_right associated_leadingForm_X_sq_mul_X_sub_X_pow_three,
    multiplicity_pow_self_of_prime prime_X]

omit [IsAlgClosed k] in
/-- The nodal cubic `Y²Z = X²(X + Z)` is `Y (X² + 2XZ) - Z³` after a change of coordinates taking
`[0 : 0 : 1]` to `[0 : 1 : 0]`. -/
private theorem linearSubst_shape_eq_X_sq_mul_X_sub_X_sq_mul_X_add_X :
    linearSubst !![-1, 1, 0; 0, 0, 1; 1, 0, 0] (shape (1 : k) 2 0 0 0 0 (-1)) =
      X 1 ^ 2 * X 2 - X 0 ^ 2 * (X 0 + X 2) := by
  simp [shape, linearSubst_X, Fin.sum_univ_three, map_ofNat C 2, map_ofNat (linearSubst _) 2]
  ring

omit [IsAlgClosed k] in
/-- The nodal cubic `Y²Z = X²(X + Z)` has a node at `[0 : 0 : 1]`, an ordinary double point with
the tangents `Y = ±X`, when `2 ≠ 0` in `k`. -/
theorem isOrdinaryMultiplePoint_X_sq_mul_X_sub_X_sq_mul_X_add_X (h2 : (2 : k) ≠ 0) :
    IsOrdinaryMultiplePoint (X 1 ^ 2 * X 2 - X 0 ^ 2 * (X 0 + X 2) : MvPolynomial (Fin 3) k)
      (mk k ![0, 0, 1] (by simp)) := by
  have hM : Function.Injective
      (!![-1, 1, 0; 0, 0, 1; 1, 0, 0] : Matrix (Fin 3) (Fin 3) k).mulVecLin :=
    Matrix.mulVecLin_injective_iff_isUnit_det.2 <| Ne.isUnit (by simp [Matrix.det_fin_three])
  rw [← linearSubst_shape_eq_X_sq_mul_X_sub_X_sq_mul_X_add_X,
    isOrdinaryMultiplePoint_linearSubst_iff (isHomogeneous_shape _ _ _ _ _ _ _) hM,
    map_mk_eq_of_mulVec_eq hM (by ext i; fin_cases i <;> simp), isOrdinaryMultiplePoint_def,
    isMultiplePoint_def]
  obtain ⟨h1, h2'⟩ := mult_and_leadingForm_shape (a := (1 : k)) (b := 2) (d := 0) (e := 0) (f := 0)
    (g := -1) (Or.inl one_ne_zero)
  exact ⟨h1.ge, h2'.squarefree_iff.2 ((squarefree_C_mul_X_sq_add_iff (Or.inl one_ne_zero)).2 h2)⟩

/-! ### The Legendre form of a nonsingular cubic -/

/-- **Legendre form of a nonsingular cubic.** Over an algebraically closed field `k` with
`2 ≠ 0`, a nonsingular cubic `F` is projectively equivalent to `Y²Z = X(X - Z)(X - λZ)` for some
`λ ≠ 0, 1`: some invertible change of coordinates carries `F` to
`Y²Z - X(X - Z)(X - λZ)` exactly ([Fulton2008], Problem 5.24 (b), there in characteristic
zero). -/
theorem IsNonsingular.exists_linearSubst_eq_legendre (h2 : (2 : k) ≠ 0)
    (hF : F.IsHomogeneous 3) (h : IsNonsingular F) :
    ∃ (M : Matrix (Fin 3) (Fin 3) k) (l : k), Function.Injective M.mulVecLin ∧ l ≠ 0 ∧ l ≠ 1 ∧
      linearSubst M F = X 1 ^ 2 * X 2 - X 0 * (X 0 - X 2) * (X 0 - C l * X 2) := by
  -- a flex, and the Weierstrass form `Y²Z = X³ + a₂X²Z + a₄XZ² + a₆Z³` there
  obtain ⟨O, hO⟩ := h.exists_isFlex hF le_rfl
    (by have := mul_ne_zero h2 h2; norm_num at this ⊢; exact this)
  obtain ⟨T, c, W, hT, hc, -, hTF, h1, h3, -⟩ :=
    hO.exists_linearSubst_eq_smul_polynomial_of_two_ne_zero h2 hF (h.irreducible hF three_ne_zero)
  -- the roots `e₁, e₂, e₃` of the `2`-division polynomial, distinct as `F` is nonsingular
  have hPa : W.twoTorsionPolynomial.a = 4 := by simp only [WeierstrassCurve.twoTorsionPolynomial]
  have ha : W.twoTorsionPolynomial.a ≠ 0 := by
    rw [hPa, show (4 : k) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  obtain ⟨e₁, e₂, e₃, he⟩ := (Cubic.splits_iff_roots_eq_three (φ := RingHom.id k) ha).1
    (IsAlgClosed.splits _)
  have hP := Cubic.eq_prod_three_roots ha he
  rw [Cubic.map_toPoly, Polynomial.map_id, RingHom.id_apply, hPa] at hP
  have hns : IsNonsingular (X 1 ^ 2 * X 2 -
      (X 0 - C e₁ * X 2) * (X 0 - C e₂ * X 2) * (X 0 - C e₃ * X 2)) := by
    rw [← WeierstrassCurve.toProjective_polynomial_eq_prod h2 h1 h3 hP,
      ← isNonsingular_smul_iff hc, ← hTF, isNonsingular_linearSubst_iff hT]
    exact h
  have h12 : e₂ ≠ e₁ := by
    rintro rfl
    exact not_isNonsingular_X_sq_mul_X_sub_X_sub_C_mul_X_sq_mul e₂ (X 0 - C e₃ * X 2)
      (by convert hns using 2; ring)
  have h13 : e₃ ≠ e₁ := by
    rintro rfl
    exact not_isNonsingular_X_sq_mul_X_sub_X_sub_C_mul_X_sq_mul e₃ (X 0 - C e₂ * X 2)
      (by convert hns using 2; ring)
  have h23 : e₃ ≠ e₂ := by
    rintro rfl
    exact not_isNonsingular_X_sq_mul_X_sub_X_sub_C_mul_X_sq_mul e₃ (X 0 - C e₁ * X 2)
      (by convert hns using 2; ring)
  -- Tau Ceti's change of variables to the Legendre form, with `λ = (e₃ - e₁) / (e₂ - e₁)`
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (e₂ - e₁) two_pos
  obtain ⟨V, hV⟩ := WeierstrassCurve.exists_variableChange_smul_eq_freyCurve_one h2 hP h12 hu
  set l := (e₃ - e₁) / (e₂ - e₁)
  set G : MvPolynomial (Fin 3) k := X 1 ^ 2 * X 2 - X 0 * (X 0 - X 2) * (X 0 - C l * X 2)
  have hfrey :
      (TauCeti.freyCurve 1 ((e₁ - e₃) / (e₂ - e₁))).toProjective.polynomial = G := by
    rw [show (e₁ - e₃) / (e₂ - e₁) = -l by rw [← neg_div, neg_sub]]
    simp [WeierstrassCurve.Projective.polynomial, G]
    ring
  have hTV : linearSubst (T * V.toMatrix) F = C (c * V.u ^ 6) * G := by
    rw [linearSubst_mul_apply, hTF, map_smul, WeierstrassCurve.Projective.linearSubst_polynomial,
      hV, hfrey, smul_eq_C_mul, map_mul]
    ring
  -- a scaling `X ↦ sX` with `s³ = (c u⁶)⁻¹` removes the scalar
  have hcu : c * V.u ^ 6 ≠ 0 := mul_ne_zero hc (pow_ne_zero _ V.u.ne_zero)
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (c * V.u ^ 6)⁻¹ three_pos
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact inv_ne_zero hcu (hs.symm.trans (zero_pow three_ne_zero))
  have hD : Function.Injective (Matrix.diagonal fun _ : Fin 3 ↦ s).mulVecLin :=
    Matrix.mulVecLin_injective_iff_isUnit_det.2 <| Ne.isUnit (by simp [hs0])
  refine ⟨T * V.toMatrix * Matrix.diagonal fun _ ↦ s, l,
    Matrix.mulVecLin_mul_injective (Matrix.mulVecLin_mul_injective hT
      (Matrix.mulVecLin_injective_iff_isUnit_det.2
        (Matrix.isUnit_det_of_right_inverse V.toMatrix_mul_toMatrix_inv))) hD,
    div_ne_zero (sub_ne_zero.2 h13) (sub_ne_zero.2 h12), ?_, ?_⟩
  · rw [Ne, div_eq_one_iff_eq (sub_ne_zero.2 h12)]
    exact fun h ↦ h23 (sub_left_injective h)
  · have hDG : linearSubst (Matrix.diagonal fun _ ↦ s) G = C s ^ 3 * G := by
      simp [G, linearSubst_X, Fin.sum_univ_three, Matrix.diagonal_apply]
      ring
    have hs1 : C (c * V.u ^ 6) * C s ^ 3 = (1 : MvPolynomial (Fin 3) k) := by
      rw [← map_pow, ← map_mul, hs, mul_inv_cancel₀ hcu, map_one]
    rw [linearSubst_mul_apply, hTV, map_mul, hDG, algHom_C, algebraMap_eq]
    linear_combination G * hs1

end IsAlgClosed

end PlaneCurves.Projective

end
