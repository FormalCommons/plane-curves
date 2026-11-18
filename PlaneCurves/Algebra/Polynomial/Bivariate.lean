/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Coefficients and degrees of bivariate polynomials in two variables

Mathlib's `Polynomial.Bivariate.equivMvPolynomial` identifies `R[X][Y]` with
`MvPolynomial (Fin 2) R`, the inner variable `X` becoming `X 0` and the outer variable `Y`
becoming `X 1`. This file computes the image of a constant and the coefficients of the image,
and shows that the degree in `Y` is the degree in the variable `X 1`.

## Main results

* `Polynomial.Bivariate.equivMvPolynomial_C`: `equivMvPolynomial` sends a constant `C r`, for
  `r ∈ R[X]`, to `r(X₀)`.
* `Polynomial.Bivariate.coeff_equivMvPolynomial`: the coefficient of `X 0 ^ i * X 1 ^ j` in the
  image of `p` is the coefficient of `X ^ i` in the coefficient of `Y ^ j` of `p`.
* `Polynomial.Bivariate.degreeOf_one_equivMvPolynomial`: the degree in `X 1` of the image of `p`
  is the degree of `p` in `Y`.
-/

public section

namespace Polynomial.Bivariate

variable {R : Type*} [CommSemiring R]

/-- The isomorphism `R[X][Y] ≃ R[X₀, X₁]` sends a constant `C r`, for `r ∈ R[X]`, to `r(X₀)`. -/
@[simp]
theorem equivMvPolynomial_C (r : R[X]) :
    equivMvPolynomial R (C r) = aeval (MvPolynomial.X 0) r := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    simp [← C_mul_X_pow_eq_monomial, MvPolynomial.algebraMap_eq]

/-- The coefficient of the monomial `m` in the polynomial in two variables given by
`p ∈ R[X][Y]` is the coefficient of `X ^ m 0` in the coefficient of `Y ^ m 1` of `p`. -/
theorem coeff_equivMvPolynomial (p : R[X][Y]) (m : Fin 2 →₀ ℕ) :
    (equivMvPolynomial R p).coeff m = (p.coeff (m 1)).coeff (m 0) := by
  classical
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb => simp_all [map_add]
    | monomial i c =>
      have h : equivMvPolynomial R (monomial n (monomial i c)) =
          MvPolynomial.monomial (Finsupp.single 0 i + Finsupp.single 1 n) c := by
        rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, MvPolynomial.monomial_eq,
          Finsupp.prod_add_index' (by simp) (by simp [pow_add])]
        simp [mul_assoc]
      rw [h, MvPolynomial.coeff_monomial, coeff_monomial_apply]
      by_cases h1 : n = m 1 <;> by_cases h0 : i = m 0
      · rw [ite_eq_left (by ext j; fin_cases j <;> simp [h0, h1]), ite_eq_left h1,
          coeff_monomial_apply, ite_eq_left h0]
      all_goals
        have hne : Finsupp.single 0 i + Finsupp.single 1 n ≠ m := by
          rintro rfl
          simp at h0 h1
        rw [ite_eq_right hne]
        simp [h0, h1]

/-- The degree in `X 1` of the polynomial in two variables given by `p ∈ R[X][Y]` is the degree
of `p` in `Y`. -/
theorem degreeOf_one_equivMvPolynomial (p : R[X][Y]) :
    (equivMvPolynomial R p).degreeOf 1 = p.natDegree := by
  classical
  refine le_antisymm (MvPolynomial.degreeOf_le_iff.mpr fun m hm ↦ ?_) ?_
  · rw [MvPolynomial.mem_support_iff, coeff_equivMvPolynomial] at hm
    exact le_natDegree_of_ne_zero fun h ↦ hm (by rw [h, coeff_zero])
  · rcases eq_or_ne p 0 with rfl | hp
    · simp
    obtain ⟨i, hi⟩ : ∃ i, (p.coeff p.natDegree).coeff i ≠ 0 := by
      by_contra! h
      exact hp (leadingCoeff_eq_zero.mp (by ext j; exact h j))
    let m : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 p.natDegree
    have hm : m ∈ (equivMvPolynomial R p).support := by
      rw [MvPolynomial.mem_support_iff, coeff_equivMvPolynomial]
      simpa [m] using hi
    simpa [m] using MvPolynomial.monomial_le_degreeOf 1 hm

end Polynomial.Bivariate

end
