/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Bivariate polynomials as polynomials in two variables

Complements to Mathlib's `Polynomial.Bivariate.equivMvPolynomial : R[X][Y] ≃ₐ[R] R[X₀, X₁]`.

## Main results

* `Polynomial.Bivariate.equivMvPolynomial_C`: `equivMvPolynomial` sends a constant `C r`, for
  `r ∈ R[X]`, to `r(X₀)`.
-/

public section

namespace Polynomial.Bivariate

/-- The isomorphism `S[X][Y] ≃ S[X₀, X₁]` sends a constant `C r`, for `r ∈ S[X]`, to `r(X₀)`. -/
@[simp]
theorem equivMvPolynomial_C {S : Type*} [CommSemiring S] (r : S[X]) :
    equivMvPolynomial S (C r) = aeval (MvPolynomial.X 0) r := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    simp [← C_mul_X_pow_eq_monomial, MvPolynomial.algebraMap_eq]

end Polynomial.Bivariate

end
