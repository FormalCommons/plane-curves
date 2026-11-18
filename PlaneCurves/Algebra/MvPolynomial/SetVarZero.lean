/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Setting a variable of a polynomial to zero

For a polynomial `p` in the variables `X j`, `j ∈ σ`, the substitution
`bind₁ (Function.update X i 0)` sets the variable `X i` to zero and leaves the others alone.

## Main results

* `MvPolynomial.bind₁_update_X_zero_bind₁_update_X_zero`: setting `X i` to zero is idempotent.
* `MvPolynomial.X_dvd_sub_bind₁_update_X_zero`: `p` and its value at `X i = 0` agree modulo
  `X i`.
* `MvPolynomial.X_dvd_of_bind₁_update_X_zero_eq_zero`: a polynomial that vanishes at `X i = 0` is
  divisible by `X i`.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] [DecidableEq σ]

/-- Setting the variable `X i` to zero twice is setting it to zero once. -/
@[simp]
theorem bind₁_update_X_zero_bind₁_update_X_zero (i : σ) (p : MvPolynomial σ R) :
    bind₁ (Function.update X i 0) (bind₁ (Function.update X i 0) p) =
      bind₁ (Function.update X i (0 : MvPolynomial σ R)) p := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun j ↦ ?_
  rcases eq_or_ne j i with rfl | hj <;> simp [*]

/-- A polynomial and its value at `X i = 0` agree modulo `X i`. -/
theorem X_dvd_sub_bind₁_update_X_zero (i : σ) (p : MvPolynomial σ R) :
    X i ∣ p - bind₁ (Function.update X i 0) p := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  change Ideal.Quotient.mkₐ R _ p = Ideal.Quotient.mkₐ R _ (bind₁ _ p)
  rw [← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun j ↦ ?_
  rcases eq_or_ne j i with rfl | hj
  · simp
  · simp [hj]

/-- A polynomial whose value at `X i = 0` vanishes is divisible by `X i`. -/
theorem X_dvd_of_bind₁_update_X_zero_eq_zero {i : σ} {p : MvPolynomial σ R}
    (hp : bind₁ (Function.update X i 0) p = 0) : X i ∣ p := by
  simpa [hp] using X_dvd_sub_bind₁_update_X_zero i p

end MvPolynomial

end
