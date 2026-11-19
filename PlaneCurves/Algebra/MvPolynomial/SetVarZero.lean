/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

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
* `MvPolynomial.X_dvd_iff_bind₁_update_X_zero_eq_zero`: `X i` divides `p` exactly when `p`
  vanishes at `X i = 0`.
* `MvPolynomial.eval_bind₁_update_X_zero`: evaluating `p` with `X i` set to zero.
* `MvPolynomial.IsHomogeneous.bind₁_update_X_zero`: setting `X i` to zero in a form of degree
  `n` gives a form of degree `n`.
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

/-- A polynomial is divisible by `X i` exactly when its value at `X i = 0` vanishes. -/
theorem X_dvd_iff_bind₁_update_X_zero_eq_zero {i : σ} {p : MvPolynomial σ R} :
    X i ∣ p ↔ bind₁ (Function.update X i 0) p = 0 := by
  refine ⟨?_, X_dvd_of_bind₁_update_X_zero_eq_zero⟩
  rintro ⟨q, rfl⟩
  simp

/-- Evaluating `p` with `X i` set to zero at `v` is evaluating `p` at `v` with its `i`-th
coordinate set to zero. -/
theorem eval_bind₁_update_X_zero (i : σ) (v : σ → R) (p : MvPolynomial σ R) :
    eval v (bind₁ (Function.update X i 0) p) = eval (Function.update v i 0) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp [hp, hj]

/-- Setting the variable `X i` to zero in a form of degree `n` gives a form of degree `n`. -/
theorem IsHomogeneous.bind₁_update_X_zero {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) (i : σ) : (bind₁ (Function.update X i 0) p).IsHomogeneous n := by
  have := hp.aeval (n := 1) (Function.update (X : σ → MvPolynomial σ R) i 0) fun j ↦ by
    rcases eq_or_ne j i with rfl | hj
    · simpa using isHomogeneous_zero σ R 1
    · simpa [Function.update_of_ne hj] using isHomogeneous_X R j
  rwa [aeval_eq_bind₁, one_mul] at this

end MvPolynomial

end
