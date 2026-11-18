/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# Linear forms

A linear form in the variables `X i`, `i : σ`, is written `∑ i, C (a i) * X i` with a
coefficient vector `a : σ → R`; there is no definition for it. This file gives its value, its
coefficients and its substitution by a matrix, and shows that every form of degree one has this
shape.

## Main results

* `MvPolynomial.eval_sum_C_mul_X`: the value of `∑ i, C (a i) * X i` at `x` is `a ⬝ᵥ x`.
* `MvPolynomial.coeff_single_sum_C_mul_X`, `MvPolynomial.sum_C_mul_X_injective`: the
  coefficient vector is recovered from the form.
* `MvPolynomial.IsHomogeneous.eq_sum_C_mul_X`: a form of degree one is the linear form of its
  coefficients of the monomials `X i`.
* `MvPolynomial.linearSubst_sum_C_mul_X`: substituting `X ↦ M X` into the linear form with
  coefficients `a` gives the linear form with coefficients `a ᵥ* M`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §4.2
-/

public section

namespace MvPolynomial

open Matrix

variable {σ R : Type*} [Fintype σ] [CommSemiring R]

@[simp]
theorem eval_sum_C_mul_X (a x : σ → R) : eval x (∑ i, C (a i) * X i) = a ⬝ᵥ x := by
  simp [dotProduct]

theorem isHomogeneous_sum_C_mul_X (a : σ → R) : (∑ i, C (a i) * X i).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun i _ ↦ isHomogeneous_C_mul_X (a i) i

@[simp]
theorem coeff_single_sum_C_mul_X (a : σ → R) (i : σ) :
    (∑ j, C (a j) * X j).coeff (Finsupp.single i 1) = a i := by
  classical
  simp [coeff_X, Finsupp.single_left_inj one_ne_zero]

/-- A linear form determines its coefficient vector. -/
theorem sum_C_mul_X_injective : Function.Injective fun a : σ → R ↦ ∑ i, C (a i) * X i := by
  classical
  intro a b h
  funext i
  simpa using congrArg (·.coeff (Finsupp.single i 1)) h

/-- A form of degree one is the linear form whose coefficients are its coefficients of the
monomials `X i`. -/
theorem IsHomogeneous.eq_sum_C_mul_X {φ : MvPolynomial σ R} (h : φ.IsHomogeneous 1) :
    φ = ∑ i, C (φ.coeff (Finsupp.single i 1)) * X i := by
  classical
  ext m
  by_cases hm : m.degree = 1
  · obtain ⟨i, rfl⟩ : m ∈ Set.range fun i : σ ↦ Finsupp.single i 1 := by
      rw [Finsupp.range_single_one]
      exact hm
    rw [coeff_single_sum_C_mul_X]
  · rw [h.coeff_eq_zero hm, eq_comm]
    exact (isHomogeneous_sum_C_mul_X _).coeff_eq_zero hm

/-- Substituting `X ↦ M X` into the linear form with coefficients `a` gives the linear form with
coefficients `a ᵥ* M`. -/
theorem linearSubst_sum_C_mul_X (M : Matrix σ σ R) (a : σ → R) :
    linearSubst M (∑ i, C (a i) * X i) = ∑ j, C ((a ᵥ* M) j) * X j := by
  simp only [map_sum, map_mul, linearSubst_X, algHom_C, algebraMap_eq, Finset.mul_sum,
    Matrix.vecMul, dotProduct, map_sum C, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_assoc]

end MvPolynomial

end
