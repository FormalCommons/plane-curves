/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.Tactic.LinearCombination
public import TauCeti.RingTheory.Polynomial.GaussLemma

/-!
# Relatively prime polynomials over a GCD domain

Let `R` be a GCD domain. By Gauss's lemma, relatively prime `p, q ∈ R[X]` stay relatively prime
over the fraction field `K` of `R` (Tau Ceti's `IsRelPrime.map_fraction_map`), so `a p + b q = 1`
for some `a, b ∈ K[X]`. Clearing denominators gives a nonzero constant in the ideal `(p, q)`.

## Main results

* `Polynomial.exists_C_mem_span_pair_of_isRelPrime`: over a GCD domain `R`, two relatively
  prime polynomials in `R[X]` generate an ideal that contains a nonzero constant.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §1.6, Proposition 2.
-/

public section

open scoped nonZeroDivisors

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]

/-- Over a GCD domain `R`, two relatively prime polynomials `p, q ∈ R[X]` generate an ideal that
contains a nonzero constant: `a p + b q = C r` with `r ≠ 0`. -/
theorem exists_C_mem_span_pair_of_isRelPrime {p q : R[X]} (h : IsRelPrime p q) :
    ∃ r : R, r ≠ 0 ∧ C r ∈ Ideal.span {p, q} := by
  classical
  obtain ⟨a, b, hab⟩ := isRelPrime_iff_isCoprime.mp (h.map_fraction_map (K := FractionRing R))
  obtain ⟨c, hc, hca⟩ := IsLocalization.integerNormalization_spec R⁰ a
  obtain ⟨d, hd, hdb⟩ := IsLocalization.integerNormalization_spec R⁰ b
  refine ⟨c * d, mul_ne_zero (nonZeroDivisors.ne_zero hc) (nonZeroDivisors.ne_zero hd), ?_⟩
  have key : C d * IsLocalization.integerNormalization R⁰ a * p +
      C c * IsLocalization.integerNormalization R⁰ b * q = C (c * d) := by
    apply map_injective _ (IsFractionRing.injective R (FractionRing R))
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, hca, hdb, Algebra.smul_def,
      Polynomial.algebraMap_apply, map_mul]
    linear_combination (C (algebraMap R (FractionRing R) c) *
      C (algebraMap R (FractionRing R) d)) * hab
  rw [← key]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

end Polynomial

end
