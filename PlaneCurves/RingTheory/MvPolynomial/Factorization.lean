/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import PlaneCurves.RingTheory.UniqueFactorizationDomain.Radical

/-!
# Factors of a multivariate polynomial

Over a field, a nonzero polynomial has at most as many irreducible factors, counted with
multiplicity, as its total degree. Over a unique factorization domain `R`, a nonzero polynomial
`F ∈ R[X_σ]` factors as `F' U`, where `U` does not vanish at a given point `P` and every
irreducible factor of `F'` vanishes at `P`. Over a field, a squarefree polynomial is a nonzero
constant times the product of its distinct irreducible factors.

## Main results

* `MvPolynomial.card_factors_le_totalDegree`: over a field, a nonzero polynomial has at most
  `deg F` irreducible factors, counted with multiplicity.
* `MvPolynomial.exists_eq_mul_eval_ne_zero`: a nonzero polynomial is `F' U` with `U(P) ≠ 0` and
  every irreducible factor of `F'` vanishing at `P`.
* `MvPolynomial.exists_eq_smul_prod_toFinset_factors`: over a field, a squarefree polynomial is
  `c ∏ q` with `c ≠ 0`, the product over its distinct irreducible factors.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/-- A nonzero polynomial is `F' U` with `U(P) ≠ 0` and every irreducible factor of `F'` vanishing
at `P`. -/
theorem exists_eq_mul_eval_ne_zero (P : σ → R) {F : MvPolynomial σ R} (hF : F ≠ 0) :
    ∃ F' U, F = F' * U ∧ eval P U ≠ 0 ∧ ∀ H, Irreducible H → H ∣ F' → eval P H = 0 := by
  induction F using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hF
  | h₂ u hu => exact ⟨1, u, (one_mul u).symm, (hu.map (eval P)).ne_zero,
      fun H hH h => (hH.not_isUnit (isUnit_of_dvd_one h)).elim⟩
  | h₃ a p ha hp ih =>
    obtain ⟨F', U, rfl, hU, hF'⟩ := ih ha
    by_cases hpP : eval P p = 0
    · refine ⟨p * F', U, by ring, hU, fun H hH h => ?_⟩
      rcases hH.prime.dvd_or_dvd h with h | h
      · obtain ⟨c, rfl⟩ := (hH.associated_of_dvd hp.irreducible h).symm
        simp [hpP]
      · exact hF' H hH h
    · exact ⟨F', p * U, by ring, by simpa [hpP] using hU, hF'⟩

/-- Over a field, a nonzero polynomial has at most as many irreducible factors, counted with
multiplicity, as its total degree: the factors are nonconstant and degrees add. -/
theorem card_factors_le_totalDegree {k : Type*} [Field k] {F : MvPolynomial σ k} (hF : F ≠ 0) :
    (UniqueFactorizationMonoid.factors F).card ≤ F.totalDegree := by
  induction F using WfDvdMonoid.induction_on_irreducible with
  | zero => exact absurd rfl hF
  | unit u hu => simp [UniqueFactorizationMonoid.factors_of_isUnit hu]
  | mul a p ha hp ih =>
    rw [Multiset.card_eq_card_of_rel (UniqueFactorizationMonoid.factors_mul hp.ne_zero ha),
      Multiset.card_add, UniqueFactorizationMonoid.card_factors_of_irreducible hp,
      totalDegree_mul_of_isDomain hp.ne_zero ha]
    have hp0 : p.totalDegree ≠ 0 := fun h0 ↦ hp.not_isUnit <| by
      rw [totalDegree_eq_zero_iff_eq_C.1 h0, isUnit_map_iff, isUnit_iff_ne_zero]
      rintro hc
      exact hp.ne_zero (by rw [totalDegree_eq_zero_iff_eq_C.1 h0, hc, map_zero])
    have := ih ha
    omega

/-- Over a field, a squarefree polynomial is a nonzero constant times the product of its distinct
irreducible factors. -/
theorem exists_eq_smul_prod_toFinset_factors {k : Type*} [Field k]
    [DecidableEq (MvPolynomial σ k)] {F : MvPolynomial σ k} (hF : Squarefree F) :
    ∃ c : k, c ≠ 0 ∧ F = c • ∏ q ∈ (UniqueFactorizationMonoid.factors F).toFinset, q := by
  obtain ⟨u, hu⟩ := hF.associated_prod_toFinset_factors
  obtain ⟨c, hc, hcu⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
  refine ⟨c, hc.ne_zero, ?_⟩
  conv_lhs => rw [← hu]
  rw [hcu, smul_eq_C_mul, mul_comm]

end MvPolynomial

end
