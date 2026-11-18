/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Splitting off the factors of a polynomial that vanish at a point

Over a unique factorization domain `R`, a nonzero polynomial `F ∈ R[X_σ]` factors as `F' U`,
where `U` does not vanish at a given point `P` and every irreducible factor of `F'` vanishes
at `P`.

## Main results

* `MvPolynomial.exists_eq_mul_eval_ne_zero`: a nonzero polynomial is `F' U` with `U(P) ≠ 0` and
  every irreducible factor of `F'` vanishing at `P`.
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

end MvPolynomial

end
