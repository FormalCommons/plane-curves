/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
# Irreducibility of some multivariate polynomials

Mathlib's `MvPolynomial.irreducible_of_totalDegree_eq_one` asks that the coefficients of a
polynomial of total degree `1` have no common non-unit divisor. Over a field this always holds,
so every polynomial of total degree `1`, in particular every nonzero linear form, is irreducible.
Over a domain, `X₀ⁿ + X₁` is irreducible, as the image of `X₁` under an automorphism.

## Main results

* `MvPolynomial.irreducible_of_totalDegree_eq_one'`: over a field, a polynomial of total
  degree `1` is irreducible.
* `MvPolynomial.irreducible_of_isHomogeneous_one`: over a field, a nonzero linear form, in any
  number of variables, is irreducible.
* `MvPolynomial.irreducible_X_pow_add_X`: over a domain, `X₀ⁿ + X₁` is irreducible.
* `MvPolynomial.not_irreducible_mul_of_eval_eq_zero`: a product of two polynomials that vanish
  at a common point is not irreducible.
-/

public section

namespace MvPolynomial

variable {σ k : Type*} [Field k]

/-- Over a field, a polynomial of total degree `1` is irreducible. -/
theorem irreducible_of_totalDegree_eq_one' {p : MvPolynomial σ k}
    (hp : p.totalDegree = 1) : Irreducible p := by
  have h₀ : p ≠ 0 := by rintro rfl; simp at hp
  refine irreducible_of_totalDegree_eq_one hp fun x hx ↦ ?_
  obtain ⟨d, hd⟩ := ne_zero_iff.1 h₀
  exact (ne_zero_of_dvd_ne_zero hd (hx d)).isUnit

/-- Over a field, a nonzero linear form, in any number of variables, is irreducible. -/
theorem irreducible_of_isHomogeneous_one {L : MvPolynomial σ k}
    (hL : L.IsHomogeneous 1) (hL₀ : L ≠ 0) : Irreducible L :=
  irreducible_of_totalDegree_eq_one' (hL.totalDegree hL₀)

/-- Over a domain, `X₀ⁿ + X₁` is irreducible in two variables: the automorphism
`X₁ ↦ X₀ⁿ + X₁` sends the prime `X₁` to it. -/
theorem irreducible_X_pow_add_X {R : Type*} [CommRing R] [IsDomain R] (n : ℕ) :
    Irreducible (X 0 ^ n + X 1 : MvPolynomial (Fin 2) R) := by
  let e : MvPolynomial (Fin 2) R ≃ₐ[R] MvPolynomial (Fin 2) R :=
    AlgEquiv.ofAlgHom (aeval ![X 0, X 0 ^ n + X 1]) (aeval ![X 0, X 1 - X 0 ^ n])
      (by ext i; fin_cases i <;> simp) (by ext i; fin_cases i <;> simp)
  have : e (X 1) = X 0 ^ n + X 1 := by simp [e]
  rw [← this]
  exact (MulEquiv.irreducible_iff e.toMulEquiv).2 prime_X.irreducible

/-- Over a nontrivial commutative semiring, a product of two polynomials that vanish at a common
point is not irreducible: evaluation at the point sends units to units, which are nonzero. -/
theorem not_irreducible_mul_of_eval_eq_zero {R : Type*} [CommSemiring R] [Nontrivial R]
    {x : σ → R} {p q : MvPolynomial σ R} (hp : eval x p = 0) (hq : eval x q = 0) :
    ¬Irreducible (p * q) := fun h ↦ by
  rcases h.isUnit_or_isUnit rfl with h | h
  · exact (h.map (eval x)).ne_zero hp
  · exact (h.map (eval x)).ne_zero hq

end MvPolynomial

end
