/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
# Irreducibility of polynomials of total degree one over a field

Mathlib's `MvPolynomial.irreducible_of_totalDegree_eq_one` asks that the coefficients of a
polynomial of total degree `1` have no common non-unit divisor. Over a field this always holds,
so every polynomial of total degree `1` is irreducible.

## Main results

* `MvPolynomial.irreducible_of_totalDegree_eq_one'`: over a field, a polynomial of total
  degree `1` is irreducible.
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

end MvPolynomial

end
