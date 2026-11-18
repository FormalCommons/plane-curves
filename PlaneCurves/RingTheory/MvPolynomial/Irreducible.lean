/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
# Polynomials of total degree one are irreducible

Over a field, a polynomial of total degree one, such as a nonzero linear form
`a₀X₀ + ⋯ + aₙXₙ`, is irreducible.

## Main results

* `MvPolynomial.irreducible_of_totalDegree_eq_one'`: over a field, a polynomial of total
  degree `1` is irreducible.
-/

public section

namespace MvPolynomial

variable {σ k : Type*} [Field k]

/-- Over a field, a polynomial of total degree `1` is irreducible. -/
theorem irreducible_of_totalDegree_eq_one' {p : MvPolynomial σ k} (hp : p.totalDegree = 1) :
    Irreducible p := by
  have h₀ : p ≠ 0 := by rintro rfl; simp at hp
  refine irreducible_of_totalDegree_eq_one hp fun x hx ↦ ?_
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero h₀
  exact isUnit_iff_ne_zero.2 fun h ↦ hd (zero_dvd_iff.1 (h ▸ hx d))

end MvPolynomial

end
