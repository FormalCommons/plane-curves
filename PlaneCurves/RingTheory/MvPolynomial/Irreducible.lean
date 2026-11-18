/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
# Linear forms are irreducible

Over a field, a nonzero form of degree one, that is a nonzero linear form `a₀X₀ + ⋯ + aₙXₙ`, is
irreducible.

## Main results

* `MvPolynomial.IsHomogeneous.irreducible_of_degree_eq_one`: a nonzero linear form is
  irreducible.
-/

public section

namespace MvPolynomial

variable {σ k : Type*} [Field k] {f : MvPolynomial σ k}

/-- Over a field, a nonzero form of degree one is irreducible. -/
theorem IsHomogeneous.irreducible_of_degree_eq_one (hf : f.IsHomogeneous 1) (hf0 : f ≠ 0) :
    Irreducible f := by
  refine irreducible_of_totalDegree_eq_one (hf.totalDegree hf0) fun x hx ↦ ?_
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero hf0
  exact isUnit_iff_ne_zero.2 fun h ↦ hd (zero_dvd_iff.1 (h ▸ hx d))

end MvPolynomial

end
