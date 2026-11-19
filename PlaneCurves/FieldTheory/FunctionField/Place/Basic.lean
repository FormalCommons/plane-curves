/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Basic

/-!
# The valuation ring of a place

For a place `Q` of a field extension `K/k`, Tau Ceti gives two valuations on `K`: the normalized
valuation `Q.valuation` of the place, and the valuation `Q.integers.valuation` of its valuation
ring `𝒪_Q`, with values in the value group of `𝒪_Q`. This file shows that they are equivalent,
so that statements about either can be read off the other, and that `𝒪_Q` is not all of `K`.

## Main results

* `TauCeti.Place.isEquiv_valuation_integers`: `Q.valuation` and `Q.integers.valuation` are
  equivalent valuations.
* `TauCeti.Place.valuation_integers_lt_one_iff`: they agree on which elements have valuation
  `< 1`, the maximal ideal of `𝒪_Q`.
* `TauCeti.Place.exists_notMem_integers`: some element of `K` is not in `𝒪_Q`.

## References

* [H. Stichtenoth, *Algebraic Function Fields and Codes*][Stichtenoth2009], §1.1
-/

public section

namespace TauCeti.Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K] (Q : Place k K)

/-- The valuation of a place is equivalent to the valuation of its valuation ring. -/
theorem isEquiv_valuation_integers : Q.valuation.IsEquiv Q.integers.valuation := by
  rw [integers_def]
  exact Valuation.isEquiv_valuation_valuationSubring _

/-- An element has valuation `< 1` for the valuation ring of a place iff it has valuation `< 1`
for the place. -/
theorem valuation_integers_lt_one_iff {z : K} :
    Q.integers.valuation z < 1 ↔ Q.valuation z < 1 :=
  Q.isEquiv_valuation_integers.lt_one_iff_lt_one.symm

/-- The valuation ring of a place is not the whole field. -/
theorem exists_notMem_integers : ∃ z, z ∉ Q.integers := by
  by_contra! h
  exact Q.integers_ne_top (eq_top_iff.2 fun z _ ↦ h z)

end TauCeti.Place

end
