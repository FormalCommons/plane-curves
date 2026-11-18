/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.Tactic.Ring

/-!
# Multiplicity of a prime in a product of irreducibles

The multiplicity of a prime `p` in the product of a multiset `u` of irreducible elements is the
number of elements of `u` associated to `p`. This is a multiset version of
`Finset.emultiplicity_prod` for products of irreducibles.

## Main results

* `Multiset.emultiplicity_prod_eq_countP`, `Multiset.multiplicity_prod_eq_countP`: the
  multiplicity of a prime in a product of irreducibles counts the factors associated to it.
-/

public section

namespace Multiset

variable {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α] [WfDvdMonoid α] {p : α}
  [DecidablePred (Associated p)] {u : Multiset α}

/-- The multiplicity of a prime in a product of irreducibles is the number of factors associated
to it. -/
theorem emultiplicity_prod_eq_countP (hp : Prime p) (hu : ∀ q ∈ u, Irreducible q) :
    emultiplicity p u.prod = u.countP (Associated p) := by
  induction u using Multiset.induction_on with
  | empty => simp [emultiplicity_of_one_right hp.not_isUnit]
  | cons q u ih =>
    rw [Multiset.prod_cons, emultiplicity_mul hp,
      ih fun r hr ↦ hu r (Multiset.mem_cons_of_mem hr), Multiset.countP_cons]
    have hq := hu q (Multiset.mem_cons_self q u)
    split_ifs with h
    · rw [emultiplicity_eq_of_associated_right h.symm,
        (FiniteMultiplicity.of_prime_left hp hp.ne_zero).emultiplicity_self]
      push_cast
      ring
    · rw [emultiplicity_eq_zero.2 fun hd ↦ h (hp.irreducible.associated_of_dvd hq hd)]
      simp

/-- The multiplicity of a prime in a product of irreducibles is the number of factors associated
to it. -/
theorem multiplicity_prod_eq_countP (hp : Prime p) (hu : ∀ q ∈ u, Irreducible q) :
    multiplicity p u.prod = u.countP (Associated p) :=
  multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_prod_eq_countP hp hu)

end Multiset

end
