/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Multiset

/-!
# The finitely supported function counting the images of a multiset

For a map `g : α → β` and a multiset `s` of elements of `α`, the sum
`(s.map fun a ↦ single (g a) 1).sum : β →₀ ℕ` counts, at each `b : β`, the elements of `s` that
`g` sends to `b`. This is how a multiset of points is written as a zero-cycle.

## Main results

* `Finsupp.degree_multiset_sum_map_single`: its degree is the cardinality of `s`.
* `Finsupp.exists_mem_of_multiset_sum_map_single_apply_ne_zero`: a point of its support is the
  image of an element of `s`.
* `Multiset.sum_map_single_eq_toFinsupp`: it is the multiset `s.map g`, seen as a finitely
  supported function.
-/

public section

namespace Finsupp

variable {α β : Type*}

/-- The sum of `single (g a) 1` over a multiset `s` has degree the cardinality of `s`. -/
@[simp]
theorem degree_multiset_sum_map_single (s : Multiset α) (g : α → β) :
    (s.map fun a ↦ single (g a) 1).sum.degree = Multiset.card s := by
  rw [map_multiset_sum, Multiset.map_map]
  simp [Finsupp.degree_single]

/-- A point in the support of the sum of `single (g a) 1` over a multiset `s` is the image under
`g` of an element of `s`. -/
theorem exists_mem_of_multiset_sum_map_single_apply_ne_zero {s : Multiset α} {g : α → β}
    {b : β} (h : (s.map fun a ↦ single (g a) 1).sum b ≠ 0) : ∃ a ∈ s, g a = b := by
  classical
  obtain ⟨_, hf, hb⟩ := mem_support_multiset_sum b (mem_support_iff.2 h)
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hf
  exact ⟨a, ha, (Finset.mem_singleton.1 (support_single_subset hb)).symm⟩

end Finsupp

namespace Multiset

variable {α β : Type*}

/-- The sum of `single (g a) 1` over a multiset `s` is the multiset `s.map g`, seen as a finitely
supported function. -/
theorem sum_map_single_eq_toFinsupp [DecidableEq β] (g : α → β) (s : Multiset α) :
    (s.map fun a ↦ Finsupp.single (g a) 1).sum = toFinsupp (s.map g) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [map_cons, sum_cons, ih, map_cons, ← singleton_add, toFinsupp_add, toFinsupp_singleton]

end Multiset

end
