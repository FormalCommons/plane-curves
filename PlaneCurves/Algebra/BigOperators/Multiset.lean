/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Multiset.Filter

/-!
# Counting the elements of a multiset by classes

If every element of a multiset `u` satisfies `p b` for exactly one `b` in a finite set `s`, then
the numbers of elements satisfying each `p b` add up to the cardinality of `u`.

## Main results

* `Multiset.sum_countP_eq_card`: the counts of the classes add up to the cardinality.
-/

public section

namespace Multiset

/-- If every element of `u` satisfies `p b` for exactly one `b ∈ s`, then the numbers of elements
of `u` satisfying `p b`, for `b ∈ s`, add up to the cardinality of `u`. -/
theorem sum_countP_eq_card {α β : Type*} (s : Finset β) (p : β → α → Prop)
    [∀ b, DecidablePred (p b)] (u : Multiset α) (h : ∀ x ∈ u, ∃! b, b ∈ s ∧ p b x) :
    ∑ b ∈ s, u.countP (p b) = card u := by
  classical
  induction u using Multiset.induction_on with
  | empty => simp
  | cons a u ih =>
    simp only [Multiset.countP_cons, Finset.sum_add_distrib, Multiset.card_cons]
    rw [ih fun x hx ↦ h x (Multiset.mem_cons_of_mem hx), Finset.sum_boole, Nat.cast_id]
    congr 1
    obtain ⟨b, ⟨hb, hpb⟩, huniq⟩ := h a (Multiset.mem_cons_self a u)
    exact Finset.card_eq_one.2 ⟨b, Finset.eq_singleton_iff_unique_mem.2
      ⟨Finset.mem_filter.2 ⟨hb, hpb⟩, fun c hc ↦ huniq c (Finset.mem_filter.1 hc)⟩⟩

end Multiset

end
