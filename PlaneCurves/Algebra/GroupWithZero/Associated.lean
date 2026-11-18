/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Set.Pairwise.Basic

/-!
# Representatives of the association classes of a multiset

Every multiset `u` in a monoid has a finite set of representatives of the association classes of
its elements: elements of `u`, pairwise not associated, such that every element of `u` is
associated to one of them.

## Main results

* `Multiset.exists_finset_pairwise_not_associated`: a multiset has a finite set of pairwise
  non-associated representatives of its elements up to association.
-/

public section

namespace Multiset

/-- A multiset `u` has a finite set of elements of `u`, pairwise not associated, such that every
element of `u` is associated to one of them. -/
theorem exists_finset_pairwise_not_associated {α : Type*} [Monoid α] (u : Multiset α) :
    ∃ s : Finset α, (∀ x ∈ s, x ∈ u) ∧ (s : Set α).Pairwise (fun x y ↦ ¬Associated x y) ∧
      ∀ x ∈ u, ∃ y ∈ s, Associated x y := by
  classical
  induction u using Multiset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | cons a u ih =>
    obtain ⟨s, hsu, hs, hcov⟩ := ih
    by_cases ha : ∃ y ∈ s, Associated a y
    · refine ⟨s, fun x hx ↦ Multiset.mem_cons_of_mem (hsu x hx), hs, fun x hx ↦ ?_⟩
      rcases Multiset.mem_cons.1 hx with rfl | hx
      · exact ha
      · exact hcov x hx
    · push Not at ha
      refine ⟨insert a s, fun x hx ↦ ?_, ?_, fun x hx ↦ ?_⟩
      · rcases Finset.mem_insert.1 hx with rfl | hx
        · exact Multiset.mem_cons_self _ _
        · exact Multiset.mem_cons_of_mem (hsu x hx)
      · rw [Finset.coe_insert]
        exact hs.insert fun y hy _ ↦ ⟨ha y hy, fun h ↦ ha y hy h.symm⟩
      · rcases Multiset.mem_cons.1 hx with rfl | hx
        · exact ⟨x, Finset.mem_insert_self _ _, Associated.refl _⟩
        · obtain ⟨y, hy, hxy⟩ := hcov x hx
          exact ⟨y, Finset.mem_insert_of_mem hy, hxy⟩

end Multiset

end
