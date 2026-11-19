/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Squarefree.Basic

/-!
# Squarefree elements under multiplicative equivalences

A multiplicative equivalence preserves and reflects being squarefree.

## Main results

* `MulEquiv.squarefree_iff`: `Squarefree (f x) ↔ Squarefree x` for a multiplicative
  equivalence `f`.
* `Squarefree.map`: the image of a squarefree element under a multiplicative equivalence is
  squarefree.
-/

public section

section MulEquivClass

variable {F M N : Type*} [Monoid M] [Monoid N] [EquivLike F M N] [MulEquivClass F M N]
  (f : F) {x : M}

/-- A multiplicative equivalence preserves and reflects being squarefree. -/
theorem MulEquiv.squarefree_iff : Squarefree (f x) ↔ Squarefree x := by
  simp [Squarefree, (EquivLike.surjective f).forall, ← map_mul, map_dvd_iff]

/-- The image of a squarefree element under a multiplicative equivalence is squarefree. -/
alias ⟨_, Squarefree.map⟩ := MulEquiv.squarefree_iff

end MulEquivClass


end
