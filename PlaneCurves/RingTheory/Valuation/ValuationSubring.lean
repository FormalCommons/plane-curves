/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# Valuation subrings containing a large subfield

A valuation subring `R` of a field `L` is integrally closed in `L`. Hence if `R` contains a
subfield `E` over which `L` is algebraic, then `R = L`
(`ValuationSubring.eq_top_of_forall_algebraMap_mem`): every element of `L` is integral over `E`,
hence over `R`. In particular a valuation subring that is not `L` itself does not contain such a
subfield (Fulton, Problem 1.50, in the form used in §7.1).

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.1, Corollary 1, and Problem 1.50
-/

public section

namespace ValuationSubring

variable {E L : Type*} [Field E] [Field L] [Algebra E L]

/-- A valuation subring `R` of `L` containing (the image of) a field `E` over which `L` is
algebraic is all of `L`. -/
theorem eq_top_of_forall_algebraMap_mem [Algebra.IsAlgebraic E L] {R : ValuationSubring L}
    (h : ∀ a : E, algebraMap E L a ∈ R) : R = ⊤ := by
  let : Algebra E R := ((algebraMap E L).codRestrict R.toSubring h).toAlgebra
  have : IsScalarTower E R L := .of_algebraMap_eq fun _ ↦ rfl
  refine top_unique fun x _ ↦ ?_
  have hx : IsIntegral R x := (Algebra.IsIntegral.isIntegral (R := E) x).tower_top
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx
  exact y.2

/-- A valuation subring of `L` other than `L` does not contain (the image of) a field `E` over
which `L` is algebraic. -/
theorem exists_algebraMap_notMem_of_ne_top [Algebra.IsAlgebraic E L] {R : ValuationSubring L}
    (hR : R ≠ ⊤) : ∃ a : E, algebraMap E L a ∉ R := by
  by_contra! h
  exact hR (eq_top_of_forall_algebraMap_mem h)

end ValuationSubring

end
