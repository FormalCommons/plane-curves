/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# A separable and a purely inseparable subextension generate the field

If `K / L` is separable and `K / M` is purely inseparable, for intermediate fields `L` and `M`
of `K / F`, then `L ⊔ M = K`: an element `a` has a power `a ^ q ^ n` in `M`, and
`L(a) = L(a ^ q ^ n)` because `a` is separable over `L`.

## Main results

* `IntermediateField.sup_eq_top_of_isSeparable_of_isPurelyInseparable`: `L ⊔ M = ⊤`.
-/

public section

open scoped IntermediateField

namespace IntermediateField

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- If `K` is separable over the intermediate field `L` and purely inseparable over the
intermediate field `M`, then `L ⊔ M = ⊤`. -/
theorem sup_eq_top_of_isSeparable_of_isPurelyInseparable (L M : IntermediateField F K)
    [Algebra.IsSeparable L K] [IsPurelyInseparable M K] : L ⊔ M = ⊤ := by
  obtain ⟨q, _⟩ := ExpChar.exists F
  have : ExpChar L q := expChar_of_injective_algebraMap (algebraMap F L).injective q
  have : ExpChar M q := expChar_of_injective_algebraMap (algebraMap F M).injective q
  refine eq_top_iff.2 fun a _ ↦ ?_
  obtain ⟨n, b, hb⟩ := IsPurelyInseparable.pow_mem M q a
  have hle : L⟮a ^ q ^ n⟯ ≤ extendScalars (le_sup_left : L ≤ L ⊔ M) := by
    rw [adjoin_simple_le_iff, mem_extendScalars, ← hb]
    exact le_sup_right (a := L) b.2
  have ha : a ∈ L⟮a⟯ := mem_adjoin_simple_self L a
  rw [adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable' L K a q n] at ha
  exact hle ha

end IntermediateField

end
