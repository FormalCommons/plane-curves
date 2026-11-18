/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Radicals of principal ideals

If `y` is radical, divides `x`, and has a power divisible by `x`, then the radical of the
principal ideal `(x)` is `(y)`. In a unique factorization domain, this computes the radical of
`(λ F₁^e₁ ⋯ F_r^e_r)` as `(F₁ ⋯ F_r)` without choosing normalized factors (compare Mathlib's
`Ideal.radical_span_singleton_eq_span_radical`).

## Main results

* `Ideal.radical_span_singleton_eq_of_dvd`: `Rad (x) = (y)` for radical `y` with `y ∣ x` and
  `x ∣ y ^ m`.
-/

public section

namespace Ideal

variable {R : Type*} [CommSemiring R] {x y : R}

/-- If `y` is radical, divides `x`, and `x` divides a power of `y`, then the radical of the
principal ideal `(x)` is `(y)`. -/
theorem radical_span_singleton_eq_of_dvd (hy : _root_.IsRadical y) (hyx : y ∣ x) {m : ℕ}
    (hxy : x ∣ y ^ m) : (span {x}).radical = span {y} := by
  refine le_antisymm ?_ ?_
  · rw [(isRadical_iff_span_singleton.1 hy).radical_le_iff]
    exact span_singleton_le_span_singleton.2 hyx
  · rw [span_singleton_le_iff_mem]
    exact ⟨m, mem_span_singleton.2 hxy⟩

end Ideal

end
