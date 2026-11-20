/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Cast

/-!
# `2 * m.choose 2 = m (m - 1)` in a ring

Mathlib's `Nat.choose_two_right` gives `m.choose 2 = m * (m - 1) / 2` in `ℕ`, and
`Nat.cast_choose_two` the same formula in a division ring. This file gives the form without
division, `2 * (m.choose 2 : R) = m * (m - 1)`, which holds in every ring.

## Main results

* `Nat.two_mul_cast_choose_two`: `2 * (m.choose 2 : R) = m * (m - 1)` in a ring `R`.
-/

public section

namespace Nat

/-- Twice the binomial coefficient `m.choose 2` is `m (m - 1)` in any ring, the subtraction being
that of the ring. -/
theorem two_mul_cast_choose_two {R : Type*} [Ring R] (m : ℕ) :
    2 * (m.choose 2 : R) = m * (m - 1) := by
  rw [← cast_descFactorial_two, descFactorial_eq_factorial_mul_choose, factorial_two, cast_mul,
    cast_two]

end Nat

end
