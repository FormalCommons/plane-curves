/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Derivation.Basic

/-!
# The chain rule for a derivation of a polynomial expression

For a derivation `d : A → M` over `R`, a family `x : σ → A` indexed by a finite type and a
polynomial `p` over `R` in the variables `σ`,
`d (p(x)) = ∑ᵢ (∂p/∂Xᵢ)(x) • d (xᵢ)`.

## Main results

* `Derivation.map_aeval_mvPolynomial`: the chain rule.
-/

public section

namespace Derivation

open MvPolynomial

variable {R A M σ : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M]
  [Module A M] [Module R M] [Fintype σ]

/-- **The chain rule** for a derivation: `d (p(x)) = ∑ᵢ (∂p/∂Xᵢ)(x) • d (xᵢ)` for a polynomial
`p` in finitely many variables and a point `x`. -/
theorem map_aeval_mvPolynomial (d : Derivation R A M) (x : σ → A) (p : MvPolynomial σ R) :
    d (aeval x p) = ∑ i, aeval x (pderiv i p) • d (x i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_smul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp [Derivation.leibniz, hp, add_smul, Finset.sum_add_distrib, Finset.smul_sum,
      Pi.single_apply, smul_smul, mul_comm, add_comm, apply_ite, ite_smul]

end Derivation

end
