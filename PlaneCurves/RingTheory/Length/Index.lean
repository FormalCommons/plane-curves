/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.RingTheory.Length

/-!
# The index lemma for lengths

Let `T : M → M` be an injective linear endomorphism of a module and `N ≤ M` a submodule with
`T(N) ⊆ N` and `M ⧸ N` of finite length. Then `M ⧸ T(M)` and `N ⧸ T(N)` have the same length:
both lengths are what remains of `ℓ(M ⧸ T(N))` after removing `ℓ(M ⧸ N) = ℓ(T(M) ⧸ T(N))`.
This is the "index" step in Fulton's proof that the intersection number of two curves is a sum
of orders at places.

## Main results

* `LinearMap.length_quotient_range_eq_length_quotient_map`: `ℓ(M ⧸ T(M)) = ℓ(N ⧸ T(N))`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.5, Proposition 2
-/

public section

namespace LinearMap

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- **The index lemma.** For an injective linear endomorphism `T` of `M` and a submodule `N` with
`T(N) ⊆ N` and `M ⧸ N` of finite length, the quotients `M ⧸ T(M)` and `N ⧸ T(N)` have the same
length. Here `N ⧸ T(N)` is the quotient of `N` by the preimage of `T(N)` under the inclusion of
`N` in `M`. -/
theorem length_quotient_range_eq_length_quotient_map {T : M →ₗ[R] M}
    (hT : Function.Injective T) {N : Submodule R M} (hTN : N.map T ≤ N)
    (hN : IsFiniteLength R (M ⧸ N)) :
    Module.length R (M ⧸ range T) =
      Module.length R (↥N ⧸ (N.map T).comap N.subtype) := by
  have h₁ := TauCeti.length_quotient_eq_length_quotient_comap_subtype_add hTN
  rw [TauCeti.length_quotient_eq_length_quotient_comap_subtype_add (map_le_range (p := N)),
    TauCeti.length_quotient_comap_subtype_range_map hT, add_comm] at h₁
  exact (WithTop.add_right_inj (Module.length_ne_top_iff.mpr hN)).mp h₁

end LinearMap

end
