/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import TauCeti.RingTheory.Length

/-!
# Lengths under ring isomorphisms

## Main results

* `IsLocalRing.length_quotient_maximalIdeal_pow_eq_of_ringEquiv`: isomorphic local rings have
  the same lengths `ℓ(R ⧸ 𝔪 ^ n)`.
-/

public section

open IsLocalRing

/-- Isomorphic local rings have the same Hilbert–Samuel function:
`ℓ_R(R ⧸ 𝔪_R ^ n) = ℓ_S(S ⧸ 𝔪_S ^ n)` for a ring isomorphism `R ≃+* S`. -/
theorem IsLocalRing.length_quotient_maximalIdeal_pow_eq_of_ringEquiv {R S : Type*} [CommRing R]
    [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) :
    Module.length R (R ⧸ maximalIdeal R ^ n) = Module.length S (S ⧸ maximalIdeal S ^ n) := by
  rw [← map_ringEquiv_maximalIdeal e, ← Ideal.map_pow,
    Ideal.length_quotient_map_of_surjective _ e.surjective, RingHom.ker_equiv e, sup_bot_eq]

end
