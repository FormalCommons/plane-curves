/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import TauCeti.RingTheory.Length

/-!
# Lengths under ring isomorphisms

Ring isomorphisms preserve the lengths of corresponding quotients, and so orders of vanishing.

## Main results

* `IsLocalRing.length_quotient_maximalIdeal_pow_eq_of_ringEquiv`: isomorphic local rings have
  the same lengths `ℓ(R ⧸ 𝔪 ^ n)`.
* `Ideal.length_quotient_span_pair_eq_of_ringEquiv`: a ring isomorphism carrying `a` and `b` to
  associates of `a'` and `b'` identifies `ℓ(R ⧸ (a, b))` with `ℓ(S ⧸ (a', b'))`.
* `Ring.ord_ringEquiv`: ring isomorphisms preserve orders of vanishing `Ring.ord`.
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

/-- An isomorphism of rings carrying `a` and `b` to associates of `a'` and `b'` identifies the
lengths of `R ⧸ (a, b)` and `S ⧸ (a', b')`. -/
theorem Ideal.length_quotient_span_pair_eq_of_ringEquiv {R S : Type*} [CommRing R]
    [CommRing S] (φ : R ≃+* S) {a b : R} {a' b' : S} (ha : Associated (φ a) a')
    (hb : Associated (φ b) b') :
    Module.length S (S ⧸ Ideal.span {a', b'}) = Module.length R (R ⧸ Ideal.span {a, b}) := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  rw [Ideal.span_insert, Ideal.span_singleton_mul_right_unit u.isUnit,
    Ideal.span_singleton_mul_right_unit v.isUnit, ← Ideal.span_insert, ← Set.image_pair,
    ← Ideal.map_span, Ideal.length_quotient_map_of_surjective _ φ.surjective,
    RingHom.ker_equiv φ, sup_bot_eq]

/-- Ring isomorphisms preserve orders of vanishing: `ord_S (φ x) = ord_R x` for `φ : R ≃+* S`. -/
theorem Ring.ord_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (φ : R ≃+* S) (x : R) :
    Ring.ord S (φ x) = Ring.ord R x := by
  rw [Ring.ord, Ring.ord, ← Set.image_singleton, ← Ideal.map_span,
    Ideal.length_quotient_map_of_surjective _ φ.surjective, RingHom.ker_equiv φ, sup_bot_eq]

end
