/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Lengths under ring isomorphisms and over a residue field

## Main results

* `Module.length_eq_of_bijective`: a bijective semilinear map along a surjective ring
  homomorphism preserves lengths.
* `Ideal.length_quotient_eq_of_map_eq`: a ring isomorphism `e : R ≃+* S` with `I.map e = J`
  gives `ℓ_R(R ⧸ I) = ℓ_S(S ⧸ J)`.
* `IsLocalRing.length_eq_length_of_bijective`: for a local `k`-algebra `A` whose residue field
  is `k`, the length of an `A`-module over `A` is its length over `k`.
* `IsLocalRing.length_quotient_maximalIdeal_pow_eq_of_ringEquiv`: isomorphic local rings have
  the same lengths `ℓ(R ⧸ 𝔪 ^ n)`.
-/

public section

open Module IsLocalRing

/-- A bijective semilinear map, along a surjective ring homomorphism, preserves lengths. -/
theorem Module.length_eq_of_bijective {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module S N] {τ : R →+* S} [RingHomSurjective τ]
    (f : M →ₛₗ[τ] N) (hf : Function.Bijective f) :
    Module.length R M = Module.length S N := by
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

/-- A ring isomorphism `e : R ≃+* S` carrying an ideal `I` to `J` gives `ℓ_R(R ⧸ I) = ℓ_S(S ⧸ J)`.
-/
theorem Ideal.length_quotient_eq_of_map_eq {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    {I : Ideal R} {J : Ideal S} (h : J = I.map e) :
    Module.length R (R ⧸ I) = Module.length S (S ⧸ J) := by
  have : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  let f : (R ⧸ I) →ₛₗ[(e : R →+* S)] S ⧸ J :=
    { toFun := Ideal.quotientEquiv I J e h
      map_add' := map_add _
      map_smul' := fun r x ↦ by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }
  exact Module.length_eq_of_bijective f (Ideal.quotientEquiv I J e h).bijective

/-- For a local `k`-algebra `A` whose residue field is `k` (the map `k → κ(A)` is bijective),
the length over `A` of an `A`-module is its length over `k`. -/
theorem IsLocalRing.length_eq_length_of_bijective (k : Type*) {A M : Type*} [Field k]
    [CommRing A] [IsLocalRing A] [Algebra k A] [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] (h : Function.Bijective (algebraMap k (ResidueField A))) :
    Module.length A M = Module.length k M := by
  rw [IsLocalRing.length_restrictScalars k A M]
  have h1 : Module.length (ResidueField k) (ResidueField A) = 1 := by
    rw [← Module.length_eq_of_surjective (S := k) residue_surjective,
      ← (LinearEquiv.ofBijective (Algebra.linearMap k (ResidueField A)) h).length_eq,
      Module.length_eq_finrank, Module.finrank_self, Nat.cast_one]
  rw [h1, mul_one]

/-- Isomorphic local rings have the same Hilbert–Samuel function:
`ℓ_R(R ⧸ 𝔪_R ^ n) = ℓ_S(S ⧸ 𝔪_S ^ n)` for a ring isomorphism `R ≃+* S`. -/
theorem IsLocalRing.length_quotient_maximalIdeal_pow_eq_of_ringEquiv {R S : Type*} [CommRing R]
    [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (n : ℕ) :
    Module.length R (R ⧸ maximalIdeal R ^ n) = Module.length S (S ⧸ maximalIdeal S ^ n) :=
  Ideal.length_quotient_eq_of_map_eq e (by rw [Ideal.map_pow, map_ringEquiv_maximalIdeal])
