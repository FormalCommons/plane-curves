/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import PlaneCurves.RingTheory.Ideal.Span
public import TauCeti.RingTheory.Length

/-!
# Lengths under ring isomorphisms and restriction of scalars

Ring isomorphisms preserve the lengths of corresponding quotients, and so orders of vanishing.
Restricting scalars along `A → B` preserves lengths when every simple `B`-module has length one
over `A`.

## Main results

* `IsLocalRing.length_quotient_maximalIdeal_pow_eq_of_ringEquiv`: isomorphic local rings have
  the same lengths `ℓ(R ⧸ 𝔪 ^ n)`.
* `Ideal.length_quotient_span_pair_eq_of_ringEquiv`: a ring isomorphism carrying `a` and `b` to
  associates of `a'` and `b'` identifies `ℓ(R ⧸ (a, b))` with `ℓ(S ⧸ (a', b'))`.
* `Ring.ord_ringEquiv`: ring isomorphisms preserve orders of vanishing `Ring.ord`.
* `Module.length_restrictScalars_of_forall_isMaximal`: if `ℓ_A(B ⧸ 𝔪) = 1` for every maximal
  ideal `𝔪` of `B`, then `ℓ_A(M) = ℓ_B(M)` for every `B`-module `M`.
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
  rw [← Ideal.map_span_pair_eq_of_associated φ ha hb,
    Ideal.length_quotient_map_of_surjective _ φ.surjective, RingHom.ker_equiv φ, sup_bot_eq]

/-- Ring isomorphisms preserve orders of vanishing: `ord_S (φ x) = ord_R x` for `φ : R ≃+* S`. -/
theorem Ring.ord_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (φ : R ≃+* S) (x : R) :
    Ring.ord S (φ x) = Ring.ord R x := by
  rw [Ring.ord, Ring.ord, ← Set.image_singleton, ← Ideal.map_span,
    Ideal.length_quotient_map_of_surjective _ φ.surjective, RingHom.ker_equiv φ, sup_bot_eq]

/-- **Lengths under restriction of scalars.** Let `B` be an `A`-algebra such that `B ⧸ 𝔪` has
length one over `A` for every maximal ideal `𝔪` of `B`. Then every `B`-module `M` has the same
length over `A` as over `B`, since the factors of a composition series of `M` over `B` are the
`B ⧸ 𝔪`. -/
theorem Module.length_restrictScalars_of_forall_isMaximal {A B M : Type*} [CommRing A]
    [CommRing B] [Algebra A B] [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (h : ∀ m : Ideal B, m.IsMaximal → Module.length A (B ⧸ m) = 1) :
    Module.length A M = Module.length B M := by
  have hcov : ∀ {p q : Submodule B M}, p ⋖ q →
      Module.length A q = Module.length A p + 1 := by
    intro p q hpq
    let f : p →ₗ[B] q := Submodule.inclusion hpq.le
    have key : IsSimpleModule B (q ⧸ LinearMap.range f) := by
      rwa [Submodule.range_inclusion, ← covBy_iff_quot_is_simple hpq.le]
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp key
    let g : q →ₗ[B] B ⧸ m := e.toLinearMap.comp (LinearMap.range f).mkQ
    have hf : Function.Injective f := Submodule.inclusion_injective _
    have hg : Function.Surjective g := e.surjective.comp (LinearMap.range f).mkQ_surjective
    have hfg : Function.Exact f g :=
      LinearMap.exact_iff.mpr ((e.ker_comp _).trans (LinearMap.range f).ker_mkQ)
    rw [Module.length_eq_add_of_exact (f.restrictScalars A) (g.restrictScalars A)
      (by simpa) (by simpa) (by simpa), h m hm]
  by_cases hM : IsFiniteLength B M
  · obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp hM
    rw [← Module.length_compositionSeries s hs_bot hs_top]
    suffices ∀ i, Module.length A (s i) = i by
      rw [← Fin.val_last s.length, ← this, ← RelSeries.last, hs_top]
      exact Module.length_top.symm
    intro i
    induction i using Fin.induction with
    | zero => rw [← RelSeries.head, hs_bot]; simp
    | succ i hi => rw [hcov (s.step i), hi]; simp
  · have : ¬ IsFiniteLength A M := by
      contrapose hM
      rw [isFiniteLength_iff_isNoetherian_isArtinian] at hM ⊢
      exact hM.imp (isNoetherian_of_tower A) (isArtinian_of_tower A)
    rw [← Module.length_ne_top_iff, not_ne_iff] at hM this
    rw [hM, this]

end
