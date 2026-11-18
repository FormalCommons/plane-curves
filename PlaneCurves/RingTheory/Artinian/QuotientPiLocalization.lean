/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import PlaneCurves.RingTheory.Localization.Quotient

/-!
# An Artinian quotient is the product of its localizations

Let `A` be a commutative ring and `I` an ideal of `A` with `A ⧸ I` Artinian. Then `A ⧸ I` is the
product, over the finitely many maximal ideals `𝔪 ⊇ I`, of the rings `A_𝔪 ⧸ I A_𝔪`, by the map
whose components are induced by `A → A_𝔪`.

The maximal ideals may be indexed by any type `ι`: the result is stated for a family
`p : ι → Ideal A` of primes containing `I` that lists every maximal ideal containing `I` exactly
once, so that, for instance, the points of a finite zero set can index the factors.

## Main definitions

* `Ideal.quotientToPiLocalization I p`: the map `A ⧸ I → ∏ i, A_{p i} ⧸ I A_{p i}`.
* `Ideal.quotientPiLocalizationAlgEquiv`: it is an isomorphism when `A ⧸ I` is Artinian and `p`
  lists the maximal ideals containing `I`.
* `Ideal.quotientPiLocalizationMaximalAlgEquiv`: the same, indexed by the maximal ideals of `A`
  that contain `I`.

## Main results

* `Ideal.bijective_quotientToPiLocalization`: the map `A ⧸ I → ∏ i, A_{p i} ⧸ I A_{p i}` is
  bijective.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §2.9, Proposition 6
-/

public section

open Ideal

namespace Ideal

variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A)
  {ι : Type*} (p : ι → Ideal A) [∀ i, (p i).IsPrime]

/-- The map `A ⧸ I → ∏ i, A_{p i} ⧸ I A_{p i}`, whose components are induced by the
localization maps `A → A_{p i}`. -/
noncomputable def quotientToPiLocalization :
    A ⧸ I →ₐ[R] ∀ i,
      Localization.AtPrime (p i) ⧸ I.map (algebraMap A (Localization.AtPrime (p i))) :=
  AlgHom.pi fun i =>
    quotientMapₐ _ (IsScalarTower.toAlgHom R A (Localization.AtPrime (p i))) le_comap_map

theorem quotientToPiLocalization_def : quotientToPiLocalization R I p =
    AlgHom.pi fun i =>
      quotientMapₐ _ (IsScalarTower.toAlgHom R A (Localization.AtPrime (p i))) le_comap_map :=
  (rfl)

variable {R I p}

@[simp]
theorem quotientToPiLocalization_mk (a : A) (i : ι) :
    quotientToPiLocalization R I p (Ideal.Quotient.mk I a) i =
      Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime (p i)) a) := by
  rw [quotientToPiLocalization_def]
  rfl

theorem quotientToPiLocalization_apply (x : A ⧸ I) (i : ι) :
    quotientToPiLocalization R I p x i = algebraMap (A ⧸ I) _ x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quotientToPiLocalization_mk]
  rfl

/-- **An Artinian quotient is the product of its localizations.** Let `A ⧸ I` be Artinian and
let `p : ι → Ideal A` be an injective family of prime ideals containing `I` such that every maximal
ideal containing `I` is some `p i`. Then the map `A ⧸ I → ∏ i, A_{p i} ⧸ I A_{p i}` induced by the
localization maps is bijective. -/
theorem bijective_quotientToPiLocalization [IsArtinianRing (A ⧸ I)] (hp : ∀ i, I ≤ p i)
    (hinj : Function.Injective p) (hsurj : ∀ q : Ideal A, q.IsMaximal → I ≤ q → ∃ i, p i = q) :
    Function.Bijective (quotientToPiLocalization R I p) := by
  have hker : ∀ i, RingHom.ker (Ideal.Quotient.mk I) ≤ p i := fun i => by
    rw [mk_ker]; exact hp i
  have hprime : ∀ i, ((p i).map (Ideal.Quotient.mk I)).IsPrime := fun i =>
    map_isPrime_of_surjective Quotient.mk_surjective (hker i)
  let e : ι → PrimeSpectrum (A ⧸ I) := fun i => ⟨(p i).map (Ideal.Quotient.mk I), hprime i⟩
  have he : Function.Bijective e := by
    refine ⟨fun i j hij => hinj ?_, fun q => ?_⟩
    · have := congrArg (fun q : PrimeSpectrum (A ⧸ I) => q.asIdeal.comap (Ideal.Quotient.mk I)) hij
      simpa only [e, comap_map_of_surjective' _ Quotient.mk_surjective, sup_eq_left.2 (hker _)]
        using this
    · have hmax : (q.asIdeal.comap (Ideal.Quotient.mk I)).IsMaximal :=
        comap_isMaximal_of_surjective _ Quotient.mk_surjective
      obtain ⟨i, hi⟩ := hsurj _ hmax (by simpa using ker_le_comap (Ideal.Quotient.mk I))
      refine ⟨i, PrimeSpectrum.ext ?_⟩
      simp only [e, hi, map_comap_of_surjective _ Quotient.mk_surjective]
  let F : PrimeSpectrum (A ⧸ I) → Type _ := fun q => Localization.AtPrime q.asIdeal
  let E := Equiv.piCongrLeft F (Equiv.ofBijective e he)
  let G : (∀ i, F (e i)) ≃ ∀ i,
      Localization.AtPrime (p i) ⧸ I.map (algebraMap A (Localization.AtPrime (p i))) :=
    Equiv.piCongrRight fun i =>
      (Localization.AtPrime.quotientAlgEquiv (I := I) R (hp i)).toEquiv
  have h : ⇑(quotientToPiLocalization R I p) =
      G ∘ E.symm ∘ PrimeSpectrum.toPiLocalization (A ⧸ I) := by
    funext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    funext i
    simp only [Function.comp_apply, G, E, Equiv.piCongrRight_apply, AlgEquiv.toEquiv_eq_coe,
      AlgEquiv.coe_toEquiv, quotientToPiLocalization_mk]
    exact (Localization.AtPrime.quotientAlgEquiv_algebraMap_mk (hp i) a).symm
  rw [h]
  exact G.bijective.comp (E.symm.bijective.comp PrimeSpectrum.toPiLocalization_bijective)

variable (R) in
/-- **An Artinian quotient is the product of its localizations.** For `A ⧸ I` Artinian and an
injective family `p` of primes containing `I` that contains every maximal ideal containing `I`,
`A ⧸ I ≃ ∏ i, A_{p i} ⧸ I A_{p i}` by the map induced by the localization maps. -/
noncomputable def quotientPiLocalizationAlgEquiv [IsArtinianRing (A ⧸ I)] (hp : ∀ i, I ≤ p i)
    (hinj : Function.Injective p) (hsurj : ∀ q : Ideal A, q.IsMaximal → I ≤ q → ∃ i, p i = q) :
    (A ⧸ I) ≃ₐ[R] (∀ i,
      Localization.AtPrime (p i) ⧸ I.map (algebraMap A (Localization.AtPrime (p i)))) :=
  .ofBijective _ (bijective_quotientToPiLocalization hp hinj hsurj)

theorem quotientPiLocalizationAlgEquiv_def [IsArtinianRing (A ⧸ I)] (hp : ∀ i, I ≤ p i)
    (hinj : Function.Injective p) (hsurj : ∀ q : Ideal A, q.IsMaximal → I ≤ q → ∃ i, p i = q) :
    quotientPiLocalizationAlgEquiv R hp hinj hsurj =
      .ofBijective _ (bijective_quotientToPiLocalization hp hinj hsurj) :=
  (rfl)

@[simp]
theorem coe_quotientPiLocalizationAlgEquiv [IsArtinianRing (A ⧸ I)] (hp : ∀ i, I ≤ p i)
    (hinj : Function.Injective p) (hsurj : ∀ q : Ideal A, q.IsMaximal → I ≤ q → ∃ i, p i = q) :
    ⇑(quotientPiLocalizationAlgEquiv R hp hinj hsurj) = quotientToPiLocalization R I p :=
  (rfl)

theorem quotientPiLocalizationAlgEquiv_mk [IsArtinianRing (A ⧸ I)] (hp : ∀ i, I ≤ p i)
    (hinj : Function.Injective p) (hsurj : ∀ q : Ideal A, q.IsMaximal → I ≤ q → ∃ i, p i = q)
    (a : A) (i : ι) :
    quotientPiLocalizationAlgEquiv R hp hinj hsurj (Ideal.Quotient.mk I a) i =
      Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime (p i)) a) := by
  simp

variable (R I) in
/-- **An Artinian quotient is the product of its localizations**, indexed by the maximal ideals:
for `A ⧸ I` Artinian, `A ⧸ I ≃ ∏_{𝔪 ⊇ I} A_𝔪 ⧸ I A_𝔪`, the product being over the maximal ideals
of `A` that contain `I`. -/
noncomputable def quotientPiLocalizationMaximalAlgEquiv [IsArtinianRing (A ⧸ I)] :
    (A ⧸ I) ≃ₐ[R] (∀ m : {m : MaximalSpectrum A // I ≤ m.asIdeal},
      Localization.AtPrime m.1.asIdeal ⧸
        I.map (algebraMap A (Localization.AtPrime m.1.asIdeal))) :=
  quotientPiLocalizationAlgEquiv R (I := I)
    (p := fun m : {m : MaximalSpectrum A // I ≤ m.asIdeal} => m.1.asIdeal) (fun m => m.2)
    (fun _ _ h => Subtype.ext (MaximalSpectrum.ext h)) fun q hq hIq => ⟨⟨⟨q, hq⟩, hIq⟩, rfl⟩

theorem quotientPiLocalizationMaximalAlgEquiv_def [IsArtinianRing (A ⧸ I)] :
    quotientPiLocalizationMaximalAlgEquiv R I =
      quotientPiLocalizationAlgEquiv R (I := I)
        (p := fun m : {m : MaximalSpectrum A // I ≤ m.asIdeal} => m.1.asIdeal) (fun m => m.2)
        (fun _ _ h => Subtype.ext (MaximalSpectrum.ext h)) fun q hq hIq => ⟨⟨⟨q, hq⟩, hIq⟩, rfl⟩ :=
  (rfl)

@[simp]
theorem quotientPiLocalizationMaximalAlgEquiv_mk [IsArtinianRing (A ⧸ I)] (a : A)
    (m : {m : MaximalSpectrum A // I ≤ m.asIdeal}) :
    quotientPiLocalizationMaximalAlgEquiv R I (Ideal.Quotient.mk I a) m =
      Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime m.1.asIdeal) a) := by
  rw [quotientPiLocalizationMaximalAlgEquiv_def]
  exact quotientPiLocalizationAlgEquiv_mk _ _ _ a m

end Ideal

end
