/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import PlaneCurves.AlgebraicGeometry.AffineSpace.FiniteZeroLocus
public import PlaneCurves.AlgebraicGeometry.AffineSpace.LocalRing
public import PlaneCurves.RingTheory.Artinian.QuotientPiLocalization

/-!
# Ideals with finitely many zeros

Let `k` be an algebraically closed field and `I` an ideal of `k[X] = MvPolynomial σ k`, in
finitely many variables, whose zero locus `V(I) = {P₁, …, P_N}` is finite. Write
`𝒪_P = 𝒪_P(𝔸ⁿ)` for the local ring of affine space at `P`. The maps `k[X] → 𝒪_P` induce an
isomorphism of `k`-algebras `k[X] ⧸ I ≅ ∏_{P ∈ V(I)} 𝒪_P ⧸ I 𝒪_P`. Consequently
`dim_k k[X] ⧸ I = ∑_{P ∈ V(I)} dim_k 𝒪_P ⧸ I 𝒪_P`, and if `V(I) = {P}` then
`k[X] ⧸ I ≅ 𝒪_P ⧸ I 𝒪_P`.

Over any field, the same holds with the points replaced by the maximal ideals containing `I`
whenever `k[X] ⧸ I` is finite-dimensional: that is `Ideal.quotientPiLocalizationMaximalAlgEquiv`.

## Main definitions

* `PlaneCurves.AffineSpace.quotientPiLocalRingAlgEquiv`:
  `k[X] ⧸ I ≃ₐ[k] ∏_{P ∈ V(I)} 𝒪_P ⧸ I 𝒪_P`.
* `PlaneCurves.AffineSpace.quotientLocalRingAlgEquiv`: `k[X] ⧸ I ≃ₐ[k] 𝒪_P ⧸ I 𝒪_P` when
  `V(I) = {P}`.

## Main results

* `PlaneCurves.AffineSpace.bijective_quotientToPiLocalization_zeroLocus`: the map
  `k[X] ⧸ I → ∏_{P ∈ V(I)} 𝒪_P ⧸ I 𝒪_P` is bijective.
* `PlaneCurves.AffineSpace.finrank_quotient_eq_sum`:
  `dim_k k[X] ⧸ I = ∑_{P ∈ V(I)} dim_k 𝒪_P ⧸ I 𝒪_P`.
* `PlaneCurves.AffineSpace.bijective_quotientMap_localRing`: if `V(I) = {P}`, the map
  `k[X] ⧸ I → 𝒪_P ⧸ I 𝒪_P` is bijective.
* `PlaneCurves.AffineSpace.quotient_decomposition`: the three statements together.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §2.9, Proposition 6 and Corollaries 1 and 2
-/

public section

open MvPolynomial Ideal

namespace PlaneCurves.AffineSpace

variable {k σ : Type*} [Field k] [IsAlgClosed k] [Finite σ] (I : Ideal (MvPolynomial σ k))

/-- The map `k[X] ⧸ I → ∏_{P ∈ V(I)} 𝒪_P ⧸ I 𝒪_P` induced by the maps `k[X] → 𝒪_P` is
bijective, for `V(I)` finite, over an algebraically closed field and in finitely many
variables. -/
theorem bijective_quotientToPiLocalization_zeroLocus (hI : (zeroLocus k I).Finite) :
    Function.Bijective
      (quotientToPiLocalization k I fun P : zeroLocus k I => vanishingIdeal k {P.1}) := by
  have : Module.Finite k (MvPolynomial σ k ⧸ I) := (finite_zeroLocus_iff I).1 hI
  have : IsArtinianRing (MvPolynomial σ k ⧸ I) := IsArtinianRing.of_finite k _
  refine Ideal.bijective_quotientToPiLocalization
    (fun P => le_zeroLocus_iff_le_vanishingIdeal.1 (Set.singleton_subset_iff.2 P.2))
    (fun P Q h => Subtype.ext (vanishingIdeal_singleton_injective h)) fun q hq hIq => ?_
  obtain ⟨P, rfl⟩ := isMaximal_iff_eq_vanishingIdeal_singleton.1 hq
  exact ⟨⟨P, Set.singleton_subset_iff.1 (le_zeroLocus_iff_le_vanishingIdeal.2 hIq)⟩, rfl⟩

/-- **Ideals with finitely many zeros.** For `V(I)` finite, over an algebraically closed field
and in finitely many variables, `k[X] ⧸ I ≃ₐ[k] ∏_{P ∈ V(I)} 𝒪_P ⧸ I 𝒪_P`, by the map induced
by the maps `k[X] → 𝒪_P`. -/
noncomputable def quotientPiLocalRingAlgEquiv (hI : (zeroLocus k I).Finite) :
    (MvPolynomial σ k ⧸ I) ≃ₐ[k]
      ∀ P : zeroLocus k I, localRing k P.1 ⧸ I.map (algebraMap _ (localRing k P.1)) :=
  .ofBijective _ (bijective_quotientToPiLocalization_zeroLocus I hI)

theorem quotientPiLocalRingAlgEquiv_def (hI : (zeroLocus k I).Finite) :
    quotientPiLocalRingAlgEquiv I hI =
      .ofBijective _ (bijective_quotientToPiLocalization_zeroLocus I hI) :=
  (rfl)

@[simp]
theorem quotientPiLocalRingAlgEquiv_mk (hI : (zeroLocus k I).Finite) (f : MvPolynomial σ k)
    (P : zeroLocus k I) :
    quotientPiLocalRingAlgEquiv I hI (Ideal.Quotient.mk I f) P =
      Ideal.Quotient.mk _ (algebraMap _ (localRing k P.1) f) := by
  rw [quotientPiLocalRingAlgEquiv_def, AlgEquiv.ofBijective_apply]
  exact quotientToPiLocalization_mk f P

/-- **Ideals with finitely many zeros, dimension.** For `V(I)` finite, over an algebraically
closed field and in finitely many variables,
`dim_k k[X] ⧸ I = ∑_{P ∈ V(I)} dim_k 𝒪_P ⧸ I 𝒪_P`. -/
theorem finrank_quotient_eq_sum (hI : (zeroLocus k I).Finite) :
    Module.finrank k (MvPolynomial σ k ⧸ I) =
      ∑ P ∈ hI.toFinset,
        Module.finrank k (localRing k P ⧸ I.map (algebraMap _ (localRing k P))) := by
  have : Fintype (zeroLocus k I) := hI.fintype
  have : Module.Finite k (MvPolynomial σ k ⧸ I) := (finite_zeroLocus_iff I).1 hI
  let e := (quotientPiLocalRingAlgEquiv I hI).toLinearEquiv
  have : Module.Finite k
      (∀ P : zeroLocus k I, localRing k P.1 ⧸ I.map (algebraMap _ (localRing k P.1))) :=
    Module.Finite.equiv e
  have : ∀ P : zeroLocus k I,
      Module.Finite k (localRing k P.1 ⧸ I.map (algebraMap _ (localRing k P.1))) := fun P =>
    Module.Finite.of_surjective (LinearMap.proj (R := k) (φ := fun Q : zeroLocus k I =>
      localRing k Q.1 ⧸ I.map (algebraMap _ (localRing k Q.1))) P) (Function.surjective_eval P)
  have : ∀ P : zeroLocus k I,
      Module.Free k (localRing k P.1 ⧸ I.map (algebraMap _ (localRing k P.1))) := fun _ =>
    Module.Free.of_divisionRing k _
  rw [e.finrank_eq]
  refine (Module.finrank_pi_fintype k (M := fun P : zeroLocus k I =>
    localRing k P.1 ⧸ I.map (algebraMap _ (localRing k P.1)))).trans ?_
  exact (Finset.sum_subtype hI.toFinset (by simp)
    fun P => Module.finrank k (localRing k P ⧸ I.map (algebraMap _ (localRing k P)))).symm

variable {I} in
/-- **Ideals with one zero.** If `V(I) = {P}`, over an algebraically closed field and in finitely
many variables, the map `k[X] ⧸ I → 𝒪_P ⧸ I 𝒪_P` induced by `k[X] → 𝒪_P` is bijective. -/
theorem bijective_quotientMap_localRing {P : σ → k} (hI : zeroLocus k I = {P}) :
    Function.Bijective (quotientMapₐ (I.map (algebraMap _ (localRing k P)))
      (IsScalarTower.toAlgHom k (MvPolynomial σ k) (localRing k P)) le_comap_map) := by
  have hfin : (zeroLocus k I).Finite := hI ▸ Set.finite_singleton P
  have hP : P ∈ zeroLocus k I := hI ▸ Set.mem_singleton P
  have hsub : ∀ Q : zeroLocus k I, Q = ⟨P, hP⟩ := fun Q =>
    Subtype.ext ((Set.ext_iff.1 hI Q.1).1 Q.2)
  let ev := Function.eval (β := fun Q : zeroLocus k I =>
    localRing k Q.1 ⧸ I.map (algebraMap _ (localRing k Q.1))) ⟨P, hP⟩
  have hev : Function.Bijective ev := by
    refine ⟨fun f g h => funext fun Q => ?_, Function.surjective_eval _⟩
    obtain rfl := hsub Q
    exact h
  have key : ⇑(quotientMapₐ (I.map (algebraMap _ (localRing k P)))
      (IsScalarTower.toAlgHom k (MvPolynomial σ k) (localRing k P)) le_comap_map) =
      ev ∘ quotientToPiLocalization k I fun P : zeroLocus k I => vanishingIdeal k {P.1} := by
    funext f
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
    simp only [Function.comp_apply, ev, Function.eval, quotientToPiLocalization_mk]
    rfl
  rw [key]
  exact hev.comp (bijective_quotientToPiLocalization_zeroLocus I hfin)

variable {I} in
/-- **Ideals with one zero.** If `V(I) = {P}`, over an algebraically closed field and in finitely
many variables, `k[X] ⧸ I ≃ₐ[k] 𝒪_P ⧸ I 𝒪_P`, by the map induced by `k[X] → 𝒪_P`. -/
noncomputable def quotientLocalRingAlgEquiv {P : σ → k} (hI : zeroLocus k I = {P}) :
    (MvPolynomial σ k ⧸ I) ≃ₐ[k] localRing k P ⧸ I.map (algebraMap _ (localRing k P)) :=
  .ofBijective _ (bijective_quotientMap_localRing hI)

theorem quotientLocalRingAlgEquiv_def {P : σ → k} (hI : zeroLocus k I = {P}) :
    quotientLocalRingAlgEquiv hI = .ofBijective _ (bijective_quotientMap_localRing hI) :=
  (rfl)

@[simp]
theorem quotientLocalRingAlgEquiv_mk {P : σ → k} (hI : zeroLocus k I = {P})
    (f : MvPolynomial σ k) :
    quotientLocalRingAlgEquiv hI (Ideal.Quotient.mk I f) =
      Ideal.Quotient.mk _ (algebraMap _ (localRing k P) f) := by
  rw [quotientLocalRingAlgEquiv_def, AlgEquiv.ofBijective_apply]
  rfl

/-- **Global-to-local decomposition.** Let `k` be algebraically closed and `I` an ideal of
`k[X] = MvPolynomial σ k`, in finitely many variables, with `V(I)` finite. Write `𝒪_P` for the
local ring of affine space at `P`. Then the maps `k[X] → 𝒪_P` induce an isomorphism
`k[X] ⧸ I ≅ ∏_{P ∈ V(I)} 𝒪_P ⧸ I 𝒪_P`; hence
`dim_k k[X] ⧸ I = ∑_{P ∈ V(I)} dim_k 𝒪_P ⧸ I 𝒪_P`, and if `V(I) = {P}` then the map
`k[X] ⧸ I → 𝒪_P ⧸ I 𝒪_P` is an isomorphism.

Milestone: *Global-to-local decomposition of a polynomial ring modulo an ideal with finitely
many zeros*. -/
theorem quotient_decomposition (hI : (zeroLocus k I).Finite) :
    Function.Bijective
        (quotientToPiLocalization k I fun P : zeroLocus k I => vanishingIdeal k {P.1}) ∧
      Module.finrank k (MvPolynomial σ k ⧸ I) =
        ∑ P ∈ hI.toFinset,
          Module.finrank k (localRing k P ⧸ I.map (algebraMap _ (localRing k P))) ∧
      ∀ P : σ → k, zeroLocus k I = {P} →
        Function.Bijective (quotientMapₐ (I.map (algebraMap _ (localRing k P)))
          (IsScalarTower.toAlgHom k (MvPolynomial σ k) (localRing k P)) le_comap_map) :=
  ⟨bijective_quotientToPiLocalization_zeroLocus I hI, finrank_quotient_eq_sum I hI,
    fun _ h => bijective_quotientMap_localRing h⟩

end PlaneCurves.AffineSpace

end
