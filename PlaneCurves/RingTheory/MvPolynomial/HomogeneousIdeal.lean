/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Noetherian.Basic
public import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient
public import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# Homogeneous ideals of polynomial rings: finite generation by forms

This file proves that a homogeneous ideal of a Noetherian graded ring is spanned by finitely many
homogeneous elements, and specializes this to polynomial rings in finitely many variables over a
Noetherian ring, graded by total degree: a homogeneous ideal of `MvPolynomial σ R` is generated
by finitely many forms (Fulton, Proposition 1 of §4.2).

## Main results

* `Ideal.IsHomogeneous.exists_finset_span_eq`: a homogeneous ideal of a Noetherian graded ring
  is spanned by a finite set of homogeneous elements.
* `Ideal.IsHomogeneous.span_setOf_isHomogeneous`: a homogeneous ideal of a polynomial ring is
  spanned by the forms it contains.
* `MvPolynomial.exists_finset_isHomogeneous_span_eq`: a homogeneous ideal of `MvPolynomial σ R`,
  for `σ` finite and `R` Noetherian, is spanned by finitely many forms.
* `MvPolynomial.pow_idealOfVars_le_iff`: an ideal contains the `N`-th power of the ideal of the
  variables exactly when it contains every form of degree at least `N`.

## Related results elsewhere

* That an ideal is homogeneous if and only if it is spanned by homogeneous elements is Mathlib's
  `Ideal.IsHomogeneous.iff_exists` and `Ideal.homogeneous_span`.
* For a homogeneous ideal `I` of `MvPolynomial σ k`, `σ` finite, each graded piece
  `I.quotientGrading d` of `MvPolynomial σ k ⧸ I` is a finite `k`-module (Fulton, Problem 4.9).
  This is found by instance search, from Tau Ceti's `TauCeti.GradedAlgebra.finite_quotientPiece`
  and `MvPolynomial.homogeneousSubmodule_moduleFinite`; the example at the end of this file
  checks it.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008]
-/

public section

open DirectSum

section GradedRing

variable {ι σ A : Type*} [Semiring A] [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ι → σ}
  [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]

/-- A homogeneous ideal of a Noetherian graded ring is spanned by a finite set of homogeneous
elements: the homogeneous components of a finite generating set. -/
theorem Ideal.IsHomogeneous.exists_finset_span_eq [IsNoetherianRing A] {I : Ideal A}
    (hI : I.IsHomogeneous 𝒜) :
    ∃ s : Finset A, (∀ x ∈ s, SetLike.IsHomogeneousElem 𝒜 x) ∧ Ideal.span (s : Set A) = I := by
  classical
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian I : I.FG)
  refine ⟨t.biUnion fun x ↦ (decompose 𝒜 x).support.image fun i ↦ (decompose 𝒜 x i : A),
    ?_, le_antisymm ?_ ?_⟩
  · simp only [Finset.mem_biUnion, Finset.mem_image]
    rintro _ ⟨x, -, i, -, rfl⟩
    exact ⟨i, SetLike.coe_mem _⟩
  · rw [Ideal.span_le]
    intro y hy
    simp only [Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image] at hy
    obtain ⟨x, hx, i, -, rfl⟩ := hy
    exact hI i (ht ▸ Submodule.subset_span hx)
  · rw [← ht, Submodule.span_le]
    intro x hx
    rw [← sum_support_decompose 𝒜 x]
    refine Ideal.sum_mem _ fun i hi ↦ Ideal.subset_span ?_
    simp only [Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion, Set.mem_image]
    exact ⟨x, hx, i, hi, rfl⟩

end GradedRing

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ R : Type*} [Finite σ] [CommRing R] [IsNoetherianRing R]

/-- A homogeneous ideal of the polynomial ring in finitely many variables over a Noetherian ring,
graded by total degree, is spanned by finitely many forms. -/
theorem exists_finset_isHomogeneous_span_eq {I : Ideal (MvPolynomial σ R)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R)) :
    ∃ s : Finset (MvPolynomial σ R), (∀ f ∈ s, ∃ d, f.IsHomogeneous d) ∧
      Ideal.span (s : Set (MvPolynomial σ R)) = I := by
  obtain ⟨s, hs, hspan⟩ := hI.exists_finset_span_eq
  exact ⟨s, fun f hf ↦ (hs f hf).imp fun d hd ↦ (mem_homogeneousSubmodule d f).mp hd, hspan⟩

/-- A homogeneous ideal of a polynomial ring is spanned by the forms it contains. -/
theorem _root_.Ideal.IsHomogeneous.span_setOf_isHomogeneous {σ R : Type*} [CommSemiring R]
    {I : Ideal (MvPolynomial σ R)} (hI : I.IsHomogeneous (homogeneousSubmodule σ R)) :
    Ideal.span {f | f ∈ I ∧ ∃ d, f.IsHomogeneous d} = I := by
  refine le_antisymm (Ideal.span_le.2 fun f hf ↦ hf.1) fun f hf ↦ ?_
  rw [← sum_homogeneousComponent f]
  exact Ideal.sum_mem _ fun d _ ↦ Ideal.subset_span
    ⟨homogeneousComponent_mem_of_mem hI hf d, d, homogeneousComponent_isHomogeneous d f⟩

/-- A form of degree `d` lies in the `N`-th power of the ideal of the variables for `N ≤ d`. -/
theorem IsHomogeneous.mem_pow_idealOfVars {σ R : Type*} [CommSemiring R]
    {f : MvPolynomial σ R} {d N : ℕ} (hf : f.IsHomogeneous d) (hN : N ≤ d) :
    f ∈ idealOfVars σ R ^ N := by
  refine (mem_pow_idealOfVars_iff N f).2 fun x hx ↦ ?_
  rw [Finsupp.degree_eq_weight_one]
  exact hN.trans (hf (mem_support_iff.1 hx)).ge

/-- An ideal contains the `N`-th power of the ideal of the variables exactly when it contains
every form of degree at least `N`. -/
theorem pow_idealOfVars_le_iff {σ R : Type*} [CommSemiring R] {I : Ideal (MvPolynomial σ R)}
    (N : ℕ) :
    idealOfVars σ R ^ N ≤ I ↔ ∀ d, N ≤ d → ∀ f : MvPolynomial σ R, f.IsHomogeneous d → f ∈ I := by
  refine ⟨fun h d hd f hf ↦ h (hf.mem_pow_idealOfVars hd), fun h f hf ↦ ?_⟩
  rw [← sum_homogeneousComponent f]
  refine Ideal.sum_mem _ fun d _ ↦ ?_
  by_cases hd : N ≤ d
  · exact h d hd _ (homogeneousComponent_isHomogeneous d f)
  · have : homogeneousComponent d f = 0 := by
      ext x
      rw [coeff_homogeneousComponent]
      split_ifs with hx
      · exact (mem_pow_idealOfVars_iff' N f).1 hf x (by omega)
      · simp
    simp [this]

/-- Each graded piece of the quotient of a polynomial ring in finitely many variables over a
field by a homogeneous ideal is finite-dimensional. -/
example {k : Type*} [Field k] (I : HomogeneousIdeal (homogeneousSubmodule σ k)) (d : ℕ) :
    Module.Finite k (I.quotientGrading d) :=
  inferInstance

end MvPolynomial

end
