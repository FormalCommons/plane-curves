/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.Irreducible
public import PlaneCurves.LinearAlgebra.Projectivization.AffineChart
public import PlaneCurves.RingTheory.MvPolynomial.Homogenize.Ideal
public import PlaneCurves.RingTheory.MvPolynomial.VanishingIdeal
public import TauCeti.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.RingTheory.MvPolynomial.ZariskiClosure

/-!
# Projective closure and affine part

Fix a field `k` and a coordinate `i : Fin (n + 1)`. The chart
`φᵢ = (affineChart i).symm : 𝔸ⁿ → ℙⁿ`, `a ↦ [Fin.insertNth i 1 a]`, identifies `𝔸ⁿ` with the
affine open `Uᵢ = affineOpen i`, whose complement is the hyperplane at infinity `Xᵢ = 0`.
Following Fulton (§4.3), this file defines

* `PlaneCurves.ProjectiveSpace.projectiveClosure i V`: the projective closure
  `V* = V(I(V)*)` of a set `V ⊆ 𝔸ⁿ`, where `I(V)*` is the homogenization
  `Ideal.homogenization (MvPolynomial.vanishingIdeal k V) i`;
* `PlaneCurves.ProjectiveSpace.affinePart i W`: the affine part `W_* = V(I(W)_*)` of a set
  `W ⊆ ℙⁿ`, where `I(W)_*` is the image of `I(W)` under `TauCeti.dehomogenize i`.

## Main results

* `affinePart_eq_preimage`: `W_* = φᵢ⁻¹(V(I(W)))`, so `W_* = φᵢ⁻¹(W)` for an algebraic `W`
  (`mem_affinePart_iff`).
* `image_subset_projectiveClosure`: `φᵢ(V) ⊆ V*`.
* `vanishingIdeal_projectiveClosure`: `I(V*) = I(V)*` for every set `V`, over any field.
* `projectiveClosure_subset_iff`: `V*` is the smallest projective algebraic set containing
  `φᵢ(V)` (Proposition 3 (5)); `projectiveClosure_zeroLocus_vanishingIdeal`: `V*` is algebraic.
* `projectiveClosure_mono`, `affinePart_mono`: both operations are monotone
  (Proposition 3 (2)).
* `projectiveClosure_inter_affineOpen`, `affinePart_projectiveClosure`: for an algebraic `V`,
  `V* ∩ Uᵢ = φᵢ(V)` and `(V*)_* = V` (Proposition 3 (1)).
* `projectiveClosure_injOn`, `projectiveClosure_union`, `projectiveClosure_biUnion`,
  `projectiveClosure_empty`, `projectiveClosure_univ`: `V ↦ V*` is injective on algebraic sets
  and preserves finite unions, `∅` and, over an infinite field, `𝔸ⁿ`.
* `isPrime_vanishingIdeal_projectiveClosure`, `projectiveClosure_nonempty`: the projective
  closure of an affine variety is a projective variety (Proposition 3 (3)).
* `projectiveClosure_irreducibleDecomposition`: the closures of the members of an irreducible
  decomposition of `V` form one of `V*` (Proposition 3 (4)).
* `not_projectiveClosure_subset_compl_affineOpen`,
  `compl_affineOpen_not_subset_projectiveClosure`: for `∅ ≠ V ⊊ 𝔸ⁿ` algebraic, `V*` neither lies
  in nor, over an infinite field, contains the hyperplane at infinity (Proposition 3 (6)).
* `projectiveClosure_zeroLocus`, `projectiveClosure_zeroLocus_span_singleton`: over an
  algebraically closed field, `V(J)* = V(J*)`, and in particular `V(F)* = V(F*)`.
* `projectiveClosure_affinePart`: a projective variety `W` not contained in the hyperplane at
  infinity satisfies `(W_*)* = W` (Proposition 3 (7)), over any field; then
  `vanishingIdeal_affinePart` (`I(W_*) = I(W)_*`) and `isPrime_vanishingIdeal_affinePart`.
* `affinePart_ne_univ`, `projectiveClosure_affinePart_sUnion`, `affinePart_sUnion_ne_univ`:
  (7) for finite unions of projective varieties, none contained in (and, for `W_* ≠ 𝔸ⁿ` over an
  infinite field, none containing) the hyperplane at infinity.
* `projectiveClosureEquiv`: `V ↦ V*` is a bijection from affine varieties to projective
  varieties not contained in the hyperplane at infinity, with inverse `W ↦ W_*`.

## Implementation notes

Fulton works over an algebraically closed field with the chart `i = n + 1`. Every statement
here holds over any field and for every chart: the key point is that `I(V*) = I(V)*` holds for
every set `V`. Affine sets `V` are algebraic when `MvPolynomial.zeroLocus k
(MvPolynomial.vanishingIdeal k V) = V`, projective sets `W` when `zeroLocus (vanishingIdeal W) = W`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §4.3
-/

public section

open MvPolynomial Projectivization TauCeti
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PlaneCurves.ProjectiveSpace

variable {k : Type*} [Field k] {n : ℕ} (i : Fin (n + 1))

/-- The projective closure `V*` of a set `V ⊆ 𝔸ⁿ` with respect to the chart `i`: the zero locus
in `ℙⁿ` of the homogenization of the ideal of `V`. -/
noncomputable def projectiveClosure (V : Set (Fin n → k)) : Set (ℙ k (Fin (n + 1) → k)) :=
  zeroLocus ((MvPolynomial.vanishingIdeal k V).homogenization i : Set _)

theorem projectiveClosure_def (V : Set (Fin n → k)) :
    projectiveClosure i V =
      zeroLocus ((MvPolynomial.vanishingIdeal k V).homogenization i : Set _) :=
  (rfl)

/-- The affine part `W_*` of a set `W ⊆ ℙⁿ` with respect to the chart `i`: the zero locus in
`𝔸ⁿ` of the dehomogenization of the ideal of `W`. -/
noncomputable def affinePart (W : Set (ℙ k (Fin (n + 1) → k))) : Set (Fin n → k) :=
  MvPolynomial.zeroLocus k ((vanishingIdeal W).toIdeal.map (dehomogenize i))

theorem affinePart_def (W : Set (ℙ k (Fin (n + 1) → k))) :
    affinePart i W =
      MvPolynomial.zeroLocus k ((vanishingIdeal W).toIdeal.map (dehomogenize i)) :=
  (rfl)

variable {i}

/-- The point `φᵢ(a)` lies in the zero locus of a homogeneous ideal `I` exactly when `a` lies in
the zero locus of the dehomogenization `I_*`. -/
theorem affineChart_symm_mem_zeroLocus_iff
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)) (a : Fin n → k) :
    (affineChart i).symm a ∈ zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k)) ↔
      a ∈ MvPolynomial.zeroLocus k (I.toIdeal.map (dehomogenize i)) := by
  rw [affineChart_symm_apply]
  refine (mk_mem_zeroLocus_iff_mem_zeroLocus I.isHomogeneous _ _).trans ?_
  simp only [MvPolynomial.mem_zeroLocus_iff, aeval_eq_eval]
  refine ⟨fun h g hg ↦ ?_, fun h f hf ↦ ?_⟩
  · have : I.toIdeal.map (dehomogenize i) ≤ RingHom.ker (eval a) :=
      Ideal.map_le_iff_le_comap.2 fun f hf ↦ by
        simpa [RingHom.mem_ker, eval_dehomogenize] using h f hf
    exact this hg
  · simpa [eval_dehomogenize] using h _ (Ideal.mem_map_of_mem _ hf)

/-! ### The affine part -/

/-- **The affine part is the preimage under the chart.** `W_* = φᵢ⁻¹(V(I(W)))`. -/
theorem affinePart_eq_preimage (W : Set (ℙ k (Fin (n + 1) → k))) :
    affinePart i W = (affineChart i).symm ⁻¹' zeroLocus (vanishingIdeal W) := by
  ext a
  exact (affineChart_symm_mem_zeroLocus_iff _ a).symm

/-- For an algebraic set `W ⊆ ℙⁿ`, `a ∈ W_*` exactly when `φᵢ(a) ∈ W`. -/
theorem mem_affinePart_iff {W : Set (ℙ k (Fin (n + 1) → k))}
    (hW : zeroLocus (vanishingIdeal W) = W) {a : Fin n → k} :
    a ∈ affinePart i W ↔ (affineChart i).symm a ∈ W := by
  rw [affinePart_eq_preimage, Set.mem_preimage, hW]

theorem affinePart_mono : Monotone (affinePart (k := k) i) := fun _ _ h ↦ by
  simp only [affinePart_eq_preimage]
  exact Set.preimage_mono (zeroLocus_anti_mono (vanishingIdeal_anti_mono h))

theorem affinePart_union (W W' : Set (ℙ k (Fin (n + 1) → k))) :
    affinePart i (W ∪ W') = affinePart i W ∪ affinePart i W' := by
  simp only [affinePart_eq_preimage, vanishingIdeal_union, ← Set.preimage_union]
  exact congrArg _ (zeroLocus_inf (vanishingIdeal W).isHomogeneous
    (vanishingIdeal W').isHomogeneous)

@[simp]
theorem affinePart_univ : affinePart i (Set.univ : Set (ℙ k (Fin (n + 1) → k))) = Set.univ := by
  rw [affinePart_eq_preimage, Set.eq_univ_iff_forall]
  exact fun a ↦ subset_zeroLocus_vanishingIdeal _ (Set.mem_univ _)

@[simp]
theorem affinePart_empty : affinePart i (∅ : Set (ℙ k (Fin (n + 1) → k))) = ∅ := by
  rw [affinePart_eq_preimage, vanishingIdeal_empty, HomogeneousIdeal.coe_top, zeroLocus_univ,
    Set.preimage_empty]

/-! ### The projective closure -/

/-- The preimage of `V*` under the chart is the affine algebraic set `V(I(V))`. -/
theorem preimage_projectiveClosure (V : Set (Fin n → k)) :
    (affineChart i).symm ⁻¹' projectiveClosure i V =
      MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k V) := by
  ext a
  rw [Set.mem_preimage, projectiveClosure_def, affineChart_symm_mem_zeroLocus_iff,
    Ideal.map_dehomogenize_homogenization]

/-- `φᵢ(V) ⊆ V*`. -/
theorem image_subset_projectiveClosure (V : Set (Fin n → k)) :
    (affineChart i).symm '' V ⊆ projectiveClosure i V := by
  rw [Set.image_subset_iff, preimage_projectiveClosure]
  exact MvPolynomial.zeroLocus_vanishingIdeal_le V

/-- `V*` is a projective algebraic set. -/
@[simp]
theorem projectiveClosure_zeroLocus_vanishingIdeal (V : Set (Fin n → k)) :
    zeroLocus (vanishingIdeal (projectiveClosure i V)) = projectiveClosure i V :=
  zeroLocus_vanishingIdeal_zeroLocus _

/-- The forms of a homogeneous ideal `I` vanishing at `φᵢ(V)` dehomogenize into `I(V)`, so `I`
lies in `I(V)*`. -/
theorem le_homogenization_vanishingIdeal_of_image_subset
    {I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)} {V : Set (Fin n → k)}
    (h : (affineChart i).symm '' V ⊆ zeroLocus (I : Set (MvPolynomial (Fin (n + 1)) k))) :
    I ≤ (MvPolynomial.vanishingIdeal k V).homogenization i := by
  rw [Ideal.le_homogenization_iff, ← MvPolynomial.le_zeroLocus_iff_le_vanishingIdeal]
  intro a ha
  exact (affineChart_symm_mem_zeroLocus_iff I a).1 (h ⟨a, ha, rfl⟩)

/-- **The ideal of the projective closure.** `I(V*) = I(V)*` for every set `V ⊆ 𝔸ⁿ`. -/
theorem vanishingIdeal_projectiveClosure (V : Set (Fin n → k)) :
    vanishingIdeal (projectiveClosure i V) = (MvPolynomial.vanishingIdeal k V).homogenization i :=
  le_antisymm (le_homogenization_vanishingIdeal_of_image_subset
      ((image_subset_projectiveClosure V).trans (subset_zeroLocus_vanishingIdeal _)))
    (le_vanishingIdeal_zeroLocus _)

/-- **Fulton, §4.3, Proposition 3 (5).** `V*` is the smallest projective algebraic set
containing `φᵢ(V)`. -/
theorem projectiveClosure_subset_iff {V : Set (Fin n → k)} {W : Set (ℙ k (Fin (n + 1) → k))}
    (hW : zeroLocus (vanishingIdeal W) = W) :
    projectiveClosure i V ⊆ W ↔ (affineChart i).symm '' V ⊆ W := by
  refine ⟨(image_subset_projectiveClosure V).trans, fun h ↦ ?_⟩
  rw [← hW] at h ⊢
  exact zeroLocus_anti_mono (le_homogenization_vanishingIdeal_of_image_subset h)

/-- **Fulton, §4.3, Proposition 3 (2).** `V ↦ V*` is monotone. -/
theorem projectiveClosure_mono : Monotone (projectiveClosure (k := k) i) := fun _ _ h ↦
  zeroLocus_anti_mono (Ideal.homogenization_mono (MvPolynomial.vanishingIdeal_anti_mono h))

/-- The part of `V*` in the affine open `Uᵢ` is the image of `V(I(V))`. -/
theorem projectiveClosure_inter_affineOpen_eq_image (V : Set (Fin n → k)) :
    projectiveClosure i V ∩ affineOpen i =
      (affineChart i).symm '' MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k V) := by
  rw [← preimage_projectiveClosure, Set.image_preimage_eq_inter_range, ← affineChart_source,
    ← (affineChart i).symm_image_target_eq_source, affineChart_target, Set.image_univ]

/-- **Fulton, §4.3, Proposition 3 (1).** For an algebraic set `V ⊆ 𝔸ⁿ`, `V* ∩ Uᵢ = φᵢ(V)`. -/
theorem projectiveClosure_inter_affineOpen {V : Set (Fin n → k)}
    (hV : MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k V) = V) :
    projectiveClosure i V ∩ affineOpen i = (affineChart i).symm '' V := by
  rw [projectiveClosure_inter_affineOpen_eq_image, hV]

/-- The affine part of `V*` is `V(I(V))`, for every set `V ⊆ 𝔸ⁿ`. -/
theorem affinePart_projectiveClosure_eq_zeroLocus (V : Set (Fin n → k)) :
    affinePart i (projectiveClosure i V) =
      MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k V) := by
  rw [affinePart_eq_preimage, projectiveClosure_zeroLocus_vanishingIdeal,
    preimage_projectiveClosure]

/-- **Fulton, §4.3, Proposition 3 (1).** For an algebraic set `V ⊆ 𝔸ⁿ`, `(V*)_* = V`. -/
theorem affinePart_projectiveClosure {V : Set (Fin n → k)}
    (hV : MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k V) = V) :
    affinePart i (projectiveClosure i V) = V := by
  rw [affinePart_projectiveClosure_eq_zeroLocus, hV]

/-- For an algebraic set `V' ⊆ 𝔸ⁿ`, `V* ⊆ V'*` exactly when `V ⊆ V'`. -/
theorem projectiveClosure_subset_projectiveClosure_iff {V V' : Set (Fin n → k)}
    (hV' : MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k V') = V') :
    projectiveClosure i V ⊆ projectiveClosure i V' ↔ V ⊆ V' := by
  refine ⟨fun h ↦ ?_, fun h ↦ projectiveClosure_mono h⟩
  have := affinePart_mono (i := i) h
  rw [affinePart_projectiveClosure hV', affinePart_projectiveClosure_eq_zeroLocus] at this
  exact (MvPolynomial.zeroLocus_vanishingIdeal_le V).trans this

/-- `V ↦ V*` is injective on affine algebraic sets. -/
theorem projectiveClosure_injOn :
    Set.InjOn (projectiveClosure (k := k) i)
      {V | MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k V) = V} := fun _ hV _ hV' h ↦
  ((projectiveClosure_subset_projectiveClosure_iff hV').1 h.le).antisymm
    ((projectiveClosure_subset_projectiveClosure_iff hV).1 h.ge)

theorem projectiveClosure_union (V V' : Set (Fin n → k)) :
    projectiveClosure i (V ∪ V') = projectiveClosure i V ∪ projectiveClosure i V' := by
  simp only [projectiveClosure_def, MvPolynomial.vanishingIdeal_union,
    Ideal.homogenization_inf]
  exact zeroLocus_inf (Ideal.homogenization (MvPolynomial.vanishingIdeal k V) i).isHomogeneous
    (Ideal.homogenization (MvPolynomial.vanishingIdeal k V') i).isHomogeneous

@[simp]
theorem projectiveClosure_empty : projectiveClosure i (∅ : Set (Fin n → k)) = ∅ := by
  rw [projectiveClosure_def, MvPolynomial.vanishingIdeal_empty, Ideal.homogenization_top,
    HomogeneousIdeal.coe_top, zeroLocus_univ]

theorem projectiveClosure_biUnion {ι : Type*} (s : Finset ι) (V : ι → Set (Fin n → k)) :
    projectiveClosure i (⋃ j ∈ s, V j) = ⋃ j ∈ s, projectiveClosure i (V j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s _ ih => rw [Finset.set_biUnion_insert, Finset.set_biUnion_insert,
      projectiveClosure_union, ih]

theorem projectiveClosure_sUnion {C : Set (Set (Fin n → k))} (hC : C.Finite) :
    projectiveClosure i (⋃₀ C) = ⋃₀ (projectiveClosure i '' C) := by
  induction C, hC using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ ih => rw [Set.sUnion_insert, Set.image_insert_eq, Set.sUnion_insert,
      projectiveClosure_union, ih]

/-- Over an infinite field, the projective closure of `𝔸ⁿ` is `ℙⁿ`. -/
@[simp]
theorem projectiveClosure_univ [Infinite k] :
    projectiveClosure i (Set.univ : Set (Fin n → k)) = Set.univ := by
  have h : MvPolynomial.vanishingIdeal k (Set.univ : Set (Fin n → k)) = ⊥ := by
    simpa using MvPolynomial.vanishingIdeal_pi_eq_bot (k := k) (K := k)
      (s := fun _ : Fin n ↦ (Set.univ : Set k)) fun _ ↦ Set.infinite_univ
  rw [projectiveClosure_def, h, Ideal.homogenization_bot, HomogeneousIdeal.coe_bot]
  exact zeroLocus_singleton_zero

/-! ### Closures of affine varieties -/

/-- The projective closure of a nonempty set is nonempty. -/
theorem projectiveClosure_nonempty {V : Set (Fin n → k)} (hV : V.Nonempty) :
    (projectiveClosure i V).Nonempty :=
  (hV.image _).mono (image_subset_projectiveClosure V)

/-- `I(V*)` is prime exactly when `I(V)` is. -/
theorem isPrime_vanishingIdeal_projectiveClosure_iff {V : Set (Fin n → k)} :
    (vanishingIdeal (projectiveClosure i V)).toIdeal.IsPrime ↔
      (MvPolynomial.vanishingIdeal k V).IsPrime := by
  rw [vanishingIdeal_projectiveClosure, Ideal.isPrime_homogenization_iff]

/-- **Fulton, §4.3, Proposition 3 (3).** If `I(V)` is prime, so is `I(V*)`: with
`projectiveClosure_zeroLocus_vanishingIdeal` and `projectiveClosure_nonempty`, the projective
closure of an affine variety is a projective variety. -/
theorem isPrime_vanishingIdeal_projectiveClosure {V : Set (Fin n → k)}
    (h : (MvPolynomial.vanishingIdeal k V).IsPrime) :
    (vanishingIdeal (projectiveClosure i V)).toIdeal.IsPrime :=
  isPrime_vanishingIdeal_projectiveClosure_iff.2 h

/-- **Fulton, §4.3, Proposition 3 (4).** If `C` is an irreducible decomposition of an affine
algebraic set `V` (a finite set of affine varieties, none contained in another, with union `V`),
then the projective closures of its members form an irreducible decomposition of `V*`, in the
form of `existsUnique_irreducibleDecomposition`. -/
theorem projectiveClosure_irreducibleDecomposition {V : Set (Fin n → k)}
    {C : Set (Set (Fin n → k))} (hC : C.Finite)
    (hCW : ∀ W ∈ C, MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k W) = W ∧
      (MvPolynomial.vanishingIdeal k W).IsPrime)
    (hCU : ⋃₀ C = V) (hCi : ∀ W ∈ C, ∀ W' ∈ C, W ⊆ W' → W = W') :
    (projectiveClosure i '' C).Finite ∧
      (∀ W ∈ projectiveClosure i '' C,
        zeroLocus (vanishingIdeal W : Set (MvPolynomial (Fin (n + 1)) k)) = W ∧
          (vanishingIdeal W).toIdeal.IsPrime) ∧
      ⋃₀ (projectiveClosure i '' C) = projectiveClosure i V ∧
      ∀ W ∈ projectiveClosure i '' C, ∀ W' ∈ projectiveClosure i '' C, W ⊆ W' → W = W' := by
  refine ⟨hC.image _, ?_, by rw [← hCU, projectiveClosure_sUnion hC], ?_⟩
  · rintro _ ⟨W, hW, rfl⟩
    exact ⟨projectiveClosure_zeroLocus_vanishingIdeal W,
      isPrime_vanishingIdeal_projectiveClosure (hCW W hW).2⟩
  · rintro _ ⟨W, hW, rfl⟩ _ ⟨W', hW', rfl⟩ h
    rw [hCi W hW W' hW' ((projectiveClosure_subset_projectiveClosure_iff (hCW W' hW').1).1 h)]

/-- **Fulton, §4.3, Proposition 3 (6)**, first half. The projective closure of a nonempty set,
such as an affine variety, does not lie in the hyperplane at infinity `(affineOpen i)ᶜ`. -/
theorem not_projectiveClosure_subset_compl_affineOpen {V : Set (Fin n → k)} (hV : V.Nonempty) :
    ¬ projectiveClosure i V ⊆ (affineOpen i)ᶜ := by
  obtain ⟨a, ha⟩ := hV
  refine fun h ↦ h (image_subset_projectiveClosure V ⟨a, ha, rfl⟩) ?_
  rw [← affineChart_source]
  exact (affineChart i).map_target (by simp [affineChart_target])

/-- **Fulton, §4.3, Proposition 3 (6)**, second half. Over an infinite field, the projective
closure of a nonempty algebraic set `V ⊊ 𝔸ⁿ` does not contain the hyperplane at infinity
`(affineOpen i)ᶜ`. -/
theorem compl_affineOpen_not_subset_projectiveClosure [Infinite k] {V : Set (Fin n → k)}
    (hV : MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k V) = V)
    (hne : V ≠ Set.univ) (hne' : V.Nonempty) :
    ¬ (affineOpen i)ᶜ ⊆ projectiveClosure i V := by
  obtain ⟨f, hf, hf0⟩ : ∃ f ∈ MvPolynomial.vanishingIdeal k V, f ≠ 0 := by
    by_contra! h
    refine hne ?_
    rw [← hV, (Submodule.eq_bot_iff _).2 h, MvPolynomial.zeroLocus_bot]
    rfl
  obtain ⟨a, ha⟩ : ∃ a, eval a (homogeneousComponent f.totalDegree f) ≠ 0 := by
    by_contra! h
    exact homogeneousComponent_totalDegree_ne_zero f hf0 (MvPolynomial.funext fun a ↦ by simp [h])
  have hN : f.totalDegree ≠ 0 := by
    intro h0
    obtain ⟨b, hb⟩ := hne'
    have := MvPolynomial.mem_vanishingIdeal_iff.1 hf b hb
    rw [totalDegree_eq_zero_iff_eq_C.1 h0] at this hf0
    simp_all
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp [eval_zero, constantCoeff_eq, coeff_homogeneousComponent, Ne.symm hN] at ha
  intro h
  have hP := h (insertZero_notMem_affineOpen i (mk k a ha0))
  rw [insertZero_mk, projectiveClosure_def, ← coe_toIdeal,
    mk_mem_zeroLocus_iff_mem_zeroLocus (HomogeneousIdeal.isHomogeneous _)] at hP
  have := MvPolynomial.mem_zeroLocus_iff.1 hP _ (Ideal.homogenize_mem_homogenization (i := i) hf)
  rw [aeval_eq_eval, eval_insertNth_zero_homogenize] at this
  exact ha this

/-- Over an algebraically closed field, the projective closure of the zero locus of an ideal `J`
is the zero locus of its homogenization: `V(J)* = V(J*)`. -/
theorem projectiveClosure_zeroLocus [IsAlgClosed k] (J : Ideal (MvPolynomial (Fin n) k)) :
    projectiveClosure i (MvPolynomial.zeroLocus k J) = zeroLocus (J.homogenization i : Set _) := by
  rw [projectiveClosure_def, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]
  refine (zeroLocus_anti_mono (Ideal.homogenization_mono J.le_radical)).antisymm ?_
  have := zeroLocus_anti_mono
    (SetLike.coe_subset_coe.2 (Ideal.homogenization_radical_le (i := i) J))
  rwa [← coe_toIdeal, HomogeneousIdeal.coe_radical, zeroLocus_radical, coe_toIdeal] at this

/-- **`V(F)* = V(F*)`.** Over an algebraically closed field, the projective closure of the
hypersurface `V(F) ⊆ 𝔸ⁿ` is the zero locus of the homogenization
`F* = homogenize i F.totalDegree F`. -/
theorem projectiveClosure_zeroLocus_span_singleton [IsAlgClosed k] (F : MvPolynomial (Fin n) k) :
    projectiveClosure i (MvPolynomial.zeroLocus k (Ideal.span {F})) =
      zeroLocus {homogenize i F.totalDegree F} := by
  rw [projectiveClosure_zeroLocus, ← coe_toIdeal,
    Ideal.homogenization_span_singleton, zeroLocus_span]
/-! ### Affine parts of projective varieties -/

/-- The hyperplane at infinity `(affineOpen i)ᶜ = V(Xᵢ)` is algebraic. -/
theorem zeroLocus_vanishingIdeal_compl_affineOpen (i : Fin (n + 1)) :
    zeroLocus (vanishingIdeal (affineOpen (K := k) i)ᶜ : Set (MvPolynomial (Fin (n + 1)) k)) =
      (affineOpen i)ᶜ := by
  rw [← zeroLocus_singleton_X]
  exact zeroLocus_vanishingIdeal_zeroLocus_of_isHomogeneous fun f hf ↦
    ⟨1, (Set.mem_singleton_iff.1 hf) ▸ isHomogeneous_X k i⟩

/-- The affine part of a set is an affine algebraic set. -/
@[simp]
theorem zeroLocus_vanishingIdeal_affinePart (W : Set (ℙ k (Fin (n + 1) → k))) :
    MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k (affinePart i W)) = affinePart i W := by
  rw [affinePart_def, MvPolynomial.zeroLocus_vanishingIdeal_zeroLocus]

/-- `φᵢ(W_*) ⊆ W` for an algebraic set `W ⊆ ℙⁿ`. -/
theorem image_affinePart_subset {W : Set (ℙ k (Fin (n + 1) → k))}
    (hW : zeroLocus (vanishingIdeal W) = W) : (affineChart i).symm '' affinePart i W ⊆ W := by
  rintro _ ⟨a, ha, rfl⟩
  exact (mem_affinePart_iff hW).1 ha

/-- `(W_*)* ⊆ W` for an algebraic set `W ⊆ ℙⁿ`. -/
theorem projectiveClosure_affinePart_subset {W : Set (ℙ k (Fin (n + 1) → k))}
    (hW : zeroLocus (vanishingIdeal W) = W) : projectiveClosure i (affinePart i W) ⊆ W :=
  (projectiveClosure_subset_iff hW).2 (image_affinePart_subset hW)

/-- Every set `W ⊆ ℙⁿ` lies in `(W_*)*` together with the hyperplane at infinity. -/
theorem subset_projectiveClosure_affinePart_union (W : Set (ℙ k (Fin (n + 1) → k))) :
    W ⊆ projectiveClosure i (affinePart i W) ∪ (affineOpen i)ᶜ := by
  intro P hP
  by_cases hU : P ∈ affineOpen i
  · have hP' : (affineChart i).symm (affineChart i P) = P :=
      (affineChart i).left_inv (by rwa [affineChart_source])
    refine Or.inl (hP' ▸ image_subset_projectiveClosure _ ⟨_, ?_, rfl⟩)
    rw [affinePart_eq_preimage, Set.mem_preimage, hP']
    exact subset_zeroLocus_vanishingIdeal W hP
  · exact Or.inr hU

/-- **Fulton, §4.3, Proposition 3 (7).** A projective variety `W` not contained in the
hyperplane at infinity is the projective closure of its affine part: `(W_*)* = W`. -/
theorem projectiveClosure_affinePart {W : Set (ℙ k (Fin (n + 1) → k))}
    (hW : zeroLocus (vanishingIdeal W) = W) (hp : (vanishingIdeal W).toIdeal.IsPrime)
    (h : ¬ W ⊆ (affineOpen i)ᶜ) : projectiveClosure i (affinePart i W) = W :=
  (projectiveClosure_affinePart_subset hW).antisymm <|
    (subset_or_subset_of_subset_union hp (projectiveClosure_zeroLocus_vanishingIdeal _)
      (zeroLocus_vanishingIdeal_compl_affineOpen i)
      (subset_projectiveClosure_affinePart_union W)).resolve_right h

/-- For a projective variety `W` not contained in the hyperplane at infinity, `I(W_*)* = I(W)`. -/
theorem homogenization_vanishingIdeal_affinePart {W : Set (ℙ k (Fin (n + 1) → k))}
    (hW : zeroLocus (vanishingIdeal W) = W) (hp : (vanishingIdeal W).toIdeal.IsPrime)
    (h : ¬ W ⊆ (affineOpen i)ᶜ) :
    (MvPolynomial.vanishingIdeal k (affinePart i W)).homogenization i = vanishingIdeal W := by
  rw [← vanishingIdeal_projectiveClosure, projectiveClosure_affinePart hW hp h]

/-- **The ideal of the affine part.** For a projective variety `W` not contained in the
hyperplane at infinity, `I(W_*) = I(W)_*`. -/
theorem vanishingIdeal_affinePart {W : Set (ℙ k (Fin (n + 1) → k))}
    (hW : zeroLocus (vanishingIdeal W) = W) (hp : (vanishingIdeal W).toIdeal.IsPrime)
    (h : ¬ W ⊆ (affineOpen i)ᶜ) :
    MvPolynomial.vanishingIdeal k (affinePart i W) =
      (vanishingIdeal W).toIdeal.map (dehomogenize i) := by
  rw [← homogenization_vanishingIdeal_affinePart hW hp h, Ideal.map_dehomogenize_homogenization]

/-- The affine part of a projective variety `W` not contained in the hyperplane at infinity has
a prime ideal: with `zeroLocus_vanishingIdeal_affinePart`, it is an affine variety. -/
theorem isPrime_vanishingIdeal_affinePart {W : Set (ℙ k (Fin (n + 1) → k))}
    (hW : zeroLocus (vanishingIdeal W) = W) (hp : (vanishingIdeal W).toIdeal.IsPrime)
    (h : ¬ W ⊆ (affineOpen i)ᶜ) : (MvPolynomial.vanishingIdeal k (affinePart i W)).IsPrime :=
  Ideal.IsPrime.of_homogenization (i := i) (by
    rwa [homogenization_vanishingIdeal_affinePart hW hp h])

/-- Over an infinite field, the affine part of a projective variety that neither lies in nor
contains the hyperplane at infinity is not all of `𝔸ⁿ`. -/
theorem affinePart_ne_univ [Infinite k] {W : Set (ℙ k (Fin (n + 1) → k))}
    (hW : zeroLocus (vanishingIdeal W) = W) (hp : (vanishingIdeal W).toIdeal.IsPrime)
    (h : ¬ W ⊆ (affineOpen i)ᶜ) (h' : ¬ (affineOpen i)ᶜ ⊆ W) : affinePart i W ≠ Set.univ := by
  intro hu
  refine h' ?_
  rw [← projectiveClosure_affinePart hW hp h, hu, projectiveClosure_univ]
  exact Set.subset_univ _

/-- The affine part of a finite union is the union of the affine parts. -/
theorem affinePart_sUnion {C : Set (Set (ℙ k (Fin (n + 1) → k)))} (hC : C.Finite) :
    affinePart i (⋃₀ C) = ⋃₀ (affinePart i '' C) := by
  induction C, hC using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ ih => rw [Set.sUnion_insert, Set.image_insert_eq, Set.sUnion_insert,
      affinePart_union, ih]

/-- **Fulton, §4.3, Proposition 3 (7)**, for a finite union `W` of projective varieties, none
contained in the hyperplane at infinity: `(W_*)* = W`. -/
theorem projectiveClosure_affinePart_sUnion {C : Set (Set (ℙ k (Fin (n + 1) → k)))}
    (hC : C.Finite)
    (hCW : ∀ W ∈ C, zeroLocus (vanishingIdeal W) = W ∧ (vanishingIdeal W).toIdeal.IsPrime)
    (hCH : ∀ W ∈ C, ¬ W ⊆ (affineOpen i)ᶜ) :
    projectiveClosure i (affinePart i (⋃₀ C)) = ⋃₀ C := by
  rw [affinePart_sUnion hC, projectiveClosure_sUnion (hC.image _), Set.image_image]
  exact congrArg _ ((Set.image_congr fun W hW ↦
    projectiveClosure_affinePart (hCW W hW).1 (hCW W hW).2 (hCH W hW)).trans (Set.image_id C))

/-- **Fulton, §4.3, Proposition 3 (7)**, the condition `W_* ≠ 𝔸ⁿ`. Over an infinite field, a
finite union `W` of projective varieties, none of which lies in or contains the hyperplane at
infinity, has `W_* ≠ 𝔸ⁿ`. -/
theorem affinePart_sUnion_ne_univ [Infinite k] {C : Set (Set (ℙ k (Fin (n + 1) → k)))}
    (hC : C.Finite)
    (hCW : ∀ W ∈ C, zeroLocus (vanishingIdeal W) = W ∧ (vanishingIdeal W).toIdeal.IsPrime)
    (hCH : ∀ W ∈ C, ¬ W ⊆ (affineOpen i)ᶜ) (hCH' : ∀ W ∈ C, ¬ (affineOpen i)ᶜ ⊆ W) :
    affinePart i (⋃₀ C) ≠ Set.univ := by
  intro hu
  have hsub : (Set.univ : Set (ℙ k (Fin (n + 1) → k))) ⊆ ⋃₀ C := by
    rw [← projectiveClosure_affinePart_sUnion hC hCW hCH, hu, projectiveClosure_univ]
  have hp : (vanishingIdeal (Set.univ : Set (ℙ k (Fin (n + 1) → k)))).toIdeal.IsPrime := by
    rw [vanishingIdeal_univ, HomogeneousIdeal.toIdeal_bot]
    exact Ideal.isPrime_bot
  obtain ⟨W, hWC, hW⟩ := exists_subset_of_subset_sUnion hp hC (fun W hW ↦ (hCW W hW).1) hsub
  exact hCH' W hWC ((Set.subset_univ _).trans hW)

/-! ### The correspondence -/

variable (i) in
/-- **Affine and projective varieties.** `V ↦ V*` is a bijection from the affine varieties in
`𝔸ⁿ` to the projective varieties in `ℙⁿ` not contained in the hyperplane at infinity
`(affineOpen i)ᶜ`, with inverse `W ↦ W_*`. -/
noncomputable def projectiveClosureEquiv :
    {V : Set (Fin n → k) // MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k V) = V ∧
      (MvPolynomial.vanishingIdeal k V).IsPrime} ≃
    {W : Set (ℙ k (Fin (n + 1) → k)) // zeroLocus (vanishingIdeal W) = W ∧
      (vanishingIdeal W).toIdeal.IsPrime ∧ ¬ W ⊆ (affineOpen i)ᶜ} where
  toFun V := ⟨projectiveClosure i V.1, projectiveClosure_zeroLocus_vanishingIdeal V.1,
    isPrime_vanishingIdeal_projectiveClosure V.2.2,
    not_projectiveClosure_subset_compl_affineOpen <| Set.nonempty_iff_ne_empty.2 fun h ↦
      V.2.2.ne_top (by rw [h, MvPolynomial.vanishingIdeal_empty])⟩
  invFun W := ⟨affinePart i W.1, zeroLocus_vanishingIdeal_affinePart W.1,
    isPrime_vanishingIdeal_affinePart W.2.1 W.2.2.1 W.2.2.2⟩
  left_inv V := Subtype.ext (affinePart_projectiveClosure V.2.1)
  right_inv W := Subtype.ext (projectiveClosure_affinePart W.2.1 W.2.2.1 W.2.2.2)

@[simp]
theorem projectiveClosureEquiv_apply
    (V : {V : Set (Fin n → k) // MvPolynomial.zeroLocus k (MvPolynomial.vanishingIdeal k V) = V ∧
      (MvPolynomial.vanishingIdeal k V).IsPrime}) :
    (projectiveClosureEquiv i V : Set (ℙ k (Fin (n + 1) → k))) = projectiveClosure i V :=
  (rfl)

@[simp]
theorem projectiveClosureEquiv_symm_apply
    (W : {W : Set (ℙ k (Fin (n + 1) → k)) // zeroLocus (vanishingIdeal W) = W ∧
      (vanishingIdeal W).toIdeal.IsPrime ∧ ¬ W ⊆ (affineOpen i)ᶜ}) :
    ((projectiveClosureEquiv i).symm W : Set (Fin n → k)) = affinePart i W :=
  (rfl)

end PlaneCurves.ProjectiveSpace

end
