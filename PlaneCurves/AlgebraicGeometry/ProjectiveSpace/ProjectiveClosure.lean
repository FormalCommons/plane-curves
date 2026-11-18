/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.ZeroLocus
public import PlaneCurves.RingTheory.MvPolynomial.Homogenize.Ideal
public import PlaneCurves.RingTheory.MvPolynomial.VanishingIdeal
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

/-- Over an infinite field, the projective closure of `𝔸ⁿ` is `ℙⁿ`. -/
@[simp]
theorem projectiveClosure_univ [Infinite k] :
    projectiveClosure i (Set.univ : Set (Fin n → k)) = Set.univ := by
  have h : MvPolynomial.vanishingIdeal k (Set.univ : Set (Fin n → k)) = ⊥ := by
    simpa using MvPolynomial.vanishingIdeal_pi_eq_bot (k := k) (K := k)
      (s := fun _ : Fin n ↦ (Set.univ : Set k)) fun _ ↦ Set.infinite_univ
  rw [projectiveClosure_def, h, Ideal.homogenization_bot, HomogeneousIdeal.coe_bot]
  exact zeroLocus_singleton_zero

end PlaneCurves.ProjectiveSpace

end
