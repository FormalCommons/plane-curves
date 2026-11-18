/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.ZeroLocus
public import PlaneCurves.RingTheory.MvPolynomial.LinearForm
public import PlaneCurves.RingTheory.MvPolynomial.VanishingIdeal

/-!
# Zero loci of linear forms in projective space

A linear subvariety of `ℙⁿ = ℙ k (Fin (n + 1) → k)` is the projectivization
`p.projectivization` of a subspace `p` of `kⁿ⁺¹`; a linear form is `∑ i, C (a i) * X i` for a
coefficient vector `a`, with functional `dotProductEquiv k (Fin (n + 1)) a`. This file shows that
the linear subvarieties are exactly the zero loci of linear forms, counts their dimension, and
shows that a nonempty linear subvariety is a projective variety.

## Main results

* `zeroLocus_image_sum_C_mul_X`: the zero locus of the linear forms with coefficients in `s` is
  the projectivization of the annihilator of `s`; `zeroLocus_singleton_sum_C_mul_X` is the case
  of one form, a hyperplane if `a ≠ 0`.
* `finrank_add_finrank_span_of_zeroLocus_eq`: `V(H₁, …, H_r)` has dimension
  `n - rank (H₁, …, H_r)`.
* `exists_finset_zeroLocus_image_sum_C_mul_X_eq`: every linear subvariety of dimension `m` is
  the zero locus of `n - m` linear forms.
* `zeroLocus_image_sum_C_mul_X_nonempty`: at most `n` linear forms have a common zero in `ℙⁿ`.
* `cone_projectivization`: the cone over `p.projectivization` is `p`.
* `isPrime_vanishingIdeal_projectivization`, `zeroLocus_vanishingIdeal_projectivization`: over
  an infinite field, the ideal of a nonempty linear subvariety is prime, and the subvariety is
  its zero locus.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §4.2, Problems 4.11–4.13
-/

public section

open MvPolynomial Module Projectivization
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PlaneCurves.ProjectiveSpace

variable {k : Type*} [Field k] {n : ℕ}

private theorem forall_isHomogeneous_image_sum_C_mul_X (s : Set (Fin (n + 1) → k)) :
    ∀ f ∈ (fun a : Fin (n + 1) → k ↦ ∑ i, C (a i) * X i) '' s, ∃ d, f.IsHomogeneous d := by
  rintro _ ⟨a, -, rfl⟩
  exact ⟨1, isHomogeneous_sum_C_mul_X a⟩

/-- The zero locus of the linear forms with coefficient vectors in `s` is the projectivization of
the subspace annihilated by the functionals `v ↦ a ⬝ᵥ v`, `a ∈ s`. -/
theorem zeroLocus_image_sum_C_mul_X (s : Set (Fin (n + 1) → k)) :
    zeroLocus ((fun a : Fin (n + 1) → k ↦ ∑ i, C (a i) * X i) '' s) =
      ((Submodule.span k s).map
        (dotProductEquiv k (Fin (n + 1))).toLinearMap).dualCoannihilator.projectivization := by
  ext P
  induction P using Projectivization.ind with | h v hv =>
  rw [mk_mem_zeroLocus_iff (forall_isHomogeneous_image_sum_C_mul_X s), SetLike.mem_coe,
    Submodule.mk_mem_projectivization_iff, Submodule.mem_dualCoannihilator]
  simp only [Set.forall_mem_image, eval_sum_C_mul_X, Submodule.mem_map, LinearEquiv.coe_coe,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, dotProductEquiv_apply_apply]
  refine ⟨fun h a ha ↦ ?_, fun h a ha ↦ h a (Submodule.subset_span ha)⟩
  induction ha using Submodule.span_induction with
  | mem a ha => exact h ha
  | zero => simp
  | add a b _ _ ha hb => simp [add_dotProduct, ha, hb]
  | smul c a _ ha => simp [smul_dotProduct, ha]

/-- The zero locus of one linear form is the projectivization of the kernel of its functional;
for `a ≠ 0` it is a hyperplane. -/
theorem zeroLocus_singleton_sum_C_mul_X (a : Fin (n + 1) → k) :
    zeroLocus {∑ i, C (a i) * X i} =
      (LinearMap.ker (dotProductEquiv k (Fin (n + 1)) a)).projectivization := by
  ext P
  induction P using Projectivization.ind with | h v hv =>
  rw [mk_mem_zeroLocus_iff (by simpa using ⟨1, isHomogeneous_sum_C_mul_X a⟩), SetLike.mem_coe,
    Submodule.mk_mem_projectivization_iff]
  simp [dotProduct]

/-- **Dimension of a linear subvariety in equations.** If the zero locus of the linear forms with
coefficients in `s` is `p.projectivization`, then `dim p + rank s = n + 1`: the zero locus of
`H₁, …, H_r` has dimension `n - rank (H₁, …, H_r)`. -/
theorem finrank_add_finrank_span_of_zeroLocus_eq {s : Set (Fin (n + 1) → k)}
    {p : Submodule k (Fin (n + 1) → k)}
    (h : zeroLocus ((fun a : Fin (n + 1) → k ↦ ∑ i, C (a i) * X i) '' s) = p.projectivization) :
    finrank k p + finrank k (Submodule.span k s) = n + 1 := by
  set W := (Submodule.span k s).map (dotProductEquiv k (Fin (n + 1))).toLinearMap
  have hp : W.dualCoannihilator = p := by
    rw [zeroLocus_image_sum_C_mul_X] at h
    exact Submodule.projectivization.injective (SetLike.coe_injective h)
  have := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  rw [hp, LinearEquiv.finrank_map_eq, finrank_fin_fun] at this
  omega

/-- **Linear subvarieties are zero loci of linear forms.** For every subspace `p` of `kⁿ⁺¹`
there is a set `s` of
`n + 1 - dim p` coefficient vectors whose linear forms have zero locus `p.projectivization`. -/
theorem exists_finset_zeroLocus_image_sum_C_mul_X_eq (p : Submodule k (Fin (n + 1) → k)) :
    ∃ s : Finset (Fin (n + 1) → k), s.card + finrank k p = n + 1 ∧
      zeroLocus ((fun a : Fin (n + 1) → k ↦ ∑ i, C (a i) * X i) '' ↑s) = p.projectivization := by
  classical
  set D := dotProductEquiv k (Fin (n + 1))
  set B := p.dualAnnihilator.comap D.toLinearMap
  have hB : B.map D.toLinearMap = p.dualAnnihilator :=
    Submodule.map_comap_eq_of_surjective D.surjective _
  set b := Module.finBasis k B
  set f : Fin (finrank k B) → Fin (n + 1) → k := fun i ↦ b i
  have hf : Function.Injective f := Subtype.val_injective.comp b.injective
  have hspan : Submodule.span k (Set.range f) = B := by
    rw [show f = B.subtype ∘ b from rfl, Set.range_comp, Submodule.span_image, b.span_eq,
      Submodule.map_subtype_top]
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin,
      ← LinearEquiv.finrank_map_eq D B, hB, add_comm,
      Subspace.finrank_add_finrank_dualAnnihilator_eq, finrank_fin_fun]
  · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, zeroLocus_image_sum_C_mul_X, hspan,
      hB, Subspace.dualAnnihilator_dualCoannihilator_eq]

/-- **At most `n` hyperplanes meet in `ℙⁿ`.** At most `n` linear forms in `n + 1` variables have
a common zero in `ℙⁿ`. -/
theorem zeroLocus_image_sum_C_mul_X_nonempty (s : Finset (Fin (n + 1) → k)) (h : s.card ≤ n) :
    (zeroLocus ((fun a : Fin (n + 1) → k ↦ ∑ i, C (a i) * X i) '' ↑s)).Nonempty := by
  set W := (Submodule.span k (s : Set (Fin (n + 1) → k))).map
    (dotProductEquiv k (Fin (n + 1))).toLinearMap
  have hW : finrank k W ≤ n := by
    rw [LinearEquiv.finrank_map_eq]
    exact (finrank_span_finset_le_card s).trans h
  have hne : W.dualCoannihilator ≠ ⊥ := by
    intro hbot
    have := Subspace.finrank_add_finrank_dualCoannihilator_eq W
    rw [hbot, finrank_bot, finrank_fin_fun] at this
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨mk k v hv0, by rw [zeroLocus_image_sum_C_mul_X]; exact hv⟩

/-- The affine cone over the linear subvariety `p.projectivization` is the subspace `p`. -/
@[simp]
theorem cone_projectivization (p : Submodule k (Fin (n + 1) → k)) :
    cone (p.projectivization : Set (ℙ k (Fin (n + 1) → k))) = p := by
  ext v
  by_cases hv : v = 0
  · simp [hv]
  · rw [mem_cone_iff_of_ne_zero hv, SetLike.mem_coe, SetLike.mem_coe,
      Submodule.mk_mem_projectivization_iff]

/-- A linear subvariety is the zero locus of its homogeneous ideal. -/
@[simp]
theorem zeroLocus_vanishingIdeal_projectivization (p : Submodule k (Fin (n + 1) → k)) :
    zeroLocus (vanishingIdeal (p.projectivization : Set (ℙ k (Fin (n + 1) → k))) :
      Set (MvPolynomial (Fin (n + 1)) k)) = p.projectivization := by
  refine (subset_zeroLocus_vanishingIdeal _).antisymm' ?_
  obtain ⟨s, -, hs⟩ := exists_finset_zeroLocus_image_sum_C_mul_X_eq p
  refine (zeroLocus_anti_mono ?_).trans hs.le
  rintro _ ⟨a, ha, rfl⟩
  beta_reduce
  rw [SetLike.mem_coe,
    mem_vanishingIdeal_iff_of_isHomogeneous (isHomogeneous_sum_C_mul_X a)]
  intro P hP
  rw [← hs] at hP
  exact (mem_zeroLocus_iff_eval_rep (forall_isHomogeneous_image_sum_C_mul_X _)).1 hP _
    ⟨a, ha, rfl⟩

/-- **Linear subvarieties are varieties.** Over an infinite field, the homogeneous ideal of a
nonempty linear subvariety is prime. -/
theorem isPrime_vanishingIdeal_projectivization [Infinite k] {p : Submodule k (Fin (n + 1) → k)}
    (hp : p ≠ ⊥) :
    (vanishingIdeal (p.projectivization : Set (ℙ k (Fin (n + 1) → k)))).toIdeal.IsPrime := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp
  rw [← vanishingIdeal_cone ⟨mk k v hv0, hv⟩, cone_projectivization]
  exact isPrime_vanishingIdeal_submodule p

end PlaneCurves.ProjectiveSpace

end
