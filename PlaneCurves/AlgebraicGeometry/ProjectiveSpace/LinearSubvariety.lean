/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Projectivization.Constructions
public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import PlaneCurves.LinearAlgebra.Projectivization.LinearSubspace
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.ZeroLocus
public import PlaneCurves.RingTheory.MvPolynomial.LinearForm
public import PlaneCurves.RingTheory.MvPolynomial.VanishingIdeal

/-!
# Zero loci of linear forms in projective space

A linear subvariety of `ℙⁿ = ℙ k (Fin (n + 1) → k)` is the projectivization
`p.projectivization` of a subspace `p` of `kⁿ⁺¹`; a linear form is `∑ i, C (a i) * X i` for a
coefficient vector `a`, with functional `dotProductEquiv k (Fin (n + 1)) a`. This file shows that
the linear subvarieties are exactly the zero loci of linear forms, counts their dimension, and
shows that a nonempty linear subvariety is a projective variety. It then states changes of
coordinates, general position and the lines of the plane in equations.

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
* `exists_mulVecLin_map_eq_of_independent`, `exists_mulVecLin_map_eq`: a matrix change of
  coordinates moves independent points, or one point, to any others.
* `independent_iff_forall_not_subset_zeroLocus`: `n + 1` points are independent iff they are not
  on a hyperplane.
* `exists_linearSubst_sum_C_mul_X_eq_X`, `exists_preimage_map_zeroLocus_eq`: independent linear
  forms can be made coordinates, and every linear subvariety of dimension `m` is carried to
  `V(X (m + 1), …, X n)`; `map_mk_single_eq_of_linearSubst_sum_C_mul_X_eq_X`: where such a change
  of coordinates sends the coordinate points.
* `exists_sum_C_mul_X_forall_notMem_zeroLocus`,
  `exists_sum_C_mul_X_mem_zeroLocus_forall_notMem_zeroLocus`,
  `exists_sum_C_mul_X_mem_zeroLocus_notMem_zeroLocus`, `setOf_mem_zeroLocus_sum_C_mul_X`:
  hyperplanes missing finitely many points, one through a point missing another, and the
  hyperplanes through a point.
* `exists_eval_rep_ne_zero_notMem`: over an infinite field, a point off a hypersurface and off
  a finite set.
* `exists_isHomogeneous_eval_rep_ne_zero_forall_eval_rep_eq_zero`: a form vanishing on a finite
  set and not at a point outside it.
* `linearIndependent_rep_of_dotProduct`: two distinct hyperplanes through a point and one missing
  it are independent.
* `zeroLocus_singleton_sum_C_mul_X_crossProduct`, `zeroLocus_pair_sum_C_mul_X`,
  `single_one_mem_zeroLocus_sum_C_mul_X_iff`: in `ℙ²`, the line through two points, the point
  of two lines, and the lines through `[0 : 1 : 0]`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §4.2, Problems 4.11–4.15, 4.24 and 4.25
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
  rw [mk_mem_zeroLocus_singleton_iff (isHomogeneous_sum_C_mul_X a), SetLike.mem_coe,
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
there is a set `s` of `n + 1 - dim p` coefficient vectors whose linear forms have zero locus
`p.projectivization`. -/
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

/-! ### Coordinates -/

/-- A point lies on the hyperplane `V(∑ i, a i X i)` iff `a ⬝ᵥ P.rep = 0`. -/
theorem mem_zeroLocus_singleton_sum_C_mul_X_iff (a : Fin (n + 1) → k)
    (P : ℙ k (Fin (n + 1) → k)) :
    P ∈ zeroLocus {∑ i, C (a i) * X i} ↔ a ⬝ᵥ P.rep = 0 := by
  rw [mem_zeroLocus_singleton_iff (isHomogeneous_sum_C_mul_X a)]
  simp [dotProduct]

/-- A linear equivalence of `kⁿ⁺¹`, as a change of coordinates of `ℙⁿ`, is the map of a
matrix. -/
private theorem exists_mulVecLin_map_eq_linearEquiv
    (e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k)) :
    ∃ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hM : Function.Injective M.mulVecLin),
      ∀ x, map M.mulVecLin hM x = map (e : (Fin (n + 1) → k) →ₗ[k] Fin (n + 1) → k)
        e.injective x := by
  have h : (LinearMap.toMatrix' e.toLinearMap).mulVecLin = e.toLinearMap :=
    Matrix.toLin'_toMatrix' _
  exact ⟨_, by rw [h]; exact e.injective, fun x ↦ by congr⟩

/-- **Moving independent points in coordinates.** Two finite families of independent points of
`ℙⁿ` differ by a change of coordinates given by an invertible matrix. -/
theorem exists_mulVecLin_map_eq_of_independent {ι : Type*} [Finite ι]
    {p q : ι → ℙ k (Fin (n + 1) → k)} (hp : Independent p) (hq : Independent q) :
    ∃ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hM : Function.Injective M.mulVecLin),
      ∀ i, map M.mulVecLin hM (p i) = q i := by
  obtain ⟨e, he⟩ := exists_linearEquiv_map_eq_of_independent hp hq
  obtain ⟨M, hM, hMe⟩ := exists_mulVecLin_map_eq_linearEquiv e
  exact ⟨M, hM, fun i ↦ (hMe _).trans (he i)⟩

/-- **Moving a point in coordinates.** Any point of `ℙⁿ` is carried to any other by a change of
coordinates given by an invertible matrix. -/
theorem exists_mulVecLin_map_eq (P Q : ℙ k (Fin (n + 1) → k)) :
    ∃ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hM : Function.Injective M.mulVecLin),
      map M.mulVecLin hM P = Q := by
  have hi : ∀ R : ℙ k (Fin (n + 1) → k), Independent fun _ : Unit ↦ R := fun R ↦
    independent_iff.mpr (linearIndependent_unique_iff.mpr R.rep_ne_zero)
  obtain ⟨M, hM, h⟩ := exists_mulVecLin_map_eq_of_independent (hi P) (hi Q)
  exact ⟨M, hM, h ()⟩

/-- **Points in general position, in equations.** `n + 1` points of `ℙⁿ` are independent iff
they do not all lie on one hyperplane `V(∑ i, a i X i)`, `a ≠ 0`. -/
theorem independent_iff_forall_not_subset_zeroLocus (p : Fin (n + 1) → ℙ k (Fin (n + 1) → k)) :
    Independent p ↔
      ∀ a : Fin (n + 1) → k, a ≠ 0 → ¬ Set.range p ⊆ zeroLocus {∑ i, C (a i) * X i} := by
  set D := dotProductEquiv k (Fin (n + 1))
  simp_rw [independent_iff_forall_dual p (by simp), Set.range_subset_iff,
    mem_zeroLocus_singleton_sum_C_mul_X_iff]
  refine ⟨fun h a ha hp ↦ ha (D.map_eq_zero_iff.mp (h (D a) fun i ↦ by simpa [D] using hp i)),
    fun h f hf ↦ ?_⟩
  by_contra hf0
  refine h (D.symm f) (by simpa using hf0) fun i ↦ ?_
  rw [← D.apply_symm_apply f] at hf
  exact hf i


/-- **Moving linear forms to coordinates.** Linearly independent linear forms
`∑ i, a j i * X i` can be carried to distinct coordinates `X (τ j)` by one change of coordinates
given by an invertible matrix. -/
theorem exists_linearSubst_sum_C_mul_X_eq_X {ι : Type*} [Finite ι] {a : ι → Fin (n + 1) → k}
    (ha : LinearIndependent k a) {τ : ι → Fin (n + 1)} (hτ : Function.Injective τ) :
    ∃ M : Matrix (Fin (n + 1)) (Fin (n + 1)) k, Function.Injective M.mulVecLin ∧
      ∀ j, linearSubst M (∑ i, C (a j i) * X i) = X (τ j) := by
  classical
  obtain ⟨e, he⟩ := ha.exists_linearEquiv_apply_eq
    ((Pi.basisFun k (Fin (n + 1))).linearIndependent.comp τ hτ)
  set N := LinearMap.toMatrix' e.toLinearMap
  have hN : Function.Injective N.mulVec := by
    rw [← Matrix.coe_mulVecLin, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
    exact e.injective
  refine ⟨N.transpose, ?_, fun j ↦ ?_⟩
  · rw [Matrix.coe_mulVecLin, Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_transpose,
      ← Matrix.mulVec_injective_iff_isUnit]
    exact hN
  · rw [linearSubst_sum_C_mul_X, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
    simp [he, Pi.single_apply]

open scoped Matrix in
/-- **Where the coordinate points go.** If a change of coordinates `M` carries the linear forms
`∑ i, a j i * X i` to the coordinates `X j`, it sends the coordinate point `[eᵢ]` to every point
at which the forms with `j ≠ i` vanish. -/
theorem map_mk_single_eq_of_linearSubst_sum_C_mul_X_eq_X
    {M : Matrix (Fin (n + 1)) (Fin (n + 1)) k} (hM : Function.Injective M.mulVecLin)
    {a : Fin (n + 1) → Fin (n + 1) → k} (hMa : ∀ j, linearSubst M (∑ i, C (a j i) * X i) = X j)
    {i : Fin (n + 1)} {P : ℙ k (Fin (n + 1) → k)} (hP : ∀ j ≠ i, a j ⬝ᵥ P.rep = 0) :
    map M.mulVecLin hM (mk k (Pi.single i 1) (by simp)) = P := by
  classical
  obtain ⟨x, hx⟩ := (LinearMap.injective_iff_surjective.1 hM) P.rep
  have hcoord (j : Fin (n + 1)) : a j ⬝ᵥ P.rep = x j := by
    rw [← eval_sum_C_mul_X, ← hx, Matrix.mulVecLin_apply, ← eval_linearSubst, hMa, eval_X]
  have hxe : x = x i • Pi.single i 1 := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj, ← hcoord, hP j hj]
  have hxi : x i ≠ 0 := fun h0 ↦ P.rep_ne_zero (by rw [← hx, hxe, h0, zero_smul, map_zero])
  rw [map_mk]
  conv_rhs => rw [← P.mk_rep]
  rw [mk_eq_mk_iff']
  refine ⟨(x i)⁻¹, ?_⟩
  have hMx : M.mulVecLin x = x i • M.mulVecLin (Pi.single i 1) := by rw [← map_smul, ← hxe]
  rw [← hx, hMx, smul_smul, inv_mul_cancel₀ hxi, one_smul]

/-- **Normal form of a linear subvariety, in equations.** If the linear forms with coefficients
in `s` have rank `n - m`, then a change of coordinates carries their zero locus to
`V(X (m + 1), …, X n)`, the coordinate subvariety of dimension `m`. -/
theorem exists_preimage_map_zeroLocus_eq (s : Set (Fin (n + 1) → k)) {m : ℕ}
    (hm : finrank k (Submodule.span k s) + (m + 1) = n + 1) :
    ∃ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hM : Function.Injective M.mulVecLin),
      map M.mulVecLin hM ⁻¹' zeroLocus ((fun a : Fin (n + 1) → k ↦ ∑ i, C (a i) * X i) '' s) =
        zeroLocus (X '' {i : Fin (n + 1) | m < i}) := by
  obtain ⟨r, hr⟩ : ∃ r, finrank k (Submodule.span k s) = r := ⟨_, rfl⟩
  rw [hr] at hm
  let b := Module.finBasisOfFinrankEq k (Submodule.span k s) hr
  let a : Fin r → Fin (n + 1) → k := fun j ↦ b j
  have ha : LinearIndependent k a :=
    b.linearIndependent.map' (Submodule.span k s).subtype (Submodule.ker_subtype _)
  have hspan : Submodule.span k (Set.range a) = Submodule.span k s := by
    rw [show a = (Submodule.span k s).subtype ∘ b from rfl, Set.range_comp, Submodule.span_image,
      b.span_eq, Submodule.map_subtype_top]
  let τ : Fin r → Fin (n + 1) := fun j ↦ ⟨m + 1 + j, by omega⟩
  have hτ : Function.Injective τ := fun i j h ↦ by
    simp only [τ, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  have hrange : Set.range τ = {i : Fin (n + 1) | m < i} := by
    ext i
    refine ⟨?_, fun hi ↦ ⟨⟨i - (m + 1), ?_⟩, Fin.ext ?_⟩⟩
    · rintro ⟨j, rfl⟩
      simp only [Set.mem_ofPred_eq, τ]
      omega
    all_goals simp only [Set.mem_ofPred_eq, τ] at hi ⊢; omega
  obtain ⟨M, hM, hMa⟩ := exists_linearSubst_sum_C_mul_X_eq_X ha hτ
  refine ⟨M, hM, ?_⟩
  rw [zeroLocus_image_sum_C_mul_X s, ← hspan, ← zeroLocus_image_sum_C_mul_X,
    ← zeroLocus_linearSubst, ← hrange, ← Set.range_comp, ← Set.range_comp, ← Set.range_comp]
  congr 2
  funext j
  exact hMa j

/-- **A hyperplane missing finitely many points, in equations.** Over an infinite field, for
finitely many points of `ℙⁿ` there is a linear form `∑ i, a i X i`, `a ≠ 0`, vanishing at none
of them. -/
theorem exists_sum_C_mul_X_forall_notMem_zeroLocus [Infinite k]
    {S : Set (ℙ k (Fin (n + 1) → k))} (hS : S.Finite) :
    ∃ a : Fin (n + 1) → k, a ≠ 0 ∧ ∀ P ∈ S, P ∉ zeroLocus {∑ i, C (a i) * X i} := by
  set D := dotProductEquiv k (Fin (n + 1))
  obtain ⟨f, hf0, hf⟩ := exists_dual_forall_apply_rep_ne_zero hS
  refine ⟨D.symm f, by simpa using hf0, fun P hP ↦ ?_⟩
  rw [mem_zeroLocus_singleton_sum_C_mul_X_iff]
  rw [← D.apply_symm_apply f] at hf
  exact hf P hP

/-- **A hyperplane through a point missing finitely many others, in equations.** Over an infinite
field, for a point `P` of `ℙⁿ`, `n ≠ 0`, and finitely many points other than `P`, there is a
linear form `∑ i, a i X i`, `a ≠ 0`, vanishing at `P` and at none of the others. For `n = 0` and
`S = ∅` there is none: the only form vanishing at the point of `ℙ⁰` is `0`. -/
theorem exists_sum_C_mul_X_mem_zeroLocus_forall_notMem_zeroLocus [Infinite k] (hn : n ≠ 0)
    (P : ℙ k (Fin (n + 1) → k)) {S : Set (ℙ k (Fin (n + 1) → k))} (hS : S.Finite) (hP : P ∉ S) :
    ∃ a : Fin (n + 1) → k, a ≠ 0 ∧ P ∈ zeroLocus {∑ i, C (a i) * X i} ∧
      ∀ Q ∈ S, Q ∉ zeroLocus {∑ i, C (a i) * X i} := by
  set D := dotProductEquiv k (Fin (n + 1))
  obtain ⟨Q, -, hQ⟩ := exists_mem_projectivization_ne (L := ⊤)
    (by rw [finrank_top, finrank_fin_fun]; omega) P
  obtain ⟨f, hfP, hf⟩ := exists_dual_apply_rep_eq_zero_forall_ne_zero P (hS.insert Q)
    (by simpa [not_or, Ne.symm hQ] using hP)
  rw [← D.apply_symm_apply f] at hfP hf
  refine ⟨D.symm f, fun h ↦ hf Q (Set.mem_insert _ _) (by simp [h]), ?_, fun R hR ↦ ?_⟩
  · rw [mem_zeroLocus_singleton_sum_C_mul_X_iff]
    exact hfP
  · rw [mem_zeroLocus_singleton_sum_C_mul_X_iff]
    exact hf R (Set.mem_insert_of_mem _ hR)

/-- **A hyperplane through one point missing another, in equations.** Over any field, for
distinct points `P` and `Q` of `ℙⁿ` there is a linear form `∑ i, a i X i` vanishing at `P` and
not at `Q`. -/
theorem exists_sum_C_mul_X_mem_zeroLocus_notMem_zeroLocus {P Q : ℙ k (Fin (n + 1) → k)}
    (h : P ≠ Q) : ∃ a : Fin (n + 1) → k, P ∈ zeroLocus {∑ i, C (a i) * X i} ∧
      Q ∉ zeroLocus {∑ i, C (a i) * X i} := by
  set D := dotProductEquiv k (Fin (n + 1))
  have hQ : Q.rep ∉ k ∙ P.rep := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by rintro rfl; exact Q.rep_ne_zero (by simp [← hc])
    refine h (Eq.symm ?_)
    rw [← P.mk_rep, ← Q.mk_rep, mk_eq_mk_iff]
    exact ⟨Units.mk0 c hc0, hc⟩
  obtain ⟨f, hfQ, hfP⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hQ inferInstance
  have hfP' : f P.rep = 0 := by
    exact (Submodule.eq_bot_iff _).1 hfP _
      (Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self _))
  rw [← D.apply_symm_apply f] at hfP' hfQ
  refine ⟨D.symm f, ?_, ?_⟩
  · rw [mem_zeroLocus_singleton_sum_C_mul_X_iff]
    exact hfP'
  · rw [mem_zeroLocus_singleton_sum_C_mul_X_iff]
    exact hfQ

/-- **The linear forms through a point.** The coefficient vectors `a` of the linear forms
`∑ i, a i X i` vanishing at `P` form the kernel of `a ↦ P.rep ⬝ᵥ a`, a subspace of dimension `n`
of `kⁿ⁺¹`. -/
theorem setOf_mem_zeroLocus_sum_C_mul_X (P : ℙ k (Fin (n + 1) → k)) :
    {a : Fin (n + 1) → k | P ∈ zeroLocus {∑ i, C (a i) * X i}} =
      LinearMap.ker (dotProductEquiv k (Fin (n + 1)) P.rep) := by
  ext a
  simp [mem_zeroLocus_singleton_sum_C_mul_X_iff, dotProduct_comm]

/-- **A point off a hypersurface and a finite set.** Over an infinite field, for a nonzero form
`f` and finitely many points of `ℙⁿ`, `n ≠ 0`, some point is neither on `f = 0` nor among them:
otherwise the nonzero form `f · ∏_Q ℓ_Q`, with `ℓ_Q` a linear form vanishing at `Q`, would
vanish on all of `ℙⁿ`. -/
theorem exists_eval_rep_ne_zero_notMem [Infinite k] (hn : n ≠ 0)
    {f : MvPolynomial (Fin (n + 1)) k} {d : ℕ} (hf : f.IsHomogeneous d) (hf0 : f ≠ 0)
    {S : Set (ℙ k (Fin (n + 1) → k))} (hS : S.Finite) :
    ∃ P : ℙ k (Fin (n + 1) → k), eval P.rep f ≠ 0 ∧ P ∉ S := by
  classical
  choose a ha0 haQ _ using fun Q : ℙ k (Fin (n + 1) → k) ↦
    exists_sum_C_mul_X_mem_zeroLocus_forall_notMem_zeroLocus hn Q Set.finite_empty
      (Set.notMem_empty Q)
  set G := f * ∏ Q ∈ hS.toFinset, ∑ i, C (a Q i) * X i
  have hG : G.IsHomogeneous (d + ∑ _Q ∈ hS.toFinset, 1) :=
    hf.mul (IsHomogeneous.prod _ _ _ fun Q _ ↦ isHomogeneous_sum_C_mul_X (a Q))
  have hG0 : G ≠ 0 :=
    mul_ne_zero hf0 (Finset.prod_ne_zero_iff.2 fun Q _ ↦ sum_C_mul_X_ne_zero (ha0 Q))
  obtain ⟨P, -, hP⟩ : ∃ P ∈ (Set.univ : Set (ℙ k (Fin (n + 1) → k))), eval P.rep G ≠ 0 := by
    by_contra! h
    have h0 := (mem_vanishingIdeal_iff_of_isHomogeneous hG).2 h
    rw [vanishingIdeal_univ, ← HomogeneousIdeal.mem_iff, HomogeneousIdeal.toIdeal_bot,
      Ideal.mem_bot] at h0
    exact hG0 h0
  rw [map_mul, mul_ne_zero_iff, map_prod, Finset.prod_ne_zero_iff] at hP
  refine ⟨P, hP.1, fun hPS ↦ hP.2 P (hS.mem_toFinset.2 hPS) ?_⟩
  have := haQ P
  rw [mem_zeroLocus_singleton_sum_C_mul_X_iff] at this
  rwa [eval_sum_C_mul_X]

/-- **A form vanishing on a finite set and not at a point.** Over any field, for a point `P` of
`ℙⁿ` and finitely many points other than `P`, some form `G` vanishes at all of them and not at
`P`: a product of linear forms, one through each of the points and not through `P`. -/
theorem exists_isHomogeneous_eval_rep_ne_zero_forall_eval_rep_eq_zero
    (P : ℙ k (Fin (n + 1) → k)) {T : Set (ℙ k (Fin (n + 1) → k))} (hT : T.Finite)
    (hPT : P ∉ T) :
    ∃ (m : ℕ) (G : MvPolynomial (Fin (n + 1)) k), G.IsHomogeneous m ∧ eval P.rep G ≠ 0 ∧
      ∀ Q ∈ T, eval Q.rep G = 0 := by
  classical
  suffices h : ∀ T : Finset (ℙ k (Fin (n + 1) → k)), P ∉ T →
      ∃ (m : ℕ) (G : MvPolynomial (Fin (n + 1)) k), G.IsHomogeneous m ∧ eval P.rep G ≠ 0 ∧
        ∀ Q ∈ T, eval Q.rep G = 0 by
    simpa using h hT.toFinset (by simpa using hPT)
  intro T hPT
  induction T using Finset.induction_on with
  | empty => exact ⟨0, 1, isHomogeneous_one _ _, by simp, by simp⟩
  | insert Q T _ ih =>
    obtain ⟨m, G, hG, hGP, hGT⟩ := ih fun h ↦ hPT (Finset.mem_insert_of_mem h)
    have hQP : Q ≠ P := fun h ↦ hPT (h ▸ Finset.mem_insert_self Q T)
    obtain ⟨a, haQ, haP⟩ := exists_sum_C_mul_X_mem_zeroLocus_notMem_zeroLocus hQP
    rw [mem_zeroLocus_singleton_iff (isHomogeneous_sum_C_mul_X a)] at haQ haP
    refine ⟨1 + m, (∑ i, C (a i) * X i) * G, (isHomogeneous_sum_C_mul_X a).mul hG,
      by rw [eval_mul]; exact mul_ne_zero haP hGP, fun Q' hQ' ↦ ?_⟩
    rcases Finset.mem_insert.1 hQ' with rfl | hQ'
    · rw [eval_mul, haQ, zero_mul]
    · rw [eval_mul, hGT Q' hQ', mul_zero]

/-! ### The plane -/

open scoped Matrix

/-- **The line through two points, in equations.** In `ℙ²`, the line through two distinct points
`[u]` and `[v]` is the zero locus of the linear form whose coefficients are `u ⨯₃ v`. -/
theorem zeroLocus_singleton_sum_C_mul_X_crossProduct {u v : Fin 3 → k} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : mk k u hu ≠ mk k v hv) :
    zeroLocus {∑ i, C ((u ⨯₃ v) i) * X i} =
      ((mk k u hu).submodule ⊔ (mk k v hv).submodule).projectivization := by
  have hw : u ⨯₃ v ≠ 0 := mt (mk_eq_mk_iff_crossProduct_eq_zero hu hv).mpr h
  have hf : dotProductEquiv k (Fin (2 + 1)) (u ⨯₃ v) ≠ 0 := by simpa using hw
  rw [zeroLocus_singleton_sum_C_mul_X]
  refine congrArg
    (fun p : Submodule k (Fin 3 → k) ↦ (p.projectivization : Set (ℙ k (Fin 3 → k)))) ?_
  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [submodule_mk, submodule_mk, sup_le_iff, Submodule.span_singleton_le_iff_mem,
      Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.mem_ker]
    simp [dotProduct_comm _ u, dotProduct_comm _ v, dot_self_cross, dot_cross_self]
  · have := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    rw [finrank_submodule_sup h]
    rw [finrank_fin_fun] at this
    exact (Nat.succ_injective this).symm

/-- **Two lines of the plane meet in one point, in equations.** In `ℙ²`, the zero locus of two
independent linear forms with coefficients `a` and `b` is the point `[a ⨯₃ b]`. -/
theorem zeroLocus_pair_sum_C_mul_X {a b : Fin 3 → k} (h : LinearIndependent k ![a, b]) :
    zeroLocus {∑ i, C (a i) * X i, ∑ i, C (b i) * X i} =
      {mk k (a ⨯₃ b) (crossProduct_ne_zero_iff_linearIndependent.mpr h)} := by
  have hw := crossProduct_ne_zero_iff_linearIndependent.mpr h
  have h2 : finrank k (Submodule.span k {a, b}) = 2 := by
    rw [← Matrix.range_cons_cons_empty a b ![], finrank_span_eq_card h]
    simp
  have hW : finrank k ((Submodule.span k {a, b}).map
      (dotProductEquiv k (Fin 3)).toLinearMap).dualCoannihilator = 1 := by
    have := Subspace.finrank_add_finrank_dualCoannihilator_eq
      ((Submodule.span k {a, b}).map (dotProductEquiv k (Fin 3)).toLinearMap)
    rw [LinearEquiv.finrank_map_eq, h2, finrank_fin_fun] at this
    omega
  have hle : (mk k (a ⨯₃ b) hw).submodule ≤ ((Submodule.span k {a, b}).map
      (dotProductEquiv k (Fin 3)).toLinearMap).dualCoannihilator := by
    rw [submodule_mk, Submodule.span_singleton_le_iff_mem, Submodule.mem_dualCoannihilator]
    simp only [Submodule.mem_map, LinearEquiv.coe_coe, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, dotProductEquiv_apply_apply]
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      rcases hc with rfl | rfl
      · exact dot_self_cross _ _
      · exact dot_cross_self _ _
    | zero => simp
    | add c d _ _ hc hd => simp [add_dotProduct, hc, hd]
    | smul t c _ hc => simp [smul_dotProduct, hc]
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_submodule, hW])
  rw [show ({∑ i, C (a i) * X i, ∑ i, C (b i) * X i} : Set (MvPolynomial (Fin 3) k)) =
      (fun c : Fin 3 → k ↦ ∑ i, C (c i) * X i) '' {a, b} by simp,
    zeroLocus_image_sum_C_mul_X, ← heq]
  ext P
  rw [Set.mem_singleton_iff, SetLike.mem_coe, Submodule.mem_projectivization_iff_submodule_le]
  refine ⟨fun hP ↦ ?_, fun hP ↦ hP ▸ le_rfl⟩
  rw [← submodule_injective.eq_iff]
  exact Submodule.eq_of_le_of_finrank_eq hP (by rw [finrank_submodule, finrank_submodule])

/-- **Two hyperplanes through a point and a third missing it are independent.** If two distinct
hyperplanes `[c₀]`, `[c₁]` contain a point `[v]` and a third `[c₂]` does not, then the coefficient
vectors of the three are linearly independent. -/
theorem linearIndependent_rep_of_dotProduct {c₀ c₁ c₂ : ℙ k (Fin (n + 1) → k)}
    {v : Fin (n + 1) → k} (h01 : c₀ ≠ c₁) (h0 : c₀.rep ⬝ᵥ v = 0) (h1 : c₁.rep ⬝ᵥ v = 0)
    (h2 : c₂.rep ⬝ᵥ v ≠ 0) : LinearIndependent k ![c₀.rep, c₁.rep, c₂.rep] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg2 : g 2 = 0 := by
    have := congrArg (· ⬝ᵥ v) hg
    simp only [Fin.sum_univ_three, add_dotProduct, smul_dotProduct, zero_dotProduct] at this
    simpa [h0, h1, h2] using this
  obtain ⟨hg0, hg1⟩ := LinearIndependent.pair_iff.1 (linearIndependent_pair_iff_ne.2 h01)
    (g 0) (g 1) (by simpa [Fin.sum_univ_three, hg2] using hg)
  intro i
  fin_cases i
  exacts [hg0, hg1, hg2]

/-- **The lines through `[0 : 1 : 0]`.** In `ℙ²`, a linear form `∑ i, a i X i`, `a ≠ 0`, vanishes
at `[0 : 1 : 0]` iff it is a nonzero multiple of `X 0 - λ X 2` for some `λ`, or of `X 2`. -/
theorem single_one_mem_zeroLocus_sum_C_mul_X_iff (a : Fin 3 → k) (ha : a ≠ 0) :
    mk k (Pi.single 1 1) (by simp) ∈ zeroLocus {∑ i, C (a i) * X i} ↔
      (∃ c ≠ 0, ∃ l, ∑ i, C (a i) * X i = C c * (X 0 - C l * X 2)) ∨
        ∃ c ≠ 0, ∑ i, C (a i) * X i = C c * X 2 := by
  rw [mk_mem_zeroLocus_singleton_iff (isHomogeneous_sum_C_mul_X a)]
  constructor
  · intro h
    have h1 : a 1 = 0 := by simpa [Fin.sum_univ_three] using h
    by_cases h0 : a 0 = 0
    · have h2 : a 2 ≠ 0 := fun h2 ↦ ha (by ext i; fin_cases i <;> simp [h0, h1, h2])
      exact Or.inr ⟨a 2, h2, by simp [Fin.sum_univ_three, h0, h1]⟩
    · refine Or.inl ⟨a 0, h0, -(a 2 / a 0), ?_⟩
      simp only [Fin.sum_univ_three, h1, map_zero, zero_mul, add_zero, map_neg]
      rw [mul_sub, neg_mul, mul_neg, sub_neg_eq_add, ← mul_assoc, ← map_mul,
        mul_div_cancel₀ _ h0]
  · rintro (⟨c, -, l, hc⟩ | ⟨c, -, hc⟩) <;> simp [hc]


end PlaneCurves.ProjectiveSpace

end
