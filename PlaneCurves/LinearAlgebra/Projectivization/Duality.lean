/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.LinearSubvariety

/-!
# Points and hyperplanes of projective space

The points of the dual projective space `ℙ K (Dual K V)` are the hyperplanes of `ℙ K V`: a point
`φ = [f]` gives the hyperplane `hyperplane φ = ker f`, and a point `x` of `ℙ K V` gives the
hyperplane `dualHyperplane x` of the dual, the linear forms vanishing at `x` (Fulton's `P*`).
This file proves the duality between points and hyperplanes (Fulton, Problem 4.18) and moves
hyperplanes in general position (Problem 4.16), and it assembles the results on linear
subvarieties of `ℙⁿ` into one theorem.

## Main definitions

* `Projectivization.hyperplane φ`: the hyperplane of `V` of a point `φ` of `ℙ K (Dual K V)`.
* `Projectivization.dualHyperplane x`: the hyperplane of `Dual K V` of a point `x` of `ℙ K V`.
* `Projectivization.hyperplaneEquiv`: for finite-dimensional `V`, `ℙ K (Dual K V)` is in
  bijection with the subspaces of codimension one of `V`.

## Main results

* `Projectivization.mem_projectivization_hyperplane_iff_mem_projectivization_dualHyperplane`,
  `Projectivization.mem_projectivization_iff_hyperplaneEquiv_symm_mem`: `P ∈ H` iff `H* ∈ P*`.
* `Projectivization.hyperplaneEquiv_symm_dualHyperplane`,
  `Projectivization.dualHyperplane_hyperplaneEquiv_symm`: `P** = P` and `H** = H`, identifying
  `V` with its double dual.
* `Projectivization.independent_iff_iInter_hyperplane_eq_empty`: `n + 1` points of the dual are
  independent iff their hyperplanes have no common point.
* `Projectivization.exists_linearEquiv_image_map_hyperplane_eq`,
  `PlaneCurves.ProjectiveSpace.exists_linearEquiv_image_map_zeroLocus_sum_C_mul_X_eq`: a change
  of coordinates carries `n + 1` hyperplanes with no common point to any other such hyperplanes.
* `PlaneCurves.ProjectiveSpace.zeroLocus_singleton_sum_C_mul_X_eq_iff`,
  `PlaneCurves.ProjectiveSpace.finrank_add_one_eq_iff_exists_zeroLocus_singleton_sum_C_mul_X_eq`:
  `V(∑ i, a i X i) ↦ [a]` is a bijection from the hyperplanes of `ℙⁿ` onto `ℙⁿ`.
* `PlaneCurves.ProjectiveSpace.linearSubvariety_changeOfCoordinates_duality`: linear
  subvarieties and projective changes of coordinates in `ℙⁿ`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §4.2, Problems 4.11–4.16 and 4.18; §4.3,
  Problems 4.24 and 4.25
-/

public section

open Module
open scoped LinearAlgebra.Projectivization

namespace Module.Dual

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- `finrank K V` linear forms with no common zero other than `0` can be carried to any other
such family by a change of coordinates: some linear automorphism `e` of `V` has
`g i ∘ e = f i` for all `i`. -/
theorem exists_linearEquiv_comp_eq [FiniteDimensional K V] {ι : Type*} [Fintype ι]
    (hι : Fintype.card ι = finrank K V) {f g : ι → Dual K V}
    (hf : ∀ v, (∀ i, f i v = 0) → v = 0) (hg : ∀ v, (∀ i, g i v = 0) → v = 0) :
    ∃ e : V ≃ₗ[K] V, ∀ i, (g i).comp (e : V →ₗ[K] V) = f i := by
  have hdim : finrank K V = finrank K (ι → K) := by rw [finrank_fintype_fun_eq_card, hι]
  have hinj : ∀ h : ι → Dual K V, (∀ v, (∀ i, h i v = 0) → v = 0) →
      Function.Injective (LinearMap.pi h) := fun h hh ↦ by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    exact fun v hv ↦ hh v fun i ↦ congr_fun (LinearMap.mem_ker.mp hv) i
  let Φf := LinearMap.linearEquivOfInjective _ (hinj f hf) hdim
  let Φg := LinearMap.linearEquivOfInjective _ (hinj g hg) hdim
  refine ⟨Φf.trans Φg.symm, fun i ↦ LinearMap.ext fun v ↦ ?_⟩
  have h1 : ∀ w, Φg w i = g i w := fun w ↦ rfl
  have h2 : Φf v i = f i v := rfl
  change g i (Φg.symm (Φf v)) = f i v
  rw [← h1, Φg.apply_symm_apply, h2]

end Module.Dual

namespace Projectivization

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-! ### The hyperplane of a point of the dual space -/

/-- The hyperplane of `V` given by a point `φ = [f]` of the dual projective space
`ℙ K (Dual K V)`: the subspace annihilated by the line of `φ`, that is, the kernel of `f`. -/
def hyperplane (φ : ℙ K (Dual K V)) : Submodule K V :=
  φ.submodule.dualCoannihilator

theorem hyperplane_def (φ : ℙ K (Dual K V)) : hyperplane φ = φ.submodule.dualCoannihilator :=
  (rfl)

/-- The hyperplane of `φ` is the kernel of any representative of `φ`. -/
theorem hyperplane_eq_ker (φ : ℙ K (Dual K V)) : hyperplane φ = LinearMap.ker φ.rep := by
  ext v
  simp only [hyperplane_def, submodule_eq, Submodule.mem_dualCoannihilator,
    Submodule.mem_span_singleton, forall_exists_index, forall_apply_eq_imp_iff,
    LinearMap.smul_apply, smul_eq_mul, LinearMap.mem_ker]
  exact ⟨fun h ↦ by simpa using h 1, fun h a ↦ by simp [h]⟩

@[simp]
theorem hyperplane_mk (f : Dual K V) (hf : f ≠ 0) : hyperplane (mk K f hf) = LinearMap.ker f := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep K f hf
  rw [hyperplane_eq_ker, ← ha, Units.smul_def, LinearMap.ker_smul _ _ a.ne_zero]

theorem mem_hyperplane_iff (φ : ℙ K (Dual K V)) (v : V) : v ∈ hyperplane φ ↔ φ.rep v = 0 := by
  rw [hyperplane_eq_ker, LinearMap.mem_ker]

/-- A point `x` of `ℙ K V` lies on the hyperplane of `φ` iff `φ.rep x.rep = 0`. -/
theorem mem_projectivization_hyperplane_iff (φ : ℙ K (Dual K V)) (x : ℙ K V) :
    x ∈ (hyperplane φ).projectivization ↔ φ.rep x.rep = 0 := by
  rw [← mk_rep x, Submodule.mk_mem_projectivization_iff, mk_rep, mem_hyperplane_iff]

/-- The hyperplane of a point of the dual has codimension one. -/
theorem finrank_hyperplane_add_one [FiniteDimensional K V] (φ : ℙ K (Dual K V)) :
    finrank K (hyperplane φ) + 1 = finrank K V := by
  have := Subspace.finrank_add_finrank_dualCoannihilator_eq φ.submodule
  rw [finrank_submodule] at this
  rw [hyperplane_def]
  omega

theorem hyperplane_injective [FiniteDimensional K V] :
    Function.Injective (hyperplane (K := K) (V := V)) := fun φ ψ h ↦ by
  rw [hyperplane_def, hyperplane_def] at h
  apply submodule_injective
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := φ.submodule),
    ← Subspace.dualCoannihilator_dualAnnihilator_eq (W := ψ.submodule), h]

/-! ### The dual hyperplane of a point -/

/-- The hyperplane of the dual space `Dual K V` given by a point `x` of `ℙ K V`: the linear forms
that vanish at `x`. This is Fulton's `P*`. -/
def dualHyperplane (x : ℙ K V) : Submodule K (Dual K V) :=
  x.submodule.dualAnnihilator

theorem dualHyperplane_def (x : ℙ K V) : dualHyperplane x = x.submodule.dualAnnihilator :=
  (rfl)

theorem mem_dualHyperplane_iff (x : ℙ K V) (f : Dual K V) :
    f ∈ dualHyperplane x ↔ f x.rep = 0 := by
  rw [dualHyperplane_def, submodule_eq, Submodule.mem_dualAnnihilator]
  refine ⟨fun h ↦ h _ (Submodule.mem_span_singleton_self _), fun h w hw ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  simp [h]

@[simp]
theorem dualHyperplane_mk (v : V) (hv : v ≠ 0) :
    dualHyperplane (mk K v hv) = LinearMap.ker (Dual.eval K V v) := by
  ext f
  rw [mem_dualHyperplane_iff, LinearMap.mem_ker, Dual.eval_apply]
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep K v hv
  rw [← ha, Units.smul_def, map_smul, smul_eq_mul, mul_eq_zero, or_iff_right a.ne_zero]

/-- A point `φ` of the dual lies on the dual hyperplane of `x` iff `φ.rep x.rep = 0`. -/
theorem mem_projectivization_dualHyperplane_iff (x : ℙ K V) (φ : ℙ K (Dual K V)) :
    φ ∈ (dualHyperplane x).projectivization ↔ φ.rep x.rep = 0 := by
  rw [← mk_rep φ, Submodule.mk_mem_projectivization_iff, mk_rep, mem_dualHyperplane_iff]

/-- The dual hyperplane of a point has codimension one in the dual. -/
theorem finrank_dualHyperplane_add_one [FiniteDimensional K V] (x : ℙ K V) :
    finrank K (dualHyperplane x) + 1 = finrank K (Dual K V) := by
  have := Subspace.finrank_add_finrank_dualAnnihilator_eq x.submodule
  rw [finrank_submodule] at this
  rw [dualHyperplane_def, Subspace.dual_finrank_eq]
  omega

theorem dualHyperplane_injective [FiniteDimensional K V] :
    Function.Injective (dualHyperplane (K := K) (V := V)) := fun _ _ h ↦
  submodule_injective (Subspace.dualAnnihilator_inj.mp h)

/-- **Incidence is symmetric.** A point `x` lies on the hyperplane of `φ` iff `φ` lies on the
dual hyperplane of `x`: `P ∈ H` iff `H* ∈ P*`. -/
theorem mem_projectivization_hyperplane_iff_mem_projectivization_dualHyperplane (x : ℙ K V)
    (φ : ℙ K (Dual K V)) :
    x ∈ (hyperplane φ).projectivization ↔ φ ∈ (dualHyperplane x).projectivization := by
  rw [mem_projectivization_hyperplane_iff, mem_projectivization_dualHyperplane_iff]

/-- Under the identification of `V` with its double dual, the hyperplane of the point of the
double dual given by `x` is the dual hyperplane of `x`. -/
theorem hyperplane_map_evalEquiv [FiniteDimensional K V] (x : ℙ K V) :
    hyperplane (map (evalEquiv K V).toLinearMap (evalEquiv K V).injective x) =
      dualHyperplane x := by
  ext f
  rw [hyperplane_def, submodule_map, dualHyperplane_def, Submodule.mem_dualCoannihilator,
    Submodule.mem_dualAnnihilator]
  simp

/-- Under the identification of `V` with its double dual, the dual hyperplane of a point `φ` of
`ℙ K (Dual K V)` is the image of the hyperplane of `φ`. -/
theorem dualHyperplane_eq_map_hyperplane [FiniteDimensional K V] (φ : ℙ K (Dual K V)) :
    dualHyperplane φ = (hyperplane φ).map (evalEquiv K V).toLinearMap := by
  rw [dualHyperplane_def, hyperplane_def, evalEquiv_toLinearMap,
    Subspace.map_dualCoannihilator]

/-! ### Hyperplanes are the points of the dual -/

/-- **Hyperplanes are the points of the dual projective space.** For finite-dimensional `V`, the
map `φ ↦ hyperplane φ` is a bijection from `ℙ K (Dual K V)` onto the subspaces of codimension
one of `V`; its inverse sends a hyperplane `H` to the point of the dual whose line is the
annihilator of `H`, Fulton's `H*`. -/
noncomputable def hyperplaneEquiv [FiniteDimensional K V] :
    ℙ K (Dual K V) ≃ {H : Submodule K V // finrank K H + 1 = finrank K V} where
  toFun φ := ⟨hyperplane φ, finrank_hyperplane_add_one φ⟩
  invFun H := mk'' H.1.dualAnnihilator <| by
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq H.1
    have := H.2
    omega
  left_inv φ := by
    apply submodule_injective
    dsimp only
    rw [submodule_mk'', hyperplane_def, Subspace.dualCoannihilator_dualAnnihilator_eq]
  right_inv H := Subtype.ext <| by
    dsimp only
    rw [hyperplane_def, submodule_mk'', Subspace.dualAnnihilator_dualCoannihilator_eq]

@[simp]
theorem coe_hyperplaneEquiv_apply [FiniteDimensional K V] (φ : ℙ K (Dual K V)) :
    (hyperplaneEquiv φ : Submodule K V) = hyperplane φ :=
  (rfl)

/-- The line of the point `H*` of the dual is the annihilator of `H`. -/
@[simp]
theorem submodule_hyperplaneEquiv_symm_apply [FiniteDimensional K V]
    (H : {H : Submodule K V // finrank K H + 1 = finrank K V}) :
    (hyperplaneEquiv.symm H).submodule = H.1.dualAnnihilator :=
  submodule_mk'' _ _

@[simp]
theorem hyperplane_hyperplaneEquiv_symm_apply [FiniteDimensional K V]
    (H : {H : Submodule K V // finrank K H + 1 = finrank K V}) :
    hyperplane (hyperplaneEquiv.symm H) = H := by
  rw [← coe_hyperplaneEquiv_apply, Equiv.apply_symm_apply]

/-- The point of the dual of the hyperplane `ker f` is `[f]`. -/
theorem hyperplaneEquiv_symm_ker [FiniteDimensional K V] (f : Dual K V) (hf : f ≠ 0)
    (h : finrank K (LinearMap.ker f) + 1 = finrank K V) :
    hyperplaneEquiv.symm ⟨LinearMap.ker f, h⟩ = mk K f hf := by
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext (hyperplane_mk f hf).symm

/-- **`P** = P`.** The point of `ℙ K (Dual K (Dual K V))` of the dual hyperplane `P*` of a
point `P` of `ℙ K V` is `P`, under the identification of `V` with its double dual. -/
theorem hyperplaneEquiv_symm_dualHyperplane [FiniteDimensional K V] (x : ℙ K V) :
    hyperplaneEquiv.symm ⟨dualHyperplane x, finrank_dualHyperplane_add_one x⟩ =
      map (evalEquiv K V).toLinearMap (evalEquiv K V).injective x := by
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext (hyperplane_map_evalEquiv x).symm

/-- **`H** = H`.** The dual hyperplane of the point `H*` of the dual of a hyperplane `H` of `V`
is `H`, under the identification of `V` with its double dual. -/
theorem dualHyperplane_hyperplaneEquiv_symm [FiniteDimensional K V]
    (H : {H : Submodule K V // finrank K H + 1 = finrank K V}) :
    dualHyperplane (hyperplaneEquiv.symm H) = H.1.map (evalEquiv K V).toLinearMap := by
  rw [dualHyperplane_eq_map_hyperplane, hyperplane_hyperplaneEquiv_symm_apply]

/-- **`P ∈ H` iff `H* ∈ P*`.** A point `x` lies on a hyperplane `H` iff the point `H*` of the
dual lies on the dual hyperplane `x*`. -/
theorem mem_projectivization_iff_hyperplaneEquiv_symm_mem [FiniteDimensional K V] (x : ℙ K V)
    (H : {H : Submodule K V // finrank K H + 1 = finrank K V}) :
    x ∈ H.1.projectivization ↔ hyperplaneEquiv.symm H ∈ (dualHyperplane x).projectivization := by
  conv_lhs => rw [← hyperplane_hyperplaneEquiv_symm_apply H]
  exact mem_projectivization_hyperplane_iff_mem_projectivization_dualHyperplane _ _

/-! ### Frames of hyperplanes -/

/-- **Hyperplanes in general position.** In a space of dimension `n + 1`, `n + 1` points of the
dual are independent iff their hyperplanes have no common point. -/
theorem independent_iff_iInter_hyperplane_eq_empty [FiniteDimensional K V] {ι : Type*}
    [Fintype ι] (φ : ι → ℙ K (Dual K V)) (hι : Fintype.card ι = finrank K V) :
    Independent φ ↔ ⋂ i, ((hyperplane (φ i)).projectivization : Set (ℙ K V)) = ∅ := by
  rw [independent_iff_forall_dual φ (by rw [hι, Subspace.dual_finrank_eq]),
    Set.eq_empty_iff_forall_notMem]
  simp only [Set.mem_iInter, SetLike.mem_coe, mem_projectivization_hyperplane_iff]
  constructor
  · intro h x hx
    have := h (evalEquiv K V x.rep) fun i ↦ by simpa using hx i
    exact x.rep_ne_zero ((evalEquiv K V).map_eq_zero_iff.mp this)
  · intro h F hF
    by_contra hF0
    obtain ⟨v, rfl⟩ := (evalEquiv K V).surjective F
    have hv : v ≠ 0 := fun hv ↦ hF0 (by simp [hv])
    refine h (mk K v hv) fun i ↦ ?_
    obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep K v hv
    have := hF i
    simp only [evalEquiv_apply, Dual.eval_apply] at this
    rw [← ha, Units.smul_def, map_smul, this, smul_zero]

/-- **Moving hyperplanes in general position.** In a space of dimension `n + 1`, given two
families of `n + 1` hyperplanes, each with no common point, some change of coordinates carries
each hyperplane of the first family onto the corresponding one of the second. -/
theorem exists_linearEquiv_image_map_hyperplane_eq [FiniteDimensional K V] {ι : Type*}
    [Fintype ι] (hι : Fintype.card ι = finrank K V) {φ ψ : ι → ℙ K (Dual K V)}
    (hφ : ⋂ i, ((hyperplane (φ i)).projectivization : Set (ℙ K V)) = ∅)
    (hψ : ⋂ i, ((hyperplane (ψ i)).projectivization : Set (ℙ K V)) = ∅) :
    ∃ e : V ≃ₗ[K] V, ∀ i, map (e : V →ₗ[K] V) e.injective ''
      ((hyperplane (φ i)).projectivization : Set (ℙ K V)) = (hyperplane (ψ i)).projectivization
    := by
  have key : ∀ χ : ι → ℙ K (Dual K V),
      ⋂ i, ((hyperplane (χ i)).projectivization : Set (ℙ K V)) = ∅ →
        ∀ v, (∀ i, (χ i).rep v = 0) → v = 0 := fun χ hχ v hv ↦ by
    by_contra hv0
    refine (Set.eq_empty_iff_forall_notMem.mp hχ) (mk K v hv0) (Set.mem_iInter.mpr fun i ↦ ?_)
    rw [SetLike.mem_coe, Submodule.mk_mem_projectivization_iff, mem_hyperplane_iff]
    exact hv i
  obtain ⟨e, he⟩ := Module.Dual.exists_linearEquiv_comp_eq hι (key φ hφ) (key ψ hψ)
  refine ⟨e, fun i ↦ ?_⟩
  rw [Submodule.image_map_projectivization, hyperplane_eq_ker, hyperplane_eq_ker, ← he i,
    LinearMap.ker_comp, Submodule.map_comap_eq_of_surjective e.surjective]

end Projectivization

namespace PlaneCurves.ProjectiveSpace

open MvPolynomial Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {n : ℕ}

/-- **Moving hyperplanes in general position, in equations.** Given two families of `n + 1`
linear forms `∑ j, a i j X j` and `∑ j, b i j X j` on `ℙⁿ`, each family with no common zero,
some change of coordinates carries each hyperplane `V(∑ j, a i j X j)` onto
`V(∑ j, b i j X j)`. -/
theorem exists_linearEquiv_image_map_zeroLocus_sum_C_mul_X_eq
    {a b : Fin (n + 1) → Fin (n + 1) → k}
    (ha : ⋂ i, zeroLocus {∑ j, C (a i j) * X j} = ∅)
    (hb : ⋂ i, zeroLocus {∑ j, C (b i j) * X j} = ∅) :
    ∃ e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k), ∀ i,
      map (e : (Fin (n + 1) → k) →ₗ[k] Fin (n + 1) → k) e.injective ''
        zeroLocus {∑ j, C (a i j) * X j} = zeroLocus {∑ j, C (b i j) * X j} := by
  set D := dotProductEquiv k (Fin (n + 1))
  have key : ∀ c : Fin (n + 1) → Fin (n + 1) → k,
      ⋂ i, zeroLocus {∑ j, C (c i j) * X j} = ∅ → ∀ v, (∀ i, D (c i) v = 0) → v = 0 :=
    fun c hc v hv ↦ by
      by_contra hv0
      refine (Set.eq_empty_iff_forall_notMem.mp hc) (mk k v hv0) (Set.mem_iInter.mpr fun i ↦ ?_)
      rw [zeroLocus_singleton_sum_C_mul_X, SetLike.mem_coe, Submodule.mk_mem_projectivization_iff]
      exact hv i
  obtain ⟨e, he⟩ := Module.Dual.exists_linearEquiv_comp_eq (by simp) (key a ha) (key b hb)
  refine ⟨e, fun i ↦ ?_⟩
  rw [zeroLocus_singleton_sum_C_mul_X, zeroLocus_singleton_sum_C_mul_X,
    Submodule.image_map_projectivization, ← he i, LinearMap.ker_comp,
    Submodule.map_comap_eq_of_surjective e.surjective]

/-- **The hyperplane `V(∑ i, a i X i)` determines `[a]`.** For nonzero coefficient vectors, the
hyperplanes `V(∑ i, a i X i)` and `V(∑ i, b i X i)` agree iff `[a] = [b]`. -/
theorem zeroLocus_singleton_sum_C_mul_X_eq_iff {a b : Fin (n + 1) → k} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    zeroLocus {∑ i, C (a i) * X i} = zeroLocus {∑ i, C (b i) * X i} ↔ mk k a ha = mk k b hb := by
  set D := dotProductEquiv k (Fin (n + 1))
  have hDa : D a ≠ 0 := by simpa using ha
  have hDb : D b ≠ 0 := by simpa using hb
  rw [zeroLocus_singleton_sum_C_mul_X, zeroLocus_singleton_sum_C_mul_X, SetLike.coe_set_eq,
    Submodule.projectivization.injective.eq_iff, ← hyperplane_mk _ hDa, ← hyperplane_mk _ hDb,
    hyperplane_injective.eq_iff, mk_eq_mk_iff, mk_eq_mk_iff]
  simp only [Units.smul_def, ← map_smul, D.injective.eq_iff]

/-- **Hyperplanes are zero loci of nonzero linear forms.** A subspace `H` of `kⁿ⁺¹` has
codimension one iff `H.projectivization` is `V(∑ i, a i X i)` for some `a ≠ 0`. -/
theorem finrank_add_one_eq_iff_exists_zeroLocus_singleton_sum_C_mul_X_eq
    (H : Submodule k (Fin (n + 1) → k)) :
    finrank k H + 1 = n + 1 ↔
      ∃ a : Fin (n + 1) → k, a ≠ 0 ∧ zeroLocus {∑ i, C (a i) * X i} = H.projectivization := by
  set D := dotProductEquiv k (Fin (n + 1))
  have := Submodule.finrank_add_one_eq_iff_exists_ker_eq H
  rw [finrank_fin_fun] at this
  rw [this]
  simp_rw [zeroLocus_singleton_sum_C_mul_X, SetLike.coe_set_eq,
    Submodule.projectivization.injective.eq_iff]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨D.symm f, by simpa using hf, by simp [D]⟩
  · rintro ⟨a, ha, h⟩
    exact ⟨D a, by simpa using ha, h⟩

/-- **Linear subvarieties and projective changes of coordinates in `ℙⁿ`**, over an infinite
field `k` (Fulton, Problems 4.11–4.16, 4.18, 4.24 and 4.25). Write `L a = ∑ i, a i X i` for the
linear form with coefficients `a`, and let changes of coordinates be linear automorphisms (or
invertible matrices) of `kⁿ⁺¹`.

(a) A change of coordinates carries a linear subvariety `V(L a₁, …, L a_r)` to a linear
  subvariety; if the `aⱼ` have rank `n - m`, some change of coordinates carries it to
  `V(X (m + 1), …, X n)`, and `V` has dimension `m`: it is `p.projectivization` with
  `dim p = m + 1`; a nonempty linear subvariety is a variety; a change of coordinates carries
  `p.projectivization` onto `q.projectivization` iff `dim p = dim q`, so the dimension does not
  depend on the coordinates; `p.projectivization` is empty iff `p = ⊥`; every
  `p.projectivization` is a linear subvariety.
(b) At most `n` hyperplanes of `ℙⁿ` have a common point.
(c) The line through `[a] ≠ [b]` is `{[l a + m b]}`; changes of coordinates carry the line
  through `P`, `Q` to the line through their images; this line has dimension one, and a line is
  the line through any two of its points; in `ℙ²` the lines are the hyperplanes; two distinct
  lines through a point can be carried to two distinct lines through any point.
(d) `n + 1` points not on a hyperplane can be carried to any other `n + 1` such points.
(e) Two distinct lines of `ℙ²` meet in exactly one point.
(f) `n + 1` hyperplanes with no common point can be carried to any other `n + 1` such
  hyperplanes.
(g) `V(L a) ↦ [a]` is a bijection from the hyperplanes onto `ℙⁿ`; with `P*` the dual hyperplane
  of `P` and `H*` the point of the dual of `H`, `P** = P` and `H** = H` (identifying `kⁿ⁺¹` with
  its double dual), and `P ∈ H` iff `H* ∈ P*`.
(h) The lines of `ℙ²` through `[0 : 1 : 0]` are the `V(X - λ Z)` and `V(Z)`.
(i) The coefficient vectors of the hyperplanes through `P` form a subspace of dimension `n` of
  `kⁿ⁺¹`; for finitely many points some hyperplane passes through none of them.

Milestone: *Linear subvarieties and projective changes of coordinates in projective space*. -/
theorem linearSubvariety_changeOfCoordinates_duality [Infinite k] :
    -- (a)
    (∀ (s : Set (Fin (n + 1) → k)) (e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k)),
      ∃ t : Set (Fin (n + 1) → k),
        map (e : (Fin (n + 1) → k) →ₗ[k] Fin (n + 1) → k) e.injective ''
          zeroLocus ((fun a : Fin (n + 1) → k ↦ ∑ i, C (a i) * X i) '' s) =
          zeroLocus ((fun a : Fin (n + 1) → k ↦ ∑ i, C (a i) * X i) '' t)) ∧
    (∀ (s : Set (Fin (n + 1) → k)) (m : ℕ), finrank k (Submodule.span k s) + (m + 1) = n + 1 →
      ∃ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hM : Function.Injective M.mulVecLin),
        map M.mulVecLin hM ⁻¹' zeroLocus ((fun a : Fin (n + 1) → k ↦ ∑ i, C (a i) * X i) '' s) =
          zeroLocus (X '' {i : Fin (n + 1) | m < i})) ∧
    (∀ (s : Set (Fin (n + 1) → k)), ∃ p : Submodule k (Fin (n + 1) → k),
      zeroLocus ((fun a : Fin (n + 1) → k ↦ ∑ i, C (a i) * X i) '' s) = p.projectivization ∧
        finrank k p + finrank k (Submodule.span k s) = n + 1) ∧
    (∀ (s : Set (Fin (n + 1) → k)),
      (zeroLocus ((fun a : Fin (n + 1) → k ↦ ∑ i, C (a i) * X i) '' s)).Nonempty →
      (vanishingIdeal (zeroLocus ((fun a : Fin (n + 1) → k ↦ ∑ i, C (a i) * X i) '' s))
        ).toIdeal.IsPrime) ∧
    (∀ p q : Submodule k (Fin (n + 1) → k),
      (∃ e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k),
        map (e : (Fin (n + 1) → k) →ₗ[k] Fin (n + 1) → k) e.injective ''
          (p.projectivization : Set (ℙ k (Fin (n + 1) → k))) = q.projectivization) ↔
        finrank k p = finrank k q) ∧
    (∀ p : Submodule k (Fin (n + 1) → k),
      (p.projectivization : Set (ℙ k (Fin (n + 1) → k))).Nonempty ↔ p ≠ ⊥) ∧
    (∀ p : Submodule k (Fin (n + 1) → k), ∃ s : Finset (Fin (n + 1) → k),
      s.card + finrank k p = n + 1 ∧
        zeroLocus ((fun a : Fin (n + 1) → k ↦ ∑ i, C (a i) * X i) '' ↑s) = p.projectivization) ∧
    -- (b)
    (∀ s : Finset (Fin (n + 1) → k), s.card ≤ n →
      (zeroLocus ((fun a : Fin (n + 1) → k ↦ ∑ i, C (a i) * X i) '' ↑s)).Nonempty) ∧
    -- (c)
    (∀ (a b : Fin (n + 1) → k) (ha : a ≠ 0) (hb : b ≠ 0) (x : ℙ k (Fin (n + 1) → k)),
      x ∈ ((mk k a ha).submodule ⊔ (mk k b hb).submodule).projectivization ↔
        ∃ (l m : k) (h : l • a + m • b ≠ 0), x = mk k (l • a + m • b) h) ∧
    (∀ (e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k)) (x y : ℙ k (Fin (n + 1) → k)),
      map (e : (Fin (n + 1) → k) →ₗ[k] Fin (n + 1) → k) e.injective ''
          ((x.submodule ⊔ y.submodule).projectivization : Set (ℙ k (Fin (n + 1) → k))) =
        ((map (e : (Fin (n + 1) → k) →ₗ[k] Fin (n + 1) → k) e.injective x).submodule ⊔
          (map (e : (Fin (n + 1) → k) →ₗ[k] Fin (n + 1) → k) e.injective y).submodule
          ).projectivization) ∧
    (∀ x y : ℙ k (Fin (n + 1) → k), x ≠ y → finrank k ↥(x.submodule ⊔ y.submodule) = 2) ∧
    (∀ (L : Submodule k (Fin (n + 1) → k)) (x y : ℙ k (Fin (n + 1) → k)), finrank k L = 2 →
      x ≠ y → x ∈ L.projectivization → y ∈ L.projectivization →
        L = x.submodule ⊔ y.submodule) ∧
    (n = 2 → ∀ L : Submodule k (Fin (n + 1) → k), finrank k L = 2 ↔
      ∃ a : Fin (n + 1) → k, a ≠ 0 ∧ zeroLocus {∑ i, C (a i) * X i} = L.projectivization) ∧
    (∀ {x x' : ℙ k (Fin (n + 1) → k)} {L₁ L₂ L₁' L₂' : Submodule k (Fin (n + 1) → k)},
      finrank k L₁ = 2 → finrank k L₂ = 2 → finrank k L₁' = 2 → finrank k L₂' = 2 →
      L₁ ≠ L₂ → L₁' ≠ L₂' → x ∈ L₁.projectivization → x ∈ L₂.projectivization →
      x' ∈ L₁'.projectivization → x' ∈ L₂'.projectivization →
      ∃ e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k),
        map (e : (Fin (n + 1) → k) →ₗ[k] Fin (n + 1) → k) e.injective x = x' ∧
          L₁.map (e : (Fin (n + 1) → k) →ₗ[k] Fin (n + 1) → k) = L₁' ∧
          L₂.map (e : (Fin (n + 1) → k) →ₗ[k] Fin (n + 1) → k) = L₂') ∧
    -- (d)
    (∀ P Q : Fin (n + 1) → ℙ k (Fin (n + 1) → k),
      (∀ a : Fin (n + 1) → k, a ≠ 0 → ¬ Set.range P ⊆ zeroLocus {∑ i, C (a i) * X i}) →
      (∀ a : Fin (n + 1) → k, a ≠ 0 → ¬ Set.range Q ⊆ zeroLocus {∑ i, C (a i) * X i}) →
      ∃ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hM : Function.Injective M.mulVecLin),
        ∀ i, map M.mulVecLin hM (P i) = Q i) ∧
    -- (e)
    (n = 2 → ∀ p q : Submodule k (Fin (n + 1) → k), finrank k p = 2 → finrank k q = 2 →
      p ≠ q → ∃! x : ℙ k (Fin (n + 1) → k), x ∈ p.projectivization ∧ x ∈ q.projectivization) ∧
    -- (f)
    (∀ a b : Fin (n + 1) → Fin (n + 1) → k,
      ⋂ i, zeroLocus {∑ j, C (a i j) * X j} = ∅ → ⋂ i, zeroLocus {∑ j, C (b i j) * X j} = ∅ →
      ∃ e : (Fin (n + 1) → k) ≃ₗ[k] (Fin (n + 1) → k), ∀ i,
        map (e : (Fin (n + 1) → k) →ₗ[k] Fin (n + 1) → k) e.injective ''
          zeroLocus {∑ j, C (a i j) * X j} = zeroLocus {∑ j, C (b i j) * X j}) ∧
    -- (g)
    (∀ H : Submodule k (Fin (n + 1) → k), finrank k H + 1 = n + 1 ↔
      ∃ a : Fin (n + 1) → k, a ≠ 0 ∧ zeroLocus {∑ i, C (a i) * X i} = H.projectivization) ∧
    (∀ (a b : Fin (n + 1) → k) (ha : a ≠ 0) (hb : b ≠ 0),
      zeroLocus {∑ i, C (a i) * X i} = zeroLocus {∑ i, C (b i) * X i} ↔
        mk k a ha = mk k b hb) ∧
    (∀ x : ℙ k (Fin (n + 1) → k),
      hyperplaneEquiv.symm ⟨dualHyperplane x, finrank_dualHyperplane_add_one x⟩ =
        map (evalEquiv k (Fin (n + 1) → k)).toLinearMap (evalEquiv k _).injective x) ∧
    (∀ H : {H : Submodule k (Fin (n + 1) → k) // finrank k H + 1 = finrank k (Fin (n + 1) → k)},
      dualHyperplane (hyperplaneEquiv.symm H) =
        H.1.map (evalEquiv k (Fin (n + 1) → k)).toLinearMap) ∧
    (∀ (x : ℙ k (Fin (n + 1) → k))
      (H : {H : Submodule k (Fin (n + 1) → k) // finrank k H + 1 = finrank k (Fin (n + 1) → k)}),
      x ∈ H.1.projectivization ↔
        hyperplaneEquiv.symm H ∈ (dualHyperplane x).projectivization) ∧
    -- (h)
    (∀ a : Fin 3 → k, a ≠ 0 →
      (mk k (Pi.single 1 1) (by simp) ∈ zeroLocus {∑ i, C (a i) * X i} ↔
        (∃ c ≠ 0, ∃ l, ∑ i, C (a i) * X i = C c * (X 0 - C l * X 2)) ∨
          ∃ c ≠ 0, ∑ i, C (a i) * X i = C c * X 2)) ∧
    -- (i)
    (∀ P : ℙ k (Fin (n + 1) → k), ∃ W : Submodule k (Fin (n + 1) → k), finrank k W = n ∧
      {a : Fin (n + 1) → k | P ∈ zeroLocus {∑ i, C (a i) * X i}} = W) ∧
    (∀ S : Set (ℙ k (Fin (n + 1) → k)), S.Finite →
      ∃ a : Fin (n + 1) → k, a ≠ 0 ∧ ∀ P ∈ S, P ∉ zeroLocus {∑ i, C (a i) * X i}) := by
  refine ⟨fun s e ↦ ?_, fun s m hm ↦ exists_preimage_map_zeroLocus_eq s hm, fun s ↦ ?_,
    fun s hs ↦ ?_, Submodule.exists_linearEquiv_image_map_projectivization_eq_iff,
    Submodule.projectivization_nonempty_iff, exists_finset_zeroLocus_image_sum_C_mul_X_eq,
    zeroLocus_image_sum_C_mul_X_nonempty, fun a b ha hb x ↦ mem_projectivization_sup_iff ha hb x,
    fun e x y ↦ ?_, fun x y h ↦ finrank_submodule_sup h, fun L x y hL hxy hx hy ↦ ?_,
    fun hn L ↦ ?_, exists_linearEquiv_map_eq_of_finrank_eq_two,
    fun P Q hP hQ ↦ exists_mulVecLin_map_eq_of_independent
      ((independent_iff_forall_not_subset_zeroLocus P).mpr hP)
      ((independent_iff_forall_not_subset_zeroLocus Q).mpr hQ),
    fun hn p q hp hq hpq ↦ existsUnique_mem_of_finrank_eq_two (by simp [hn]) hp hq hpq,
    fun a b ha hb ↦ exists_linearEquiv_image_map_zeroLocus_sum_C_mul_X_eq ha hb,
    finrank_add_one_eq_iff_exists_zeroLocus_singleton_sum_C_mul_X_eq,
    fun a b ha hb ↦ zeroLocus_singleton_sum_C_mul_X_eq_iff ha hb,
    hyperplaneEquiv_symm_dualHyperplane, dualHyperplane_hyperplaneEquiv_symm,
    mem_projectivization_iff_hyperplaneEquiv_symm_mem, single_one_mem_zeroLocus_sum_C_mul_X_iff,
    fun P ↦ ?_, fun S hS ↦ exists_sum_C_mul_X_forall_notMem_zeroLocus hS⟩
  · obtain ⟨t, -, ht⟩ := exists_finset_zeroLocus_image_sum_C_mul_X_eq
      (((Submodule.span k s).map
        (dotProductEquiv k (Fin (n + 1))).toLinearMap).dualCoannihilator.map
          (e : (Fin (n + 1) → k) →ₗ[k] Fin (n + 1) → k))
    exact ⟨t, by rw [zeroLocus_image_sum_C_mul_X, Submodule.image_map_projectivization, ht]⟩
  · exact ⟨_, zeroLocus_image_sum_C_mul_X s,
      finrank_add_finrank_span_of_zeroLocus_eq (zeroLocus_image_sum_C_mul_X s)⟩
  · rw [zeroLocus_image_sum_C_mul_X] at hs ⊢
    exact isPrime_vanishingIdeal_projectivization
      ((Submodule.projectivization_nonempty_iff _).mp hs)
  · rw [Submodule.image_map_projectivization, Submodule.map_sup,
      ← submodule_map _ e.injective, ← submodule_map _ e.injective]
  · refine line_unique hxy _ _ hL (finrank_submodule_sup hxy) hx hy ?_ ?_
    · exact (Submodule.mem_projectivization_iff_submodule_le _ _).mpr le_sup_left
    · exact (Submodule.mem_projectivization_iff_submodule_le _ _).mpr le_sup_right
  · subst hn
    rw [← finrank_add_one_eq_iff_exists_zeroLocus_singleton_sum_C_mul_X_eq]
    omega
  · refine ⟨_, ?_, setOf_mem_zeroLocus_sum_C_mul_X P⟩
    have h0 : dotProductEquiv k (Fin (n + 1)) P.rep ≠ 0 := by simpa using P.rep_ne_zero
    have := Module.Dual.finrank_ker_add_one_of_ne_zero h0
    rw [finrank_fin_fun] at this
    omega

end PlaneCurves.ProjectiveSpace

end
