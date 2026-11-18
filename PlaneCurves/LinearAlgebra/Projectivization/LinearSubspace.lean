/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.GroupTheory.CosetCover
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Projectivization.Collinear
public import Mathlib.LinearAlgebra.Projectivization.Independence
public import PlaneCurves.LinearAlgebra.FiniteDimensional.Lemmas
public import TauCeti.LinearAlgebra.Projectivization.Basic

/-!
# Linear subvarieties of projective space

A linear subvariety of `ℙ K V` is the projectivization `p.projectivization` of a subspace
`p : Submodule K V`; its dimension `m` is given by `finrank K p = m + 1`, and `p = ⊥` gives the
empty set (Fulton's `m = -1`). A line is the projectivization of a subspace of dimension `2`, and
the line through two distinct points `x`, `y` is that of `x.submodule ⊔ y.submodule`. A change of
coordinates is a linear automorphism `e : V ≃ₗ[K] V`, acting on points by
`Projectivization.map`.

## Main results

* `Submodule.image_map_projectivization`, `Submodule.preimage_map_projectivization`: images and
  preimages of linear subvarieties under injective linear maps are linear subvarieties.
* `Submodule.projectivization_nonempty_iff`: a linear subvariety is nonempty iff its subspace is
  not `⊥`.
* `Submodule.exists_linearEquiv_image_map_projectivization_eq_iff`: a change of coordinates
  carries one linear subvariety onto another iff they have the same dimension.
* `Projectivization.mem_projectivization_sup_iff`: the points of the line through `[a]` and `[b]`
  are the `[l • a + m • b]`.
* `Projectivization.finrank_submodule_sup`: the line through two distinct points has dimension
  one.
* `Projectivization.exists_forall_dual_apply_rep_eq_zero`: fewer than `finrank K V` hyperplanes
  have a common point; in `ℙⁿ`, any `m ≤ n` hyperplanes meet.
* `Projectivization.exists_linearEquiv_map_eq_of_independent`: a change of coordinates carries
  any finite independent family of points to any other one.
* `Projectivization.independent_iff_forall_dual`: `finrank K V` points are independent iff they
  are not on a hyperplane.
* `Projectivization.exists_linearEquiv_map_eq_of_finrank_eq_two`: a change of coordinates carries
  two distinct lines through a point to any two distinct lines through any point.
* `Projectivization.existsUnique_mem_of_finrank_eq_two`: two distinct lines of the projective
  plane meet in exactly one point.
* `Projectivization.exists_dual_mem_forall_apply_rep_ne_zero`, and its corollaries
  `Projectivization.exists_dual_forall_apply_rep_ne_zero` and
  `Projectivization.exists_dual_apply_rep_eq_zero_forall_ne_zero`: over an infinite field, some
  hyperplane (through a given point) misses finitely many (other) points.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §4.2, Problems 4.11–4.15, 4.24 and 4.25
-/

public section

open Module

open scoped LinearAlgebra.Projectivization

variable {K V W : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

namespace Submodule

open Projectivization

/-- The image of a linear subvariety under the map of projective spaces induced by an injective
linear map `f` is the linear subvariety of the image subspace. -/
theorem image_map_projectivization (f : V →ₗ[K] W) (hf : Function.Injective f)
    (p : Submodule K V) :
    Projectivization.map f hf '' (p.projectivization : Set (ℙ K V)) =
      ((p.map f).projectivization : Set (ℙ K W)) := by
  ext y
  induction y using Projectivization.ind with | h w hw => ?_
  simp only [Set.mem_image, SetLike.mem_coe, mk_mem_projectivization_iff, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    induction x using Projectivization.ind with | h v hv => ?_
    rw [map_mk, mk_eq_mk_iff] at hxy
    obtain ⟨a, ha⟩ := hxy
    exact ⟨a⁻¹ • v, p.smul_mem _ ((mk_mem_projectivization_iff p hv).mp hx), by simp [← ha]⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Projectivization.mk K v fun h ↦ hw (by simp [h]), hv, rfl⟩

/-- The preimage of a linear subvariety under the map of projective spaces induced by an
injective linear map `f` is the linear subvariety of the preimage subspace. -/
theorem preimage_map_projectivization (f : V →ₗ[K] W) (hf : Function.Injective f)
    (q : Submodule K W) :
    Projectivization.map f hf ⁻¹' (q.projectivization : Set (ℙ K W)) =
      ((q.comap f).projectivization : Set (ℙ K V)) := by
  ext x
  induction x using Projectivization.ind with | h v hv => ?_
  simp [map_mk]

/-- A linear subvariety is nonempty if and only if its subspace is not `⊥`. -/
theorem projectivization_nonempty_iff (p : Submodule K V) :
    (p.projectivization : Set (ℙ K V)).Nonempty ↔ p ≠ ⊥ := by
  refine ⟨?_, fun hp ↦ ?_⟩
  · rintro h rfl
    simp at h
  · obtain ⟨v, hv, hv0⟩ := p.exists_mem_ne_zero_of_ne_bot hp
    exact ⟨Projectivization.mk K v hv0, hv⟩

/-- A change of coordinates of `ℙ K V` carries the linear subvariety of `p` onto that of `q` for
some linear automorphism if and only if `p` and `q` have the same dimension. In particular a
change of coordinates preserves the dimension of a linear subvariety, and carries it onto any
other one of the same dimension. -/
theorem exists_linearEquiv_image_map_projectivization_eq_iff [FiniteDimensional K V]
    (p q : Submodule K V) :
    (∃ e : V ≃ₗ[K] V, Projectivization.map (e : V →ₗ[K] V) e.injective ''
        (p.projectivization : Set (ℙ K V)) =
        q.projectivization) ↔ finrank K p = finrank K q := by
  simp_rw [image_map_projectivization, SetLike.coe_set_eq, EmbeddingLike.apply_eq_iff_eq]
  constructor
  · rintro ⟨e, rfl⟩
    exact (LinearEquiv.finrank_map_eq e p).symm
  · exact exists_linearEquiv_map_eq

end Submodule

namespace Projectivization

/-- The points of the line through `[a]` and `[b]` are the `[l • a + m • b]`. When
`[a] ≠ [b]`, the condition `l • a + m • b ≠ 0` says that `(l, m) ≠ (0, 0)`, by
`LinearIndependent.pair_iff` and `Projectivization.linearIndependent_pair_iff_ne`. -/
theorem mem_projectivization_sup_iff {a b : V} (ha : a ≠ 0) (hb : b ≠ 0) (x : ℙ K V) :
    x ∈ ((mk K a ha).submodule ⊔ (mk K b hb).submodule).projectivization ↔
      ∃ (l m : K) (h : l • a + m • b ≠ 0), x = mk K (l • a + m • b) h := by
  simp_rw [submodule_mk]
  constructor
  · induction x using Projectivization.ind with | h v hv => ?_
    rw [Submodule.mk_mem_projectivization_iff, Submodule.mem_sup]
    rintro ⟨_, hy, _, hz, rfl⟩
    obtain ⟨l, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨l, m, hv, rfl⟩
  · rintro ⟨l, m, h, rfl⟩
    exact add_mem
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b)))

/-- The line through two distinct points of projective space is the projectivization of a
subspace of dimension `2`: it is a linear subvariety of dimension one. With
`Projectivization.line_unique`, each line is the line through any two of its distinct points. -/
theorem finrank_submodule_sup {x y : ℙ K V} (h : x ≠ y) :
    finrank K ↥(x.submodule ⊔ y.submodule) = 2 := by
  rw [submodule_eq, submodule_eq, ← Submodule.span_union, Set.singleton_union,
    ← Matrix.range_cons_cons_empty, finrank_span_eq_card (linearIndependent_pair_iff_ne.mpr h)]
  simp

/-- Fewer than `finrank K V` hyperplanes of `ℙ K V` have a common point: with
`finrank K V = n + 1`, any `m ≤ n` hyperplanes of `ℙⁿ` meet. -/
theorem exists_forall_dual_apply_rep_eq_zero [FiniteDimensional K V] {ι : Type*} [Fintype ι]
    (f : ι → Dual K V) (h : Fintype.card ι < finrank K V) :
    ∃ x : ℙ K V, ∀ i, f i x.rep = 0 := by
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := LinearMap.pi f)
    (by rwa [finrank_fintype_fun_eq_card])
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep K v hv0
  refine ⟨mk K v hv0, fun i ↦ ?_⟩
  rw [← ha, Units.smul_def, map_smul, smul_eq_mul, mul_eq_zero]
  exact Or.inr (congr_fun (LinearMap.mem_ker.mp hv) i)

/-- A change of coordinates carries any finite independent family of points of `ℙ K V` to any
other one with the same index type. With `finrank K V = n + 1` and `n + 1` points, this moves
any `n + 1` points in general position to the coordinate points. -/
theorem exists_linearEquiv_map_eq_of_independent {ι : Type*} [Finite ι] {p q : ι → ℙ K V}
    (hp : Independent p) (hq : Independent q) :
    ∃ e : V ≃ₗ[K] V, ∀ i, map (e : V →ₗ[K] V) e.injective (p i) = q i := by
  obtain ⟨e, he⟩ := (independent_iff.mp hp).exists_linearEquiv_apply_eq (independent_iff.mp hq)
  refine ⟨e, fun i ↦ ?_⟩
  rw [← mk_rep (p i), map_mk]
  simp only [LinearEquiv.coe_coe, Function.comp_apply] at he ⊢
  simp only [he, mk_rep]

/-- A linear subvariety of dimension at least one has a point other than any given point. -/
theorem exists_mem_projectivization_ne {L : Submodule K V} (hL : 1 < finrank K L) (x : ℙ K V) :
    ∃ y ∈ L.projectivization, y ≠ x := by
  have hle : ¬ L ≤ x.submodule := fun h ↦ by
    have := Submodule.finrank_mono (s := L) (t := x.submodule) h
    rw [finrank_submodule] at this
    omega
  obtain ⟨v, hv, hvx⟩ := IsConcreteLE.not_le_iff_exists.mp hle
  have hv0 : v ≠ 0 := fun h ↦ hvx (h ▸ zero_mem _)
  refine ⟨mk K v hv0, hv, fun h ↦ hvx ?_⟩
  rw [← h, submodule_mk]
  exact Submodule.mem_span_singleton_self v

/-- Three points `z`, `x`, `y` with `x ≠ y` are independent if and only if `z` is not on the
line through `x` and `y`. -/
theorem independent_triple_iff_notMem {x y z : ℙ K V} (hxy : x ≠ y) :
    Independent ![z, x, y] ↔ z ∉ (x.submodule ⊔ y.submodule).projectivization := by
  rw [independent_iff, ← mk_rep z, Submodule.mk_mem_projectivization_iff, mk_rep,
    submodule_eq, submodule_eq, ← Submodule.span_union, Set.singleton_union,
    ← Matrix.range_cons_cons_empty _ _ ![]]
  have : Projectivization.rep ∘ ![z, x, y] = Fin.cons z.rep ![x.rep, y.rep] := by
    ext i; fin_cases i <;> rfl
  rw [this, linearIndependent_finCons]
  simp [linearIndependent_pair_iff_ne.mpr hxy]

/-- In the projective plane, two distinct lines meet in exactly one point. -/
theorem existsUnique_mem_of_finrank_eq_two (hV : finrank K V = 3)
    {p q : Submodule K V} (hp : finrank K p = 2) (hq : finrank K q = 2) (hpq : p ≠ q) :
    ∃! x : ℙ K V, x ∈ p.projectivization ∧ x ∈ q.projectivization := by
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ hV
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq p q
  have hle := Submodule.finrank_le (p ⊔ q)
  have hinf : p ⊓ q ≠ ⊥ := fun h ↦ by
    rw [h, finrank_bot] at hsup
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  refine ⟨mk K v hv0, ⟨hv.1, hv.2⟩, fun y hy ↦ ?_⟩
  by_contra h
  exact hpq (line_unique h p q hp hq hy.1 hv.1 hy.2 hv.2)

/-- A line is the line through any two of its distinct points. -/
private theorem eq_submodule_sup_of_mem {L : Submodule K V} (hL : finrank K L = 2) {x y : ℙ K V}
    (hxy : x ≠ y) (hx : x ∈ L.projectivization) (hy : y ∈ L.projectivization) :
    L = x.submodule ⊔ y.submodule := by
  refine line_unique hxy _ _ hL (finrank_submodule_sup hxy) hx hy ?_ ?_
  · exact (Submodule.mem_projectivization_iff_submodule_le _ _).mpr le_sup_left
  · exact (Submodule.mem_projectivization_iff_submodule_le _ _).mpr le_sup_right

/-- Two distinct lines through `x` have points `y₁`, `y₂` other than `x` such that `y₂, x, y₁`
are independent and the lines are those through `x` and `yᵢ`. -/
private theorem independent_of_finrank_eq_two {x : ℙ K V} {L₁ L₂ : Submodule K V}
    (h₁ : finrank K L₁ = 2) (h₂ : finrank K L₂ = 2) (hL : L₁ ≠ L₂)
    (hx₁ : x ∈ L₁.projectivization) (hx₂ : x ∈ L₂.projectivization) :
    ∃ y₁ ∈ L₁.projectivization, ∃ y₂ ∈ L₂.projectivization,
      Independent ![y₂, x, y₁] ∧ L₁ = x.submodule ⊔ y₁.submodule ∧
        L₂ = x.submodule ⊔ y₂.submodule := by
  obtain ⟨y₁, hy₁, hy₁x⟩ := exists_mem_projectivization_ne (h₁ ▸ one_lt_two) x
  obtain ⟨y₂, hy₂, hy₂x⟩ := exists_mem_projectivization_ne (h₂ ▸ one_lt_two) x
  have e₁ := eq_submodule_sup_of_mem h₁ hy₁x.symm hx₁ hy₁
  refine ⟨y₁, hy₁, y₂, hy₂, (independent_triple_iff_notMem hy₁x.symm).mpr fun h ↦ hL ?_, e₁,
    eq_submodule_sup_of_mem h₂ hy₂x.symm hx₂ hy₂⟩
  exact line_unique hy₂x.symm _ _ h₁ h₂ hx₁ (e₁ ▸ h) hx₂ hy₂

/-- Given two distinct lines `L₁`, `L₂` through a point `x` and two distinct lines `L₁'`, `L₂'`
through a point `x'`, some change of coordinates carries `x` to `x'`, `L₁` onto `L₁'` and `L₂`
onto `L₂'`. -/
theorem exists_linearEquiv_map_eq_of_finrank_eq_two {x x' : ℙ K V}
    {L₁ L₂ L₁' L₂' : Submodule K V} (h₁ : finrank K L₁ = 2) (h₂ : finrank K L₂ = 2)
    (h₁' : finrank K L₁' = 2) (h₂' : finrank K L₂' = 2) (hL : L₁ ≠ L₂) (hL' : L₁' ≠ L₂')
    (hx₁ : x ∈ L₁.projectivization) (hx₂ : x ∈ L₂.projectivization)
    (hx₁' : x' ∈ L₁'.projectivization) (hx₂' : x' ∈ L₂'.projectivization) :
    ∃ e : V ≃ₗ[K] V, map (e : V →ₗ[K] V) e.injective x = x' ∧
      L₁.map (e : V →ₗ[K] V) = L₁' ∧ L₂.map (e : V →ₗ[K] V) = L₂' := by
  obtain ⟨y₁, -, y₂, -, hi, rfl, rfl⟩ := independent_of_finrank_eq_two h₁ h₂ hL hx₁ hx₂
  obtain ⟨y₁', -, y₂', -, hi', rfl, rfl⟩ := independent_of_finrank_eq_two h₁' h₂' hL' hx₁' hx₂'
  obtain ⟨e, he⟩ := exists_linearEquiv_map_eq_of_independent hi hi'
  have h0 : map (e : V →ₗ[K] V) e.injective y₂ = y₂' := he 0
  have h1 : map (e : V →ₗ[K] V) e.injective x = x' := he 1
  have h2 : map (e : V →ₗ[K] V) e.injective y₁ = y₁' := he 2
  refine ⟨e, h1, ?_, ?_⟩ <;>
    rw [Submodule.map_sup, ← submodule_map _ e.injective, ← submodule_map _ e.injective, h1]
  exacts [congrArg _ (congrArg _ h2), congrArg _ (congrArg _ h0)]

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- In a space of dimension `n + 1`, a family of `n + 1` points is independent if and only if
the points are not all on one hyperplane: the only linear form vanishing at all of them is `0`. -/
theorem independent_iff_forall_dual [FiniteDimensional K V] {ι : Type*} [Fintype ι]
    (p : ι → ℙ K V) (h : Fintype.card ι = finrank K V) :
    Independent p ↔ ∀ f : Dual K V, (∀ i, f (p i).rep = 0) → f = 0 := by
  have hspan : LinearIndependent K (Projectivization.rep ∘ p) ↔
      Submodule.span K (Set.range (Projectivization.rep ∘ p)) = ⊤ :=
    ⟨fun hl ↦ hl.span_eq_top_of_card_eq_finrank' h,
      fun hs ↦ linearIndependent_of_top_le_span_of_card_eq_finrank hs.ge h⟩
  rw [independent_iff, hspan, ← Submodule.dualAnnihilator_eq_bot_iff, Submodule.eq_bot_iff]
  refine forall_congr' fun f ↦ imp_congr_left ?_
  rw [Submodule.mem_dualAnnihilator]
  exact ⟨fun hf i ↦ hf _ (Submodule.subset_span ⟨i, rfl⟩), fun hf w hw ↦
    (Submodule.span_le (p := LinearMap.ker f)).mpr (Set.range_subset_iff.mpr hf) hw⟩

/-- Over an infinite field, if each of finitely many points of `ℙ K V` is off the hyperplane of
some linear form of a subspace `W` of the dual, then some single form of `W` vanishes at none of
them. -/
theorem exists_dual_mem_forall_apply_rep_ne_zero [Infinite K] (W : Submodule K (Dual K V))
    {S : Set (ℙ K V)} (hS : S.Finite) (h : ∀ x ∈ S, ∃ f ∈ W, f x.rep ≠ 0) :
    ∃ f ∈ W, ∀ x ∈ S, f x.rep ≠ 0 := by
  classical
  let U : ℙ K V → Submodule K W := fun x ↦ LinearMap.ker ((Dual.eval K V x.rep).comp W.subtype)
  have hU : ⊤ ∉ hS.toFinset.image U := by
    simp only [Finset.mem_image, Set.Finite.mem_toFinset, not_exists, not_and]
    intro x hx hxU
    obtain ⟨f, hfW, hf⟩ := h x hx
    have : (⟨f, hfW⟩ : W) ∈ U x := hxU ▸ Submodule.mem_top
    exact hf (by simpa [U] using this)
  obtain ⟨f, hf⟩ := (Set.ne_univ_iff_exists_notMem _).mp
    (Subspace.biUnion_ne_univ_of_top_notMem (k := K) (E := W) hU)
  simp only [Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_iUnion, SetLike.mem_coe,
    exists_prop, not_exists, not_and] at hf
  refine ⟨f, f.2, fun x hx ↦ ?_⟩
  simpa [U] using hf _ ⟨x, hx, rfl⟩

/-- Over an infinite field, some hyperplane of `ℙ K V` passes through none of finitely many
points. -/
theorem exists_dual_forall_apply_rep_ne_zero [Infinite K] [Nontrivial V] {S : Set (ℙ K V)}
    (hS : S.Finite) : ∃ f : Dual K V, f ≠ 0 ∧ ∀ x ∈ S, f x.rep ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨f, -, hf⟩ := exists_dual_mem_forall_apply_rep_ne_zero ⊤ (hS.insert (mk K v hv))
    fun x _ ↦ by
      obtain ⟨f, hf⟩ :=
        not_forall.mp (mt (forall_dual_apply_eq_zero_iff K x.rep).mp x.rep_ne_zero)
      exact ⟨f, Submodule.mem_top, hf⟩
  refine ⟨f, fun h ↦ hf _ (Set.mem_insert _ _) (by simp [h]), fun x hx ↦ hf x (.inr hx)⟩

/-- Over an infinite field, through a point `x` of `ℙ K V` passes a hyperplane that misses
finitely many other points. -/
theorem exists_dual_apply_rep_eq_zero_forall_ne_zero [Infinite K] (x : ℙ K V)
    {S : Set (ℙ K V)} (hS : S.Finite) (hx : x ∉ S) :
    ∃ f : Dual K V, f x.rep = 0 ∧ ∀ y ∈ S, f y.rep ≠ 0 := by
  obtain ⟨f, hfW, hf⟩ := exists_dual_mem_forall_apply_rep_ne_zero (K ∙ x.rep).dualAnnihilator hS
    fun y hy ↦ by
      have hxy : y ≠ x := fun h ↦ hx (h ▸ hy)
      have hli := linearIndependent_pair_iff_ne.mpr hxy
      rw [← Fin.cons_self_tail ![y.rep, x.rep], linearIndependent_finCons] at hli
      obtain ⟨f, hfy, hle⟩ := Submodule.exists_le_ker_of_notMem (by simpa using hli.2)
      exact ⟨f, (Submodule.mem_dualAnnihilator _).mpr fun w hw ↦ hle hw, hfy⟩
  exact ⟨f, (Submodule.mem_dualAnnihilator _).mp hfW _ (Submodule.mem_span_singleton_self _), hf⟩

end Field

end Projectivization
