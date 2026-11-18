/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import PlaneCurves.LinearAlgebra.FiniteDimensional.Lemmas

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

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §4.2, Problems 4.11–4.13
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

end Projectivization
