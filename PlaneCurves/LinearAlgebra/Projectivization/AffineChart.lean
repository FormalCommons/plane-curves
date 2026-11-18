/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Group.Fin.Tuple
public import Mathlib.LinearAlgebra.Pi
public import TauCeti.LinearAlgebra.Projectivization.AffineChart
public import TauCeti.LinearAlgebra.Projectivization.Basic

/-!
# The hyperplane at infinity of a standard affine chart

The complement of the standard affine open `Projectivization.affineOpen i` of
`ℙ K (Fin (n + 1) → K)`
is the hyperplane `{xᵢ = 0}`. This file identifies it with `ℙ K (Fin n → K)`, by inserting a
zero homogeneous coordinate in position `i`.

## Main definitions

* `Fin.insertNthZeroLinearMap i`: the linear injection `(Fin n → M) → (Fin (n + 1) → M)` that
  inserts a zero coordinate in position `i`.
* `Projectivization.insertZero i : ℙ K (Fin n → K) → ℙ K (Fin (n + 1) → K)`: the map of projective
  spaces it induces, `[v] ↦ [Fin.insertNth i 0 v]`.
* `Projectivization.insertZeroEquiv i`: `ℙ K (Fin n → K)` is in bijection with the complement of
  `affineOpen i`.

## Main results

* `Projectivization.insertZero_injective` and `Projectivization.range_insertZero`: `insertZero i`
  is injective, with image the complement of `affineOpen i`.
* `Projectivization.bijOn_insertZero_last`: the hyperplane at infinity `H∞ = (affineOpen (Fin.last
  n))ᶜ` of `ℙⁿ` is in bijection with `ℙⁿ⁻¹`; for `n = 0` it is empty and `ℙ⁰` is a point.

## References

* [W. Fulton, *Algebraic Curves*, §4.1][Fulton2008]
-/

public section

open Set

open scoped LinearAlgebra.Projectivization

namespace Fin

section Zero

variable {M : Type*} [Zero M] {n : ℕ}

/-- A tuple with an inserted entry is zero exactly when the entry and the tuple are. -/
@[simp]
theorem insertNth_eq_zero_iff (i : Fin (n + 1)) (x : M) (v : Fin n → M) :
    i.insertNth (α := fun _ ↦ M) x v = 0 ↔ x = 0 ∧ v = 0 := by
  rw [insertNth_eq_iff]
  simp [funext_iff, removeNth]

end Zero

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ}

/-- The linear map `(Fin n → M) → (Fin (n + 1) → M)` that inserts a zero coordinate in
position `i`. -/
def insertNthZeroLinearMap (i : Fin (n + 1)) : (Fin n → M) →ₗ[R] (Fin (n + 1) → M) where
  toFun v := i.insertNth (α := fun _ ↦ M) 0 v
  map_add' v w := by rw [← insertNth_add, add_zero]
  map_smul' c v := by
    funext j
    refine i.succAboveCases ?_ (fun j ↦ ?_) j <;> simp

@[simp]
theorem insertNthZeroLinearMap_apply (i : Fin (n + 1)) (v : Fin n → M) :
    insertNthZeroLinearMap (R := R) i v = i.insertNth (α := fun _ ↦ M) 0 v :=
  (rfl)

/-- Inserting a zero coordinate is injective. -/
theorem insertNthZeroLinearMap_injective (i : Fin (n + 1)) :
    Function.Injective (insertNthZeroLinearMap (R := R) (M := M) i) := by
  intro v w h
  simpa using h

end Fin

namespace Projectivization

variable {K : Type*} [DivisionRing K] {n : ℕ}

/-- The map `ℙ K (Fin n → K) → ℙ K (Fin (n + 1) → K)`, `[v] ↦ [Fin.insertNth i 0 v]`, inserting
a zero homogeneous coordinate in position `i`. Its image is the hyperplane `{xᵢ = 0}`, the
complement of the standard affine open `affineOpen i` (`range_insertZero`). -/
def insertZero (i : Fin (n + 1)) : ℙ K (Fin n → K) → ℙ K (Fin (n + 1) → K) :=
  map (Fin.insertNthZeroLinearMap i) (Fin.insertNthZeroLinearMap_injective i)

theorem insertZero_def (i : Fin (n + 1)) :
    insertZero (K := K) i =
      map (Fin.insertNthZeroLinearMap i) (Fin.insertNthZeroLinearMap_injective i) :=
  (rfl)

/-- `insertZero i` in homogeneous coordinates: `[v] ↦ [Fin.insertNth i 0 v]`. -/
@[simp]
theorem insertZero_mk (i : Fin (n + 1)) (v : Fin n → K) (hv : v ≠ 0) :
    insertZero i (mk K v hv) =
      mk K (i.insertNth (α := fun _ ↦ K) 0 v) (by simpa using hv) := by
  rw [insertZero_def, map_mk]
  rfl

/-- `insertZero i` is injective. -/
theorem insertZero_injective (i : Fin (n + 1)) : Function.Injective (insertZero (K := K) i) :=
  map_injective (τ := RingHom.id K) _ _

@[simp]
theorem insertZero_inj (i : Fin (n + 1)) {x y : ℙ K (Fin n → K)} :
    insertZero i x = insertZero i y ↔ x = y :=
  (insertZero_injective i).eq_iff

/-- The image of `insertZero i` lies outside the standard affine open `affineOpen i`. -/
theorem insertZero_notMem_affineOpen (i : Fin (n + 1)) (x : ℙ K (Fin n → K)) :
    insertZero i x ∉ affineOpen i := by
  induction x using ind with | h v hv => simp

/-- The image of `insertZero i` is the hyperplane `{xᵢ = 0}`, the complement of the standard
affine open `affineOpen i`. -/
theorem range_insertZero (i : Fin (n + 1)) :
    range (insertZero (K := K) i) = (affineOpen i)ᶜ := by
  refine Subset.antisymm (range_subset_iff.2 (insertZero_notMem_affineOpen i)) fun x hx ↦ ?_
  induction x using ind with | h w hw =>
  have hwi : w i = 0 := by simpa using hx
  have hw' : i.removeNth w ≠ 0 := fun h ↦ hw (by
    rw [← Fin.insertNth_self_removeNth i w, hwi, h]
    simp)
  refine ⟨mk K _ hw', ?_⟩
  rw [insertZero_mk]
  congr 1
  rw [← hwi, Fin.insertNth_self_removeNth]

/-- A point lies in the image of `insertZero i` exactly when it lies outside `affineOpen i`. -/
theorem mem_range_insertZero_iff (i : Fin (n + 1)) (x : ℙ K (Fin (n + 1) → K)) :
    x ∈ range (insertZero i) ↔ x ∉ affineOpen i := by
  rw [range_insertZero, mem_compl_iff]

/-- `ℙ K (Fin n → K)` is in bijection with the complement of the standard affine open
`affineOpen i` of `ℙ K (Fin (n + 1) → K)`, by inserting a zero homogeneous coordinate in
position `i`. -/
noncomputable def insertZeroEquiv (i : Fin (n + 1)) :
    ℙ K (Fin n → K) ≃ ↥(affineOpen (K := K) i)ᶜ :=
  Equiv.ofBijective (fun x ↦ ⟨insertZero i x, insertZero_notMem_affineOpen i x⟩)
    ⟨fun _ _ h ↦ insertZero_injective i (congrArg Subtype.val h), fun x ↦ by
      obtain ⟨y, hy⟩ : (x : ℙ K (Fin (n + 1) → K)) ∈ range (insertZero i) := by
        rw [range_insertZero]; exact x.2
      exact ⟨y, Subtype.ext hy⟩⟩

@[simp]
theorem coe_insertZeroEquiv_apply (i : Fin (n + 1)) (x : ℙ K (Fin n → K)) :
    (insertZeroEquiv i x : ℙ K (Fin (n + 1) → K)) = insertZero i x :=
  (rfl)

@[simp]
theorem insertZero_insertZeroEquiv_symm_apply (i : Fin (n + 1)) (x : ↥(affineOpen (K := K) i)ᶜ) :
    insertZero i ((insertZeroEquiv i).symm x) = x := by
  rw [← coe_insertZeroEquiv_apply, Equiv.apply_symm_apply]

/-- The projective space of dimension zero has exactly one point. -/
noncomputable instance instUniqueFinOne : Unique (ℙ K (Fin 1 → K)) :=
  have : Subsingleton (ℙ K (Fin 1 → K)) := subsingleton_of_rank_le_one (by simp)
  uniqueOfSubsingleton (Classical.arbitrary _)

/-- The hyperplane at infinity of the standard chart `U_{n+1} = affineOpen (Fin.last n)` of
`ℙⁿ = ℙ K (Fin (n + 1) → K)`: the map `insertZero (Fin.last n)`, which appends a zero coordinate,
is a bijection of `ℙⁿ⁻¹ = ℙ K (Fin n → K)` onto `H∞ = ℙⁿ \ U_{n+1}`; its inverse drops the last
(zero) coordinate. For `n = 0`, `H∞` is empty and `ℙ⁰` is a single point.

Milestone: *Standard affine charts of projective space*. -/
theorem bijOn_insertZero_last (n : ℕ) :
    BijOn (insertZero (K := K) (Fin.last n)) univ (affineOpen (Fin.last n))ᶜ ∧
      (n = 0 → (affineOpen (K := K) (Fin.last n))ᶜ = ∅ ∧
        ∃ x : ℙ K (Fin (n + 1) → K), ∀ y, y = x) := by
  refine ⟨?_, ?_⟩
  · rw [← range_insertZero, ← image_univ]
    exact (insertZero_injective _).injOn.bijOn_image
  · rintro rfl
    exact ⟨by rw [affineOpen_eq_univ (ι := Fin 1), compl_univ],
      (instUniqueFinOne (K := K)).default, (instUniqueFinOne (K := K)).eq_default⟩

end Projectivization

end
