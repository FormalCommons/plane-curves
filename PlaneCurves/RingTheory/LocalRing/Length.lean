/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.LocalRing.Length

/-!
# Lengths over a local algebra whose residue field is the base field

Let `B` be a local algebra over a field `k`. This file proves:

* `Module.finrank_eq_toNat_length`: over a field, the dimension of a vector space is the natural
  number its length gives;
* `IsLocalRing.algebraMap_mem_maximalIdeal_iff`: an element of `k` lies in the maximal ideal of
  `B` if and only if it is zero;
* `IsLocalRing.length_eq_length_of_surjective_algebraMap_residueField`: if the residue field of
  `B` is `k`, lengths of `B`-modules over `k` and over `B` agree;
* `IsLocalRing.existsUnique_sub_algebraMap_mem_maximalIdeal`: if the residue field of `B` is `k`,
  every `z ∈ B` has a unique `c ∈ k` with `z - c` in the maximal ideal;
* `IsLocalRing.length_quotient_isMaximal_of_finite`: if `k` is algebraically closed and the
  residue field of a local `k`-algebra `A` is `k`, then `B ⧸ 𝔪` has length one over `A` for every
  finite `A`-algebra `B` and maximal ideal `𝔪` of `B`.
-/

public section

open IsLocalRing


/-- Over a field, the dimension of a vector space is the natural number its length gives
(`0` when the length is infinite). -/
theorem Module.finrank_eq_toNat_length (K M : Type*) [Field K] [AddCommGroup M] [Module K M] :
    Module.finrank K M = (Module.length K M).toNat := by
  simp [Module.length_eq_rank, Module.finrank]

section LocalAlgebra

variable {k B : Type*} [Field k] [CommRing B] [IsLocalRing B] [Algebra k B]

/-- In a local algebra over a field `k`, an element of `k` lies in the maximal ideal if and only
if it is zero. -/
@[simp]
theorem IsLocalRing.algebraMap_mem_maximalIdeal_iff {c : k} :
    algebraMap k B c ∈ maximalIdeal B ↔ c = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  by_contra hc
  exact (mem_maximalIdeal _).mp h ((Units.mk0 c hc).isUnit.map (algebraMap k B))

/-- If `B` is a local algebra over a field `k` whose residue field is `k`, then lengths of
`B`-modules over `k` and over `B` agree: `ℓ_k(M) = ℓ_B(M)`. -/
theorem IsLocalRing.length_eq_length_of_surjective_algebraMap_residueField (M : Type*)
    [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]
    (h : Function.Surjective (algebraMap k (ResidueField B))) :
    Module.length k M = Module.length B M := by
  rw [IsLocalRing.length_restrictScalars k B M,
    ← Module.length_eq_of_surjective (R := ResidueField k) (M := ResidueField B)
      residue_surjective, Module.length_eq_of_surjective h]
  simp

/-- If `B` is a local algebra over a field `k` whose residue field is `k`, then every `z ∈ B`
has a unique `c ∈ k` with `z - c` in the maximal ideal. -/
theorem IsLocalRing.existsUnique_sub_algebraMap_mem_maximalIdeal
    (h : Function.Surjective (algebraMap k (ResidueField B))) (z : B) :
    ∃! c : k, z - algebraMap k B c ∈ maximalIdeal B := by
  obtain ⟨c, hc⟩ := h (residue B z)
  have hmem : z - algebraMap k B c ∈ maximalIdeal B := by
    rw [← residue_eq_zero_iff, map_sub, ← hc, sub_eq_zero]
    rfl
  refine ⟨c, hmem, fun d hd ↦ ?_⟩
  have := sub_mem hd hmem
  rw [sub_sub_sub_cancel_left, ← map_sub, algebraMap_mem_maximalIdeal_iff] at this
  exact (sub_eq_zero.mp this).symm

end LocalAlgebra

/-- Let `A` be a local algebra over an algebraically closed field `k` whose residue field is `k`,
and `B` a finite `A`-algebra. For every maximal ideal `𝔪` of `B`, the field `B ⧸ 𝔪` is `k`, so it
has length one over `A`. -/
theorem IsLocalRing.length_quotient_isMaximal_of_finite {k A B : Type*} [Field k] [IsAlgClosed k]
    [CommRing A] [IsLocalRing A] [Algebra k A] [CommRing B] [Algebra A B] [Algebra k B]
    [IsScalarTower k A B] [Module.Finite A B]
    (hres : Function.Surjective (algebraMap k (ResidueField A))) (m : Ideal B) [m.IsMaximal] :
    Module.length A (B ⧸ m) = 1 := by
  have hcomap : m.comap (algebraMap A B) = maximalIdeal A :=
    eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal m)
  -- every element of `A` acts on `B ⧸ m` as a constant
  have hconst : ∀ a : A, ∃ c : k, ∀ y : B ⧸ m, a • y = c • y := by
    intro a
    obtain ⟨c, hc, -⟩ := existsUnique_sub_algebraMap_mem_maximalIdeal hres a
    refine ⟨c, fun y ↦ ?_⟩
    rw [← hcomap, Ideal.mem_comap] at hc
    rw [← algebraMap_smul A c, ← sub_eq_zero, ← sub_smul, Algebra.smul_def,
      ← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem.mpr hc, zero_mul]
  have hfin : Module.Finite k (B ⧸ m) := by
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := B ⧸ m)
    refine ⟨⟨s, eq_top_iff.mpr ?_⟩⟩
    let N : Submodule A (B ⧸ m) :=
      { carrier := Submodule.span k (s : Set (B ⧸ m))
        add_mem' := add_mem
        zero_mem' := zero_mem _
        smul_mem' := fun a y hy ↦ by
          obtain ⟨c, hc⟩ := hconst a
          rw [hc]
          exact Submodule.smul_mem _ c hy }
    have : Submodule.span A (s : Set (B ⧸ m)) ≤ N := Submodule.span_le.mpr Submodule.subset_span
    rw [hs] at this
    exact fun y _ ↦ this trivial
  have hsurj : Function.Surjective (algebraMap k (B ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral.2
  have hrank : Module.finrank k (B ⧸ m) = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
      ⟨(algebraMap k (B ⧸ m)).injective, hsurj⟩
  rw [← IsLocalRing.length_eq_length_of_surjective_algebraMap_residueField _ hres,
    Module.length_eq_finrank, hrank, Nat.cast_one]

end
