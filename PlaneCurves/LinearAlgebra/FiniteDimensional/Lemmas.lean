/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Extending linear equivalences, and hyperplanes as kernels

Supporting linear algebra for linear subvarieties of projective space.

## Main results

* `LinearIndependent.exists_linearEquiv_apply_eq`: a linear automorphism of `V` carries any finite
  linearly independent family to any other one indexed by the same type.
* `Submodule.exists_linearEquiv_map_eq`: a linear automorphism of `V` carries any
  finite-dimensional subspace onto any other one of the same dimension.
* `Submodule.finrank_add_one_eq_iff_exists_ker_eq`: in a finite-dimensional space, the subspaces
  of codimension one are exactly the kernels of the nonzero linear forms.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §4.2, Problems 4.11–4.13
-/

public section

open Module

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

namespace LinearIndependent

/-- A linear automorphism of `V` carries a finite linearly independent family `v` to any other
linearly independent family `w` with the same index type. No finite dimension of `V` is
needed. -/
theorem exists_linearEquiv_apply_eq {ι : Type*} [Finite ι] {v w : ι → V}
    (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    ∃ e : V ≃ₗ[K] V, ∀ i, e (v i) = w i := by
  have : FiniteDimensional K (Submodule.span K (Set.range v)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range _)
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq
    (hv.linearCombinationEquiv.symm ≪≫ₗ hw.linearCombinationEquiv)
  refine ⟨e, fun i ↦ ?_⟩
  have h := he ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
  rw [← h, LinearEquiv.trans_apply]
  have hr : hv.linearCombinationEquiv.symm ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ =
      Finsupp.single i 1 :=
    hv.repr_eq_single i _ rfl
  rw [hr]
  simp

end LinearIndependent

namespace Submodule

/-- A linear automorphism of `V` carries a finite-dimensional subspace `p` onto any other
finite-dimensional subspace `q` of the same dimension. The converse is
`LinearEquiv.finrank_map_eq`. -/
theorem exists_linearEquiv_map_eq {p q : Submodule K V} [FiniteDimensional K p]
    [FiniteDimensional K q] (h : finrank K p = finrank K q) :
    ∃ e : V ≃ₗ[K] V, p.map (e : V →ₗ[K] V) = q := by
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq (LinearEquiv.ofFinrankEq p q h)
  refine ⟨e, le_antisymm ?_ fun x hx ↦ ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [LinearEquiv.coe_coe, ← he ⟨x, hx⟩]
    exact Submodule.coe_mem _
  · refine ⟨((LinearEquiv.ofFinrankEq p q h).symm ⟨x, hx⟩ : V), Submodule.coe_mem _, ?_⟩
    rw [LinearEquiv.coe_coe, ← he]
    simp

/-- In a finite-dimensional space, a subspace has codimension one if and only if it is the
kernel of a nonzero linear form. When `finrank K V = 3` this says that the lines of the
projective plane are its hyperplanes. -/
theorem finrank_add_one_eq_iff_exists_ker_eq [FiniteDimensional K V] (p : Submodule K V) :
    finrank K p + 1 = finrank K V ↔ ∃ f : Dual K V, f ≠ 0 ∧ LinearMap.ker f = p := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hp : p < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun hp ↦ ?_
      rw [hp, finrank_top] at h
      omega
    obtain ⟨f, hf, hpf⟩ := p.exists_le_ker_of_lt_top hp
    refine ⟨f, hf, (Submodule.eq_of_le_of_finrank_eq hpf ?_).symm⟩
    have := Dual.finrank_ker_add_one_of_ne_zero hf
    omega
  · rintro ⟨f, hf, rfl⟩
    exact Dual.finrank_ker_add_one_of_ne_zero hf

end Submodule
