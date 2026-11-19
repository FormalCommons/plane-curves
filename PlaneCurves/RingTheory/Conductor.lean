/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.Localization.Integer
public import TauCeti.RingTheory.Conductor

/-!
# Conductor elements in a localization

Let `A → B → L` be ring maps, with `L` a localization of `A` at a submonoid `M`, `B` finite
over `A` and `B → L` injective. Then `B` sits between `A` and `M⁻¹A`, and a common denominator
of finitely many generators of `B` lies in the conductor of `B` over `A`.

* `TauCeti.Algebra.exists_mem_conductor_of_isLocalization`: some `a ∈ M` lies in
  `TauCeti.Algebra.conductor A B`.

For `A` the local ring of a curve at a point, `B` its integral closure in the function field
and `M` the nonzero elements, this gives a nonzero element of `A` in the conductor.
-/

public section

namespace TauCeti.Algebra

/-- Let `L` be the localization of `A` at `M`, and `B` a finite `A`-algebra with an injective
map `B → L` compatible with `A`. Then some element of `M` lies in the conductor of `B` over
`A`: it carries every element of `B` into the image of `A`. -/
theorem exists_mem_conductor_of_isLocalization
    {A B L : Type*} [CommRing A] [CommRing B] [CommRing L] [Algebra A B] [Algebra A L]
    [Algebra B L] [IsScalarTower A B L] (M : Submonoid A) [IsLocalization M L]
    [Module.Finite A B] (hB : Function.Injective (algebraMap B L)) :
    ∃ a ∈ M, a ∈ conductor A B := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := B)
  obtain ⟨⟨a, ha⟩, h⟩ := IsLocalization.exist_integer_multiples_of_finset M
    (s.image (algebraMap B L))
  refine ⟨a, ha, mem_conductor_iff.mpr fun b ↦ ?_⟩
  have hle : (⊤ : Submodule A B) ≤
      (1 : Submodule A B).comap (LinearMap.mulLeft A (algebraMap A B a)) := by
    rw [← hs, Submodule.span_le]
    intro g hg
    obtain ⟨c, hc⟩ := h _ (Finset.mem_image_of_mem _ hg)
    refine Submodule.mem_one.mpr ⟨c, hB ?_⟩
    rw [← IsScalarTower.algebraMap_apply, hc, LinearMap.mulLeft_apply, map_mul,
      ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
  obtain ⟨c, hc⟩ := Submodule.mem_one.mp (hle Submodule.mem_top)
  exact ⟨c, hc⟩

end TauCeti.Algebra

end
