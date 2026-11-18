/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Surjectivity of induced maps of projective spaces

A semilinear map `f : V → W` that is injective induces `Projectivization.map f : ℙ V → ℙ W`.
This file shows that the induced map is onto when `f` is.

## Main results

* `Projectivization.map_surjective`: if `f` is bijective, so is `Projectivization.map f`.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {K L V W : Type*} [DivisionRing K] [DivisionRing L] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module L W] {σ : K →+* L}

/-- The map of projective spaces induced by a surjective injective semilinear map is
surjective. -/
theorem map_surjective (f : V →ₛₗ[σ] W) (hf : Function.Injective f)
    (hs : Function.Surjective f) : Function.Surjective (map f hf) := by
  intro P
  obtain ⟨w, hw⟩ := hs P.rep
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact P.rep_ne_zero (by simpa using hw.symm)
  exact ⟨mk K w hw0, by simp only [map_mk, hw, mk_rep]⟩

/-- The map of projective spaces induced by a bijective semilinear map is bijective. -/
theorem map_bijective {τ : L →+* K} [RingHomInvPair σ τ] (f : V →ₛₗ[σ] W)
    (hf : Function.Injective f) (hs : Function.Surjective f) : Function.Bijective (map f hf) :=
  ⟨map_injective f hf, map_surjective f hf hs⟩

end Projectivization

end
