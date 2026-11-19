/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.Adjoin.Tower
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Subalgebras inside a finite module over a smaller subalgebra

Let `A ≤ B` be subalgebras of an `R`-algebra `S`, with `A` finitely generated over `R` and
Noetherian. If `B` lies in a finitely generated `A`-submodule of `S`, then `B` is a finitely
generated `R`-algebra: `B` is a finite `A`-module, since `A` is Noetherian, and generators of
`A` over `R` together with generators of `B` over `A` generate `B` over `R`.

## Main results

* `Subalgebra.fg_of_le_of_subset_fg`.
-/

public section

namespace Subalgebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Let `A ≤ B` be subalgebras of `S`, with `A` finitely generated and Noetherian. If `B` lies in
a finitely generated `A`-submodule of `S`, then `B` is finitely generated. -/
theorem fg_of_le_of_subset_fg {A B : Subalgebra R S} (hA : A.FG) [IsNoetherianRing A]
    (hAB : A ≤ B) {M : Submodule A S} (hM : M.FG) (hBM : (B : Set S) ⊆ M) : B.FG := by
  classical
  let B' : Subalgebra A S :=
    { B.toSubsemiring with algebraMap_mem' := fun a ↦ hAB a.2 }
  have : IsNoetherian A M := isNoetherian_of_fg_of_noetherian M hM
  obtain ⟨s, hs⟩ := fg_of_fg_toSubmodule
    (Submodule.FG.of_le_of_isNoetherian (S := Subalgebra.toSubmodule B') (T := M) hBM)
  obtain ⟨t, rfl⟩ := hA
  refine ⟨t ∪ s, ?_⟩
  rw [Finset.coe_union, Algebra.adjoin_union_eq_adjoin_adjoin]
  ext x
  rw [mem_restrictScalars, hs]
  exact Iff.rfl

end Subalgebra

end
