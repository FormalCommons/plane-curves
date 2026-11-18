/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.AffineSpace.QuotientPiLocalRing
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.Basic

/-!
# The sum of the local intersection numbers

Let `k` be algebraically closed and `F, G ∈ k[X, Y]`. If `F` and `G` have finitely many common
zeros, for instance if they have no common component, then the local intersection numbers add
up to the dimension of the intersection ring:
`∑_{P ∈ V(F, G)} I(P, F ∩ G) = dim_k k[X, Y] ⧸ (F, G)`. This is Fulton's property (9).

## Main results

* `PlaneCurves.Affine.intersectionNumber_eq_finrank`: if `k[X, Y] ⧸ (F, G)` is
  finite-dimensional, `I(P, F ∩ G)` is the dimension of `𝒪_P(𝔸²) ⧸ (F, G) 𝒪_P(𝔸²)`.
* `PlaneCurves.Affine.sum_intersectionNumber_eq_finrank`: property (9) when `V(F, G)` is finite.
* `PlaneCurves.Affine.sum_intersectionNumber_eq_finrank_of_isRelPrime`: property (9) for `F` and
  `G` without common component.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.3, property (9)
-/

public section

open MvPolynomial

namespace PlaneCurves.Affine

variable {k : Type*} [Field k] {F G : MvPolynomial (Fin 2) k}

/-- If `k[X, Y] ⧸ (F, G)` is finite-dimensional, then `I(P, F ∩ G)` is the (finite) dimension
over `k` of `𝒪_P(𝔸²) ⧸ (F, G) 𝒪_P(𝔸²)`. -/
theorem intersectionNumber_eq_finrank
    [Module.Finite k (MvPolynomial (Fin 2) k ⧸ Ideal.span {F, G})] (P : Fin 2 → k) :
    intersectionNumber P F G = Module.finrank k (AffineSpace.localRing k P ⧸
      (Ideal.span {F, G}).map (algebraMap _ (AffineSpace.localRing k P))) := by
  have h := intersectionNumber_ne_top_of_finite (P := P) (F := F) (G := G)
  rw [intersectionNumber_eq_rank, Ideal.map_span, Set.image_pair, Module.finrank,
    ← Cardinal.toNat_toENat] at *
  exact (ENat.natCast_toNat h).symm

variable [IsAlgClosed k]

/-- **Property (9)**, for finitely many common zeros. Let `k` be algebraically closed and
`F, G ∈ k[X, Y]` with finitely many common zeros. Then
`∑_{P ∈ V(F, G)} I(P, F ∩ G) = dim_k k[X, Y] ⧸ (F, G)`, which is finite. -/
theorem sum_intersectionNumber_eq_finrank (h : (zeroLocus k (Ideal.span {F, G})).Finite) :
    ∑ P ∈ h.toFinset, intersectionNumber P F G =
      Module.finrank k (MvPolynomial (Fin 2) k ⧸ Ideal.span {F, G}) := by
  have := (finite_zeroLocus_iff _).1 h
  rw [AffineSpace.finrank_quotient_eq_sum _ h, Nat.cast_sum]
  exact Finset.sum_congr rfl fun P _ => intersectionNumber_eq_finrank P

/-- **Sum of local intersection numbers equals the dimension of the intersection ring**
(Fulton, §3.3, property (9)). Let `k` be algebraically closed and `F, G ∈ k[X, Y]` with no
common component. Then `V(F, G)` is finite, `k[X, Y] ⧸ (F, G)` is finite-dimensional, and
`∑_{P ∈ V(F, G)} I(P, F ∩ G) = dim_k k[X, Y] ⧸ (F, G)`.

Milestone: *Sum of local intersection numbers equals the dimension of the intersection ring*. -/
theorem sum_intersectionNumber_eq_finrank_of_isRelPrime (h : IsRelPrime F G) :
    ∃ hV : (zeroLocus k (Ideal.span {F, G})).Finite,
      Module.Finite k (MvPolynomial (Fin 2) k ⧸ Ideal.span {F, G}) ∧
      ∑ P ∈ hV.toFinset, intersectionNumber P F G =
        Module.finrank k (MvPolynomial (Fin 2) k ⧸ Ideal.span {F, G}) :=
  ⟨finite_zeroLocus_span_pair_of_isRelPrime h k, finite_quotient_span_pair_of_isRelPrime h,
    sum_intersectionNumber_eq_finrank _⟩

end PlaneCurves.Affine

end
