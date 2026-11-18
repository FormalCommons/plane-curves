/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import TauCeti.RingTheory.Intersection
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.LocalRing

/-!
# The intersection number at a simple point

For plane curves `F` and `G` and a point `P`, the intersection number `I(P, F ∩ G)` is the order
`ord_P^F(G)` of the image of `G` in the local ring `𝒪_P(𝔸²)/(F)` of `F` at `P`, in the sense of
Mathlib's `Ring.ord` (the length of `(𝒪_P(𝔸²)/(F))/(G)`). When `P` is a simple point of `F`, this
local ring is a discrete valuation ring, so the intersection number is a valuation: this is
Fulton's Property (8). It is `⊤` exactly when the component of `F` through `P` divides `G`, and
it satisfies `I(P, F ∩ (G + H)) ≥ min (I(P, F ∩ G), I(P, F ∩ H))` (Problem 3.20).

## Main results

* `PlaneCurves.Affine.intersectionNumber_eq_ord`: `I(P, F ∩ G) = ord_P^F(G)`, for any `F`.
* `PlaneCurves.Affine.IsSimplePoint.associated_of_irreducible_dvd`: at a simple point, `F` has
  only one irreducible factor through `P`, up to associates.
* `PlaneCurves.Affine.IsSimplePoint.intersectionNumber_eq_top_iff_dvd`: at a simple point,
  `I(P, F ∩ G) = ⊤` iff the component of `F` through `P` divides `G`.
* `PlaneCurves.Affine.IsSimplePoint.min_le_intersectionNumber_add`: Problem 3.20.
* `PlaneCurves.Affine.IsSimplePoint.intersectionNumber_eq_ord_and_eq_top_iff_and_min_le`:
  all of these together, Property (8) of §3.3 of Fulton.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.3, Property (8), Problems 3.18 and 3.20
-/

public section

open MvPolynomial Ideal

namespace PlaneCurves.Affine

open AffineSpace

variable {k : Type*} [Field k] {F G H : MvPolynomial (Fin 2) k} {P : Fin 2 → k}

/-- The intersection number `I(P, F ∩ G)` is the order of the image of `G` in the local ring
`𝒪_P(𝔸²)/(F)` of `F` at `P`: the length of its quotient by `G`. -/
theorem intersectionNumber_eq_ord (P : Fin 2 → k) (F G : MvPolynomial (Fin 2) k) :
    intersectionNumber P F G = Ring.ord (localRing k P ⧸ span {algebraMap _ (localRing k P) F})
      (Ideal.Quotient.mk _ (algebraMap _ (localRing k P) G)) :=
  (intersectionNumber_def P F G).trans (TauCeti.ord_eq_length_quotient_span_pair _ _).symm

/-- At a simple point `P` of `F`, any two irreducible factors of `F` vanishing at `P` are
associated: exactly one component of `F` passes through `P`. -/
theorem IsSimplePoint.associated_of_irreducible_dvd (hF : IsSimplePoint F P)
    {H H' : MvPolynomial (Fin 2) k} (hH : Irreducible H) (hHF : H ∣ F) (hHP : eval P H = 0)
    (hH' : Irreducible H') (hH'F : H' ∣ F) (hH'P : eval P H' = 0) : Associated H H' := by
  by_contra hne
  obtain ⟨c, rfl⟩ := hH'F
  have hHc : H ∣ c := (hH.prime.dvd_or_dvd hHF).resolve_left
    fun h ↦ hne (hH.associated_of_dvd hH' h)
  obtain ⟨e, rfl⟩ := hHc
  have h1 := isSimplePoint_iff_orderAt_eq_one.1 hF
  rw [orderAt_mul, orderAt_mul] at h1
  have := add_le_add (Order.one_le_iff_pos.2 (orderAt_pos_iff.2 hH'P))
    (le_add_right (Order.one_le_iff_pos.2 (orderAt_pos_iff.2 hHP)) :
      1 ≤ H.orderAt P + e.orderAt P)
  rw [h1] at this
  norm_num at this

/-- At a simple point `P` of `F`, with `H` the component of `F` through `P`,
`I(P, F ∩ G) = ⊤` iff `H` divides `G`. -/
theorem IsSimplePoint.intersectionNumber_eq_top_iff_dvd (hF : IsSimplePoint F P)
    (hH : Irreducible H) (hHF : H ∣ F) (hHP : eval P H = 0) :
    intersectionNumber P F G = ⊤ ↔ H ∣ G := by
  rw [intersectionNumber_eq_top_iff, intersectProperlyAt_def]
  refine ⟨fun h ↦ ?_, fun hG h ↦ h H hH hHF hG hHP⟩
  push Not at h
  obtain ⟨H', hH', hH'F, hH'G, hH'P⟩ := h
  exact (hF.associated_of_irreducible_dvd hH hHF hHP hH' hH'F hH'P).dvd.trans hH'G

/-- **Problem 3.20**: at a simple point `P` of `F`,
`I(P, F ∩ (G + H)) ≥ min (I(P, F ∩ G), I(P, F ∩ H))`. -/
theorem IsSimplePoint.min_le_intersectionNumber_add (hF : IsSimplePoint F P)
    (G H : MvPolynomial (Fin 2) k) :
    min (intersectionNumber P F G) (intersectionNumber P F H) ≤
      intersectionNumber P F (G + H) := by
  obtain ⟨_, _⟩ := (exists_isDiscreteValuationRing_quotient_iff hF.eval_eq_zero).2 hF
  rw [intersectionNumber_eq_ord, intersectionNumber_eq_ord, intersectionNumber_eq_ord, map_add,
    map_add]
  exact Ring.ord_add (R := localRing k P ⧸ span {algebraMap _ (localRing k P) F}) _ _

/-- **The intersection number at a simple point is an order of vanishing** (Property (8)). Let
`P` be a simple point of a plane curve `F` over a field `k`, so that the local ring
`𝒪 = 𝒪_P(𝔸²)/(F)` of `F` at `P` is a discrete valuation ring
(`exists_isDiscreteValuationRing_quotient_iff`), which is `𝒪_P(F₁)` for the only component `F₁`
of `F` through `P`. Then:

1. `I(P, F ∩ G) = ord_P^F(G)`, the order `Ring.ord 𝒪` of the image of `G` (which is its
   valuation, by `Ring.ord_eq_addVal`);
2. `I(P, F ∩ G) = ⊤` iff `F₁ ∣ G`, for `F₁` an irreducible factor of `F` vanishing at `P`;
3. `I(P, F ∩ (G + H)) ≥ min (I(P, F ∩ G), I(P, F ∩ H))` (Problem 3.20).

Milestone: *Intersection number at a simple point is an order of vanishing*. -/
theorem IsSimplePoint.intersectionNumber_eq_ord_and_eq_top_iff_and_min_le
    (hF : IsSimplePoint F P) :
    (∃ _ : IsDomain (localRing k P ⧸ span {algebraMap _ (localRing k P) F}),
      IsDiscreteValuationRing (localRing k P ⧸ span {algebraMap _ (localRing k P) F})) ∧
    (∀ G, intersectionNumber P F G =
      Ring.ord (localRing k P ⧸ span {algebraMap _ (localRing k P) F})
        (Ideal.Quotient.mk _ (algebraMap _ (localRing k P) G))) ∧
    (∀ G F₁, Irreducible F₁ → F₁ ∣ F → eval P F₁ = 0 → (intersectionNumber P F G = ⊤ ↔ F₁ ∣ G)) ∧
    (∀ G H, min (intersectionNumber P F G) (intersectionNumber P F H) ≤
      intersectionNumber P F (G + H)) :=
  ⟨(exists_isDiscreteValuationRing_quotient_iff hF.eval_eq_zero).2 hF,
    intersectionNumber_eq_ord P F, fun _ _ h₁ h₂ h₃ ↦ hF.intersectionNumber_eq_top_iff_dvd h₁ h₂ h₃,
    hF.min_le_intersectionNumber_add⟩

end PlaneCurves.Affine

end
