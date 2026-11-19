/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.IntersectionNumber
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.SimplePoint
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.GenericLine

/-!
# The nonsingular model of a projective plane curve

Let `k` be an algebraically closed field and `C : F = 0` an irreducible projective plane curve
with function field `K = k(C)`. The **nonsingular model** of `C` is the set `Place k K` of places
of `K` (the discrete valuation rings of `K` over `k`), with the centre map
`center hF : Place k K → C` sending a place `Q` to the unique point `P` whose local ring
`𝒪_P(C)` is dominated by the valuation ring of `Q`. The places centred at `P` are the places
of `C` over `P`.

This file proves the properties of the centre map that make it the nonsingular model of `C`:
it is surjective, its fibres are finite, it has exactly one point over a simple point `P` (whose
valuation ring is `𝒪_P(C)`), and over any point `P` at most `m_P(C)` places lie. The last
bound follows from `I(P, C ∩ L) = ∑_{Q over P} ord_Q(L) ≥ #{Q over P}` for a line `L` through
`P` that is not tangent to `C` at `P`, where `I(P, C ∩ L) = m_P(C)`.

## Main results

* `ncard_placesOver_le_mult`: at most `m_P(C)` places of `k(C)` lie over a point `P ∈ C`.
* `center_spec`: the milestone, the nonsingular model of `C` and its centre map.

## The scheme-theoretic form

As schemes, the nonsingular projective curve with function field `K` is Tau Ceti's
`TauCeti.AlgebraicGeometry.twoChartModel`, whose closed points are the places of `K`
(`TauCeti.AlgebraicGeometry.twoChartModel.equivPlace`); a nonsingular projective curve is
determined up to unique isomorphism by its function field
(`AlgebraicGeometry.Scheme.isoOfFunctionFieldAlgEquiv`, and
`TauCeti.AlgebraicGeometry.RegularProjectiveCurveCat.equivFunctionFieldCat` for the
anti-equivalence with function fields of one variable). A dominant morphism of proper curves is
surjective (Fulton's Problem 8.18), by Mathlib's instance
`AlgebraicGeometry.Surjective.of_universallyClosed_of_isDominant`; in terms of places, every
place of a function field extends to a finite extension (`TauCeti.Place.restrict_surjective`).

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.5, Theorem 3 and Problem 7.17
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti
open TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
  (hF : F.IsHomogeneous d) [Fact (Irreducible F)]

/-- **At most `m_P(C)` places lie over a point.** For a point `P` of an irreducible projective
plane curve `C : F = 0`, the number of places of `k(C)` centred at `P` is at most the
multiplicity `m_P(C)`: for a line `L` through `P` not tangent to `C` at `P`,
`m_P(C) = I(P, C ∩ L) = ∑_{Q over P} ord_Q(L)`, and every term is at least `1`. -/
theorem ncard_placesOver_le_mult
    (P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))) :
    (placesOver hF P).ncard ≤ (mult F P.1).toNat := by
  have hF0 : F ≠ 0 := (Fact.out : Irreducible F).ne_zero
  obtain ⟨c, hcP, hcT⟩ := ((infinite_setOf_eval_sum_C_mul_X_eq_zero P.1).sdiff
    (finite_setOf_isTangentAt hF0 P.1)).nonempty
  have hL := isHomogeneous_sum_C_mul_X (R := k) c.rep
  have hI : intersectionNumber P.1 F (∑ i, C (c.rep i) * X i) = mult F P.1 :=
    (intersectionNumber_eq_mult_iff_not_isTangentAt hF hF0 hL
      (sum_C_mul_X_ne_zero c.rep_ne_zero) hcP).2 hcT
  have hsum := map_natCast_intersectionNumber_eq_sum_ordForm hF P hL
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (mult_ne_top hF0)
  rw [hI, ← hn] at hsum
  have hle : ∑ _Q ∈ (placesOver_finite hF P).toFinset, (1 : WithTop ℤ) ≤
      ∑ Q ∈ (placesOver_finite hF P).toFinset, ordForm hF Q hL := by
    have h1 : ∀ x : WithTop ℤ, 0 < x → 1 ≤ x := by
      intro x hx
      induction x with
      | top => exact le_top
      | coe a => exact_mod_cast (show (0 : ℤ) < a by exact_mod_cast hx)
    refine Finset.sum_le_sum fun Q hQ ↦ h1 _ ((ordForm_pos_iff hL).2 ?_)
    rwa [mem_placesOver_iff.1 ((placesOver_finite hF P).mem_toFinset.1 hQ)]
  rw [← hsum, Finset.sum_const, nsmul_one, ENat.map_natCast] at hle
  rw [Set.ncard_eq_toFinset_card _ (placesOver_finite hF P), ← hn, ENat.toNat_natCast]
  exact_mod_cast hle

/-- **Existence and uniqueness of the nonsingular model of a projective plane curve.** Let `k`
be algebraically closed and `C : F = 0` an irreducible projective plane curve with function
field `K = k(C)`. The nonsingular model of `C` is the set of places of `K`, the points `Q`
corresponding to their valuation rings `𝒪_Q`, the discrete valuation rings of `K` over `k`;
the morphism to `C` is the centre map, `Q` being centred at `P` exactly when `𝒪_Q` dominates
`𝒪_P(C)`. Then:

* (a) a place is determined by its valuation ring;
* (b) `Q` is centred at `P` iff `𝒪_P(C) ⊆ 𝒪_Q`;
* (c) the centre map is surjective, and every point `P ∈ C` has a nonempty finite set of
  places centred at it, at most `m_P(C)` of them;
* (d) a simple point `P` has exactly one place centred at it, with valuation ring `𝒪_P(C)`;
* (e) if `C` is nonsingular, the centre map is a bijection, so that `C` is its own nonsingular
  model.

The nonsingular model as a scheme, and its uniqueness up to unique isomorphism, are Tau Ceti's
(see the module docstring).

Milestone: *Existence and uniqueness of the nonsingular model of a projective curve*. -/
theorem center_spec :
    -- (a)
    Function.Injective (fun Q : Place k (functionField hF) ↦ Q.integers) ∧
    -- (b)
    (∀ (Q : Place k (functionField hF)) P,
      center hF Q = P ↔ (localSubring hF P).toSubring ≤ Q.integers.toSubring) ∧
    -- (c)
    Function.Surjective (center hF) ∧
    (∀ P, (placesOver hF P).Nonempty ∧ (placesOver hF P).Finite ∧
      (placesOver hF P).ncard ≤ (mult F P.1).toNat) ∧
    -- (d)
    (∀ P, IsSimplePoint F P.1 →
      (∃! Q : Place k (functionField hF), center hF Q = P) ∧
      ∀ Q : Place k (functionField hF), center hF Q = P →
        Q.integers.toSubring = (localSubring hF P).toSubring) ∧
    -- (e)
    (IsNonsingular F → Function.Bijective (center hF)) := by
  refine ⟨Place.integers_injective, fun _ _ ↦ center_eq_iff_le, center_surjective hF,
    fun P ↦ ⟨placesOver_nonempty hF P, placesOver_finite hF P, ncard_placesOver_le_mult hF P⟩,
    fun P hP ↦ ⟨⟨placeAt hF hP, center_placeAt hP, fun Q hQ ↦ ?_⟩, fun Q hQ ↦ ?_⟩,
    center_bijective hF⟩
  · simpa [placesOver_eq_singleton hP] using (mem_placesOver_iff (P := P)).2 hQ
  · rw [← hQ, ← integers_toSubring_placeAt (hQ ▸ hP), placeAt_center]

end PlaneCurves.Projective

end
