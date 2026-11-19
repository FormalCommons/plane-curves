/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.NonsingularModel.Normalization
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.IntersectionNumber.Properties

/-!
# Intersection numbers as sums of orders at places

Let `C : F = 0` be an irreducible projective plane curve over an algebraically closed field `k`,
with function field `K = k(C)`, and `P ∈ C`. The places of `K` centred at `P` are the points of
the nonsingular model of `C` over `P`. This file proves Fulton's Proposition 2 of §7.5: for every
form `G`,
`I(P, C ∩ G) = ∑_{Q over P} ord_Q(G)`,
both sides being `⊤` exactly when `F ∣ G`. More generally, for every nonzero `g ∈ 𝒪_P(C)`, the
length (that is, the `k`-dimension) of `𝒪_P(C) ⧸ (g)` is `∑_{Q over P} ord_Q(g)`.

The proof is the library route of the atlas: the integral closure `Õ` of `𝒪_P(C)` in `K` is the
holomorphy ring of the places over `P`, a finite `𝒪_P(C)`-module with a nonzero conductor
element; so `ℓ(𝒪_P(C) ⧸ (g)) = ℓ(Õ ⧸ (g)) = ∑_Q ord_Q g`
(`TauCeti.ord_eq_sum_ord_of_integralClosure_eq_holomorphyRing`).

## Main results

* `PlaneCurves.Projective.ord_localSubring_eq_sum_ord`: `ℓ(𝒪_P(C) ⧸ (g)) = ∑_Q ord_Q g` for every
  nonzero `g ∈ 𝒪_P(C)`, the sum running over the places over `P`, and
  `map_natCast_ord_localSubring_eq_sum_addValuation`, the same in `WithTop ℤ`.
* `PlaneCurves.Projective.map_natCast_intersectionNumber_eq_sum_ordForm`: intersection numbers
  as sums of orders at places, `I(P, C ∩ G) = ∑_Q ord_Q(G)`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.5, Proposition 2
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti
open TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
  (hF : F.IsHomogeneous d) [Fact (Irreducible F)]
  (P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)))

/-- A nonzero conductor element of `𝒪_P(C)` in its integral closure, in the form that
`TauCeti.ord_eq_sum_ord_of_integralClosure_eq_holomorphyRing` takes. -/
private theorem exists_ne_zero_mul_mem_range :
    ∃ t : (localSubring hF P).toSubring, t ≠ 0 ∧
      ∀ z ∈ integralClosure (localSubring hF P).toSubring (functionField hF),
        algebraMap (localSubring hF P).toSubring (functionField hF) t * z ∈
          (algebraMap (localSubring hF P).toSubring (functionField hF)).range := by
  obtain ⟨t, htP, ht0, ht⟩ := exists_ne_zero_mul_mem_localSubring hF P
  refine ⟨⟨t, htP⟩, fun h ↦ ht0 (congrArg Subtype.val h), fun z hz ↦ ?_⟩
  rw [← Subalgebra.mem_toSubring, integralClosure_localSubring] at hz
  exact ⟨⟨_, ht z hz⟩, rfl⟩

private theorem integralClosure_localSubring_toFinset :
    (integralClosure (localSubring hF P).toSubring (functionField hF)).toSubring =
      (holomorphyRing
        ((placesOver_finite hF P).toFinset : Set (Place k (functionField hF)))).toSubring := by
  rw [Set.Finite.coe_toFinset]
  exact integralClosure_localSubring hF P

/-- **`ℓ(𝒪_P(C) ⧸ (g)) = ∑_Q ord_Q g`.** For a nonzero `g` in the local ring `𝒪_P(C)` of an
irreducible projective plane curve at a point `P`, the length of `𝒪_P(C) ⧸ (g)` is the sum of the
orders of `g` at the places of `k(C)` centred at `P`. -/
theorem ord_localSubring_eq_sum_ord {g : (localSubring hF P).toSubring} (hg : g ≠ 0) :
    Ring.ord (localSubring hF P).toSubring g =
      ∑ Q ∈ (placesOver_finite hF P).toFinset, ((Q.ord (g : functionField hF)).toNat : ℕ∞) :=
  have := finite_integralClosure_localSubring hF P
  have ht := (exists_ne_zero_mul_mem_range hF P).choose_spec
  ord_eq_sum_ord_of_integralClosure_eq_holomorphyRing Subtype.val_injective
    (integralClosure_localSubring_toFinset hF P)
    (surjective_algebraMap_residueField_localSubring P) ht.1 ht.2 hg

/-- `ℓ(𝒪_P(C) ⧸ (g)) = ∑_Q ord_Q g` (`PlaneCurves.Projective.ord_localSubring_eq_sum_ord`), with
the orders read as the additive valuations `TauCeti.Place.addValuation` in `WithTop ℤ` and the
length cast from `ℕ∞`. -/
theorem map_natCast_ord_localSubring_eq_sum_addValuation {g : (localSubring hF P).toSubring}
    (hg : g ≠ 0) :
    (Ring.ord (localSubring hF P).toSubring g).map (Nat.cast : ℕ → ℤ) =
      ∑ Q ∈ (placesOver_finite hF P).toFinset, Q.addValuation (g : functionField hF) :=
  have := finite_integralClosure_localSubring hF P
  have ht := (exists_ne_zero_mul_mem_range hF P).choose_spec
  map_natCast_ord_eq_sum_addValuation_of_integralClosure_eq_holomorphyRing Subtype.val_injective
    (integralClosure_localSubring_toFinset hF P)
    (surjective_algebraMap_residueField_localSubring P) ht.1 ht.2 hg

/-- **Intersection numbers as sums of orders at places.** Let `k` be algebraically closed,
`C : F = 0` an irreducible projective plane curve, `P ∈ C`, and `G` any form of degree `m`. Then
`I(P, C ∩ G) = ∑_{Q over P} ord_Q(G)`,
the sum running over the places of `k(C)` centred at `P` (the points of the nonsingular model over
`P`), where `ord_Q(G)` is the order at `Q` of `G / Hᵐ` for any linear form `H` with `H(P) ≠ 0`.
The intersection number is cast from `ℕ∞` to `WithTop ℤ`; both sides are `⊤` exactly when
`F ∣ G`.

Milestone: *Intersection numbers as sums of orders at places*. -/
theorem map_natCast_intersectionNumber_eq_sum_ordForm {m : ℕ} {G : MvPolynomial (Fin 3) k}
    (hG : G.IsHomogeneous m) :
    (intersectionNumber P.1 F G).map (Nat.cast : ℕ → ℤ) =
      ∑ Q ∈ (placesOver_finite hF P).toFinset, ordForm hF Q hG := by
  by_cases hFG : F ∣ G
  · obtain ⟨Q, hQ⟩ := placesOver_nonempty hF P
    have hI : intersectionNumber P.1 F G = ⊤ := by
      by_contra h
      exact (intersectionNumber_ne_top_iff hF hG).1 h F (Fact.out) dvd_rfl hFG
        ((mem_zeroLocus_ideal_iff hF).1 P.2)
    rw [hI, ENat.map_top, eq_comm]
    exact WithTop.sum_eq_top.mpr ⟨Q, (placesOver_finite hF P).mem_toFinset.mpr hQ,
      (ordForm_eq_top_iff hG).mpr hFG⟩
  obtain ⟨i, hi⟩ := exists_mem_affineOpen P.1
  let c : HomogeneousLocalization.NumDenSameDeg (homogeneousSubmodule (Fin 3) k)
      (pointIdeal P.1).toIdeal.primeCompl :=
    ⟨m, ⟨G, (mem_homogeneousSubmodule _ _).2 hG⟩,
      ⟨X i ^ m, (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X_pow _ _)⟩,
      pow_mem (X_mem_primeCompl_pointIdeal hi) m⟩
  have hXP : eval P.1.rep (X i ^ m : MvPolynomial (Fin 3) k) ≠ 0 := by
    simpa using pow_ne_zero m ((mem_affineOpen_iff _ _).1 hi)
  set g := toLocalSubring hF P (HomogeneousLocalization.mk c)
  have hord : ∀ Q ∈ (placesOver_finite hF P).toFinset,
      ordForm hF Q hG = Q.addValuation (g : functionField hF) := by
    intro Q hQ
    have hQP : center hF Q = P :=
      mem_placesOver_iff.mp ((placesOver_finite hF P).mem_toFinset.mp hQ)
    rw [ordForm_eq_addValuation_mk hG (isHomogeneous_X_pow _ _) (hQP ▸ hXP),
      coe_toLocalSubring_mk]
  have hg : g ≠ 0 := by
    obtain ⟨Q, hQ⟩ := placesOver_nonempty hF P
    intro h
    have := hord Q ((placesOver_finite hF P).mem_toFinset.mpr hQ)
    rw [h, ZeroMemClass.coe_zero, AddValuation.map_zero, ordForm_eq_top_iff] at this
    exact hFG this
  rw [intersectionNumber_eq_ord_localSubring hF P c,
    map_natCast_ord_localSubring_eq_sum_addValuation hF P hg]
  exact (Finset.sum_congr rfl hord).symm

end PlaneCurves.Projective

end
