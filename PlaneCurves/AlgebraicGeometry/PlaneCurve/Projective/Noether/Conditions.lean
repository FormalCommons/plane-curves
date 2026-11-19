/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.IntersectionNumber.Properties
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Noether.Basic

/-!
# Local criteria for Noether's conditions

Let `F`, `G` and `H` be forms in `k[X, Y, Z]` and `P` a point of `ℙ²`. Noether's conditions hold
at `P` (`NoetherConditionsAt P F G H`, that is `H_* ∈ (F_*, G_*)` in `𝒪_P(ℙ²)`) in each of the
following cases (Fulton, §5.5, Proposition 1):

1. `F` and `G` meet transversally at `P`, that is `I(P, F ∩ G) = 1`, and `H(P) = 0`;
2. `P` is a simple point of `F` and `I(P, F ∩ G) ≤ I(P, F ∩ H)`;
3. `F` and `G` have no common tangent at `P` and `m_P(H) ≥ m_P(F) + m_P(G) - 1`.

For (2), `𝒪_P(ℙ²) ⧸ (F_*)` is a discrete valuation ring in which `I(P, F ∩ G)` is the order of
`G_*`, so the inequality says that `G_*` divides `H_*` there. For (3), in an affine chart the
power `𝔪_P ^ t` of the maximal ideal lies in `(F_*, G_*)` for `t ≥ m_P(F) + m_P(G) - 1`. And (1)
follows from (2): transversality makes `P` a simple point of `F`, and `I(P, F ∩ H) ≥ 1`.

None of the criteria asks that `F` and `G` have no common component through `P`, and (1) and (2)
hold over any field.

## Main results

* `noetherConditionsAt_of_intersectionNumber_eq_one`: criterion (1).
* `noetherConditionsAt_of_isSimplePoint`: criterion (2).
* `noetherConditionsAt_of_not_exists_isTangentAt`: criterion (3).

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.5, Proposition 1
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {P : ℙ k (Fin 3 → k)} {F G H : MvPolynomial (Fin 3) k}
  {d e r : ℕ}

/-- **Noether's conditions at a simple point** (Fulton, §5.5, Proposition 1 (2)). If `P` is a
simple point of the form `F` and `I(P, F ∩ G) ≤ I(P, F ∩ H)` for forms `G` and `H`, then
Noether's conditions hold at `P`: `H_* ∈ (F_*, G_*)`. The curve `F` may be reducible, and
`I(P, F ∩ H)` may be infinite. -/
theorem noetherConditionsAt_of_isSimplePoint (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e)
    (hH : H.IsHomogeneous r) (hP : IsSimplePoint F P)
    (h : intersectionNumber P F G ≤ intersectionNumber P F H) : NoetherConditionsAt P F G H := by
  have hP0 : eval P.rep F = 0 :=
    mult_pos_iff_eval_rep.1 (by rw [isSimplePoint_def.1 hP]; exact one_pos)
  obtain ⟨_, _⟩ := (exists_isDiscreteValuationRing_quotient_iff hF hP0).2 hP
  rw [intersectionNumber_eq_ord hF hG, intersectionNumber_eq_ord hF hH, Ring.ord_eq_addVal,
    Ring.ord_eq_addVal, IsDiscreteValuationRing.addVal_le_iff_dvd] at h
  obtain ⟨c, hc⟩ := h
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hc
  obtain ⟨a, ha⟩ := hc
  rw [noetherConditionsAt_iff hF hG, Ideal.mem_span_pair]
  exact ⟨a, c, by linear_combination ha⟩

/-- **Noether's conditions at a transversal intersection** (Fulton, §5.5, Proposition 1 (1)).
If the forms `F` and `G` meet transversally at `P`, that is `I(P, F ∩ G) = 1`, then Noether's
conditions hold at `P` for every form `H` with `H(P) = 0`. -/
theorem noetherConditionsAt_of_intersectionNumber_eq_one (hF : F.IsHomogeneous d)
    (hG : G.IsHomogeneous e) (hH : H.IsHomogeneous r) (h1 : intersectionNumber P F G = 1)
    (hHP : eval P.rep H = 0) : NoetherConditionsAt P F G H := by
  have hPF : eval P.rep F = 0 ∧ eval P.rep G = 0 := by
    have h0 : intersectionNumber P F G ≠ 0 := by rw [h1]; exact one_ne_zero
    simpa [intersectionNumber_eq_zero_iff hF hG] using h0
  have hmF : 0 < mult F P := mult_pos_iff_eval_rep.2 hPF.1
  have hmG : 1 ≤ mult G P := Order.one_le_iff_pos.2 (mult_pos_iff_eval_rep.2 hPF.2)
  have hle : mult F P ≤ 1 := by
    calc mult F P = mult F P * 1 := (mul_one _).symm
      _ ≤ mult F P * mult G P := mul_le_mul_right hmG _
      _ ≤ 1 := h1 ▸ mul_mult_le_intersectionNumber hF hG
  refine noetherConditionsAt_of_isSimplePoint hF hG hH
    (isSimplePoint_def.2 (le_antisymm hle (Order.one_le_iff_pos.2 hmF))) ?_
  rw [h1]
  exact one_le_intersectionNumber hF hH hPF.1 hHP

/-- **Noether's conditions without common tangents** (Fulton, §5.5, Proposition 1 (3)). Let `k`
be algebraically closed and `F`, `G`, `H` forms. If `F` and `G` have no common tangent at `P`
and `m_P(H) ≥ m_P(F) + m_P(G) - 1`, then Noether's conditions hold at `P`. -/
theorem noetherConditionsAt_of_not_exists_isTangentAt [IsAlgClosed k] (hF : F.IsHomogeneous d)
    (hG : G.IsHomogeneous e) (hH : H.IsHomogeneous r)
    (hT : ¬∃ L, IsTangentAt F P L ∧ IsTangentAt G P L)
    (hm : mult F P + mult G P - 1 ≤ mult H P) : NoetherConditionsAt P F G H := by
  by_cases hF0 : F = 0
  · obtain rfl : H = 0 := by simpa [hF0] using hm
    rw [noetherConditionsAt_iff hF hG, map_zero]
    exact zero_mem _
  obtain ⟨i, hP⟩ := exists_mem_affineOpen P
  rw [noetherConditionsAt_iff hF hG, ← Ideal.mem_span_pair_iff_of_ringEquiv
    (localRing.chartEquiv i hP).toRingEquiv (associated_chartEquiv_localEquation hF hP)
    (associated_chartEquiv_localEquation hG hP) (associated_chartEquiv_localEquation hH hP)]
  rw [exists_isTangentAt_iff_affine hF hG hP,
    ← Affine.isRelPrime_leadingFormAt_iff_not_exists_isTangentAt
    (dehomogenize_ne_zero_of_isHomogeneous i hF hF0)] at hT
  rw [mult_eq_orderAt_dehomogenize hF hP, mult_eq_orderAt_dehomogenize hG hP,
    mult_eq_orderAt_dehomogenize hH hP] at hm
  refine Affine.algebraMap_mem_span_pair_of_isRelPrime_leadingFormAt hT (le_trans ?_ hm)
  rw [ENat.natCast_sub, Nat.cast_add, Nat.cast_one]
  exact tsub_le_tsub_right (add_le_add (ENat.natCast_toNat_le_self _)
    (ENat.natCast_toNat_le_self _)) _

end PlaneCurves.Projective

end
