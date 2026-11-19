/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Bezout.Corollaries
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.IntersectionNumber.Properties
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Noether.Basic

/-!
# Local criteria for Noether's conditions and the residual intersection

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

Criteria (1) and (2) are also necessary (Fulton, Problem 5.29): Noether's conditions force
`H(P) = 0` at a common zero of `F` and `G`, and `I(P, F ∩ G) ≤ I(P, F ∩ H)` always, since
`(F_*, H_*) ⊆ (F_*, G_*)`. Criterion (3) is not: for `P = [0 : 1 : 0]`, `F = X³ - YZ²` and
`G = Z³ - X²Y` have tangent cones `Z²` and `X²` at `P`, and `H = F` satisfies Noether's conditions
with `m_P(H) = 2 < 3 = m_P(F) + m_P(G) - 1`.

**The residual intersection** (Fulton, §5.5, Corollary to Proposition 1). Let `k` be
algebraically closed, `F` of positive degree and prime to `G` and `H`. If Noether's conditions
hold at every point of `V(F) ∩ V(G)`, Max Noether's theorem writes `H = A F + B G` with `B` a form
of degree `deg H - deg G`, so `H • F = B • F + G • F`, and `B` is prime to `F`, since a common
component of `B` and `F` would divide `H`. Criteria (1) and (2) give the two cases of the
Corollary: `V(F) ∩ V(G)` consists of `deg F * deg G` points, all transversal by Corollary 2 of
Bézout's theorem, and `H` vanishes at them; or every point of `V(F) ∩ V(G)` is simple on `F` and
`G • F ≤ H • F`. Fulton's curves are nonconstant; for a constant `F` the Corollary fails
(`exists_isHomogeneous_zero_and_not_le`).

## Main results

* `noetherConditionsAt_of_intersectionNumber_eq_one`: criterion (1).
* `noetherConditionsAt_of_isSimplePoint`: criterion (2).
* `noetherConditionsAt_of_not_exists_isTangentAt`: criterion (3).
* `noetherConditionsAt_iff_eval_rep_eq_zero`, `noetherConditionsAt_iff_intersectionNumber_le`:
  criteria (1) and (2) are necessary.
* `exists_noetherConditionsAt_and_mult_lt`: criterion (3) is not necessary.
* `exists_isHomogeneous_intersectionCycle_eq_add_of_forall_noetherConditionsAt`: the residual
  intersection, from Noether's conditions at every point.
* `exists_isHomogeneous_intersectionCycle_eq_sub_of_card_eq_mul`,
  `exists_isHomogeneous_intersectionCycle_eq_sub_of_isSimplePoint`: the Corollary, cases (1)
  and (2).
* `noetherConditionsAt_of_intersectionNumber_eq_one_spec`: the milestone, combining
  Proposition 1, Problem 5.29 and the Corollary.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.5, Proposition 1, its Corollary and Problem 5.29
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

/-! ### Necessity of criteria (1) and (2) -/

/-- Noether's conditions at a common zero `P` of the forms `F` and `G` force `H(P) = 0`: then
`(F_*, G_*)` lies in the maximal ideal of `𝒪_P(ℙ²)`. -/
theorem NoetherConditionsAt.eval_rep_eq_zero (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e)
    (hH : H.IsHomogeneous r) (h : NoetherConditionsAt P F G H) (hPF : eval P.rep F = 0)
    (hPG : eval P.rep G = 0) : eval P.rep H = 0 := by
  rw [noetherConditionsAt_iff hF hG] at h
  have hle : Ideal.span {localEquation P F, localEquation P G} ≤
      IsLocalRing.maximalIdeal (localRing P) := by
    rw [Ideal.span_le, Set.pair_subset_iff]
    exact ⟨(IsLocalRing.mem_maximalIdeal _).2 fun hu ↦ (isUnit_localEquation_iff hF).1 hu hPF,
      (IsLocalRing.mem_maximalIdeal _).2 fun hu ↦ (isUnit_localEquation_iff hG).1 hu hPG⟩
  by_contra hPH
  exact (IsLocalRing.mem_maximalIdeal _).1 (hle h) ((isUnit_localEquation_iff hH).2 hPH)

/-- Noether's conditions at `P` force `I(P, F ∩ G) ≤ I(P, F ∩ H)`: `H_* ∈ (F_*, G_*)` gives
`(F_*, H_*) ⊆ (F_*, G_*)`, so `𝒪_P(ℙ²) ⧸ (F_*, G_*)` is a quotient of
`𝒪_P(ℙ²) ⧸ (F_*, H_*)`. -/
theorem NoetherConditionsAt.intersectionNumber_le (hF : F.IsHomogeneous d)
    (hG : G.IsHomogeneous e) (hH : H.IsHomogeneous r) (h : NoetherConditionsAt P F G H) :
    intersectionNumber P F G ≤ intersectionNumber P F H := by
  rw [noetherConditionsAt_iff hF hG] at h
  have hle : Ideal.span {localEquation P F, localEquation P H} ≤
      Ideal.span {localEquation P F, localEquation P G} := by
    rw [Ideal.span_le, Set.pair_subset_iff]
    exact ⟨Ideal.subset_span (by simp), h⟩
  rw [intersectionNumber_eq_length_localEquation hF hG,
    intersectionNumber_eq_length_localEquation hF hH]
  exact Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)

/-- **Criterion (1) is necessary** (Fulton, Problem 5.29). If the forms `F` and `G` meet
transversally at `P`, that is `I(P, F ∩ G) = 1`, then Noether's conditions hold at `P` for a form
`H` if and only if `H(P) = 0`. -/
theorem noetherConditionsAt_iff_eval_rep_eq_zero (hF : F.IsHomogeneous d)
    (hG : G.IsHomogeneous e) (hH : H.IsHomogeneous r) (h1 : intersectionNumber P F G = 1) :
    NoetherConditionsAt P F G H ↔ eval P.rep H = 0 := by
  refine ⟨fun h ↦ ?_, noetherConditionsAt_of_intersectionNumber_eq_one hF hG hH h1⟩
  have hPF : eval P.rep F = 0 ∧ eval P.rep G = 0 := by
    have h0 : intersectionNumber P F G ≠ 0 := by rw [h1]; exact one_ne_zero
    simpa [intersectionNumber_eq_zero_iff hF hG] using h0
  exact h.eval_rep_eq_zero hF hG hH hPF.1 hPF.2

/-- **Criterion (2) is necessary** (Fulton, Problem 5.29). If `P` is a simple point of the form
`F`, then Noether's conditions hold at `P` for forms `G` and `H` if and only if
`I(P, F ∩ G) ≤ I(P, F ∩ H)`. The forms may have a common component through `P`. -/
theorem noetherConditionsAt_iff_intersectionNumber_le (hF : F.IsHomogeneous d)
    (hG : G.IsHomogeneous e) (hH : H.IsHomogeneous r) (hP : IsSimplePoint F P) :
    NoetherConditionsAt P F G H ↔ intersectionNumber P F G ≤ intersectionNumber P F H :=
  ⟨fun h ↦ h.intersectionNumber_le hF hG hH, noetherConditionsAt_of_isSimplePoint hF hG hH hP⟩

/-! ### Criterion (3) is not necessary -/

/-- No linear form divides both `X ^ 2` and `Z ^ 2`. -/
private theorem not_dvd_X_zero_sq_and_X_two_sq {L : MvPolynomial (Fin 3) k}
    (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) (h0 : L ∣ X 0 ^ 2) (h2 : L ∣ X 2 ^ 2) : False := by
  have hirr := irreducible_of_isHomogeneous_one hL hL0
  have h0' := hirr.associated_of_dvd (prime_X (R := k)).irreducible (hirr.prime.dvd_of_dvd_pow h0)
  have h2' := hirr.associated_of_dvd (prime_X (R := k)).irreducible (hirr.prime.dvd_of_dvd_pow h2)
  have h := (h0'.symm.trans h2').dvd
  rw [X_dvd_X] at h
  exact absurd h (by decide)

/-- **Criterion (3) is not necessary** (Fulton, Problem 5.29). Over every field there are forms
`F`, `G`, `H` and a point `P` such that `F` and `G` have no common tangent at `P` and Noether's
conditions hold at `P`, yet `m_P(H) < m_P(F) + m_P(G) - 1`. For instance `P = [0 : 1 : 0]`,
`F = X³ - YZ²`, `G = Z³ - X²Y` and `H = F`: the tangent cones at `P` are `Z²` and `X²`, so
`m_P(F) = m_P(G) = m_P(H) = 2 < 3`, and `H ∈ (F, G)`. -/
theorem exists_noetherConditionsAt_and_mult_lt :
    ∃ (F G H : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k)),
      F.IsHomogeneous 3 ∧ G.IsHomogeneous 3 ∧ H.IsHomogeneous 3 ∧
      (¬∃ L, IsTangentAt F P L ∧ IsTangentAt G P L) ∧ NoetherConditionsAt P F G H ∧
      mult H P < mult F P + mult G P - 1 := by
  set F : MvPolynomial (Fin 3) k := X 0 ^ 3 - X 1 * X 2 ^ 2
  set G : MvPolynomial (Fin 3) k := X 2 ^ 3 - X 0 ^ 2 * X 1
  have hFh : F.IsHomogeneous 3 :=
    (isHomogeneous_X_pow _ 3).sub ((isHomogeneous_X _ _).mul (isHomogeneous_X_pow _ 2))
  have hGh : G.IsHomogeneous 3 :=
    (isHomogeneous_X_pow _ 3).sub ((isHomogeneous_X_pow _ 2).mul (isHomogeneous_X _ _))
  obtain ⟨hmF, hF, -⟩ := mult_eq_and_isTangentAt_iff_of_eq_sum (F := F) (d := 3) (m := 2)
    (G := fun i ↦ if i = 2 then -X 1 ^ 2 else if i = 3 then X 0 ^ 3 else 0)
    (fun i ↦ by
      split_ifs with h h'
      · subst h; exact (isHomogeneous_X_pow _ 2).neg
      · subst h'; exact isHomogeneous_X_pow _ 3
      · exact isHomogeneous_zero _ _ _)
    (by simp [F, Finset.sum_range_succ]; ring) (by norm_num)
    (fun i hi ↦ by simp [show i ≠ 2 by omega, show i ≠ 3 by omega])
    (by simp [X_ne_zero])
  obtain ⟨hmG, hG, -⟩ := mult_eq_and_isTangentAt_iff_of_eq_sum (F := G) (d := 3) (m := 2)
    (G := fun i ↦ if i = 2 then -X 0 ^ 2 else if i = 3 then X 1 ^ 3 else 0)
    (fun i ↦ by
      split_ifs with h h'
      · subst h; exact (isHomogeneous_X_pow _ 2).neg
      · subst h'; exact isHomogeneous_X_pow _ 3
      · exact isHomogeneous_zero _ _ _)
    (by simp [G, Finset.sum_range_succ]; ring) (by norm_num)
    (fun i hi ↦ by simp [show i ≠ 2 by omega, show i ≠ 3 by omega])
    (by simp [X_ne_zero])
  refine ⟨F, G, F, mk k ![0, 1, 0] (by simp), hFh, hGh, hFh, ?_,
    noetherConditionsAt_of_mem_span_pair hFh hGh (Ideal.subset_span (Set.mem_insert _ _)), ?_⟩
  · rintro ⟨L, hLF, hLG⟩
    rw [isTangentAt_def] at hLF hLG
    refine not_dvd_X_zero_sq_and_X_two_sq hLF.1 hLF.2.1 ?_ ?_
    · simpa using hLG.2.2.2.trans hG.dvd
    · simpa using hLF.2.2.2.trans hF.dvd
  · rw [hmF, hmG]
    decide

/-! ### The residual intersection -/

section Residual

variable [IsAlgClosed k]

/-- **The residual intersection.** Let `k` be algebraically closed and `F`, `G`, `H` forms of
degrees `d > 0`, `e` and `r`, with `F` prime to both `G` and `H`. If Noether's conditions hold at
every point of `V(F) ∩ V(G)`, then `e ≤ r` and there is a nonzero form `B` of degree `r - e`
(possibly a constant), prime to `F`, with `H • F = B • F + G • F`. -/
theorem exists_isHomogeneous_intersectionCycle_eq_add_of_forall_noetherConditionsAt
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e) (hH : H.IsHomogeneous r) (hd : 0 < d)
    (hFG : IsRelPrime F G) (hFH : IsRelPrime F H)
    (hN : ∀ P : ℙ k (Fin 3 → k), eval P.rep F = 0 → eval P.rep G = 0 →
      NoetherConditionsAt P F G H) :
    e ≤ r ∧ ∃ B : MvPolynomial (Fin 3) k, B.IsHomogeneous (r - e) ∧ B ≠ 0 ∧ IsRelPrime F B ∧
      intersectionCycle H F = intersectionCycle B F + intersectionCycle G F := by
  obtain ⟨A, B, -, hB, -, hB0, hAB⟩ :=
    (exists_isHomogeneous_mul_add_mul_eq_iff_forall_noetherConditionsAt hF hG hH hFG).2 hN
  have hFB : IsRelPrime F B := fun D hDF hDB ↦
    hFH hDF (hAB ▸ dvd_add (dvd_mul_of_dvd_right hDF A) (dvd_mul_of_dvd_left hDB G))
  have hBne : B ≠ 0 := by
    rintro rfl
    have hu := isRelPrime_zero_right.1 hFB
    have h := hF.totalDegree hu.ne_zero
    rw [(isUnit_iff_totalDegree_of_isReduced.1 hu).2] at h
    omega
  refine ⟨not_lt.1 fun h ↦ hBne (hB0 h), B, hB, hBne, hFB, ?_⟩
  rw [intersectionCycle_comm H, intersectionCycle_comm B, intersectionCycle_comm G, ← hAB,
    add_comm, intersectionCycle_add_mul, intersectionCycle_mul_right hF hB hG hFB hFG]

/-- **The residual intersection at simple points** (Fulton, §5.5, Corollary to Proposition 1,
case (2)). Let `k` be algebraically closed and `F`, `G`, `H` forms of degrees `d > 0`, `e` and
`r`, with `F` prime to both `G` and `H`. If every point of `V(F) ∩ V(G)` is a simple point of `F`
and `G • F ≤ H • F`, then `e ≤ r` and there is a nonzero form `B` of degree `r - e` (possibly a
constant), prime to `F`, with `B • F = H • F - G • F`. -/
theorem exists_isHomogeneous_intersectionCycle_eq_sub_of_isSimplePoint
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e) (hH : H.IsHomogeneous r) (hd : 0 < d)
    (hFG : IsRelPrime F G) (hFH : IsRelPrime F H)
    (hP : ∀ P : ℙ k (Fin 3 → k), eval P.rep F = 0 → eval P.rep G = 0 → IsSimplePoint F P)
    (hle : intersectionCycle G F ≤ intersectionCycle H F) :
    e ≤ r ∧ ∃ B : MvPolynomial (Fin 3) k, B.IsHomogeneous (r - e) ∧ B ≠ 0 ∧ IsRelPrime F B ∧
      intersectionCycle B F = intersectionCycle H F - intersectionCycle G F := by
  obtain ⟨her, B, hB, hBne, hFB, hc⟩ :=
    exists_isHomogeneous_intersectionCycle_eq_add_of_forall_noetherConditionsAt hF hG hH hd hFG
      hFH fun P hPF hPG ↦ noetherConditionsAt_of_isSimplePoint hF hG hH (hP P hPF hPG) (by
        rw [← intersectionCycle_apply hF hG hFG, ← intersectionCycle_apply hF hH hFH,
          intersectionCycle_comm F, intersectionCycle_comm F, Nat.cast_le]
        exact hle P)
  exact ⟨her, B, hB, hBne, hFB, by rw [hc, add_tsub_cancel_right]⟩

/-- **The residual intersection at `de` distinct points** (Fulton, §5.5, Corollary to
Proposition 1, case (1)). Let `k` be algebraically closed and `F`, `G`, `H` forms of degrees
`d > 0`, `e` and `r`, with `F` prime to `H`. If `V(F) ∩ V(G)` consists of the `de` points of `s`
and `H` vanishes at all of them, then `e ≤ r` and there is a nonzero form `B` of degree `r - e`
(possibly a constant), prime to `F`, with `B • F = H • F - G • F`. That `F` and `G` have no
common component follows from the finiteness of `V(F) ∩ V(G)`. -/
theorem exists_isHomogeneous_intersectionCycle_eq_sub_of_card_eq_mul
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e) (hH : H.IsHomogeneous r) (hd : 0 < d)
    (hFH : IsRelPrime F H) {s : Finset (ℙ k (Fin 3 → k))}
    (hs : ∀ P, P ∈ s ↔ eval P.rep F = 0 ∧ eval P.rep G = 0) (h : s.card = d * e)
    (hHs : ∀ P ∈ s, eval P.rep H = 0) :
    e ≤ r ∧ ∃ B : MvPolynomial (Fin 3) k, B.IsHomogeneous (r - e) ∧ B ≠ 0 ∧ IsRelPrime F B ∧
      intersectionCycle B F = intersectionCycle H F - intersectionCycle G F := by
  have hFG : IsRelPrime F G := isRelPrime_of_finite_zeroLocus_pair hF hG
    (s.finite_toSet.subset fun Q hQ ↦ (hs Q).2 (by
      rw [mem_zeroLocus_iff_eval_rep (by rintro f (rfl | rfl); exacts [⟨d, hF⟩, ⟨e, hG⟩])] at hQ
      exact ⟨hQ F (by simp), hQ G (by simp)⟩))
  obtain ⟨her, B, hB, hBne, hFB, hc⟩ :=
    exists_isHomogeneous_intersectionCycle_eq_add_of_forall_noetherConditionsAt hF hG hH hd hFG
      hFH fun P hPF hPG ↦
        noetherConditionsAt_of_intersectionNumber_eq_one hF hG hH
          (intersectionNumber_eq_one_of_card_eq_mul hF hG hs h ((hs P).2 ⟨hPF, hPG⟩))
          (hHs P ((hs P).2 ⟨hPF, hPG⟩))
  exact ⟨her, B, hB, hBne, hFB, by rw [hc, add_tsub_cancel_right]⟩

end Residual

/-- The residual intersection needs `deg F > 0`: for the constant `F = 1`, `G = X` and `H = 1`,
the hypotheses of both cases hold, since `V(F) ∩ V(G)` is empty, but `deg G > deg H`. -/
theorem exists_isHomogeneous_zero_and_not_le :
    ∃ (F G H : MvPolynomial (Fin 3) k) (s : Finset (ℙ k (Fin 3 → k))),
      F.IsHomogeneous 0 ∧ G.IsHomogeneous 1 ∧ H.IsHomogeneous 0 ∧ IsRelPrime F G ∧
      IsRelPrime F H ∧ (∀ P, P ∈ s ↔ eval P.rep F = 0 ∧ eval P.rep G = 0) ∧ s.card = 0 * 1 ∧
      (∀ P ∈ s, eval P.rep H = 0) ∧
      (∀ P : ℙ k (Fin 3 → k), eval P.rep F = 0 → eval P.rep G = 0 → IsSimplePoint F P) ∧
      intersectionCycle G F ≤ intersectionCycle H F ∧ ¬1 ≤ 0 :=
  ⟨1, X 0, 1, ∅, isHomogeneous_one _ _, isHomogeneous_X _ _, isHomogeneous_one _ _,
    isRelPrime_one_left, isRelPrime_one_left, by simp, rfl, by simp, by simp,
    by rw [← C_1, intersectionCycle_C_right one_ne_zero]; exact zero_le, by decide⟩

/-! ### The local criteria and the residual intersection -/

/-- **Local criteria for Noether's conditions and the residual intersection** (Fulton, §5.5,
Proposition 1, its Corollary, and Problem 5.29). Let `k` be algebraically closed and `F`, `G`,
`H` forms of degrees `d`, `e` and `r` in `k[X, Y, Z]`.

1. **Proposition 1.** Noether's conditions hold at `P` if (1) `I(P, F ∩ G) = 1` and `H(P) = 0`;
   or (2) `P` is a simple point of `F` and `I(P, F ∩ G) ≤ I(P, F ∩ H)` (the right side may be
   `∞`); or (3) `F` and `G` have no common tangent at `P` and `m_P(H) ≥ m_P(F) + m_P(G) - 1`.
   No hypothesis on common components is needed.
2. **Problem 5.29.** The conditions on `H` in (1) and (2) are also necessary; those in (3) are
   not: there are cubics `F'`, `G'`, `H'` and a point `Q` where (3) fails although Noether's
   conditions hold.
3. **Corollary.** Let `d > 0` and `F` be prime to `H`. If (1) `V(F) ∩ V(G)` consists of `de`
   distinct points and `H` vanishes at all of them, or (2) `F` is prime to `G`, every point of
   `V(F) ∩ V(G)` is a simple point of `F` and `G • F ≤ H • F`, then `e ≤ r` and there is a
   nonzero form `B` of degree `r - e` (possibly a constant), prime to `F`, with
   `B • F = H • F - G • F`.

Milestone: *Local criteria for Noether's conditions and the residual intersection corollary*. -/
theorem noetherConditionsAt_of_intersectionNumber_eq_one_spec [IsAlgClosed k]
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e) (hH : H.IsHomogeneous r) :
    -- Proposition 1
    ((∀ P : ℙ k (Fin 3 → k), intersectionNumber P F G = 1 → eval P.rep H = 0 →
        NoetherConditionsAt P F G H) ∧
      (∀ P : ℙ k (Fin 3 → k), IsSimplePoint F P →
        intersectionNumber P F G ≤ intersectionNumber P F H → NoetherConditionsAt P F G H) ∧
      ∀ P : ℙ k (Fin 3 → k), (¬∃ L, IsTangentAt F P L ∧ IsTangentAt G P L) →
        mult F P + mult G P - 1 ≤ mult H P → NoetherConditionsAt P F G H) ∧
    -- Problem 5.29
    ((∀ P : ℙ k (Fin 3 → k), intersectionNumber P F G = 1 →
        (NoetherConditionsAt P F G H ↔ eval P.rep H = 0)) ∧
      (∀ P : ℙ k (Fin 3 → k), IsSimplePoint F P →
        (NoetherConditionsAt P F G H ↔ intersectionNumber P F G ≤ intersectionNumber P F H)) ∧
      ∃ (F' G' H' : MvPolynomial (Fin 3) k) (Q : ℙ k (Fin 3 → k)),
        F'.IsHomogeneous 3 ∧ G'.IsHomogeneous 3 ∧ H'.IsHomogeneous 3 ∧
        (¬∃ L, IsTangentAt F' Q L ∧ IsTangentAt G' Q L) ∧ NoetherConditionsAt Q F' G' H' ∧
        mult H' Q < mult F' Q + mult G' Q - 1) ∧
    -- the Corollary
    (0 < d → IsRelPrime F H →
      (∀ s : Finset (ℙ k (Fin 3 → k)), (∀ P, P ∈ s ↔ eval P.rep F = 0 ∧ eval P.rep G = 0) →
        s.card = d * e → (∀ P ∈ s, eval P.rep H = 0) →
        e ≤ r ∧ ∃ B : MvPolynomial (Fin 3) k, B.IsHomogeneous (r - e) ∧ B ≠ 0 ∧
          IsRelPrime F B ∧
          intersectionCycle B F = intersectionCycle H F - intersectionCycle G F) ∧
      (IsRelPrime F G →
        (∀ P : ℙ k (Fin 3 → k), eval P.rep F = 0 → eval P.rep G = 0 → IsSimplePoint F P) →
        intersectionCycle G F ≤ intersectionCycle H F →
        e ≤ r ∧ ∃ B : MvPolynomial (Fin 3) k, B.IsHomogeneous (r - e) ∧ B ≠ 0 ∧
          IsRelPrime F B ∧
          intersectionCycle B F = intersectionCycle H F - intersectionCycle G F)) :=
  ⟨⟨fun _ h1 hHP ↦ noetherConditionsAt_of_intersectionNumber_eq_one hF hG hH h1 hHP,
      fun _ hP h ↦ noetherConditionsAt_of_isSimplePoint hF hG hH hP h,
      fun _ hT hm ↦ noetherConditionsAt_of_not_exists_isTangentAt hF hG hH hT hm⟩,
    ⟨fun _ h1 ↦ noetherConditionsAt_iff_eval_rep_eq_zero hF hG hH h1,
      fun _ hP ↦ noetherConditionsAt_iff_intersectionNumber_le hF hG hH hP,
      exists_noetherConditionsAt_and_mult_lt⟩,
    fun hd hFH ↦ ⟨fun _ hs h hHs ↦
        exists_isHomogeneous_intersectionCycle_eq_sub_of_card_eq_mul hF hG hH hd hFH hs h hHs,
      fun hFG hP hle ↦
        exists_isHomogeneous_intersectionCycle_eq_sub_of_isSimplePoint hF hG hH hd hFG hFH hP
          hle⟩⟩

end PlaneCurves.Projective

end
