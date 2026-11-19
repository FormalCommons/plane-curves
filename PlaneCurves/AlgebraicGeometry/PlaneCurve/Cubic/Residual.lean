/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.GenericLine
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.MultiplePoints
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Noether.Conditions

/-!
# Residual points on a cubic

Two applications of Max Noether's theorem to plane cubics (Fulton, §5.6), in Fulton's letters;
the theorems call the cubic `F`.

**Proposition 2.** Let `C` and `C'` be cubics without common component, and `Q` a conic prime to
`C` with `Q • C ≤ C' • C`, all of whose intersections with `C` are simple points of `C`. Then
the residual cycle `C' • C - Q • C` is cut out on `C` by a line `L`, not a component of `C`. In
Fulton's words: if `C' • C = P₁ + ⋯ + P₉` and `Q • C = P₁ + ⋯ + P₆`, then `P₇`, `P₈`, `P₉` are
collinear.

**Proposition 3.** Let `C` be an irreducible cubic and `C'`, `C''` cubics that are not multiples
of `C`, with `C' • C = D + P` and `C'' • C = D + Q` for a cycle `D` (of degree 8) of simple
points of `C` and a simple point `P` of `C`. Then `Q = P`.

The proof of Proposition 3 takes a line `L` through `P` that misses the multiple points of `C`
(an irreducible cubic has at most one), so that `L • C = P + T` with `T` a cycle of degree 2 on
simple points of `C`. The residual intersection with `F = C`, `G = C'` and `H = L C''` gives a
line `L'` with `L' • C = T + Q`. Two lines that both contain a cycle of degree 2 on simple points
of `C` agree: they share two distinct points, or both are the tangent at a point
(`associated_of_le_intersectionCycle`). Hence `L • C = L' • C`, and `P = Q`.

Fulton lets `L` be any line through `P` not through `Q`; if `L` passes through the multiple point
of `C`, the cycle `T` is twice that point and the last step fails, so `L` must avoid it. Avoiding
`Q` is not needed.

## Main results

* `exists_isHomogeneous_one_intersectionCycle_eq`: Proposition 2.
* `eq_of_intersectionCycle_eq_add_single`: Proposition 3.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.6, Propositions 2 and 3
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F G H : MvPolynomial (Fin 3) k} {P Q : ℙ k (Fin 3 → k)}
  {d : ℕ}

/-! ### Residual points of a conic on a cubic -/

variable [IsAlgClosed k]

/-- **Residual points of a conic on a cubic are collinear** (Fulton, §5.6, Proposition 2). Let
`k` be algebraically closed, `F` and `H` cubics without common component and `G` a conic prime to
`F`, with `H • F = G • F + E` for a zero-cycle `E`. If every point of `G • F` is a simple point
of `F`, then there is a line `L`, not a component of `F`, with `L • F = E`. In Fulton's terms:
if `H • F = P₁ + ⋯ + P₉` and `G • F = P₁ + ⋯ + P₆`, then `L • F = P₇ + P₈ + P₉`, so `P₇`, `P₈`
and `P₉` are collinear. The cubic `F` may be reducible.

Milestone: *Residual points of a conic on a cubic are collinear*. -/
theorem exists_isHomogeneous_one_intersectionCycle_eq (hF : F.IsHomogeneous 3)
    (hG : G.IsHomogeneous 2) (hH : H.IsHomogeneous 3) (hFG : IsRelPrime F G)
    (hFH : IsRelPrime F H) {E : ℙ k (Fin 3 → k) →₀ ℕ}
    (hE : intersectionCycle H F = intersectionCycle G F + E)
    (hs : ∀ P ∈ (intersectionCycle G F).support, IsSimplePoint F P) :
    ∃ L : MvPolynomial (Fin 3) k, L.IsHomogeneous 1 ∧ L ≠ 0 ∧ IsRelPrime F L ∧
      intersectionCycle L F = E := by
  obtain ⟨-, L, hL, hL0, hFL, hLF⟩ :=
    exists_isHomogeneous_intersectionCycle_eq_sub_of_isSimplePoint hF hG hH (by norm_num) hFG hFH
    (fun P hPF hPG ↦ hs P ((mem_support_intersectionCycle_iff hG hF hFG.symm).2 ⟨hPG, hPF⟩))
    (hE ▸ le_self_add)
  exact ⟨L, hL, hL0, hFL, by rw [hLF, hE, add_tsub_cancel_left]⟩

/-! ### Eight points of a cubic determine the ninth -/

/-- **Eight simple points of an irreducible cubic determine the ninth** (Fulton, §5.6,
Proposition 3). Let `k` be algebraically closed, `F` an irreducible cubic, and `G`, `H` cubics
that are not multiples of `F`. If `G • F = D + P` and `H • F = D + Q` for a zero-cycle `D` and
points `P`, `Q`, where `P` and the points of `D` are simple points of `F`, then `Q = P`. In
Fulton's terms, `G • F = P₁ + ⋯ + P₉` and `H • F = P₁ + ⋯ + P₈ + Q` with the `Pᵢ` simple and not
necessarily distinct give `Q = P₉`.

Milestone: *Eight simple points of an irreducible cubic determine the ninth*. -/
theorem eq_of_intersectionCycle_eq_add_single (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hG : G.IsHomogeneous 3) (hH : H.IsHomogeneous 3) (hFG : ¬F ∣ G) (hFH : ¬F ∣ H)
    {D : ℙ k (Fin 3 → k) →₀ ℕ} (hD : ∀ R ∈ D.support, IsSimplePoint F R) (hP : IsSimplePoint F P)
    (hGF : intersectionCycle G F = D + Finsupp.single P 1)
    (hHF : intersectionCycle H F = D + Finsupp.single Q 1) : Q = P := by
  classical
  replace hFG := hirr.isRelPrime_iff_not_dvd.2 hFG
  replace hFH := hirr.isRelPrime_iff_not_dvd.2 hFH
  -- a line `L` through `P` that misses the multiple points of `F`
  have hfin : {R | IsMultiplePoint F R}.Finite := Set.Subsingleton.finite
    fun R hR S hS ↦ eq_of_isMultiplePoint_of_degree_three hF hirr hR hS
  obtain ⟨c, hPL, hc⟩ := ((infinite_setOf_eval_sum_C_mul_X_eq_zero P).sdiff
    (finite_setOf_eval_sum_C_mul_X_eq_zero_of_finite hfin P)).nonempty
  set L : MvPolynomial (Fin 3) k := ∑ i, C (c.rep i) * X i
  have hL : L.IsHomogeneous 1 := isHomogeneous_sum_C_mul_X _
  have hL0 : L ≠ 0 := sum_C_mul_X_ne_zero c.rep_ne_zero
  have hFL : IsRelPrime F L := hirr.isRelPrime_iff_not_dvd.2 fun h ↦ by
    have := totalDegree_le_of_dvd_of_isDomain h hL0
    rw [hF.totalDegree hirr.ne_zero, hL.totalDegree hL0] at this
    omega
  -- `L • F = T + P` with `T` of degree 2 on simple points of `F`
  have hPLF : Finsupp.single P 1 ≤ intersectionCycle L F := by
    rw [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero, ← Finsupp.mem_support_iff,
      mem_support_intersectionCycle_iff hL hF hFL.symm]
    exact ⟨hPL, hP.eval_rep_eq_zero⟩
  set T := intersectionCycle L F - Finsupp.single P 1
  have hLT : T + Finsupp.single P 1 = intersectionCycle L F := tsub_add_cancel_of_le hPLF
  have hT : T.degree = 2 := by
    have := degree_intersectionCycle hL hF hFL.symm
    rw [← hLT, map_add, Finsupp.degree_single] at this
    omega
  have hTs : ∀ R ∈ T.support, IsSimplePoint F R := fun R hR ↦ by
    obtain ⟨hRL, hRF⟩ := (mem_support_intersectionCycle_iff hL hF hFL.symm).1
      (Finsupp.support_mono (hLT ▸ le_self_add) hR)
    by_cases hRP : R = P
    · exact hRP ▸ hP
    by_contra hns
    exact hc ⟨hPL, R, isMultiplePoint_iff_not_isSimplePoint.2 ⟨hRF, hns⟩, hRP, hRL⟩
  -- the residual intersection gives a line `B` with `B • F = T + Q`
  have hcyc : intersectionCycle (L * H) F = intersectionCycle L F + intersectionCycle H F :=
    intersectionCycle_mul_left hL hH hF hFL.symm hFH.symm
  obtain ⟨-, B, hB, hB0, hFB, hBF⟩ :=
    exists_isHomogeneous_intersectionCycle_eq_sub_of_isSimplePoint hF hG (hL.mul hH) (by norm_num)
    hFG (hFL.mul_right hFH)
    (fun R hRF hRG ↦ by
      by_cases hRP : R = P
      · exact hRP ▸ hP
      refine hD R ?_
      have := (mem_support_intersectionCycle_iff hG hF hFG.symm).2 ⟨hRG, hRF⟩
      rw [hGF, Finsupp.mem_support_iff, Finsupp.add_apply,
        Finsupp.single_eq_of_ne hRP] at this
      simpa using this)
    (by
      rw [hcyc, hGF, hHF, ← hLT, Finsupp.le_def]
      intro R
      simp only [Finsupp.coe_add, Pi.add_apply]
      omega)
  have hBT : intersectionCycle B F = T + Finsupp.single Q 1 := by
    rw [hBF, hcyc, hGF, hHF, ← hLT]
    ext R
    simp only [Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply]
    omega
  have hLB : Associated L B := associated_of_le_intersectionCycle hF hL hL0 hB hB0 hFL hFB hT hTs
    (by rw [← hLT]; exact le_self_add) (by rw [hBT]; exact le_self_add)
  have hcyc' : intersectionCycle B F = intersectionCycle L F := intersectionCycle_congr fun R ↦ by
    rw [intersectionNumber_comm, intersectionNumber_comm R L,
      intersectionNumber_congr_right_of_associated hLB.symm]
  rw [hBT, ← hLT] at hcyc'
  exact Finsupp.single_left_injective one_ne_zero (add_left_cancel hcyc')

end PlaneCurves.Projective

end
