/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Bezout.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.IntersectionNumber.Properties
public import PlaneCurves.RingTheory.MvPolynomial.Homogeneous
public import PlaneCurves.RingTheory.MvPolynomial.Irreducible

/-!
# Corollaries of Bézout's theorem

Let `k` be algebraically closed and `F`, `G` forms of degrees `m` and `n` in `k[X, Y, Z]`.
Bézout's theorem `∑_P I(P, F ∩ G) = mn` and the inequality `I(P, F ∩ G) ≥ m_P(F) m_P(G)`,
with `I(P, F ∩ G) ≥ 1` at each common zero, give Fulton's three corollaries (§5.3):

1. if `F` and `G` have no common component, `∑_P m_P(F) m_P(G) ≤ mn`;
2. if `V(F) ∩ V(G)` has exactly `mn` points, each of them is a simple point of `F` and of `G`,
   and `F` and `G` meet transversally there;
3. if `V(F) ∩ V(G)` has more than `mn` points, `F` and `G` have a common component.

A common component is a common factor that is not a unit, so "no common component" is
`IsRelPrime F G`. Corollary 2 needs no such hypothesis: forms with finitely many common zeros are
relatively prime (`PlaneCurves.Projective.isRelPrime_of_finite_zeroLocus_pair`), since a common
component has infinitely many zeros.

## Main results

* `PlaneCurves.Projective.finsum_mult_mul_mult_le`: Corollary 1, and
  `PlaneCurves.Projective.sum_mult_mul_mult_le`, its form over a `Finset` of points.
* `PlaneCurves.Projective.sum_intersectionNumber_le_mul`: for relatively prime forms, the sum of
  the intersection numbers over any `Finset` of points is at most `mn`.
* `PlaneCurves.Projective.card_le_mul_of_isRelPrime`: relatively prime forms have at most `mn`
  common zeros, and `PlaneCurves.Projective.not_isRelPrime_of_mul_lt_card`, Corollary 3.
* `PlaneCurves.Projective.intersectionNumber_eq_one_of_card_eq_mul` and
  `PlaneCurves.Projective.isSimplePoint_of_card_eq_mul`: Corollary 2.
* `PlaneCurves.Projective.finsum_mult_mul_mult_le_spec`: the three corollaries together.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.3, Corollaries 1–3
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] [IsAlgClosed k] {F G : MvPolynomial (Fin 3) k} {m n : ℕ}

/-- **Corollary 1 of Bézout's theorem.** Let `k` be algebraically closed and `F`, `G` forms of
degrees `m` and `n` with no common component. Then `∑_P m_P(F) m_P(G) ≤ mn`; the sum has only
finitely many nonzero terms. -/
theorem finsum_mult_mul_mult_le (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hFG : IsRelPrime F G) : ∑ᶠ P, mult F P * mult G P ≤ ↑(m * n) := by
  have hfin := finite_support_intersectionNumber hF hG hFG
  rw [← finsum_intersectionNumber_eq_mul hF hG hFG]
  refine finsum_le_finsum (hfin.subset fun P hP h0 ↦ hP ?_) hfin
    (fun P ↦ mul_mult_le_intersectionNumber hF hG)
  exact le_antisymm (h0 ▸ mul_mult_le_intersectionNumber hF hG) zero_le

/-- The sum of the intersection numbers of relatively prime forms of degrees `m` and `n` over a
`Finset` of points is at most `mn`. -/
theorem sum_intersectionNumber_le_mul (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hFG : IsRelPrime F G) (s : Finset (ℙ k (Fin 3 → k))) :
    ∑ P ∈ s, intersectionNumber P F G ≤ ↑(m * n) := by
  classical
  have hfin := finite_support_intersectionNumber hF hG hFG
  rw [← finsum_intersectionNumber_eq_mul hF hG hFG,
    finsum_eq_sum_of_support_subset (s := s ∪ hfin.toFinset) _ (by simp)]
  exact Finset.sum_le_sum_of_subset Finset.subset_union_left

/-- **Corollary 1 of Bézout's theorem**, over a `Finset` of points. Let `k` be algebraically
closed and `F`, `G` forms of degrees `m` and `n` with no common component. Then
`∑_{P ∈ s} m_P(F) m_P(G) ≤ mn` for every finite set `s` of points. -/
theorem sum_mult_mul_mult_le (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hFG : IsRelPrime F G) (s : Finset (ℙ k (Fin 3 → k))) :
    ∑ P ∈ s, mult F P * mult G P ≤ ↑(m * n) :=
  (Finset.sum_le_sum fun _ _ ↦ mul_mult_le_intersectionNumber hF hG).trans
    (sum_intersectionNumber_le_mul hF hG hFG s)

/-- Relatively prime forms of degrees `m` and `n`, over an algebraically closed field, have at
most `mn` common zeros in `ℙ²`. -/
theorem card_le_mul_of_isRelPrime (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hFG : IsRelPrime F G) {s : Finset (ℙ k (Fin 3 → k))}
    (hs : ∀ P ∈ s, eval P.rep F = 0 ∧ eval P.rep G = 0) : s.card ≤ m * n := by
  have h : (s.card : ℕ∞) ≤ ↑(m * n) := by
    rw [Finset.cast_card]
    exact (Finset.sum_le_sum fun P hP ↦ one_le_intersectionNumber hF hG (hs P hP).1
      (hs P hP).2).trans (sum_intersectionNumber_le_mul hF hG hFG s)
  exact_mod_cast h

/-- **Corollary 3 of Bézout's theorem.** Let `k` be algebraically closed and `F`, `G` forms of
degrees `m` and `n`. If `V(F) ∩ V(G)` has more than `mn` points, then `F` and `G` have a common
component. -/
theorem not_isRelPrime_of_mul_lt_card (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    {s : Finset (ℙ k (Fin 3 → k))} (hs : ∀ P ∈ s, eval P.rep F = 0 ∧ eval P.rep G = 0)
    (h : m * n < s.card) : ¬IsRelPrime F G :=
  fun hFG ↦ (card_le_mul_of_isRelPrime hF hG hFG hs).not_gt h

/-- A line meets a conic that it is not a component of in at most two points: if `P ≠ Q` and
`S` lie on the line `L` and on the conic `G`, and `L` does not divide `G`, then `S` is `P` or
`Q`. -/
theorem eq_or_eq_of_isHomogeneous_one_of_not_dvd {L : MvPolynomial (Fin 3) k}
    (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) (hG : G.IsHomogeneous 2) (hLG : ¬L ∣ G)
    {P Q S : ℙ k (Fin 3 → k)} (hPQ : P ≠ Q) (hP : eval P.rep L = 0 ∧ eval P.rep G = 0)
    (hQ : eval Q.rep L = 0 ∧ eval Q.rep G = 0) (hS : eval S.rep L = 0 ∧ eval S.rep G = 0) :
    S = P ∨ S = Q := by
  classical
  by_contra! h
  have := card_le_mul_of_isRelPrime hL hG
    ((irreducible_of_isHomogeneous_one hL hL0).isRelPrime_iff_not_dvd.2 hLG)
    (s := {P, Q, S}) (by simp [hP, hQ, hS])
  rw [Finset.card_insert_of_notMem (by simp [hPQ, Ne.symm h.1]),
    Finset.card_pair (Ne.symm h.2)] at this
  omega

/-- If the common zeros of forms `F` and `G` of degrees `m` and `n` are exactly the `mn` points
of `s`, then `I(P, F ∩ G) = 1` at each of them. -/
theorem intersectionNumber_eq_one_of_card_eq_mul (hF : F.IsHomogeneous m)
    (hG : G.IsHomogeneous n) {s : Finset (ℙ k (Fin 3 → k))}
    (hs : ∀ P, P ∈ s ↔ eval P.rep F = 0 ∧ eval P.rep G = 0) (h : s.card = m * n) {P}
    (hP : P ∈ s) : intersectionNumber P F G = 1 := by
  have hFG : IsRelPrime F G :=
    isRelPrime_of_forall_eval_eq_zero_mem hF hG fun P h₁ h₂ ↦ (hs P).2 ⟨h₁, h₂⟩
  have htop (Q : ℙ k (Fin 3 → k)) : intersectionNumber Q F G ≠ ⊤ :=
    intersectionNumber_ne_top_of_isRelPrime hF hG hFG
  have hone : ∀ Q ∈ s, 1 ≤ (intersectionNumber Q F G).toNat := fun Q hQ ↦ by
    have := one_le_intersectionNumber hF hG ((hs Q).1 hQ).1 ((hs Q).1 hQ).2
    rw [← ENat.natCast_toNat (htop Q)] at this
    exact_mod_cast this
  have hsum : ∑ Q ∈ s, (intersectionNumber Q F G).toNat = ∑ Q ∈ s, 1 := by
    have := sum_intersectionNumber_eq_mul hF hG hFG fun Q hQF hQG ↦ (hs Q).2 ⟨hQF, hQG⟩
    rw [← Finset.sum_congr rfl fun Q _ ↦ ENat.natCast_toNat (htop Q), ← Nat.cast_sum] at this
    rw [Finset.sum_const, smul_eq_mul, mul_one, h]
    exact_mod_cast this
  have := ((Finset.sum_eq_sum_iff_of_le hone).1 hsum.symm P hP).symm
  rw [← ENat.natCast_toNat (htop P), this, Nat.cast_one]

/-- **Corollary 2 of Bézout's theorem.** Let `k` be algebraically closed and `F`, `G` forms of
degrees `m` and `n` whose common zeros in `ℙ²` are exactly the `mn` points of `s`. Then at each of
them `P` is a simple point of `F` and of `G`, and `F` and `G` meet transversally:
`I(P, F ∩ G) = 1`, and `F` and `G` have no common tangent at `P`. No "no common component"
hypothesis is needed: a common component would have infinitely many points. -/
theorem isSimplePoint_of_card_eq_mul (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    {s : Finset (ℙ k (Fin 3 → k))} (hs : ∀ P, P ∈ s ↔ eval P.rep F = 0 ∧ eval P.rep G = 0)
    (h : s.card = m * n) {P} (hP : P ∈ s) :
    IsSimplePoint F P ∧ IsSimplePoint G P ∧ intersectionNumber P F G = 1 ∧
      ¬∃ L, IsTangentAt F P L ∧ IsTangentAt G P L := by
  have hI := intersectionNumber_eq_one_of_card_eq_mul hF hG hs h hP
  have hle := (mul_mult_le_intersectionNumber hF hG (P := P)).trans_eq hI
  have hF1 : 1 ≤ mult F P :=
    Order.one_le_iff_ne_zero.2 (mult_pos_iff_eval_rep.2 ((hs P).1 hP).1).ne'
  have hG1 : 1 ≤ mult G P :=
    Order.one_le_iff_ne_zero.2 (mult_pos_iff_eval_rep.2 ((hs P).1 hP).2).ne'
  have hmF : mult F P = 1 := le_antisymm ((le_mul_of_one_le_right zero_le hG1).trans hle) hF1
  have hmG : mult G P = 1 := le_antisymm ((le_mul_of_one_le_left zero_le hF1).trans hle) hG1
  have hF0 : F ≠ 0 := fun h0 ↦ by simp [h0] at hmF
  have hG0 : G ≠ 0 := fun h0 ↦ by simp [h0] at hmG
  refine ⟨isSimplePoint_def.2 hmF, isSimplePoint_def.2 hmG, hI,
    (intersectionNumber_eq_mul_mult_iff hF hG hF0 hG0).1 ?_⟩
  rw [hI, hmF, hmG, mul_one]

/-- **Corollaries of Bézout's theorem** (Fulton, §5.3, Corollaries 1–3). Let `k` be algebraically
closed and `F`, `G` forms of degrees `m` and `n` in `k[X, Y, Z]`.

1. If `F` and `G` have no common component, then `∑_P m_P(F) m_P(G) ≤ mn`.
2. If the common zeros of `F` and `G` are exactly the `mn` points of `s`, then each of them is a
   simple point of `F` and of `G`, and `F` and `G` meet transversally there: `I(P, F ∩ G) = 1`,
   and they have no common tangent at `P`.
3. If `F` and `G` have more than `mn` common zeros, they have a common component.

None of them needs `m` or `n` to be positive.

Milestone: *Corollaries of Bézout's theorem on multiplicities and common points*. -/
theorem finsum_mult_mul_mult_le_spec (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) :
    (IsRelPrime F G → ∑ᶠ P, mult F P * mult G P ≤ ↑(m * n)) ∧
    (∀ s : Finset (ℙ k (Fin 3 → k)), (∀ P, P ∈ s ↔ eval P.rep F = 0 ∧ eval P.rep G = 0) →
      s.card = m * n → ∀ P ∈ s, IsSimplePoint F P ∧ IsSimplePoint G P ∧
        intersectionNumber P F G = 1 ∧ ¬∃ L, IsTangentAt F P L ∧ IsTangentAt G P L) ∧
    (∀ s : Finset (ℙ k (Fin 3 → k)), (∀ P ∈ s, eval P.rep F = 0 ∧ eval P.rep G = 0) →
      m * n < s.card → ¬IsRelPrime F G) :=
  ⟨finsum_mult_mul_mult_le hF hG, fun _ hs h _ hP ↦ isSimplePoint_of_card_eq_mul hF hG hs h hP,
    fun _ hs h ↦ not_isRelPrime_of_mul_lt_card hF hG hs h⟩

end PlaneCurves.Projective

end
