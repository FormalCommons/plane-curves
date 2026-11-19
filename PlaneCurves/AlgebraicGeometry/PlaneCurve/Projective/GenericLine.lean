/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Bezout.Corollaries
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Finiteness
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.IntersectionNumber.Properties

/-!
# Lines through a point of a projective plane curve

A line of `ℙ²` is the zero locus of a nonzero linear form `L`. The lines themselves form the dual
projective plane: the line with dual coordinates `c : ℙ k (Fin 3 → k)` is `∑ i, c.rep i X i = 0`.
This file gives the facts about one line `L` and a plane curve `F` that are used to show that a
generic line through a point `P` meets `F` in distinct points outside `P`:

* the intersection number `I(P, F ∩ L)` at a point `P` of `L` is the multiplicity `m_P(F)`
  exactly when `L` is not tangent to `F` at `P`, and it is one exactly when `P` is a simple
  point of `F` and `L` is not tangent there;
* only finitely many lines are tangent to `F ≠ 0` at `P`, and only one line passes through two
  distinct points, so only finitely many lines through `P` meet a given finite set of other
  points;
* if `L` is not a component of `F` and meets `F` with intersection number one at every point
  other than `P`, then by Bézout's theorem for a line `L` meets `F` in exactly
  `deg F - I(P, F ∩ L)` points other than `P`.

Together with the polar derivative `D_P F`, which is nonzero when `deg F - m_P(F)` is nonzero in
`k`, these show that for an irreducible `F` all but finitely many lines through `P` meet `F` in
exactly `deg F - m_P(F)` points other than `P`, each with intersection number one (Fulton,
Problem 5.26).

## Main results

* `intersectionNumber_eq_mult_iff_not_isTangentAt`: `I(P, F ∩ L) = m_P(F)` iff `L` is not
  tangent to `F` at `P`.
* `intersectionNumber_eq_one_iff`: `I(P, F ∩ L) = 1` iff `P` is a simple point of `F` and `L` is
  not tangent to `F` at `P`.
* `finite_setOf_sum_C_mul_X_dvd`, `finite_setOf_isTangentAt`: finitely many lines divide a
  nonzero form, so finitely many lines are tangent to `F ≠ 0` at `P`.
* `subsingleton_setOf_eval_sum_C_mul_X_eq_zero`: at most one line passes through two distinct
  points.
* `finite_setOf_eval_sum_C_mul_X_eq_zero_of_finite`: finitely many lines through `P` meet a
  finite set of other points.
* `infinite_setOf_eval_sum_C_mul_X_eq_zero`: infinitely many lines pass through a point.
* `ncard_zeroLocus_pair_diff_add`, `ncard_zeroLocus_pair_diff`: counting the points of
  `V(F) ∩ V(L)` other than `P`.
* `eq_of_mem_zeroLocus_pair_of_intersectionNumber_eq`: if `I(P, F ∩ L) = deg F`, then `P` is
  the only common point of `F` and `L`.
* `eventually_cofinite_ncard_zeroLocus_pair_diff_eq_of_polarDerivative_ne_zero`: if `D_P F ≠ 0`,
  generic lines through `P` meet an irreducible `F` in `deg F - m_P(F)` distinct further points,
  transversally.
* `eventually_cofinite_ncard_zeroLocus_pair_diff_eq`: the same when `deg F - m_P(F) ≠ 0` in `k`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.1, §5.3, Problems 5.12, 5.26 and 5.28
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization Matrix

variable {k : Type*} [Field k] {F L : MvPolynomial (Fin 3) k} {P Q : ℙ k (Fin 3 → k)} {d : ℕ}

/-! ### Intersection numbers with a line -/

/-- For a nonzero form `F` and a line `L = 0` through `P`, `I(P, F ∩ L) = m_P(F)` iff `L` is not
tangent to `F` at `P`. -/
theorem intersectionNumber_eq_mult_iff_not_isTangentAt (hF : F.IsHomogeneous d) (hF0 : F ≠ 0)
    (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) (hLP : eval P.rep L = 0) :
    intersectionNumber P F L = mult F P ↔ ¬IsTangentAt F P L := by
  have hle : mult F P ≤ intersectionNumber P F L := by
    simpa [mult_eq_one_of_isHomogeneous_one hL hL0 hLP] using
      mul_mult_le_intersectionNumber (P := P) hF hL
  rw [isTangentAt_iff_mult_lt_intersectionNumber hF hF0 hL hL0 hLP, not_lt]
  exact ⟨fun h ↦ h.le, fun h ↦ le_antisymm h hle⟩

/-- For a form `F` and a line `L = 0` through `P`, `I(P, F ∩ L) = 1` iff `P` is a simple point
of `F` and `L` is not tangent to `F` at `P`. -/
theorem intersectionNumber_eq_one_iff (hF : F.IsHomogeneous d) (hL : L.IsHomogeneous 1)
    (hL0 : L ≠ 0) (hLP : eval P.rep L = 0) :
    intersectionNumber P F L = 1 ↔ IsSimplePoint F P ∧ ¬IsTangentAt F P L := by
  constructor
  · intro h
    have hle := mul_mult_le_intersectionNumber (P := P) hF hL
    rw [mult_eq_one_of_isHomogeneous_one hL hL0 hLP, mul_one, h] at hle
    have hpos : 0 < mult F P := mult_pos_iff_eval_rep.2
      (eval_rep_eq_zero_of_intersectionNumber_ne_zero hF hL (by simp [h])).1
    have hs : IsSimplePoint F P :=
      isSimplePoint_def.2 (le_antisymm hle (Order.one_le_iff_pos.2 hpos))
    refine ⟨hs, (intersectionNumber_eq_mult_iff_not_isTangentAt hF hs.ne_zero hL hL0 hLP).1 ?_⟩
    rw [h, isSimplePoint_def.1 hs]
  · rintro ⟨hs, ht⟩
    rw [← isSimplePoint_def.1 hs]
    exact (intersectionNumber_eq_mult_iff_not_isTangentAt hF hs.ne_zero hL hL0 hLP).2 ht

/-! ### Finiteness of sets of lines -/

/-- Only finitely many lines divide a nonzero form `G`: the lines `∑ i, c.rep i X i` dividing `G`
are, up to scalars, among its irreducible factors. -/
theorem finite_setOf_sum_C_mul_X_dvd {G : MvPolynomial (Fin 3) k} (hG : G ≠ 0) :
    {c : ℙ k (Fin 3 → k) | (∑ i, C (c.rep i) * X i) ∣ G}.Finite := by
  classical
  have hinj : Set.InjOn (fun c : ℙ k (Fin 3 → k) ↦ Associates.mk (∑ i, C (c.rep i) * X i))
      {c | (∑ i, C (c.rep i) * X i) ∣ G} := by
    intro c _ c' _ h
    obtain ⟨t, -, ht⟩ := associated_sum_C_mul_X_iff.1 (Associates.mk_eq_mk_iff_associated.1 h)
    rw [← c.mk_rep, ← c'.mk_rep, mk_eq_mk_iff']
    exact ⟨t, funext fun i ↦ by simp [ht i]⟩
  refine Set.Finite.of_finite_image ?_ hinj
  refine (((UniqueFactorizationMonoid.factors G).map Associates.mk).toFinset.finite_toSet).subset ?_
  rintro _ ⟨c, hc, rfl⟩
  obtain ⟨q, hq, hcq⟩ := UniqueFactorizationMonoid.exists_mem_factors_of_dvd hG
    (irreducible_of_isHomogeneous_one (isHomogeneous_sum_C_mul_X _)
      (sum_C_mul_X_ne_zero c.rep_ne_zero)) hc
  simp only [Finset.mem_coe, Multiset.mem_toFinset, Multiset.mem_map]
  exact ⟨q, hq, (Associates.mk_eq_mk_iff_associated.2 hcq).symm⟩

/-- Only finitely many lines are tangent to a nonzero form `F` at `P`: they divide the leading
form of `F` at `P`. -/
theorem finite_setOf_isTangentAt (hF0 : F ≠ 0) (P : ℙ k (Fin 3 → k)) :
    {c : ℙ k (Fin 3 → k) | IsTangentAt F P (∑ i, C (c.rep i) * X i)}.Finite :=
  (finite_setOf_sum_C_mul_X_dvd (leadingForm_eq_zero_iff.not.2 hF0)).subset
    fun _ hc ↦ (isTangentAt_def.1 hc).2.2.2

/-- At most one line passes through two distinct points `P` and `Q` of `ℙ²`. -/
theorem subsingleton_setOf_eval_sum_C_mul_X_eq_zero (hPQ : P ≠ Q) :
    {c : ℙ k (Fin 3 → k) | eval P.rep (∑ i, C (c.rep i) * X i) = 0 ∧
      eval Q.rep (∑ i, C (c.rep i) * X i) = 0}.Subsingleton := by
  have hind : LinearIndependent k ![P.rep, Q.rep] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent]
    refine mt (mk_eq_mk_iff_crossProduct_eq_zero P.rep_ne_zero Q.rep_ne_zero).mpr ?_
    simpa using hPQ
  have hsub : ∀ c : ℙ k (Fin 3 → k), eval P.rep (∑ i, C (c.rep i) * X i) = 0 →
      eval Q.rep (∑ i, C (c.rep i) * X i) = 0 →
      c ∈ zeroLocus {∑ i, C (P.rep i) * X i, ∑ i, C (Q.rep i) * X i} := by
    intro c hP hQ
    rw [mem_zeroLocus_iff_eval_rep
      (by rintro f (rfl | rfl) <;> exact ⟨1, isHomogeneous_sum_C_mul_X _⟩)]
    rw [eval_sum_C_mul_X] at hP hQ
    rintro f (rfl | rfl) <;> rw [eval_sum_C_mul_X, dotProduct_comm] <;> assumption
  rintro c ⟨hcP, hcQ⟩ c' ⟨hc'P, hc'Q⟩
  have h := hsub c hcP hcQ
  have h' := hsub c' hc'P hc'Q
  rw [zeroLocus_pair_sum_C_mul_X hind, Set.mem_singleton_iff] at h h'
  rw [h, h']

/-- For a finite set `S` of points of `ℙ²` and a point `P`, only finitely many lines pass through
`P` and through a point of `S` other than `P`. -/
theorem finite_setOf_eval_sum_C_mul_X_eq_zero_of_finite {S : Set (ℙ k (Fin 3 → k))}
    (hS : S.Finite) (P : ℙ k (Fin 3 → k)) :
    {c : ℙ k (Fin 3 → k) | eval P.rep (∑ i, C (c.rep i) * X i) = 0 ∧
      ∃ Q ∈ S, Q ≠ P ∧ eval Q.rep (∑ i, C (c.rep i) * X i) = 0}.Finite := by
  refine ((hS.sdiff (t := {P})).biUnion fun Q hQ ↦
    (subsingleton_setOf_eval_sum_C_mul_X_eq_zero (Ne.symm hQ.2)).finite).subset ?_
  rintro c ⟨hP, Q, hQ, hQP, hcQ⟩
  exact Set.mem_biUnion (x := Q) ⟨hQ, hQP⟩ ⟨hP, hcQ⟩

/-- Over an algebraically closed field, infinitely many lines pass through a point `P` of `ℙ²`:
in the dual plane they form the line `∑ i, P.rep i X i = 0`. -/
theorem infinite_setOf_eval_sum_C_mul_X_eq_zero [IsAlgClosed k] (P : ℙ k (Fin 3 → k)) :
    {c : ℙ k (Fin 3 → k) | eval P.rep (∑ i, C (c.rep i) * X i) = 0}.Infinite := by
  refine (zeroLocus_singleton_infinite (n := 2) le_rfl (isHomogeneous_sum_C_mul_X P.rep)
    one_ne_zero).mono fun c hc ↦ ?_
  rw [mem_zeroLocus_singleton_sum_C_mul_X_iff] at hc
  rwa [Set.mem_ofPred_eq, eval_sum_C_mul_X, dotProduct_comm]

/-! ### Counting the points of a line on a curve -/

/-- **Counting along a line.** Let `k` be algebraically closed, `F` a form of degree `d` and `L`
a line that is not a component of `F`, with `I(P, F ∩ L) = r` at a point `P`. If `L` meets `F`
with intersection number one at every other common point, then `L` meets `F` in exactly `d - r`
points other than `P`. -/
theorem ncard_zeroLocus_pair_diff_add [IsAlgClosed k] (hF : F.IsHomogeneous d)
    (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) (hLF : ¬L ∣ F) {r : ℕ}
    (hP : intersectionNumber P F L = r)
    (h1 : ∀ Q ∈ zeroLocus {F, L}, Q ≠ P → intersectionNumber Q F L = 1) :
    (zeroLocus {F, L} \ {P}).ncard + r = d := by
  classical
  have hs : (zeroLocus {F, L} \ {P} : Set (ℙ k (Fin 3 → k))).Finite :=
    (finite_zeroLocus_pair_of_isRelPrime hF hL
      ((irreducible_of_isHomogeneous_one hL hL0).isRelPrime_iff_not_dvd.2 hLF).symm).sdiff
  have hmem : ∀ Q, Q ∈ zeroLocus {F, L} ↔ eval Q.rep F = 0 ∧ eval Q.rep L = 0 := fun Q ↦ by
    rw [mem_zeroLocus_iff_eval_rep (by rintro f (rfl | rfl); exacts [⟨d, hF⟩, ⟨1, hL⟩])]
    simp
  have hsupp : (Function.support fun Q ↦ intersectionNumber Q F L) ⊆
      ↑(insert P hs.toFinset) := by
    intro Q hQ
    by_cases hQP : Q = P
    · simp [hQP]
    simpa [hQP, hmem] using eval_rep_eq_zero_of_intersectionNumber_ne_zero hF hL hQ
  have h := finsum_intersectionNumber_eq_of_isHomogeneous_one hF hL hL0 hLF
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_insert (by simp), hP,
    Finset.sum_congr rfl (g := fun _ ↦ (1 : ℕ∞)) fun Q hQ ↦ by
      rw [Set.Finite.mem_toFinset] at hQ
      exact h1 Q hQ.1 hQ.2,
    Finset.sum_const, nsmul_one, ← Set.ncard_eq_toFinset_card _ hs] at h
  rw [add_comm]
  exact_mod_cast h

/-- **Counting along a line**, in subtraction form: under the hypotheses of
`ncard_zeroLocus_pair_diff_add`, the line `L` meets `F` in exactly `d - r` points other than
`P`. -/
theorem ncard_zeroLocus_pair_diff [IsAlgClosed k] (hF : F.IsHomogeneous d)
    (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) (hLF : ¬L ∣ F) {r : ℕ}
    (hP : intersectionNumber P F L = r)
    (h1 : ∀ Q ∈ zeroLocus {F, L}, Q ≠ P → intersectionNumber Q F L = 1) :
    (zeroLocus {F, L} \ {P}).ncard = d - r := by
  have := ncard_zeroLocus_pair_diff_add hF hL hL0 hLF hP h1
  omega

/-! ### Generic lines through a point -/

/-- If the form `F` of degree `d` has `I(P, F ∩ L) = d` with a line `L` that is not a component
of `F`, then `P` is the only common point of `F` and `L`. -/
theorem eq_of_mem_zeroLocus_pair_of_intersectionNumber_eq [IsAlgClosed k]
    (hF : F.IsHomogeneous d) (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) (hLF : ¬L ∣ F)
    (hP : intersectionNumber P F L = d) (hQ : Q ∈ zeroLocus {F, L}) : Q = P := by
  classical
  by_contra hQP
  rw [mem_zeroLocus_iff_eval_rep (by rintro f (rfl | rfl); exacts [⟨d, hF⟩, ⟨1, hL⟩])] at hQ
  have h1 := one_le_intersectionNumber hF hL (hQ F (by simp)) (hQ L (by simp))
  have hle := sum_intersectionNumber_le_mul hF hL
    ((irreducible_of_isHomogeneous_one hL hL0).isRelPrime_iff_not_dvd.2 hLF).symm {P, Q}
  rw [Finset.sum_pair (Ne.symm hQP), hP, mul_one] at hle
  have h2 : (d : ℕ∞) + 1 ≤ d := (add_le_add_right h1 _).trans hle
  exact absurd h2 (by norm_cast; omega)

/-- **Generic lines through a point, from the polar derivative.** Let `k` be algebraically
closed, `F` an irreducible form of degree `d`, `P` a point of `ℙ²` and `r = m_P(F)`, and suppose
that the polar derivative `D_P F` is nonzero or that `d = r`. Then for all but finitely many lines
`L = ∑ i, c i X i` through `P`, the line `L` meets `F` in exactly `d - r` points other than `P`,
with `I(Q, F ∩ L) = 1` at each of them, and `I(P, F ∩ L) = r`.

The excluded lines are the component of `F` if `F` is a line, the tangents to `F` at `P`, the
lines through `P` and a multiple point of `F`, and the lines through `P` and a point `Q ≠ P` of
`V(F) ∩ V(D_P F)`; the last set is finite because `F` does not divide `D_P F ≠ 0`, which has
smaller degree. -/
theorem eventually_cofinite_ncard_zeroLocus_pair_diff_eq_of_polarDerivative_ne_zero
    [IsAlgClosed k] (hF : F.IsHomogeneous d) (hirr : Irreducible F) {r : ℕ} (hr : mult F P = r)
    (hD : polarDerivative P.rep F ≠ 0 ∨ d = r) :
    ∀ᶠ c : ℙ k (Fin 3 → k) in Filter.cofinite, eval P.rep (∑ i, C (c.rep i) * X i) = 0 →
      (zeroLocus {F, ∑ i, C (c.rep i) * X i} \ {P}).ncard = d - r ∧
      (∀ Q ∈ zeroLocus {F, ∑ i, C (c.rep i) * X i}, Q ≠ P →
        intersectionNumber Q F (∑ i, C (c.rep i) * X i) = 1) ∧
      intersectionNumber P F (∑ i, C (c.rep i) * X i) = r := by
  have hF0 := hirr.ne_zero
  have hmem : ∀ {L : MvPolynomial (Fin 3) k}, L.IsHomogeneous 1 → ∀ Q,
      Q ∈ zeroLocus {F, L} ↔ eval Q.rep F = 0 ∧ eval Q.rep L = 0 := fun hL Q ↦ by
    rw [mem_zeroLocus_iff_eval_rep (by rintro f (rfl | rfl); exacts [⟨d, hF⟩, ⟨_, hL⟩])]
    simp
  -- A finite set `S` of points such that a line through `P` that is not a component of `F`,
  -- not tangent at `P` and through no point of `S` other than `P` meets `F` transversally
  -- outside `P`.
  obtain ⟨S, hS, hgood⟩ : ∃ S : Set (ℙ k (Fin 3 → k)), S.Finite ∧
      ∀ {L : MvPolynomial (Fin 3) k}, L.IsHomogeneous 1 → L ≠ 0 → ¬L ∣ F →
        eval P.rep L = 0 → ¬IsTangentAt F P L → (∀ Q ∈ S, Q ≠ P → eval Q.rep L ≠ 0) →
        ∀ Q ∈ zeroLocus {F, L}, Q ≠ P → intersectionNumber Q F L = 1 := by
    rcases hD with hD0 | rfl
    · have hrel : IsRelPrime F (polarDerivative P.rep F) := by
        refine hirr.isRelPrime_iff_not_dvd.2 fun hdvd ↦ hD0 ?_
        have := totalDegree_le_of_dvd_of_isDomain hdvd hD0
        rw [hF.totalDegree hF0, (hF.polarDerivative _).totalDegree hD0] at this
        rw [(totalDegree_eq_zero_iff_eq_C (p := F)).1 (by rw [hF.totalDegree hF0]; omega),
          polarDerivative_C]
      refine ⟨{Q | IsMultiplePoint F Q} ∪ zeroLocus {F, polarDerivative P.rep F},
        (finite_setOf_isMultiplePoint_of_irreducible hF hirr).union
          (finite_zeroLocus_pair_of_isRelPrime hF (hF.polarDerivative _) hrel), ?_⟩
      intro L hL hL0 _ hLP _ hS Q hQ hQP
      obtain ⟨hQF, hQL⟩ := (hmem hL Q).1 hQ
      have hQs : IsSimplePoint F Q :=
        (isSimplePoint_or_isMultiplePoint hF
          ((mem_zeroLocus_iff_eval_rep (by simpa using ⟨d, hF⟩)).2 (by simpa))).resolve_right
          fun hm ↦ hS Q (Or.inl hm) hQP hQL
      refine (intersectionNumber_eq_one_iff hF hL hL0 hQL).2
        ⟨hQs, fun hT ↦ hS Q (Or.inr ?_) hQP hQL⟩
      obtain ⟨u, hu⟩ := hQs.associated_tangentLine_of_isTangentAt hF hT
      have hTP : eval P.rep (tangentLine F Q.rep) = 0 := by
        rw [← hu, map_mul, hLP, zero_mul]
      rw [mem_zeroLocus_iff_eval_rep
        (by rintro f (rfl | rfl); exacts [⟨d, hF⟩, ⟨_, hF.polarDerivative _⟩])]
      rintro f (rfl | rfl)
      exacts [hQF, (eval_tangentLine_eq_eval_polarDerivative F P.rep Q.rep).symm.trans hTP]
    · refine ⟨∅, Set.finite_empty, ?_⟩
      intro L hL hL0 hLF hLP hT _ Q hQ hQP
      have hP : intersectionNumber P F L = d := by
        rw [(intersectionNumber_eq_mult_iff_not_isTangentAt hF hF0 hL hL0 hLP).2 hT, hr]
      exact absurd (eq_of_mem_zeroLocus_pair_of_intersectionNumber_eq hF hL hL0 hLF hP hQ) hQP
  rw [Filter.eventually_cofinite]
  refine (((finite_setOf_sum_C_mul_X_dvd hF0).union (finite_setOf_isTangentAt hF0 P)).union
    (finite_setOf_eval_sum_C_mul_X_eq_zero_of_finite hS P)).subset fun c hc ↦ ?_
  simp only [Set.mem_ofPred_eq, not_imp] at hc
  obtain ⟨hcP, hbad⟩ := hc
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_and, not_exists] at hc
  obtain ⟨⟨hdvd, htan⟩, hS'⟩ := hc
  have hL := isHomogeneous_sum_C_mul_X c.rep
  have hL0 := sum_C_mul_X_ne_zero c.rep_ne_zero
  have hP : intersectionNumber P F (∑ i, C (c.rep i) * X i) = r := by
    rw [(intersectionNumber_eq_mult_iff_not_isTangentAt hF hF0 hL hL0 hcP).2 htan, hr]
  have h1 := hgood hL hL0 hdvd hcP htan fun Q hQ hQP ↦ hS' hcP Q hQ hQP
  exact hbad ⟨ncard_zeroLocus_pair_diff hF hL hL0 hdvd hP h1, h1, hP⟩

/-- **Generic lines through a point.** Let `k` be algebraically closed, `F` an irreducible form of
degree `d`, `P` a point of `ℙ²` and `r = m_P(F)`, and suppose that `d - r` is nonzero in `k` (for
instance, `k` has characteristic zero) or that `d = r`. Then for all but finitely many lines
`L = ∑ i, c i X i` through `P`, the line `L` meets `F` in exactly `d - r` points other than `P`,
with `I(Q, F ∩ L) = 1` at each of them, and `I(P, F ∩ L) = r`.

The excluded lines are the component of `F` if `F` is a line, the tangents to `F` at `P`, the
lines through `P` and a multiple point of `F`, and the lines through `P` and a point `Q ≠ P` of
`V(F) ∩ V(D_P F)`, where `D_P F` is the polar derivative; the last set is finite because
`D_P F ≠ 0` when `d - r ≠ 0` in `k`. Without that hypothesis the statement can fail in
characteristic `p ∣ d - r`: for `F = X^{p+1} - Y^p Z` and `P = [0 : 1 : 0]`, every tangent to `F`
at a simple point passes through `P`, so every line through `P` meets `F` in at most one point
other than `P` (Fulton, Problem 5.28).

Milestone: *Generic lines through a point meet an irreducible curve in distinct points*. -/
theorem eventually_cofinite_ncard_zeroLocus_pair_diff_eq [IsAlgClosed k]
    (hF : F.IsHomogeneous d) (hirr : Irreducible F) {r : ℕ} (hr : mult F P = r)
    (hdr : ((d - r : ℕ) : k) ≠ 0 ∨ d = r) :
    ∀ᶠ c : ℙ k (Fin 3 → k) in Filter.cofinite, eval P.rep (∑ i, C (c.rep i) * X i) = 0 →
      (zeroLocus {F, ∑ i, C (c.rep i) * X i} \ {P}).ncard = d - r ∧
      (∀ Q ∈ zeroLocus {F, ∑ i, C (c.rep i) * X i}, Q ≠ P →
        intersectionNumber Q F (∑ i, C (c.rep i) * X i) = 1) ∧
      intersectionNumber P F (∑ i, C (c.rep i) * X i) = r :=
  eventually_cofinite_ncard_zeroLocus_pair_diff_eq_of_polarDerivative_ne_zero hF hirr hr
    (hdr.imp_left (hF.polarDerivative_ne_zero (by rw [← mult_def, hr])))

end PlaneCurves.Projective

end
