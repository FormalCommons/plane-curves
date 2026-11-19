/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Bezout.Corollaries
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Finiteness
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.IntersectionCycle
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

The file also shows that two lines `L` and `B` prime to `F` agree when a cycle of degree 2 on
simple points of `F` lies below both `L • F` and `B • F`: either they share two distinct points,
or both are the tangent to `F` at one point.

## Main results

* `intersectionNumber_eq_mult_iff_not_isTangentAt`: `I(P, F ∩ L) = m_P(F)` iff `L` is not
  tangent to `F` at `P`.
* `intersectionNumber_eq_one_iff`: `I(P, F ∩ L) = 1` iff `P` is a simple point of `F` and `L` is
  not tangent to `F` at `P`.
* `intersectionNumber_bind₁_update_X_zero`: setting `Xⱼ = 0` in `F` does not change its
  intersection numbers with the line `Xⱼ = 0`.
* `squarefree_of_forall_intersectionNumber_le_one`: a form that meets a curve with all
  intersection numbers at most one is squarefree.
* `finite_setOf_sum_C_mul_X_dvd`, `finite_setOf_isTangentAt`: finitely many lines divide a
  nonzero form, so finitely many lines are tangent to `F ≠ 0` at `P`.
* `subsingleton_setOf_eval_sum_C_mul_X_eq_zero`: at most one line passes through two distinct
  points.
* `finite_setOf_eval_sum_C_mul_X_eq_zero_of_finite`: finitely many lines through `P` meet a
  finite set of other points.
* `infinite_setOf_eval_sum_C_mul_X_eq_zero`: infinitely many lines pass through a point.
* `exists_associated_sum_C_rep_mul_X`: every line is associated to the line
  `∑ i, c.rep i X i` of a point `c` of the dual plane.
* `associated_of_eval_rep_eq_zero_of_ne`: two lines through two distinct points agree.
* `eval_rep_eq_zero_of_le_intersectionCycle`: a point of a cycle below `L • F` lies on `L`.
* `associated_of_le_intersectionCycle`: two lines whose intersection cycles with a curve contain
  a common cycle of degree 2 on simple points of the curve agree.
* `ncard_zeroLocus_pair_diff_add`, `ncard_zeroLocus_pair_diff`: counting the points of
  `V(F) ∩ V(L)` other than `P`.
* `ncard_zeroLocus_pair_diff_lt_of_isTangentAt`: a line through `P` tangent to `F` at another
  point meets `F` in fewer than `deg F - m_P(F)` points other than `P`.
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

variable {k : Type*} [Field k] {F L B : MvPolynomial (Fin 3) k} {P Q : ℙ k (Fin 3 → k)} {d : ℕ}

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

/-! ### Restriction to a coordinate line and squarefree forms -/

/-- Setting `Xⱼ = 0` in `F` does not change its intersection numbers with the line `Xⱼ = 0`:
`F` and `F(…, 0, …)` agree modulo `Xⱼ`. -/
theorem intersectionNumber_bind₁_update_X_zero (P : ℙ k (Fin 3 → k))
    (F : MvPolynomial (Fin 3) k) (j : Fin 3) :
    intersectionNumber P (bind₁ (Function.update X j 0) F) (X j) =
      intersectionNumber P F (X j) := by
  obtain ⟨A, hA⟩ := X_dvd_sub_bind₁_update_X_zero j F
  rw [intersectionNumber_comm, intersectionNumber_comm P F, ← intersectionNumber_add_mul P (X j)
    (bind₁ (Function.update X j 0) F) A, mul_comm A, ← hA, add_sub_cancel]

/-- **A squarefree criterion.** Over an algebraically closed field, a nonzero form `G` that
meets a form `L` of positive degree with all intersection numbers at most one is squarefree: a
square factor `p²` of `G` meets `L` at some point `P`, where
`I(P, G ∩ L) ≥ 2 I(P, p ∩ L) ≥ 2`. -/
theorem squarefree_of_forall_intersectionNumber_le_one [IsAlgClosed k]
    {G : MvPolynomial (Fin 3) k} {e : ℕ} (hG : G.IsHomogeneous e) (hG0 : G ≠ 0)
    (hL : L.IsHomogeneous d) (hd : d ≠ 0) (h : ∀ P, intersectionNumber P G L ≤ 1) :
    Squarefree G := by
  classical
  rintro p ⟨K, rfl⟩
  by_contra hp
  obtain ⟨e', he', hp'⟩ := hG.exists_isHomogeneous_of_dvd hG0
    (dvd_mul_of_dvd_left (dvd_mul_right p p) K) hp
  have hK : K.IsHomogeneous K.totalDegree := by
    rw [mul_comm] at hG
    exact hG.of_mul_left (left_ne_zero_of_mul hG0)
  obtain ⟨P, hP⟩ := zeroLocus_nonempty_of_card_le (n := 2) (s := {p, L})
    Finset.card_le_two (by
      intro f hf
      rcases Finset.mem_insert.1 hf with rfl | hf
      · exact ⟨e', he', hp'⟩
      · rw [Finset.mem_singleton.1 hf]
        exact ⟨d, hd, hL⟩)
  rw [Finset.coe_insert, Finset.coe_singleton, mem_zeroLocus_iff_eval_rep (by
    rintro f (rfl | rfl)
    exacts [⟨e', hp'⟩, ⟨d, hL⟩])] at hP
  have h1 := one_le_intersectionNumber hp' hL (hP p (by simp)) (hP L (by simp))
  have h2 := h P
  rw [intersectionNumber_mul_left (hp'.mul hp') hK hL, intersectionNumber_mul_left hp' hp' hL]
    at h2
  have : (1 + 1 : ℕ∞) ≤ 1 := (add_le_add h1 h1).trans (le_self_add.trans h2)
  exact absurd this (by decide)

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

/-! ### Lines sharing points of a curve -/

/-- A nonzero linear form `L` is associated to the line `∑ i, c.rep i X i` of a point `c` of the
dual plane, which vanishes exactly where `L` does. -/
theorem exists_associated_sum_C_rep_mul_X (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) :
    ∃ c : ℙ k (Fin 3 → k), Associated L (∑ i, C (c.rep i) * X i) ∧
      ∀ v : Fin 3 → k, eval v (∑ i, C (c.rep i) * X i) = 0 ↔ eval v L = 0 := by
  set a : Fin 3 → k := fun i ↦ L.coeff (Finsupp.single i 1)
  have hLa : L = ∑ i, C (a i) * X i := hL.eq_sum_C_mul_X
  have ha : a ≠ 0 := fun h ↦ hL0 (by rw [hLa, h]; simp)
  obtain ⟨u, hu⟩ := exists_smul_eq_mk_rep k a ha
  refine ⟨mk k a ha, ?_, fun v ↦ ?_⟩
  · rw [hLa, associated_sum_C_mul_X_iff]
    refine ⟨(u : k)⁻¹, by simp, fun i ↦ ?_⟩
    rw [← hu, Pi.smul_apply, Units.smul_def, smul_eq_mul, inv_mul_cancel_left₀ u.ne_zero]
  · rw [hLa, eval_sum_C_mul_X, eval_sum_C_mul_X, ← hu, smul_dotProduct, Units.smul_def,
      smul_eq_mul, mul_eq_zero]
    simp

/-- Two nonzero linear forms that vanish at two distinct points of `ℙ²` are associated: one line
passes through two distinct points. -/
theorem associated_of_eval_rep_eq_zero_of_ne (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0)
    (hB : B.IsHomogeneous 1) (hB0 : B ≠ 0) (hPQ : P ≠ Q) (hLP : eval P.rep L = 0)
    (hLQ : eval Q.rep L = 0) (hBP : eval P.rep B = 0) (hBQ : eval Q.rep B = 0) :
    Associated L B := by
  obtain ⟨c, hc, hcv⟩ := exists_associated_sum_C_rep_mul_X hL hL0
  obtain ⟨c', hc', hc'v⟩ := exists_associated_sum_C_rep_mul_X hB hB0
  obtain rfl : c = c' := subsingleton_setOf_eval_sum_C_mul_X_eq_zero hPQ
    ⟨(hcv _).2 hLP, (hcv _).2 hLQ⟩ ⟨(hc'v _).2 hBP, (hc'v _).2 hBQ⟩
  exact hc.trans hc'.symm

/-- A point of a zero-cycle below `L • F` lies on `L`, for `L` prime to the form `F`. -/
theorem eval_rep_eq_zero_of_le_intersectionCycle (hF : F.IsHomogeneous d)
    (hL : L.IsHomogeneous 1) (hFL : IsRelPrime F L) {T : ℙ k (Fin 3 → k) →₀ ℕ}
    (hT : T ≤ intersectionCycle L F) (hP : P ∈ T.support) : eval P.rep L = 0 :=
  ((mem_support_intersectionCycle_iff hL hF hFL.symm).1 (Finsupp.support_mono hT hP)).1

/-- **Two lines sharing two points of a curve agree.** Let `F` be a form and `L`, `B` lines prime
to `F`. If a zero-cycle `T` of degree 2, supported on simple points of `F`, lies below both
`L • F` and `B • F`, then `L` and `B` are associated. Either `T` has two distinct points, which
lie on both lines, or `T = 2R` and both lines are the tangent to `F` at the simple point `R`. -/
theorem associated_of_le_intersectionCycle (hF : F.IsHomogeneous d) (hL : L.IsHomogeneous 1)
    (hL0 : L ≠ 0) (hB : B.IsHomogeneous 1) (hB0 : B ≠ 0) (hFL : IsRelPrime F L)
    (hFB : IsRelPrime F B) {T : ℙ k (Fin 3 → k) →₀ ℕ} (hT : T.degree = 2)
    (hs : ∀ R ∈ T.support, IsSimplePoint F R) (hTL : T ≤ intersectionCycle L F)
    (hTB : T ≤ intersectionCycle B F) : Associated L B := by
  by_cases hsub : ∃ R ∈ T.support, ∃ S ∈ T.support, R ≠ S
  · obtain ⟨R, hR, S, hS, hRS⟩ := hsub
    exact associated_of_eval_rep_eq_zero_of_ne hL hL0 hB hB0 hRS
      (eval_rep_eq_zero_of_le_intersectionCycle hF hL hFL hTL hR)
      (eval_rep_eq_zero_of_le_intersectionCycle hF hL hFL hTL hS)
      (eval_rep_eq_zero_of_le_intersectionCycle hF hB hFB hTB hR)
      (eval_rep_eq_zero_of_le_intersectionCycle hF hB hFB hTB hS)
  push Not at hsub
  obtain ⟨R, hR⟩ : T.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, Finsupp.support_eq_empty]
    rintro rfl
    simp at hT
  have hTR : T R = 2 := by
    rw [← hT, Finsupp.support_subset_singleton.1 fun S hS ↦ Finset.mem_singleton.2
      (hsub S hS R hR), Finsupp.degree_single, Finsupp.single_eq_same]
  have htan : ∀ M : MvPolynomial (Fin 3) k, M.IsHomogeneous 1 → M ≠ 0 → IsRelPrime F M →
      T ≤ intersectionCycle M F → IsTangentAt F R M := fun M hM hM0 hFM hTM ↦ by
    refine (isTangentAt_iff_mult_lt_intersectionNumber hF (hs R hR).ne_zero hM hM0
      (eval_rep_eq_zero_of_le_intersectionCycle hF hM hFM hTM hR)).2 ?_
    rw [isSimplePoint_def.1 (hs R hR), ← intersectionCycle_apply hF hM hFM,
      intersectionCycle_comm]
    have := hTM R
    rw [hTR] at this
    exact_mod_cast (by omega : 1 < intersectionCycle M F R)
  exact ((hs R hR).associated_tangentLine_of_isTangentAt hF (htan L hL hL0 hFL hTL)).trans
    ((hs R hR).associated_tangentLine_of_isTangentAt hF (htan B hB hB0 hFB hTB)).symm

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

/-- **A line tangent at another point.** Let `k` be algebraically closed, `F` a form of degree
`d`, `P` a point with `r = m_P(F)`, and `L` a line through `P` that is not a component of `F`. If
`L` is tangent to `F` at a point `Q ≠ P`, then `L` meets `F` in fewer than `d - r` points other
than `P`. -/
theorem ncard_zeroLocus_pair_diff_lt_of_isTangentAt [IsAlgClosed k] (hF : F.IsHomogeneous d)
    (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) (hLF : ¬L ∣ F) {r : ℕ} (hr : mult F P = r)
    (hLP : eval P.rep L = 0) (hQP : Q ≠ P) (hQ : IsTangentAt F Q L) :
    (zeroLocus {F, L} \ {P}).ncard < d - r := by
  classical
  have hF0 : F ≠ 0 := fun h ↦ hLF (h ▸ dvd_zero L)
  have hLQ : eval Q.rep L = 0 := (isTangentAt_def.1 hQ).2.2.1
  have hrel : IsRelPrime F L :=
    ((irreducible_of_isHomogeneous_one hL hL0).isRelPrime_iff_not_dvd.2 hLF).symm
  have hs : (zeroLocus {F, L} \ {P} : Set (ℙ k (Fin 3 → k))).Finite :=
    (finite_zeroLocus_pair_of_isRelPrime hF hL hrel).sdiff
  have hmem : ∀ Q, Q ∈ zeroLocus {F, L} ↔ eval Q.rep F = 0 ∧ eval Q.rep L = 0 := fun Q ↦ by
    rw [mem_zeroLocus_iff_eval_rep (by rintro f (rfl | rfl); exacts [⟨d, hF⟩, ⟨1, hL⟩])]
    simp
  have hQs : Q ∈ hs.toFinset := by
    simp [hmem, hQ.eval_rep_eq_zero, hLQ, hQP]
  have hQ2 : 2 ≤ intersectionNumber Q F L := by
    have h1 : 1 ≤ mult F Q :=
      Order.one_le_iff_pos.2 (mult_pos_iff_eval_rep.2 hQ.eval_rep_eq_zero)
    have h2 := (isTangentAt_iff_mult_lt_intersectionNumber hF hF0 hL hL0 hLQ).1 hQ
    simpa [one_add_one_eq_two] using Order.add_one_le_of_lt (h1.trans_lt h2)
  have hP : (r : ℕ∞) ≤ intersectionNumber P F L := by
    simpa [mult_eq_one_of_isHomogeneous_one hL hL0 hLP, hr] using
      mul_mult_le_intersectionNumber (P := P) hF hL
  have hrest : ((hs.toFinset.erase Q).card : ℕ∞) ≤
      ∑ x ∈ hs.toFinset.erase Q, intersectionNumber x F L := by
    rw [← nsmul_one, ← Finset.sum_const]
    refine Finset.sum_le_sum fun x hx ↦ ?_
    simp only [Finset.mem_erase, Set.Finite.mem_toFinset, Set.mem_sdiff, hmem] at hx
    exact one_le_intersectionNumber hF hL hx.2.1.1 hx.2.1.2
  have hle := sum_intersectionNumber_le_mul hF hL hrel (insert P hs.toFinset)
  rw [Finset.sum_insert (by simp), ← Finset.add_sum_erase _ _ hQs, mul_one] at hle
  rw [Finset.card_erase_of_mem hQs] at hrest
  have hpos : 0 < hs.toFinset.card := Finset.card_pos.2 ⟨Q, hQs⟩
  have h : ((r + (2 + (hs.toFinset.card - 1)) : ℕ) : ℕ∞) ≤ d := by
    push_cast
    exact (add_le_add hP (add_le_add hQ2 hrest)).trans hle
  rw [Set.ncard_eq_toFinset_card _ hs]
  have := Nat.cast_le.1 h
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
    · refine ⟨{Q | IsMultiplePoint F Q} ∪ zeroLocus {F, polarDerivative P.rep F},
        (finite_setOf_isMultiplePoint_of_irreducible hF hirr).union
          (finite_zeroLocus_pair_of_isRelPrime hF (hF.polarDerivative _)
            (hF.isRelPrime_polarDerivative hirr hD0)), ?_⟩
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
