/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Bezout.Basic
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
* `ncard_zeroLocus_pair_diff_add`, `ncard_zeroLocus_pair_diff`: counting the points of
  `V(F) ∩ V(L)` other than `P`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.1, §5.3, Problem 5.12
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

/-- The linear form with dual coordinates `c` is nonzero. -/
theorem sum_C_mul_X_rep_ne_zero (c : ℙ k (Fin 3 → k)) :
    (∑ i, C (c.rep i) * X i : MvPolynomial (Fin 3) k) ≠ 0 := by
  intro h
  apply c.rep_ne_zero
  exact sum_C_mul_X_injective (h.trans (by simp))

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
    (irreducible_of_isHomogeneous_one (isHomogeneous_sum_C_mul_X _) (sum_C_mul_X_rep_ne_zero c))
    hc
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

end PlaneCurves.Projective

end
