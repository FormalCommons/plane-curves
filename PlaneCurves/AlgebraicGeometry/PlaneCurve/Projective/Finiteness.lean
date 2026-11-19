/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.AffineSpace.PlaneZeroLocus
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Singular
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.ZeroLocus
public import PlaneCurves.RingTheory.MvPolynomial.Homogenize.Factorization
public import PlaneCurves.RingTheory.MvPolynomial.Homogeneous
public import PlaneCurves.RingTheory.MvPolynomial.PDeriv

/-!
# Finiteness of the intersection of two projective plane curves

Let `F` and `G` be forms in `k[X, Y, Z]`.

* If `F` and `G` are relatively prime (no common component), then `V(F) ∩ V(G) ⊆ ℙ²` is finite
  (Fulton, Problem 5.7), over any field. In each standard affine chart the dehomogenizations of
  `F` and `G` are relatively prime (`MvPolynomial.isRelPrime_dehomogenize`), so they have
  finitely many common zeros (§1.6, Proposition 2). Over an algebraically closed field the
  converse holds: a common component has infinitely many zeros.
* Over a perfect field, an irreducible form has a nonzero partial derivative, which it does not
  divide, and so only finitely many multiple points (Problem 5.8).
* Over an algebraically closed field, two curves of positive degree always meet: this is the
  projective dimension theorem `PlaneCurves.ProjectiveSpace.zeroLocus_nonempty_of_card_le`,
  for two forms in `ℙ²`.

## Main results

* `PlaneCurves.Projective.finite_zeroLocus_pair_of_isRelPrime`: `V(F, G)` is finite for
  relatively prime forms `F`, `G`.
* `PlaneCurves.Projective.isRelPrime_iff_finite_zeroLocus_pair`: over an algebraically closed
  field, `F` and `G` are relatively prime iff `V(F, G)` is finite.
* `PlaneCurves.Projective.finite_setOf_isMultiplePoint_of_irreducible`: an irreducible form over
  a perfect field has finitely many multiple points.
* `PlaneCurves.Projective.exists_finset_isSimplePoint_of_irreducible`: over an algebraically
  closed field, an irreducible form has any number of simple points outside a finite set.
* `PlaneCurves.Projective.finite_zeroLocus_pair_spec`: the three statements together.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.1, Problems 5.7 and 5.8
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F G : MvPolynomial (Fin 3) k} {m n : ℕ}

private theorem forall_isHomogeneous_pair (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) :
    ∀ f ∈ ({F, G} : Set (MvPolynomial (Fin 3) k)), ∃ d, f.IsHomogeneous d := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro f (rfl | rfl)
  exacts [⟨m, hF⟩, ⟨n, hG⟩]

/-- **Problem 5.7.** Relatively prime forms `F`, `G ∈ k[X, Y, Z]`, over any field `k`, have only
finitely many common zeros in `ℙ²`. -/
theorem finite_zeroLocus_pair_of_isRelPrime (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (h : IsRelPrime F G) : (zeroLocus {F, G}).Finite := by
  rw [← Set.inter_univ (zeroLocus _), ← iUnion_affineOpen, Set.inter_iUnion]
  refine Set.finite_iUnion fun i ↦ ?_
  refine ((finite_zeroLocus_span_pair_of_isRelPrime
    (isRelPrime_dehomogenize (i := i) hF hG h) k).image (affineChart i).symm).subset ?_
  rintro P ⟨hP, hPi⟩
  refine ⟨affineChart i P, ?_, (affineChart i).left_inv (by simpa using hPi)⟩
  rw [mem_zeroLocus_iff_affineChart (forall_isHomogeneous_pair hF hG) hPi] at hP
  rw [MvPolynomial.mem_zeroLocus_iff]
  intro p hp
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hp
  simp [hP F (by simp), hP G (by simp)]

/-- **The converse of Problem 5.7.** Over an algebraically closed field, forms `F`, `G` with only
finitely many common zeros in `ℙ²` are relatively prime: a common factor that is not a unit is a
form of positive degree (or `F = G = 0`), with infinitely many zeros. -/
theorem isRelPrime_of_finite_zeroLocus_pair [IsAlgClosed k] (hF : F.IsHomogeneous m)
    (hG : G.IsHomogeneous n) (h : (zeroLocus ({F, G} : Set (MvPolynomial (Fin 3) k))).Finite) :
    IsRelPrime F G := by
  by_contra hFG
  obtain ⟨H', e, he, hH'e, hH'F, hH'G⟩ := hF.exists_isHomogeneous_dvd_of_not_isRelPrime hG hFG
  refine zeroLocus_singleton_infinite le_rfl hH'e he (h.subset fun P hP ↦ ?_)
  rw [mem_zeroLocus_iff_eval_rep (by simpa using ⟨e, hH'e⟩)] at hP
  rw [mem_zeroLocus_iff_eval_rep (forall_isHomogeneous_pair hF hG)]
  have hP0 : eval P.rep H' = 0 := hP H' rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro f (rfl | rfl)
  exacts [zero_dvd_iff.1 (hP0 ▸ map_dvd (eval P.rep) hH'F),
    zero_dvd_iff.1 (hP0 ▸ map_dvd (eval P.rep) hH'G)]

/-- **Problem 5.7 and its converse.** Over an algebraically closed field, forms `F`, `G` are
relatively prime exactly when they have only finitely many common zeros in `ℙ²`. -/
theorem isRelPrime_iff_finite_zeroLocus_pair [IsAlgClosed k] (hF : F.IsHomogeneous m)
    (hG : G.IsHomogeneous n) :
    IsRelPrime F G ↔ (zeroLocus ({F, G} : Set (MvPolynomial (Fin 3) k))).Finite :=
  ⟨finite_zeroLocus_pair_of_isRelPrime hF hG, isRelPrime_of_finite_zeroLocus_pair hF hG⟩

/-- **Problem 5.8.** Over a perfect field, an irreducible form `F` has only finitely many
multiple points: they are common zeros of `F` and of a nonzero partial derivative of `F`, which
`F` does not divide. -/
theorem finite_setOf_isMultiplePoint_of_irreducible [PerfectField k] (hF : F.IsHomogeneous m)
    (hirr : Irreducible F) : {P | IsMultiplePoint F P}.Finite := by
  obtain ⟨i, hi⟩ := hirr.exists_pderiv_ne_zero
  have hrel : IsRelPrime F (pderiv i F) :=
    hirr.isRelPrime_iff_not_dvd.2 fun hd ↦ hi (pderiv_eq_zero_of_dvd hd)
  refine (finite_zeroLocus_pair_of_isRelPrime hF hF.pderiv hrel).subset fun P hP ↦ ?_
  induction P using Projectivization.ind with | h v hv =>
  obtain ⟨h0, h1⟩ := (isMultiplePoint_iff_eval_pderiv hF v hv).1 hP
  refine (mk_mem_zeroLocus_iff (forall_isHomogeneous_pair hF hF.pderiv) v hv).2 ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro f (rfl | rfl)
  exacts [h0, h1 i]

/-- Over an algebraically closed field, an irreducible form `F` has infinitely many simple
points: so for every finite set `s` of points and every `r`, there are `r` simple points of `F`
outside `s`. -/
theorem exists_finset_isSimplePoint_of_irreducible [IsAlgClosed k] (hF : F.IsHomogeneous m)
    (hirr : Irreducible F) (s : Finset (ℙ k (Fin 3 → k))) (r : ℕ) :
    ∃ T : Finset (ℙ k (Fin 3 → k)), Disjoint s T ∧ T.card = r ∧ ∀ Q ∈ T, IsSimplePoint F Q := by
  have hinf : ((zeroLocus ({F} : Set (MvPolynomial (Fin 3) k)) \ {P | IsMultiplePoint F P}) \
      (s : Set (ℙ k (Fin 3 → k)))).Infinite :=
    ((zeroLocus_singleton_infinite (n := 2) le_rfl hF (hF.degree_ne_zero_of_irreducible hirr)).sdiff
      (finite_setOf_isMultiplePoint_of_irreducible hF hirr)).sdiff s.finite_toSet
  obtain ⟨T, hTsub, hTcard⟩ := hinf.exists_subset_card_eq r
  refine ⟨T, Finset.disjoint_left.2 fun P hPs hPT ↦ (hTsub hPT).2 hPs, hTcard, fun Q hQ ↦ ?_⟩
  obtain ⟨⟨hQ0, hQ1⟩, -⟩ := hTsub hQ
  exact (isSimplePoint_or_isMultiplePoint hF hQ0).resolve_right hQ1

/- Positive degree is needed: the constant form `1` has no zeros. -/
example : zeroLocus ({1, X 0} : Set (MvPolynomial (Fin 3) k)) = ∅ :=
  zeroLocus_eq_empty_of_one_mem (by simp)

/-- **Finiteness of the intersection of two projective plane curves** (Fulton, Problems 5.7 and
5.8). Let `k` be algebraically closed, and `F`, `G ∈ k[X, Y, Z]` forms.

1. If `F` and `G` have no common component, then `V(F) ∩ V(G)` is finite. This holds over any
   field and for forms of any degree (`finite_zeroLocus_pair_of_isRelPrime`).
2. If `F` is irreducible, some partial derivative of `F` is nonzero, and `F` has only finitely
   many multiple points. This holds over any perfect field
   (`finite_setOf_isMultiplePoint_of_irreducible`).
3. If `F` and `G` have positive degree, they meet: `V(F) ∩ V(G) ≠ ∅`
   (`PlaneCurves.ProjectiveSpace.zeroLocus_nonempty_of_card_le`).

All three hold in every characteristic.

Milestone: *Finiteness of the intersection of two projective plane curves*. -/
theorem finite_zeroLocus_pair_spec [IsAlgClosed k] (hF : F.IsHomogeneous m)
    (hG : G.IsHomogeneous n) :
    (IsRelPrime F G → (zeroLocus {F} ∩ zeroLocus {G}).Finite) ∧
      (Irreducible F → (∃ i, pderiv i F ≠ 0) ∧ {P | IsMultiplePoint F P}.Finite) ∧
      (m ≠ 0 → n ≠ 0 → (zeroLocus {F} ∩ zeroLocus {G}).Nonempty) := by
  have hFG : zeroLocus {F} ∩ zeroLocus {G} =
      zeroLocus ({F, G} : Set (MvPolynomial (Fin 3) k)) := by
    rw [← zeroLocus_union, Set.singleton_union]
  rw [hFG]
  refine ⟨finite_zeroLocus_pair_of_isRelPrime hF hG,
    fun h ↦ ⟨h.exists_pderiv_ne_zero, finite_setOf_isMultiplePoint_of_irreducible hF h⟩,
    fun hm hn ↦ ?_⟩
  classical
  simpa using zeroLocus_nonempty_of_card_le (s := {F, G}) Finset.card_le_two
    (by simp only [Finset.mem_insert, Finset.mem_singleton]; rintro f (rfl | rfl) <;> grind)

end PlaneCurves.Projective

end
