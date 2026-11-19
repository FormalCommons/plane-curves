/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.AffineSpace.PlaneCurveDimension
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.ChartLocalRing
public import PlaneCurves.RingTheory.MvPolynomial.Homogenize.Factorization
public import PlaneCurves.RingTheory.MvPolynomial.Homogenize.Ideal

/-!
# Dimension of projective varieties of dimension zero and one

Let `k` be a field and `I` a homogeneous prime of `k[X₀, …, Xₙ]` with `Xᵢ ∉ I`, with function
field `k(V)` (`ProjectiveSpace.functionField I`). Fulton defines the dimension of `V = V(I)` as
the transcendence degree of `k(V)` over `k`. The chart isomorphism `k(V) ≅ k(V_*)`
(`functionField.chartEquiv`) and `(I_*)* = I` (`homogenization_map_dehomogenize`) reduce the
projective forms of parts (3)–(5) of Fulton's Proposition 10 of §6.5 to the affine ones of
`PlaneCurves.AlgebraicGeometry.AffineSpace.PlaneCurveDimension`.

## Main results

* `ProjectiveSpace.trdeg_functionField_eq_iff`: in `k[X₀, …, Xₙ₊₁]`, `tr.deg k(V) = n` if and
  only if `I = (F)` for an irreducible form `F`; for `n = 1`, the closed subvarieties of `ℙ²` of
  dimension one are the irreducible projective plane curves.
* `ProjectiveSpace.trdeg_functionField_eq_zero_iff`: over an algebraically closed field,
  `tr.deg k(V) = 0` if and only if `I` is the ideal of a point.
* `ProjectiveSpace.exists_eq_vanishingIdeal_singleton_of_trdeg_functionField_le_one`: if
  `tr.deg k(V) ≤ 1`, every homogeneous prime strictly containing `I` and not containing `Xᵢ` is
  the ideal of a point.
* `ProjectiveSpace.finite_zeroLocus_of_trdeg_functionField_le_one`: if `tr.deg k(V) ≤ 1`, every
  zero locus of a homogeneous ideal properly contained in `V` is finite.
* `ProjectiveSpace.trdeg_functionField_spec`: Fulton's Proposition 10 of §6.5, for the
  varieties of this library.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §6.5, Proposition 10
-/

public section

open MvPolynomial Projectivization TauCeti
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PlaneCurves.ProjectiveSpace

variable {k : Type*} [Field k] {n : ℕ} {i : Fin (n + 1)}

section chart

variable {I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)} [I.toIdeal.IsPrime]

/-- For a homogeneous prime `I` with `Xᵢ ∉ I`, the function fields of `V(I)` and of its affine
part `V(I_*)` have the same transcendence degree. -/
theorem trdeg_functionField_eq_trdeg_map_dehomogenize (hi : X i ∉ I) :
    haveI := isPrime_map_dehomogenize I hi
    Algebra.trdeg k (functionField I) =
      Algebra.trdeg k (AffineSpace.functionField (I.toIdeal.map (dehomogenize i))) :=
  (functionField.chartEquiv i hi).trdeg_eq

/-- A homogeneous prime `I` with `Xᵢ ∉ I` whose dehomogenization is the ideal of a point `Q` is
the ideal of the point `φᵢ⁻¹(Q)` of `ℙⁿ`. -/
theorem eq_vanishingIdeal_singleton_of_map_dehomogenize (hi : X i ∉ I) {Q : Fin n → k}
    (hQ : I.toIdeal.map (dehomogenize i) = MvPolynomial.vanishingIdeal k {Q}) :
    I = vanishingIdeal {(affineChart i).symm Q} := by
  rw [← projectiveClosure_singleton (i := i), vanishingIdeal_projectiveClosure, ← hQ,
    homogenization_map_dehomogenize I hi]

end chart

section hypersurface

variable {m : ℕ} {i : Fin (m + 2)}
  {I : HomogeneousIdeal (homogeneousSubmodule (Fin (m + 2)) k)} [I.toIdeal.IsPrime]

/-- **Homogeneous primes of dimension `m` in `k[X₀, …, Xₘ₊₁]`.** For a homogeneous prime `I`
with `Xᵢ ∉ I`, the function field of `V(I)` has transcendence degree `m` over `k` if and only if
`I = (F)` for an irreducible form `F`. For `m = 1`: the closed subvarieties of `ℙ²` of dimension
one are the irreducible projective plane curves `V(F)`. -/
theorem trdeg_functionField_eq_iff (hi : X i ∉ I) :
    Algebra.trdeg k (functionField I) = m ↔
      ∃ (F : MvPolynomial (Fin (m + 2)) k) (d : ℕ), Irreducible F ∧ F.IsHomogeneous d ∧
        I.toIdeal = Ideal.span {F} := by
  have := isPrime_map_dehomogenize I hi
  rw [trdeg_functionField_eq_trdeg_map_dehomogenize hi, AffineSpace.trdeg_functionField_eq_iff]
  constructor
  · rintro ⟨f, hf, hJ⟩
    refine ⟨_, _, irreducible_homogenize_totalDegree (i := i) hf,
      isHomogeneous_homogenize i _ f, ?_⟩
    rw [← Ideal.homogenization_span_singleton, ← hJ, homogenization_map_dehomogenize I hi]
  · rintro ⟨F, d, hF, hFd, hI⟩
    have hX : ¬ X i ∣ F := fun h ↦ hi (by
      rw [← HomogeneousIdeal.mem_iff, hI, Ideal.mem_span_singleton]
      exact (prime_X (R := k)).irreducible.dvd_symm hF h)
    refine ⟨_, (irreducible_dehomogenize_iff hFd hX).mpr hF, ?_⟩
    rw [hI, Ideal.map_span, Set.image_singleton]

end hypersurface

section points

variable [IsAlgClosed k] {I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)}
  [I.toIdeal.IsPrime]

/-- **Projective varieties of dimension zero.** Over an algebraically closed field, the function
field of `V(I)`, for a homogeneous prime `I` with `Xᵢ ∉ I`, has transcendence degree zero if and
only if `I` is the ideal of a point. -/
theorem trdeg_functionField_eq_zero_iff (hi : X i ∉ I) :
    Algebra.trdeg k (functionField I) = 0 ↔
      ∃ P : ℙ k (Fin (n + 1) → k), I = vanishingIdeal {P} := by
  have := isPrime_map_dehomogenize I hi
  rw [trdeg_functionField_eq_trdeg_map_dehomogenize hi,
    AffineSpace.trdeg_functionField_eq_zero_iff]
  refine ⟨fun ⟨Q, hQ⟩ ↦ ⟨_, eq_vanishingIdeal_singleton_of_map_dehomogenize hi hQ⟩, ?_⟩
  rintro ⟨P, rfl⟩
  have hP : P ∈ affineOpen i := by
    simpa [X_mem_vanishingIdeal_iff] using hi
  refine ⟨affineChart i P, ?_⟩
  rw [← Ideal.map_dehomogenize_homogenization (J := MvPolynomial.vanishingIdeal k _) (i := i),
    ← vanishingIdeal_projectiveClosure, projectiveClosure_singleton,
    (affineChart i).left_inv (by rwa [affineChart_source])]

/-- **Subvarieties of a projective curve.** Over an algebraically closed field, if the function
field of `V(I)` has transcendence degree at most one, every homogeneous prime `J` strictly
containing `I` with `Xᵢ ∉ J` is the ideal of a point: the closed subvarieties of a curve other
than the curve itself are points. -/
theorem exists_eq_vanishingIdeal_singleton_of_trdeg_functionField_le_one
    (h : Algebra.trdeg k (functionField I) ≤ 1)
    {J : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)} [J.toIdeal.IsPrime]
    (hIJ : I < J) (hi : X i ∉ J) : ∃ P : ℙ k (Fin (n + 1) → k), J = vanishingIdeal {P} := by
  have hiI : X i ∉ I := fun h ↦ hi (hIJ.le h)
  have := isPrime_map_dehomogenize I hiI
  have := isPrime_map_dehomogenize J hi
  rw [trdeg_functionField_eq_trdeg_map_dehomogenize hiI] at h
  have hlt : I.toIdeal.map (dehomogenize i) < J.toIdeal.map (dehomogenize i) := by
    refine lt_of_le_of_ne (Ideal.map_mono hIJ.le) fun heq ↦ hIJ.ne ?_
    rw [← homogenization_map_dehomogenize I hiI, ← homogenization_map_dehomogenize J hi, heq]
  obtain ⟨Q, hQ⟩ :=
    AffineSpace.exists_eq_vanishingIdeal_singleton_of_trdeg_functionField_le_one h hlt
  exact ⟨_, eq_vanishingIdeal_singleton_of_map_dehomogenize hi hQ⟩

/-- **Proper closed subsets of a projective curve are finite.** Over an algebraically closed
field, if the function field of `V(I)` has transcendence degree at most one, every zero locus
`V(J)` of a homogeneous ideal properly contained in `V(I)` is finite. Equivalently, the nonempty
subsets of `V(I)` that are open in `V(I)` are its cofinite subsets. In each chart `Uᵢ` with
`Xᵢ ∉ I`, `V(J) ∩ Uᵢ` lies in the finite set `V(I_* ⊔ J_*)`; if `Xᵢ ∈ I`, `V(I)` misses `Uᵢ`. -/
theorem finite_zeroLocus_of_trdeg_functionField_le_one
    (h : Algebra.trdeg k (functionField I) ≤ 1)
    {J : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k)}
    (hJ : zeroLocus (J : Set (MvPolynomial (Fin (n + 1)) k)) ⊂ zeroLocus (I : Set _)) :
    (zeroLocus (J : Set (MvPolynomial (Fin (n + 1)) k))).Finite := by
  have hJI : ¬ J ≤ I := fun hle ↦ hJ.not_subset (zeroLocus_anti_mono hle)
  rw [← Set.inter_univ (zeroLocus _), ← iUnion_affineOpen, Set.inter_iUnion]
  refine Set.finite_iUnion fun i ↦ ?_
  by_cases hi : X i ∈ I
  · refine Set.finite_empty.subset ?_
    rintro P ⟨hP, hPi⟩
    exact X_notMem_of_mem_affineOpen ⟨P, hJ.subset hP⟩ hPi hi
  have := isPrime_map_dehomogenize I hi
  rw [trdeg_functionField_eq_trdeg_map_dehomogenize hi] at h
  have hle : ¬ J.toIdeal.map (dehomogenize i) ≤ I.toIdeal.map (dehomogenize i) := fun hle ↦
    hJI (by rw [← homogenization_map_dehomogenize I hi]; exact Ideal.le_homogenization_iff.mpr hle)
  refine ((AffineSpace.finite_zeroLocus_sup_of_trdeg_functionField_le_one h hle).image
    (affineChart i).symm).subset ?_
  rintro P ⟨hP, hPi⟩
  have hP' : (affineChart i).symm (affineChart i P) = P :=
    (affineChart i).left_inv (by rwa [affineChart_source])
  have hPI : (affineChart i).symm (affineChart i P) ∈ zeroLocus (I : Set _) := by
    rw [hP']; exact hJ.subset hP
  have hPJ : (affineChart i).symm (affineChart i P) ∈ zeroLocus (J : Set _) := by
    rwa [hP']
  rw [affineChart_symm_mem_zeroLocus_iff] at hPI hPJ
  exact ⟨affineChart i P, (MvPolynomial.zeroLocus_sup _ _).ge ⟨hPI, hPJ⟩, hP'⟩

end points

section spec

universe u

variable (k) in
/-- **Dimension of curves and of closed subvarieties of the plane.** Let `k` be algebraically
closed, and define the dimension of a variety as the transcendence degree over `k` of its
function field. Varieties are given by their prime ideals, as everywhere in this library.

1. An open subvariety has the dimension of the variety: for a projective variety `W` not
   contained in the hyperplane `Xᵢ = 0`, the affine part `W_* = W ∩ Uᵢ` has the dimension of `W`.
2. The projective closure `V*` of an affine variety `V` has the dimension of `V`.
3. A variety of dimension zero is a point: an affine (resp. projective, meeting `Uᵢ`) variety has
   dimension zero if and only if its ideal is the ideal of a point.
4. If `R` is a domain whose fraction field has transcendence degree at most one over `k`, every
   nonzero prime of `R` is maximal. Hence the closed subvarieties of a curve, affine or
   projective, other than the curve are points, and the proper closed subsets of a curve,
   `V(J) ⊊ V(I)`, are finite; so its nonempty open subsets are its cofinite subsets.
5. The function field of an irreducible `F ∈ k[X, Y]` has transcendence degree one; the primes
   of `k[X, Y]` of dimension one are the ideals `(F)` with `F` irreducible, and the homogeneous
   primes of `k[X, Y, Z]` of dimension one (not containing `Xᵢ`) are the ideals `(F)` with `F`
   an irreducible form.

The library has no Zariski topology: the open subvarieties of part 1 are the affine parts of
projective varieties, part 3 and the first half of part 4 are stated through ideals, and the
closed subsets of part 4 are zero loci.

Milestone: *Dimension of curves and of closed subvarieties of the plane*. -/
theorem trdeg_functionField_spec [IsAlgClosed k] :
    -- (1)
    (∀ (n : ℕ) (i : Fin (n + 1)) (W : Set (ℙ k (Fin (n + 1) → k)))
        (hW : zeroLocus (vanishingIdeal W) = W) [hp : (vanishingIdeal W).toIdeal.IsPrime]
        (h : ¬ W ⊆ (affineOpen i)ᶜ),
      haveI := isPrime_vanishingIdeal_affinePart hW hp h
      Algebra.trdeg k (AffineSpace.functionField
          (MvPolynomial.vanishingIdeal k (affinePart i W))) =
        Algebra.trdeg k (functionField (vanishingIdeal W))) ∧
    -- (2)
    (∀ (n : ℕ) (i : Fin (n + 1)) (V : Set (Fin n → k))
        [hV : (MvPolynomial.vanishingIdeal k V).IsPrime],
      haveI := isPrime_vanishingIdeal_projectiveClosure (i := i) hV
      Algebra.trdeg k (functionField (vanishingIdeal (projectiveClosure i V))) =
        Algebra.trdeg k (AffineSpace.functionField (MvPolynomial.vanishingIdeal k V))) ∧
    -- (3)
    (∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime],
      Algebra.trdeg k (AffineSpace.functionField I) = 0 ↔
        ∃ P : Fin n → k, I = MvPolynomial.vanishingIdeal k {P}) ∧
    (∀ (n : ℕ) (i : Fin (n + 1)) (I : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k))
        [I.toIdeal.IsPrime], X i ∉ I →
      (Algebra.trdeg k (functionField I) = 0 ↔
        ∃ P : ℙ k (Fin (n + 1) → k), I = vanishingIdeal {P})) ∧
    -- (4)
    (∀ (R : Type u) [CommRing R] [IsDomain R] [Algebra k R] (K : Type u) [Field K]
        [Algebra R K] [IsFractionRing R K] [Algebra k K] [IsScalarTower k R K],
      Algebra.trdeg k K ≤ 1 → ∀ (p : Ideal R) [p.IsPrime], p ≠ ⊥ → p.IsMaximal) ∧
    (∀ (n : ℕ) (I J : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime] [J.IsPrime],
      Algebra.trdeg k (AffineSpace.functionField I) ≤ 1 → I < J →
        ∃ P : Fin n → k, J = MvPolynomial.vanishingIdeal k {P}) ∧
    (∀ (n : ℕ) (i : Fin (n + 1)) (I J : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k))
        [I.toIdeal.IsPrime] [J.toIdeal.IsPrime],
      Algebra.trdeg k (functionField I) ≤ 1 → I < J → X i ∉ J →
        ∃ P : ℙ k (Fin (n + 1) → k), J = vanishingIdeal {P}) ∧
    (∀ (n : ℕ) (I J : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime],
      Algebra.trdeg k (AffineSpace.functionField I) ≤ 1 →
        MvPolynomial.zeroLocus k J ⊂ MvPolynomial.zeroLocus k I →
          (MvPolynomial.zeroLocus k J).Finite) ∧
    (∀ (n : ℕ) (I J : HomogeneousIdeal (homogeneousSubmodule (Fin (n + 1)) k))
        [I.toIdeal.IsPrime],
      Algebra.trdeg k (functionField I) ≤ 1 →
        zeroLocus (J : Set (MvPolynomial (Fin (n + 1)) k)) ⊂ zeroLocus (I : Set _) →
          (zeroLocus (J : Set (MvPolynomial (Fin (n + 1)) k))).Finite) ∧
    -- (5)
    (∀ F : MvPolynomial (Fin 2) k, (hF : Irreducible F) →
      haveI := (Ideal.span_singleton_prime hF.ne_zero).mpr hF.prime
      Algebra.trdeg k (AffineSpace.functionField (Ideal.span {F})) = 1) ∧
    (∀ (I : Ideal (MvPolynomial (Fin 2) k)) [I.IsPrime],
      Algebra.trdeg k (AffineSpace.functionField I) = 1 ↔
        ∃ F, Irreducible F ∧ I = Ideal.span {F}) ∧
    (∀ (i : Fin 3) (I : HomogeneousIdeal (homogeneousSubmodule (Fin 3) k)) [I.toIdeal.IsPrime],
      X i ∉ I → (Algebra.trdeg k (functionField I) = 1 ↔
        ∃ (F : MvPolynomial (Fin 3) k) (d : ℕ), Irreducible F ∧ F.IsHomogeneous d ∧
          I.toIdeal = Ideal.span {F})) := by
  refine ⟨fun _ i _ hW _ h ↦ (functionField.affinePartEquiv i hW h).trdeg_eq.symm,
    fun _ i V _ ↦ (functionField.projectiveClosureEquiv i V).trdeg_eq,
    fun _ _ _ ↦ AffineSpace.trdeg_functionField_eq_zero_iff,
    fun _ _ _ _ hi ↦ trdeg_functionField_eq_zero_iff hi,
    fun _ _ _ _ K _ _ _ _ _ h _ _ hp ↦ Ideal.IsPrime.isMaximal_of_trdeg_fractionRing_le_one K h hp,
    fun _ _ _ _ _ h hIJ ↦
      AffineSpace.exists_eq_vanishingIdeal_singleton_of_trdeg_functionField_le_one h hIJ,
    fun _ _ _ _ _ _ h hIJ hi ↦
      exists_eq_vanishingIdeal_singleton_of_trdeg_functionField_le_one h hIJ hi,
    fun _ _ _ _ h hJ ↦ AffineSpace.finite_zeroLocus_of_trdeg_functionField_le_one h hJ,
    fun _ _ _ _ h hJ ↦ finite_zeroLocus_of_trdeg_functionField_le_one h hJ,
    fun _ hF ↦ by simpa using AffineSpace.trdeg_functionField_span_singleton (n := 1) hF,
    fun I _ ↦ by simpa using AffineSpace.trdeg_functionField_eq_iff (n := 1) I,
    fun _ _ _ hi ↦ by simpa using trdeg_functionField_eq_iff (m := 1) hi⟩

end spec

end PlaneCurves.ProjectiveSpace

end
