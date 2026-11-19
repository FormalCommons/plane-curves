/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.FieldTheory.FunctionField.ResidueRing
public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import TauCeti.RingTheory.Ideal.Quotient.Semilocal

/-!
# Domains of transcendence degree one

Let `k` be a field, `R` a `k`-algebra that is a domain, and `K` its fraction field. This file
proves the algebraic forms of parts (3) and (4) of Fulton's Proposition 10 of §6.5, and the
finiteness of poles.

* `Algebra.lift_trdeg_eq_of_isFractionRing`: `R` and `K` have the same transcendence degree
  over `k`; so do two domains with isomorphic fraction fields
  (`Algebra.lift_trdeg_eq_of_algEquiv_fractionRing`,
  `Algebra.trdeg_le_one_of_algEquiv_fractionRing`).
* `Ring.krullDimLE_one_of_trdeg_le_one`: a domain of transcendence degree at most one over `k`
  has Krull dimension at most one.
* `Module.finite_quotient_span_singleton_of_trdeg_le_one`: if `R` is moreover finitely generated,
  then `R ⧸ (t)` is finite over `k` for every `t ≠ 0`.
* `Ideal.IsPrime.isMaximal_of_trdeg_fractionRing_le_one`: if `K` has transcendence degree at
  most one over `k`, every nonzero prime of `R` is maximal (part (4): the proper closed
  subvarieties of a curve are points).
* `Algebra.bijective_algebraMap_of_trdeg_fractionRing_eq_zero`: if `k` is algebraically closed
  and `K` has transcendence degree zero over `k`, then `k → R` is bijective (part (3): a
  variety of dimension zero is a point).
* `MaximalSpectrum.finite_setOf_notMem_ofField`: in a Noetherian domain of dimension at most
  one, each element of the fraction field lies in the localization at all but finitely many
  maximal ideals (finiteness of poles).

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §6.5, Proposition 10
-/

public section

universe u u' v v'

variable {k : Type*} {R : Type u} [Field k] [CommRing R] [IsDomain R] [Algebra k R]

namespace Algebra

variable (k R) in
/-- A domain and its fraction field have the same transcendence degree over a field `k`. -/
theorem lift_trdeg_eq_of_isFractionRing (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra k K] [IsScalarTower k R K] :
    Cardinal.lift.{v} (trdeg k R) = Cardinal.lift.{u} (trdeg k K) := by
  have := IsLocalization.isAlgebraic K (nonZeroDivisors R)
  have h := lift_trdeg_add_eq k R K
  rwa [trdeg_eq_zero (R := R) (A := K), Cardinal.lift_zero, add_zero] at h

/-- Two domains over a field `k` whose fraction fields are isomorphic as `k`-algebras have the
same transcendence degree over `k`. -/
theorem lift_trdeg_eq_of_algEquiv_fractionRing {R' : Type u'} [CommRing R'] [IsDomain R']
    [Algebra k R'] {K : Type v} {K' : Type v'} [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra k K] [IsScalarTower k R K] [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    [Algebra k K'] [IsScalarTower k R' K'] (φ : K ≃ₐ[k] K') :
    Cardinal.lift.{u'} (trdeg k R) = Cardinal.lift.{u} (trdeg k R') := by
  apply Cardinal.lift_injective.{max v v'}
  have h := congrArg Cardinal.lift.{max u' v'} (lift_trdeg_eq_of_isFractionRing k R K)
  have h' := congrArg Cardinal.lift.{max u v} (lift_trdeg_eq_of_isFractionRing k R' K')
  have hφ := congrArg Cardinal.lift.{max u u'} φ.lift_trdeg_eq
  simp only [Cardinal.lift_lift] at h h' hφ ⊢
  exact h.trans (hφ.trans h'.symm)

/-- If two domains over a field `k` have isomorphic fraction fields and one has transcendence
degree at most one over `k`, so does the other. -/
theorem trdeg_le_one_of_algEquiv_fractionRing {R' : Type u'} [CommRing R'] [IsDomain R']
    [Algebra k R'] {K : Type v} {K' : Type v'} [Field K] [Algebra R K] [IsFractionRing R K]
    [Algebra k K] [IsScalarTower k R K] [Field K'] [Algebra R' K'] [IsFractionRing R' K']
    [Algebra k K'] [IsScalarTower k R' K'] (φ : K ≃ₐ[k] K') (h : trdeg k R' ≤ 1) :
    trdeg k R ≤ 1 := by
  rwa [← Cardinal.lift_le_one_iff.{_, u'},
    lift_trdeg_eq_of_algEquiv_fractionRing (R := R) (R' := R') φ, Cardinal.lift_le_one_iff]

end Algebra

/-- A domain of transcendence degree at most one over a field has Krull dimension at most
one. -/
theorem Ring.krullDimLE_one_of_trdeg_le_one (h : Algebra.trdeg k R ≤ 1) : Ring.KrullDimLE 1 R :=
  (Ring.krullDimLE_one_iff_of_isPrime_bot).mpr fun _ hp _ ↦
    Ideal.IsPrime.isMaximal_of_trdeg_le_one h hp

/-- **Prime ideals of a domain of transcendence degree one.** If the fraction field `K` of a
domain `R` has transcendence degree at most one over a field `k`, every nonzero prime ideal of
`R` is maximal. For `R` the coordinate ring of a curve, this says that the closed subvarieties
of the curve other than the curve are points. -/
theorem Ideal.IsPrime.isMaximal_of_trdeg_fractionRing_le_one (K : Type v) [Field K] [Algebra R K]
    [IsFractionRing R K] [Algebra k K] [IsScalarTower k R K] (h : Algebra.trdeg k K ≤ 1)
    {p : Ideal R} [p.IsPrime] (hp : p ≠ ⊥) : p.IsMaximal := by
  refine Ideal.IsPrime.isMaximal_of_trdeg_le_one (k := k) ?_ hp
  rw [← Cardinal.lift_le_one_iff.{_, v}, Algebra.lift_trdeg_eq_of_isFractionRing k R K]
  simpa using h

/-- **Quotients of a curve's ring.** If `R` is a finitely generated domain of transcendence
degree at most one over a field `k`, then for `t ≠ 0` the quotient `R ⧸ (t)` is finite
dimensional over `k`: the zero set of `t` on the curve is a finite set of points. -/
theorem Module.finite_quotient_span_singleton_of_trdeg_le_one [Algebra.FiniteType k R]
    (h : Algebra.trdeg k R ≤ 1) {t : R} (ht : t ≠ 0) :
    Module.Finite k (R ⧸ Ideal.span {t}) := by
  refine (Module.finite_iff_krullDimLE_zero k _).mpr
    (Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr fun J hJ ↦ ?_)
  have := hJ.1.1
  refine Ideal.IsPrime.isMaximal_of_trdeg_le_one h fun hJ0 ↦ ht ?_
  simpa [hJ0] using hJ.1.2 (Ideal.mem_span_singleton_self t)

namespace Algebra

/-- **Domains of transcendence degree zero.** If `k` is algebraically closed and the fraction
field `K` of a `k`-domain `R` is algebraic over `k`, then the map `k → R` is bijective: `R` is
`k` itself. For `R` the coordinate ring of a variety, this says that a variety of dimension
zero is a point. -/
theorem bijective_algebraMap_of_trdeg_fractionRing_eq_zero [IsAlgClosed k] (K : Type v) [Field K]
    [Algebra R K] [IsFractionRing R K] [Algebra k K] [IsScalarTower k R K]
    (h : trdeg k K = 0) : Function.Bijective (algebraMap k R) := by
  have : Algebra.IsAlgebraic k R := by
    rw [← trdeg_eq_zero_iff, ← Cardinal.lift_eq_zero.{v},
      lift_trdeg_eq_of_isFractionRing k R K, h, Cardinal.lift_zero]
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

end Algebra

namespace MaximalSpectrum

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

/-- **Finiteness of poles.** Let `A` be a Noetherian domain of dimension at most one, for
instance a finitely generated domain of transcendence degree one over a field
(`Ring.krullDimLE_one_of_trdeg_le_one`), with fraction
field `K`. Every `z : K` lies in the localization of `A` at all but finitely many maximal ideals
`m`, seen as a subring of `K`: `z` has only finitely many poles. -/
theorem finite_setOf_notMem_ofField (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (z : K) :
    {m : MaximalSpectrum A | z ∉ Localization.subalgebra.ofField K m.asIdeal.primeCompl
      m.asIdeal.primeCompl_le_nonZeroDivisors}.Finite := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) z
  refine (TauCeti.finite_setOf_mem_maximalSpectrum A (nonZeroDivisors.ne_zero hs)).subset
    fun m hm ↦ ?_
  by_contra hsm
  exact hm ⟨a, s, hsm, div_eq_mul_inv _ _⟩

end MaximalSpectrum

end
