/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.AffineSpace.RationalFunction
public import PlaneCurves.RingTheory.KrullDimension.TrdegOne
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Nullstellensatz
public import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Dimension of affine varieties of dimension zero and one

Let `k` be a field and `I` a prime ideal of `k[X₁, …, Xₙ]`, with function field
`k(V) = Frac(k[X] ⧸ I)` (`AffineSpace.functionField I`). Fulton defines the dimension of
`V = V(I)` as the transcendence degree of `k(V)` over `k`. This file relates it to the height
of `I` and proves the affine forms of parts (3)–(5) of Fulton's Proposition 10 of §6.5.

## Main results

* `AffineSpace.height_add_toNat_trdeg_functionField`: `ht I + tr.deg k(V) = n`.
* `AffineSpace.trdeg_functionField_eq_iff`: in `k[X₀, …, Xₙ]`, `tr.deg k(V) = n` if and only if
  `I = (F)` for an irreducible `F`; for `n = 1`, the closed subvarieties of `𝔸²` of dimension
  one are the irreducible plane curves.
* `AffineSpace.trdeg_functionField_span_singleton`: the function field of an irreducible
  `F ∈ k[X₀, …, Xₙ]` has transcendence degree `n`.
* `AffineSpace.trdeg_functionField_eq_zero_iff`: over an algebraically closed field,
  `tr.deg k(V) = 0` if and only if `I` is the ideal of a point.
* `AffineSpace.isMaximal_of_trdeg_functionField_le_one`: if `tr.deg k(V) ≤ 1`, every prime
  strictly containing `I` is maximal, so it is the ideal of a point when `k` is algebraically
  closed (`AffineSpace.exists_eq_vanishingIdeal_singleton_of_trdeg_functionField_le_one`).

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §6.5, Proposition 10
-/

public section

open MvPolynomial

namespace PlaneCurves.AffineSpace

variable {k : Type*} [Field k] {σ : Type*} [Finite σ]

section height

variable (I : Ideal (MvPolynomial σ k)) [I.IsPrime]

/-- The transcendence degree of the function field of an affine variety is finite. -/
theorem trdeg_functionField_lt_aleph0 : Algebra.trdeg k (functionField I) < Cardinal.aleph0 := by
  have h := Algebra.lift_trdeg_eq_of_isFractionRing k (MvPolynomial σ k ⧸ I) (functionField I)
  rw [Cardinal.lift_id, Cardinal.lift_id] at h
  exact h ▸ trdeg_lt_aleph0_of_finiteType

/-- **Height and dimension.** For a prime `I` of `k[X₁, …, Xₙ]`, the height of `I` plus the
transcendence degree of the function field of `V(I)` is `n`. -/
theorem height_add_toNat_trdeg_functionField :
    I.height + (Algebra.trdeg k (functionField I)).toNat = Nat.card σ := by
  have h := Ideal.height_add_ringKrullDim_quotient_of_finiteType k I
  rw [TauCeti.ringKrullDim_eq_toNat_trdeg_of_isFractionRing k (MvPolynomial σ k ⧸ I)
    (functionField I), MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add] at h
  exact_mod_cast h

end height

section hypersurface

variable {n : ℕ}

/-- **Primes of dimension `n` in `k[X₀, …, Xₙ]`.** For a prime `I` of `k[X₀, …, Xₙ]`, the
function field of `V(I)` has transcendence degree `n` over `k` if and only if `I = (F)` for an
irreducible `F`. For `n = 1`: the closed subvarieties of `𝔸²` of dimension one are the
irreducible plane curves `V(F)`. -/
theorem trdeg_functionField_eq_iff (I : Ideal (MvPolynomial (Fin (n + 1)) k)) [I.IsPrime] :
    Algebra.trdeg k (functionField I) = n ↔ ∃ F, Irreducible F ∧ I = Ideal.span {F} := by
  have h := height_add_toNat_trdeg_functionField I
  have hlt := trdeg_functionField_lt_aleph0 I
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have key : Algebra.trdeg k (functionField I) = n ↔ I.height = 1 := by
    obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hlt
    obtain ⟨h0, h0'⟩ := ENat.ne_top_iff_exists.mp
      (ne_top_of_le_ne_top (ENat.natCast_ne_top (n + 1)) (le_self_add.trans h.le))
    rw [hm, Cardinal.toNat_natCast, ← h0'] at h
    rw [hm, ← h0', Nat.cast_inj, Nat.cast_eq_one]
    norm_cast at h
    omega
  rw [key]
  constructor
  · intro h1
    obtain ⟨F, hF⟩ := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one h1
    have hne : I ≠ ⊥ := I.ne_bot_of_height_eq_one h1
    rw [hF, Ideal.submodule_span_eq] at hne ⊢
    refine ⟨F, ?_, rfl⟩
    have : (Ideal.span {F}).IsPrime := by rw [← Ideal.submodule_span_eq, ← hF]; infer_instance
    exact ((Ideal.span_singleton_prime (by simpa using hne)).mp this).irreducible
  · rintro ⟨F, hF, rfl⟩
    exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hF.ne_zero) hF.not_isUnit

/-- The function field of an irreducible `F ∈ k[X₀, …, Xₙ]` has transcendence degree `n` over
`k`: an irreducible hypersurface of `𝔸ⁿ⁺¹` has dimension `n`. -/
theorem trdeg_functionField_span_singleton {F : MvPolynomial (Fin (n + 1)) k}
    (hF : Irreducible F) :
    haveI := (Ideal.span_singleton_prime hF.ne_zero).mpr hF.prime
    Algebra.trdeg k (functionField (Ideal.span {F})) = n :=
  haveI := (Ideal.span_singleton_prime hF.ne_zero).mpr hF.prime
  (trdeg_functionField_eq_iff _).mpr ⟨F, hF, rfl⟩

end hypersurface

section points

variable {I : Ideal (MvPolynomial σ k)} [I.IsPrime]

/-- **Varieties of dimension zero.** Over an algebraically closed field, the function field of
`V(I)`, for a prime `I` of `k[X₁, …, Xₙ]`, has transcendence degree zero if and only if `I` is
the ideal of a point: a variety of dimension zero is a point. -/
theorem trdeg_functionField_eq_zero_iff [IsAlgClosed k] :
    Algebra.trdeg k (functionField I) = 0 ↔ ∃ P : σ → k, I = vanishingIdeal k {P} := by
  rw [← isMaximal_iff_eq_vanishingIdeal_singleton]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hb := Algebra.bijective_algebraMap_of_trdeg_fractionRing_eq_zero
      (R := MvPolynomial σ k ⧸ I) (functionField I) h
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).mpr
      ((RingEquiv.ofBijective _ hb).symm.toMulEquiv.isField (Field.toIsField k))
  · have hd := TauCeti.ringKrullDim_eq_toNat_trdeg_of_isFractionRing k (MvPolynomial σ k ⧸ I)
      (functionField I)
    rw [ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient I).mp h)] at hd
    obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp (trdeg_functionField_lt_aleph0 I)
    rw [hm, Cardinal.toNat_natCast] at hd
    rw [hm, Nat.cast_eq_zero]
    exact_mod_cast hd.symm

omit [Finite σ] in
/-- **Subvarieties of a curve.** If the function field of `V(I)` has transcendence degree at
most one, every prime ideal strictly containing `I` is maximal: the closed subvarieties of a
curve other than the curve itself are points
(`exists_eq_vanishingIdeal_singleton_of_trdeg_functionField_le_one`). -/
theorem isMaximal_of_trdeg_functionField_le_one (h : Algebra.trdeg k (functionField I) ≤ 1)
    {J : Ideal (MvPolynomial σ k)} [J.IsPrime] (hIJ : I < J) : J.IsMaximal := by
  have := Ideal.isPrime_map_quotientMk_of_isPrime hIJ.le
  have hne : J.map (Ideal.Quotient.mk I) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact hIJ.not_ge
  have := Ideal.IsPrime.isMaximal_of_trdeg_fractionRing_le_one (functionField I) h hne
  have hJ := Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    (K := J.map (Ideal.Quotient.mk I))
  rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr hIJ.le] at hJ

/-- Over an algebraically closed field, if the function field of `V(I)` has transcendence degree
at most one, every prime ideal strictly containing `I` is the ideal of a point. -/
theorem exists_eq_vanishingIdeal_singleton_of_trdeg_functionField_le_one [IsAlgClosed k]
    (h : Algebra.trdeg k (functionField I) ≤ 1) {J : Ideal (MvPolynomial σ k)} [J.IsPrime]
    (hIJ : I < J) : ∃ P : σ → k, J = vanishingIdeal k {P} :=
  isMaximal_iff_eq_vanishingIdeal_singleton.mp (isMaximal_of_trdeg_functionField_le_one h hIJ)

end points

end PlaneCurves.AffineSpace

end
