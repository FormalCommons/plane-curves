/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.SetTheory.Cardinal.ENat
public import PlaneCurves.RingTheory.MvPolynomial.VanishingIdeal

/-!
# Finite zero sets and finite-dimensional quotients of polynomial rings

Let `k` be a field and `I` an ideal of `k[X] = MvPolynomial σ k`. This file compares the number
of points of the zero locus `V(I) = MvPolynomial.zeroLocus k I ⊆ kⁿ` with the dimension of
`k[X] ⧸ I` over `k`.

## Main results

* `MvPolynomial.card_le_rank_quotient`: a finite set of points of `V(I)` has at most
  `dim_k k[X] ⧸ I` elements.
* `MvPolynomial.encard_zeroLocus_le`: `#V(I) ≤ dim_k k[X] ⧸ I`, in `ℕ∞`.
* `MvPolynomial.finite_zeroLocus_of_finite`, `MvPolynomial.ncard_zeroLocus_le_finrank`: if
  `k[X] ⧸ I` is finite-dimensional, then `V(I)` is finite, with at most `dim_k k[X] ⧸ I`
  points.
* `MvPolynomial.isMaximal_of_le_of_finite_zeroLocus`: over an algebraically closed field, in
  finitely many variables, if `V(I)` is finite then every prime ideal containing `I` is maximal.
* `MvPolynomial.finite_zeroLocus_iff`: over an algebraically closed field, in finitely many
  variables, `V(I)` is finite if and only if `k[X] ⧸ I` is finite-dimensional.
* `MvPolynomial.encard_zeroLocus_le_and_finite_zeroLocus_iff`: the two statements together.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §1.7, Corollary 4 and Problem 1.17
-/

public section

namespace MvPolynomial

open Ideal

variable {k σ : Type*} [Field k]

/-- If `S` is a finite set of zeros of an ideal
`I` of `k[X]`, then `S` has at most `dim_k k[X] ⧸ I` elements: evaluation at the points of `S`
maps `k[X] ⧸ I` onto `kˢ`, by separating polynomials. -/
theorem card_le_rank_quotient {I : Ideal (MvPolynomial σ k)} (S : Finset (σ → k))
    (hS : (S : Set (σ → k)) ⊆ zeroLocus k I) :
    (S.card : Cardinal) ≤ Module.rank k (MvPolynomial σ k ⧸ I) := by
  classical
  let ev : MvPolynomial σ k →ₐ[k] (S → k) := AlgHom.pi fun P => aeval P.1
  have hI : ∀ f ∈ I, ev f = 0 := fun f hf => funext fun P => by
    simpa [ev] using hS P.2 f hf
  have hev : Function.Surjective ev := by
    intro c
    choose g hg using exists_eval_eq_indicator S
    refine ⟨∑ P : S, c P • g P, funext fun Q => ?_⟩
    have h (P : S) : aeval Q.1 (g P) = if Q = P then 1 else 0 := by
      have := hg P Q Q.2
      by_cases hQP : Q = P
      · simpa [hQP] using this
      · simpa [hQP, Subtype.coe_ne_coe.2 hQP] using this
    simp [ev, h]
  have := (Ideal.Quotient.liftₐ I ev hI).toLinearMap.rank_le_of_surjective
    (Ideal.Quotient.lift_surjective_of_surjective I hI hev)
  simpa [rank_fun'] using this

/-- **Points of `V(I)` and `dim_k k[X] ⧸ I`.** For an ideal `I` of `k[X] = MvPolynomial σ k`
over any field `k`, the number of points of `V(I) ⊆ kⁿ` is at most `dim_k k[X] ⧸ I`, as
elements of `ℕ∞` (the bound says nothing when the dimension is infinite). -/
theorem encard_zeroLocus_le (I : Ideal (MvPolynomial σ k)) :
    (zeroLocus k I).encard ≤ (Module.rank k (MvPolynomial σ k ⧸ I)).toENat := by
  refine ENat.forall_natCast_le_iff_le.1 fun n hn => ?_
  obtain ⟨t, ht, htn⟩ := Set.exists_subset_encard_eq hn
  have htf := Set.finite_of_encard_eq_coe htn
  have hcard : htf.toFinset.card = n := by
    rw [← ENat.natCast_inj, ← Set.encard_coe_eq_coe_finsetCard, Set.Finite.coe_toFinset, htn]
  rw [Cardinal.natCast_le_toENat, ← hcard]
  exact card_le_rank_quotient _ (by simpa using ht)

/-- If `k[X] ⧸ I` is finite-dimensional over `k`, then `V(I) ⊆ kⁿ` is finite. -/
theorem finite_zeroLocus_of_finite (I : Ideal (MvPolynomial σ k))
    [Module.Finite k (MvPolynomial σ k ⧸ I)] : (zeroLocus k I).Finite := by
  rw [← Set.encard_ne_top_iff]
  refine ne_top_of_le_ne_top ?_ (encard_zeroLocus_le I)
  rw [← Module.finrank_eq_rank, Cardinal.toENat_nat]
  exact ENat.natCast_ne_top _

/-- If `k[X] ⧸ I` is finite-dimensional over `k`, then `V(I) ⊆ kⁿ` has at most
`dim_k k[X] ⧸ I` points. -/
theorem ncard_zeroLocus_le_finrank (I : Ideal (MvPolynomial σ k))
    [Module.Finite k (MvPolynomial σ k ⧸ I)] :
    (zeroLocus k I).ncard ≤ Module.finrank k (MvPolynomial σ k ⧸ I) := by
  have h := encard_zeroLocus_le I
  rw [← (finite_zeroLocus_of_finite I).cast_ncard_eq, ← Module.finrank_eq_rank,
    Cardinal.toENat_nat] at h
  exact_mod_cast h

variable [IsAlgClosed k] [Finite σ]

/-- Over an algebraically closed field, in finitely many variables, if `V(I)` is finite then
every prime ideal containing `I` is maximal: by the Nullstellensatz it is the ideal of a finite
set of points, hence contains, and so equals, the ideal of one of them. -/
theorem isMaximal_of_le_of_finite_zeroLocus {I p : Ideal (MvPolynomial σ k)}
    (hI : (zeroLocus k I).Finite) [hp : p.IsPrime] (hIp : I ≤ p) : p.IsMaximal := by
  classical
  have hT : (zeroLocus k p).Finite := hI.subset (zeroLocus_anti_mono hIp)
  have hpT : p = hT.toFinset.inf fun x => vanishingIdeal k {x} := by
    refine (IsPrime.vanishingIdeal_zeroLocus (K := k) p).symm.trans (Ideal.ext fun f => ?_)
    rw [mem_vanishingIdeal_iff, Submodule.mem_finsetInf]
    simp only [Set.Finite.mem_toFinset, mem_vanishingIdeal_iff, Set.mem_singleton_iff, forall_eq]
  obtain ⟨x, -, hx⟩ := (hp.inf_le' (s := hT.toFinset)).1 hpT.ge
  have hmax : (vanishingIdeal k {x} : Ideal (MvPolynomial σ k)).IsMaximal :=
    isMaximal_iff_eq_vanishingIdeal_singleton.2 ⟨x, rfl⟩
  rwa [← hmax.eq_of_le hp.ne_top hx]

/-- Over an algebraically closed field, in finitely many variables, `V(I) ⊆ kⁿ` is finite if and
only if `k[X] ⧸ I` is finite-dimensional over `k`. -/
theorem finite_zeroLocus_iff (I : Ideal (MvPolynomial σ k)) :
    (zeroLocus k I).Finite ↔ Module.Finite k (MvPolynomial σ k ⧸ I) := by
  refine ⟨fun hI => ?_, fun _ => finite_zeroLocus_of_finite I⟩
  rw [Module.finite_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
  intro J hJ
  have := isMaximal_of_le_of_finite_zeroLocus hI (p := J.comap (Ideal.Quotient.mk I))
    (by simpa using Ideal.ker_le_comap (Ideal.Quotient.mk I))
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under _ this

omit [IsAlgClosed k] [Finite σ] in
/-- **Finite zero sets and finite-dimensional quotients.** Let `I` be an ideal of
`k[X] = MvPolynomial σ k`. Over any field `k`, the number of points of `V(I) ⊆ kⁿ` is at most
`dim_k k[X] ⧸ I` (in `ℕ∞`). If `k` is algebraically closed and there are finitely many
variables, `V(I)` is finite if and only if `k[X] ⧸ I` is finite-dimensional.

Milestone: *Finite zero sets and finite-dimensional quotients of polynomial rings*. -/
theorem encard_zeroLocus_le_and_finite_zeroLocus_iff (I : Ideal (MvPolynomial σ k)) :
    (zeroLocus k I).encard ≤ (Module.rank k (MvPolynomial σ k ⧸ I)).toENat ∧
      (IsAlgClosed k → Finite σ →
        ((zeroLocus k I).Finite ↔ Module.Finite k (MvPolynomial σ k ⧸ I))) :=
  ⟨encard_zeroLocus_le I, fun _ _ => finite_zeroLocus_iff I⟩

end MvPolynomial

end
