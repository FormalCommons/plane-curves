/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.RingTheory.Polynomial.GaussLemma

/-!
# Relatively prime plane polynomials have finitely many common zeros

Let `k` be a field and `F G : MvPolynomial (Fin 2) k` relatively prime (`IsRelPrime F G`: every
common divisor is a unit). Proposition 2 of §1.6 of Fulton says that `V(F, G)` is finite. We
prove, over any field:

* the ideal `(F, G)` contains a nonzero polynomial `D(X)` in `X` alone and a nonzero
  polynomial `E(Y)` in `Y` alone;
* the common zeros of `F` and `G` in `K²`, for any field `K` containing `k`, are finitely many,
  at most `deg D · deg E`;
* `k[X, Y] ⧸ (F, G)` is finite-dimensional over `k`, of dimension at most `deg D · deg E`.

The first step is Gauss's lemma: `F` and `G` stay relatively prime in `k(X)[Y]`, a principal
ideal domain, so `aF + bG = 1` there, and clearing denominators gives `D`. The other two hold for
every ideal that contains such `D(X)` and `E(Y)`.

## Main results

* `Polynomial.exists_C_mem_span_pair_of_isRelPrime`: over a GCD domain `R`, two relatively
  prime polynomials in `R[X]` generate an ideal that contains a nonzero constant.
* `Polynomial.Bivariate.equivMvPolynomial_C`: `R[X][Y] ≃ R[X₀, X₁]` sends `C r` to `r(X₀)`.
* `PlaneCurves.exists_aeval_X_mem_span_pair_of_isRelPrime`: `(F, G)` contains a nonzero
  polynomial in each variable alone.
* `PlaneCurves.finite_zeroLocus_of_aeval_X_mem`, `PlaneCurves.ncard_zeroLocus_le_of_aeval_X_mem`,
  `PlaneCurves.finite_quotient_of_aeval_X_mem`, `PlaneCurves.finrank_quotient_le_of_aeval_X_mem`:
  the zero locus and the quotient of an ideal that contains `D(X)` and `E(Y)`.
* `PlaneCurves.exists_zeroLocus_span_pair_finite_of_isRelPrime`: the three statements together.
* `PlaneCurves.finite_zeroLocus_span_pair_of_isRelPrime`,
  `PlaneCurves.finite_quotient_span_pair_of_isRelPrime`: the finiteness alone.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §1.6, Proposition 2.
-/

public section

open scoped nonZeroDivisors TensorProduct

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]

/-- Over a GCD domain `R`, two relatively prime polynomials `p, q ∈ R[X]` generate an ideal that
contains a nonzero constant: `a p + b q = C r` with `r ≠ 0`. -/
theorem exists_C_mem_span_pair_of_isRelPrime {p q : R[X]} (h : IsRelPrime p q) :
    ∃ r : R, r ≠ 0 ∧ C r ∈ Ideal.span {p, q} := by
  classical
  obtain ⟨a, b, hab⟩ := isRelPrime_iff_isCoprime.mp (h.map_fraction_map (K := FractionRing R))
  obtain ⟨c, hc, hca⟩ := IsLocalization.integerNormalization_spec R⁰ a
  obtain ⟨d, hd, hdb⟩ := IsLocalization.integerNormalization_spec R⁰ b
  refine ⟨c * d, mul_ne_zero (nonZeroDivisors.ne_zero hc) (nonZeroDivisors.ne_zero hd), ?_⟩
  have key : C d * IsLocalization.integerNormalization R⁰ a * p +
      C c * IsLocalization.integerNormalization R⁰ b * q = C (c * d) := by
    apply map_injective _ (IsFractionRing.injective R (FractionRing R))
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, hca, hdb, Algebra.smul_def,
      Polynomial.algebraMap_apply, map_mul]
    linear_combination (C (algebraMap R (FractionRing R) c) *
      C (algebraMap R (FractionRing R) d)) * hab
  rw [← key]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

/-- The isomorphism `S[X][Y] ≃ S[X₀, X₁]` sends a constant `C r`, for `r ∈ S[X]`, to `r(X₀)`. -/
theorem Bivariate.equivMvPolynomial_C {S : Type*} [CommSemiring S] (r : S[X]) :
    Bivariate.equivMvPolynomial S (C r) = aeval (MvPolynomial.X 0) r := by
  induction r using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    simp [← C_mul_X_pow_eq_monomial, Bivariate.equivMvPolynomial_C_C,
      Bivariate.equivMvPolynomial_C_X, MvPolynomial.algebraMap_eq]

end Polynomial

namespace PlaneCurves

open MvPolynomial

universe u v

variable {k : Type u} [Field k]


private theorem exists_aeval_X_zero_mem_span_pair {F G : MvPolynomial (Fin 2) k}
    (h : IsRelPrime F G) :
    ∃ D : Polynomial k, D ≠ 0 ∧ Polynomial.aeval (X 0) D ∈ Ideal.span {F, G} := by
  set e := Polynomial.Bivariate.equivMvPolynomial k
  have h' : IsRelPrime (e.symm F) (e.symm G) := IsRelPrime.of_map e (by simpa using h)
  obtain ⟨r, hr, hmem⟩ := Polynomial.exists_C_mem_span_pair_of_isRelPrime h'
  refine ⟨r, hr, ?_⟩
  have := Ideal.mem_map_of_mem e hmem
  rwa [Ideal.map_span, Set.image_pair, e.apply_symm_apply, e.apply_symm_apply,
    Polynomial.Bivariate.equivMvPolynomial_C] at this

/-- **Elimination for relatively prime plane polynomials.** If `F, G ∈ k[X₀, X₁]` are
relatively prime, then for each variable `Xᵢ` the ideal `(F, G)` contains `D(Xᵢ)` for a nonzero
one-variable polynomial `D`. -/
theorem exists_aeval_X_mem_span_pair_of_isRelPrime {F G : MvPolynomial (Fin 2) k}
    (h : IsRelPrime F G) (i : Fin 2) :
    ∃ D : Polynomial k, D ≠ 0 ∧ Polynomial.aeval (X i) D ∈ Ideal.span {F, G} := by
  fin_cases i
  · exact exists_aeval_X_zero_mem_span_pair h
  · set σ := renameEquiv k (Equiv.swap (0 : Fin 2) 1)
    have h' : IsRelPrime (σ F) (σ G) := IsRelPrime.of_map σ.symm (by simpa using h)
    obtain ⟨D, hD, hmem⟩ := exists_aeval_X_zero_mem_span_pair h'
    refine ⟨D, hD, ?_⟩
    have := Ideal.mem_map_of_mem σ.symm hmem
    rw [Ideal.map_span, Set.image_pair, σ.symm_apply_apply, σ.symm_apply_apply,
      ← Polynomial.aeval_algHom_apply] at this
    simpa [σ] using this

variable {I : Ideal (MvPolynomial (Fin 2) k)} {D E : Polynomial k}

section ZeroLocus

variable {K : Type v} [Field K] [Algebra k K]

private theorem mem_roots_of_mem_zeroLocus [DecidableEq K] (hD : D ≠ 0) {i : Fin 2}
    (hDI : Polynomial.aeval (X i) D ∈ I) {P : Fin 2 → K} (hP : P ∈ zeroLocus K I) :
    P i ∈ (D.map (algebraMap k K)).roots.toFinset := by
  have := (mem_zeroLocus_iff.mp hP) _ hDI
  rw [← Polynomial.aeval_algHom_apply, aeval_X] at this
  rw [Multiset.mem_toFinset, Polynomial.mem_roots_map hD, ← Polynomial.aeval_def]
  exact this

private theorem zeroLocus_subset_image [DecidableEq K] (hD : D ≠ 0) (hE : E ≠ 0)
    (hDI : Polynomial.aeval (X 0) D ∈ I) (hEI : Polynomial.aeval (X 1) E ∈ I) :
    zeroLocus K I ⊆ ((D.map (algebraMap k K)).roots.toFinset ×ˢ
      (E.map (algebraMap k K)).roots.toFinset).image (fun x : K × K ↦ ![x.1, x.2]) := by
  intro P hP
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product, Prod.exists]
  refine ⟨P 0, P 1, ⟨mem_roots_of_mem_zeroLocus hD hDI hP,
    mem_roots_of_mem_zeroLocus hE hEI hP⟩, ?_⟩
  ext i
  fin_cases i <;> rfl

/-- An ideal of `k[X₀, X₁]` that contains a nonzero `D(X₀)` and a nonzero `E(X₁)` has finitely
many zeros in `K²`, for every field `K` containing `k`. -/
theorem finite_zeroLocus_of_aeval_X_mem (hD : D ≠ 0) (hE : E ≠ 0)
    (hDI : Polynomial.aeval (X 0) D ∈ I) (hEI : Polynomial.aeval (X 1) E ∈ I) :
    (zeroLocus K I).Finite := by
  classical
  exact (Finset.finite_toSet _).subset (zeroLocus_subset_image hD hE hDI hEI)

/-- An ideal of `k[X₀, X₁]` that contains a nonzero `D(X₀)` and a nonzero `E(X₁)` has at most
`deg D · deg E` zeros in `K²`, for every field `K` containing `k`. -/
theorem ncard_zeroLocus_le_of_aeval_X_mem (hD : D ≠ 0) (hE : E ≠ 0)
    (hDI : Polynomial.aeval (X 0) D ∈ I) (hEI : Polynomial.aeval (X 1) E ∈ I) :
    (zeroLocus K I).ncard ≤ D.natDegree * E.natDegree := by
  classical
  refine (Set.ncard_le_ncard (zeroLocus_subset_image hD hE hDI hEI) (Finset.finite_toSet _)).trans
    ?_
  rw [Set.ncard_coe_finset]
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product]
  refine Nat.mul_le_mul ?_ ?_
  · exact (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans (Polynomial.natDegree_map _).le)
  · exact (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans (Polynomial.natDegree_map _).le)

end ZeroLocus

section Quotient

private theorem aeval_mk_X_eq_zero {i : Fin 2} {P : Polynomial k}
    (h : Polynomial.aeval (X i) P ∈ I) : Polynomial.aeval (Ideal.Quotient.mk I (X i)) P = 0 := by
  rw [← Ideal.Quotient.mkₐ_eq_mk k, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem]
  exact h

/-- The `k`-algebra map `k[X]/(D) ⊗ k[Y]/(E) → k[X, Y]/I` sending the two roots to the images of
`X₀` and `X₁`, for an ideal `I` containing `D(X₀)` and `E(X₁)`. -/
private noncomputable def tensorLift (hDI : Polynomial.aeval (X 0) D ∈ I)
    (hEI : Polynomial.aeval (X 1) E ∈ I) :
    AdjoinRoot D ⊗[k] AdjoinRoot E →ₐ[k] MvPolynomial (Fin 2) k ⧸ I :=
  Algebra.TensorProduct.lift
    (AdjoinRoot.liftAlgHom D (Algebra.ofId k _) _ (aeval_mk_X_eq_zero hDI))
    (AdjoinRoot.liftAlgHom E (Algebra.ofId k _) _ (aeval_mk_X_eq_zero hEI))
    (fun _ _ ↦ Commute.all _ _)

private theorem tensorLift_surjective (hDI : Polynomial.aeval (X 0) D ∈ I)
    (hEI : Polynomial.aeval (X 1) E ∈ I) : Function.Surjective (tensorLift hDI hEI) := by
  let g : MvPolynomial (Fin 2) k →ₐ[k] AdjoinRoot D ⊗[k] AdjoinRoot E :=
    aeval ![AdjoinRoot.root D ⊗ₜ 1, 1 ⊗ₜ AdjoinRoot.root E]
  have hcomp : (tensorLift hDI hEI).comp g = Ideal.Quotient.mkₐ k I := by
    refine MvPolynomial.algHom_ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · simpa [g, tensorLift, Ideal.Quotient.mkₐ_eq_mk] using
        AdjoinRoot.liftAlgHom_root (p := D) (Algebra.ofId k _) _ (aeval_mk_X_eq_zero hDI)
    · simpa [g, tensorLift, Ideal.Quotient.mkₐ_eq_mk] using
        AdjoinRoot.liftAlgHom_root (p := E) (Algebra.ofId k _) _ (aeval_mk_X_eq_zero hEI)
  refine Function.Surjective.of_comp (g := g) ?_
  rw [← AlgHom.coe_comp, hcomp]
  exact Ideal.Quotient.mkₐ_surjective k I

/-- If an ideal `I` of `k[X₀, X₁]` contains a nonzero `D(X₀)` and a nonzero `E(X₁)`, then
`k[X₀, X₁] ⧸ I` is finite-dimensional over `k`. -/
theorem finite_quotient_of_aeval_X_mem (hD : D ≠ 0) (hE : E ≠ 0)
    (hDI : Polynomial.aeval (X 0) D ∈ I) (hEI : Polynomial.aeval (X 1) E ∈ I) :
    Module.Finite k (MvPolynomial (Fin 2) k ⧸ I) :=
  have := (AdjoinRoot.powerBasis hD).finite
  have := (AdjoinRoot.powerBasis hE).finite
  .of_surjective (tensorLift hDI hEI).toLinearMap (tensorLift_surjective hDI hEI)

/-- If an ideal `I` of `k[X₀, X₁]` contains a nonzero `D(X₀)` and a nonzero `E(X₁)`, then
`k[X₀, X₁] ⧸ I` has dimension at most `deg D · deg E` over `k`. -/
theorem finrank_quotient_le_of_aeval_X_mem (hD : D ≠ 0) (hE : E ≠ 0)
    (hDI : Polynomial.aeval (X 0) D ∈ I) (hEI : Polynomial.aeval (X 1) E ∈ I) :
    Module.finrank k (MvPolynomial (Fin 2) k ⧸ I) ≤ D.natDegree * E.natDegree := by
  have := (AdjoinRoot.powerBasis hD).finite
  have := (AdjoinRoot.powerBasis hE).finite
  refine (LinearMap.finrank_le_finrank_of_surjective (f := (tensorLift hDI hEI).toLinearMap)
    (tensorLift_surjective hDI hEI)).trans_eq ?_
  rw [Module.finrank_tensorProduct, (AdjoinRoot.powerBasis hD).finrank,
    (AdjoinRoot.powerBasis hE).finrank, AdjoinRoot.powerBasis_dim, AdjoinRoot.powerBasis_dim]

end Quotient

variable {F G : MvPolynomial (Fin 2) k}

/-- **Relatively prime plane polynomials have finitely many common zeros** (Fulton, §1.6,
Proposition 2). If `F, G ∈ k[X₀, X₁]` are relatively prime, over any field `k`, then the ideal
`(F, G)` contains `D(X₀)` and `E(X₁)` for nonzero one-variable polynomials `D` and `E`; for every
field `K` containing `k`, the common zeros of `F` and `G` in `K²` are finitely many, at most
`deg D · deg E`; and `k[X₀, X₁] ⧸ (F, G)` is finite-dimensional over `k`, of dimension at most
`deg D · deg E`.

Milestone: *Coprime plane polynomials have finitely many common zeros*. -/
theorem exists_zeroLocus_span_pair_finite_of_isRelPrime (h : IsRelPrime F G) :
    ∃ D E : Polynomial k, D ≠ 0 ∧ E ≠ 0 ∧
      Polynomial.aeval (X 0) D ∈ Ideal.span {F, G} ∧
      Polynomial.aeval (X 1) E ∈ Ideal.span {F, G} ∧
      (∀ (K : Type v) [Field K] [Algebra k K], (zeroLocus K (Ideal.span {F, G})).Finite ∧
        (zeroLocus K (Ideal.span {F, G})).ncard ≤ D.natDegree * E.natDegree) ∧
      Module.Finite k (MvPolynomial (Fin 2) k ⧸ Ideal.span {F, G}) ∧
      Module.finrank k (MvPolynomial (Fin 2) k ⧸ Ideal.span {F, G}) ≤
        D.natDegree * E.natDegree := by
  obtain ⟨D, hD, hDI⟩ := exists_aeval_X_mem_span_pair_of_isRelPrime h 0
  obtain ⟨E, hE, hEI⟩ := exists_aeval_X_mem_span_pair_of_isRelPrime h 1
  exact ⟨D, E, hD, hE, hDI, hEI, fun _ _ _ ↦ ⟨finite_zeroLocus_of_aeval_X_mem hD hE hDI hEI,
    ncard_zeroLocus_le_of_aeval_X_mem hD hE hDI hEI⟩,
    finite_quotient_of_aeval_X_mem hD hE hDI hEI, finrank_quotient_le_of_aeval_X_mem hD hE hDI hEI⟩

/-- Relatively prime `F, G ∈ k[X₀, X₁]` have finitely many common zeros in `K²`, for every field
`K` containing `k`. -/
theorem finite_zeroLocus_span_pair_of_isRelPrime (h : IsRelPrime F G) (K : Type v) [Field K]
    [Algebra k K] : (zeroLocus K (Ideal.span {F, G})).Finite := by
  obtain ⟨D, hD, hDI⟩ := exists_aeval_X_mem_span_pair_of_isRelPrime h 0
  obtain ⟨E, hE, hEI⟩ := exists_aeval_X_mem_span_pair_of_isRelPrime h 1
  exact finite_zeroLocus_of_aeval_X_mem hD hE hDI hEI

/-- For relatively prime `F, G ∈ k[X₀, X₁]`, the quotient `k[X₀, X₁] ⧸ (F, G)` is
finite-dimensional over `k`. -/
theorem finite_quotient_span_pair_of_isRelPrime (h : IsRelPrime F G) :
    Module.Finite k (MvPolynomial (Fin 2) k ⧸ Ideal.span {F, G}) := by
  obtain ⟨D, hD, hDI⟩ := exists_aeval_X_mem_span_pair_of_isRelPrime h 0
  obtain ⟨E, hE, hEI⟩ := exists_aeval_X_mem_span_pair_of_isRelPrime h 1
  exact finite_quotient_of_aeval_X_mem hD hE hDI hEI

end PlaneCurves

end
