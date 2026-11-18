/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.BigOperators.Associated
public import TauCeti.RingTheory.MvPolynomial.Finrank
public import PlaneCurves.RingTheory.MvPolynomial.Irreducible
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Bases of products of linear forms

Let `L₀, L₁, …` and `M₀, M₁, …` be linear forms in `k[X, Y]` such that no `Lᵢ` is proportional
to any `Mⱼ` (and none is zero); repetitions among the `Lᵢ`, or among the `Mⱼ`, are allowed.
For each `d`, the `d + 1` products `Aᵢ = L₀ ⋯ L_{i-1} M₀ ⋯ M_{d-i-1}`, `0 ≤ i ≤ d`, form a basis
of the forms of degree `d`.

## Main results

* `MvPolynomial.linearIndependent_prod_mul_prod`: the products `Aᵢ` are linearly independent.
* `MvPolynomial.basisProdMulProd`: they form a basis of
  `homogeneousSubmodule (Fin 2) k d`, the forms of degree `d`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §2.6, Problem 2.35 (c)
-/

public section

namespace MvPolynomial

open Finset

variable {k : Type*} [Field k]

/-- The product `A_{i+1}` for `L₀, L₁, …` is `L₀` times the product `Aᵢ` for `L₁, L₂, …`. -/
private lemma prod_mul_prod_succ (L M : ℕ → MvPolynomial (Fin 2) k) (d : ℕ) (i : Fin (d + 1)) :
    (∏ l ∈ range (i.succ : ℕ), L l) * ∏ l ∈ range (d + 1 - i.succ), M l =
      L 0 * ((∏ l ∈ range i, L (l + 1)) * ∏ l ∈ range (d - i), M l) := by
  rw [Fin.val_succ, prod_range_succ', Nat.add_sub_add_right]
  ring

/-- If `L₀, L₁, …` and `M₀, M₁, …` are linear forms in `k[X, Y]` and no `Lᵢ` is zero or
proportional to an `Mⱼ`, then for each `d` the products `L₀ ⋯ L_{i-1} M₀ ⋯ M_{d-i-1}`,
`0 ≤ i ≤ d`, are linearly independent. -/
theorem linearIndependent_prod_mul_prod {L M : ℕ → MvPolynomial (Fin 2) k}
    (hL : ∀ i, (L i).IsHomogeneous 1) (hM : ∀ j, (M j).IsHomogeneous 1)
    (hLM : ∀ i j, LinearIndependent k ![L i, M j]) (d : ℕ) :
    LinearIndependent k fun i : Fin (d + 1) ↦
      (∏ l ∈ range i, L l) * ∏ l ∈ range (d - i), M l := by
  induction d generalizing L with
  | zero => simp
  | succ d ih =>
    have hL0 : L 0 ≠ 0 := (hLM 0 0).ne_zero 0
    have hprime : Prime (L 0) := (irreducible_of_totalDegree_eq_one' ((hL 0).totalDegree hL0)).prime
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_succ] at hg
    simp only [Fin.val_zero, range_zero, prod_empty, one_mul, Nat.sub_zero, prod_mul_prod_succ]
      at hg
    have hS : ∑ i : Fin (d + 1), g i.succ •
        (L 0 * ((∏ l ∈ range i, L (l + 1)) * ∏ l ∈ range (d - i), M l)) =
        L 0 * ∑ i : Fin (d + 1), g i.succ •
          ((∏ l ∈ range i, L (l + 1)) * ∏ l ∈ range (d - i), M l) := by
      rw [mul_sum]
      exact sum_congr rfl fun i _ ↦ (mul_smul_comm _ _ _).symm
    rw [hS] at hg
    have hg0 : g 0 = 0 := by
      by_contra h0
      have hdvd : L 0 ∣ g 0 • ∏ l ∈ range (d + 1), M l :=
        (dvd_add_left (dvd_mul_right _ _)).1 (hg ▸ dvd_zero _)
      rw [smul_eq_C_mul, hprime.dvd_mul] at hdvd
      rcases hdvd with hC | hdvd
      · exact hprime.not_isUnit (isUnit_of_dvd_unit hC ((isUnit_iff_ne_zero.2 h0).map C))
      · obtain ⟨j, -, hj⟩ := hprime.exists_mem_finset_dvd hdvd
        obtain ⟨u, hu⟩ := hprime.irreducible.associated_of_dvd
          (irreducible_of_totalDegree_eq_one' ((hM j).totalDegree ((hLM 0 j).ne_zero 1))) hj
        obtain ⟨c, -, hc⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
        have := LinearIndependent.pair_iff.1 (hLM 0 j) c (-1) (by
          simp [← hu, hc, smul_eq_C_mul, mul_comm])
        exact one_ne_zero (neg_eq_zero.1 this.2)
    rw [hg0, zero_smul, zero_add, mul_eq_zero, or_iff_right hL0] at hg
    have := Fintype.linearIndependent_iff.1
      (ih (L := fun l ↦ L (l + 1)) (fun i ↦ hL _) (fun i j ↦ hLM _ j)) _ hg
    exact Fin.cases hg0 this

omit [Field k] in
/-- A product of `i` linear forms and `d - i` linear forms, for `i ≤ d`, is a form of degree `d`. -/
theorem isHomogeneous_prod_mul_prod {σ R : Type*} [CommSemiring R]
    {L M : ℕ → MvPolynomial σ R}
    (hL : ∀ i, (L i).IsHomogeneous 1) (hM : ∀ j, (M j).IsHomogeneous 1) {d i : ℕ}
    (hi : i ≤ d) :
    ((∏ l ∈ range i, L l) * ∏ l ∈ range (d - i), M l).IsHomogeneous d := by
  have h := (IsHomogeneous.prod (range i) _ (fun _ ↦ 1) fun l _ ↦ hL l).mul
    (IsHomogeneous.prod (range (d - i)) _ (fun _ ↦ 1) fun l _ ↦ hM l)
  simpa [Nat.add_sub_cancel' hi] using h

/-- If `L₀, L₁, …` and `M₀, M₁, …` are linear forms in `k[X, Y]` and no `Lᵢ` is zero or
proportional to an `Mⱼ`, then the products `L₀ ⋯ L_{i-1} M₀ ⋯ M_{d-i-1}`, `0 ≤ i ≤ d`, form a
basis of the forms of degree `d`. -/
noncomputable def basisProdMulProd {L M : ℕ → MvPolynomial (Fin 2) k}
    (hL : ∀ i, (L i).IsHomogeneous 1) (hM : ∀ j, (M j).IsHomogeneous 1)
    (hLM : ∀ i j, LinearIndependent k ![L i, M j]) (d : ℕ) :
    Module.Basis (Fin (d + 1)) k (homogeneousSubmodule (Fin 2) k d) :=
  basisOfLinearIndependentOfCardEqFinrank
    (b := fun i ↦ ⟨_, isHomogeneous_prod_mul_prod hL hM (Nat.lt_succ_iff.1 i.isLt)⟩)
    (.of_comp (Submodule.subtype _) (linearIndependent_prod_mul_prod hL hM hLM d))
    (by simp)

@[simp]
theorem coe_basisProdMulProd_apply {L M : ℕ → MvPolynomial (Fin 2) k}
    (hL : ∀ i, (L i).IsHomogeneous 1) (hM : ∀ j, (M j).IsHomogeneous 1)
    (hLM : ∀ i j, LinearIndependent k ![L i, M j]) (d : ℕ) (i : Fin (d + 1)) :
    (basisProdMulProd hL hM hLM d i : MvPolynomial (Fin 2) k) =
      (∏ l ∈ range i, L l) * ∏ l ∈ range (d - i), M l := by
  simp [basisProdMulProd]

end MvPolynomial

end
