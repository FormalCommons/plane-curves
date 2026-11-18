/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Radical
public import PlaneCurves.RingTheory.MvPolynomial.HomogeneousIdeal
public import TauCeti.RingTheory.GradedAlgebra.HilbertSeries.RegularElement
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Graded pieces of the quotient of a polynomial ring by a form

Let `k` be a field and `R = k[X_i : i ∈ σ]`, `σ` finite, graded by total degree. For a nonzero
form `F` of degree `m`, multiplication by `F` gives an exact sequence
`0 → R_n → R_{m+n} → (R/(F))_{m+n} → 0`, so that `dim (R/(F))_{m+n} = dim R_{m+n} - dim R_n`.
In three variables this is Fulton's Problem 4.10: `dim (k[X,Y,Z]/(F))_d = dm - m(m-3)/2` for
every `d ≥ m - 2`, a formula stated in `ℤ` since `m(m-3)` is negative for `m = 1, 2`.

The file ends with the summary of the basic facts on homogeneous ideals of `R` and the graded
quotients `R/I` (Fulton, §4.2), most of which are in Mathlib and Tau Ceti.

## Main results

* `Nat.two_mul_multichoose_three`: `2 * multichoose 3 d = (d + 2)(d + 1)`, twice the number
  of monomials of degree `d` in three variables.
* `MvPolynomial.finrank_quotientPiece_span_singleton_add_multichoose`: for a nonzero form `F` of
  degree `m`, `dim (R/(F))_{m+n} + dim R_n = dim R_{m+n}`, with `dim R_n` the multichoose number.
* `MvPolynomial.finrank_quotientPiece_span_singleton_fin_three`: `dim (k[X,Y,Z]/(F))_d =
  dm - m(m-3)/2` in `ℤ`, for every `d ≥ m - 2`.
* `MvPolynomial.isHomogeneous_ideal_and_quotientPiece`: homogeneous ideals of `R` and the graded
  quotients `R/I`, parts (a)–(f).

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008]
-/

public section

open TauCeti.GradedAlgebra

/-- Twice the number of monomials of degree `d` in three variables, that is, twice the dimension
of the degree-`d` piece of `k[X, Y, Z]`, is `(d + 2)(d + 1)`. -/
theorem Nat.two_mul_multichoose_three (d : ℕ) :
    2 * (3 : ℕ).multichoose d = (d + 2) * (d + 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.multichoose_succ_succ, Nat.multichoose_two, mul_add, ih]
    ring

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σ k : Type*} [Field k]

/-- A nonzero form `F` of degree `m` in finitely many variables lowers the dimension of the
degree-`m + n` piece by that of the degree-`n` piece: `dim (R/(F))_{m+n} + dim R_n = dim R_{m+n}`,
where `dim R_n` is the number of monomials of degree `n`. -/
theorem finrank_quotientPiece_span_singleton_add_multichoose [Fintype σ]
    {F : MvPolynomial σ k} {m : ℕ} (hF : F.IsHomogeneous m) (hF₀ : F ≠ 0) (n : ℕ) :
    Module.finrank k (quotientPiece (homogeneousSubmodule σ k) (Ideal.span {F}) (m + n)) +
      (Fintype.card σ).multichoose n = (Fintype.card σ).multichoose (m + n) := by
  have := finrank_quotientPiece_span_singleton_add (homogeneousSubmodule σ k)
    ((mem_homogeneousSubmodule m F).mpr hF) (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hF₀) n
  simpa using this

/-- **Problem 4.10 of Fulton.** For a nonzero form `F` of degree `m` in `k[X, Y, Z]`,
`dim (k[X,Y,Z]/(F))_d = dm - m(m-3)/2` for every `d ≥ m - 2`. The formula is in `ℤ`, where
`m(m-3)` is even, so that the division is exact. For `m ≥ 3` it fails at `d = m - 3`. -/
theorem finrank_quotientPiece_span_singleton_fin_three {F : MvPolynomial (Fin 3) k} {m d : ℕ}
    (hF : F.IsHomogeneous m) (hF₀ : F ≠ 0) (hd : m ≤ d + 2) :
    (Module.finrank k (quotientPiece (homogeneousSubmodule (Fin 3) k) (Ideal.span {F}) d) : ℤ) =
      d * m - m * (m - 3) / 2 := by
  obtain ⟨t, ht⟩ : Even ((m : ℤ) * (m - 3)) := by
    have : (m : ℤ) * (m - 3) = m * (m - 1) - 2 * m := by ring
    rw [this]
    exact (Int.even_mul_pred_self m).sub (even_two_mul _)
  have ht' : (m : ℤ) * (m - 3) / 2 = t := by omega
  rw [ht']
  refine mul_left_cancel₀ (two_ne_zero (α := ℤ)) ?_
  have hR := fun e : ℕ ↦ congrArg (fun x : ℕ ↦ (x : ℤ)) (Nat.two_mul_multichoose_three e)
  push_cast at hR
  rcases le_or_gt m d with hmd | hmd
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hmd
    have h := congrArg (fun x : ℕ ↦ (x : ℤ))
      (finrank_quotientPiece_span_singleton_add_multichoose hF hF₀ n)
    have h₁ := hR (m + n)
    simp only [Fintype.card_fin] at h
    push_cast at h h₁ ⊢
    linear_combination 2 * h + h₁ - hR n - ht
  · have h := finrank_quotientPiece_span_singleton_of_lt (homogeneousSubmodule (Fin 3) k)
      ((mem_homogeneousSubmodule m F).mpr hF) hmd
    rw [TauCeti.finrank_homogeneousSubmodule_eq_multichoose, Fintype.card_fin] at h
    rw [h]
    obtain ⟨j, hj⟩ : ∃ j : ℕ, j < 2 ∧ m = d + 1 + j := ⟨m - d - 1, by omega, by omega⟩
    obtain ⟨hj, rfl⟩ := hj
    interval_cases j <;> push_cast at ht ⊢ <;> linear_combination hR d - ht
/-- **Homogeneous ideals and graded quotients of the polynomial ring.** Let `k` be a field and
`R = k[X_i : i ∈ σ]`, `σ` finite, graded by total degree.

* (a) An ideal of `R` is homogeneous if and only if it is spanned by forms, and a homogeneous
  ideal is spanned by finitely many forms.
* (b) A homogeneous ideal `I ≠ R` is prime if and only if `FG ∈ I` implies `F ∈ I` or `G ∈ I`
  for all forms `F` and `G`.
* (c) The radical, and the sums, intersections and products, of homogeneous ideals are
  homogeneous.
* (d) For a homogeneous ideal `I`, `R/I` is the internal direct sum of its pieces `Γ_d`, the
  images of the forms of degree `d`.
* (e) Each `Γ_d` is a finite-dimensional `k`-vector space.
* (f) For a nonzero form `F` of degree `m` in `k[X, Y, Z]` and `Γ = k[X,Y,Z]/(F)`,
  multiplication by `F` gives an exact sequence `0 → R_n → R_{m+n} → Γ_{m+n} → 0`, the map
  `R_d → Γ_d` is bijective for `d < m`, and `dim Γ_d = dm - m(m-3)/2` (in `ℤ`) for `d ≥ m - 2`.

Milestone: *Homogeneous ideals and graded quotients of the polynomial ring*. -/
theorem isHomogeneous_ideal_and_quotientPiece [Finite σ] :
    -- (a)
    (∀ I : Ideal (MvPolynomial σ k), I.IsHomogeneous (homogeneousSubmodule σ k) ↔
      ∃ S : Set (MvPolynomial σ k), (∀ f ∈ S, ∃ d, f.IsHomogeneous d) ∧ Ideal.span S = I) ∧
    (∀ I : Ideal (MvPolynomial σ k), I.IsHomogeneous (homogeneousSubmodule σ k) →
      ∃ s : Finset (MvPolynomial σ k), (∀ f ∈ s, ∃ d, f.IsHomogeneous d) ∧
        Ideal.span (s : Set (MvPolynomial σ k)) = I) ∧
    -- (b)
    (∀ I : Ideal (MvPolynomial σ k), I.IsHomogeneous (homogeneousSubmodule σ k) →
      (I.IsPrime ↔ I ≠ ⊤ ∧ ∀ F G : MvPolynomial σ k, (∃ d, F.IsHomogeneous d) →
        (∃ e, G.IsHomogeneous e) → F * G ∈ I → F ∈ I ∨ G ∈ I)) ∧
    -- (c)
    (∀ I J : Ideal (MvPolynomial σ k), I.IsHomogeneous (homogeneousSubmodule σ k) →
      J.IsHomogeneous (homogeneousSubmodule σ k) →
      I.radical.IsHomogeneous (homogeneousSubmodule σ k) ∧
      (I ⊔ J).IsHomogeneous (homogeneousSubmodule σ k) ∧
      (I ⊓ J).IsHomogeneous (homogeneousSubmodule σ k) ∧
      (I * J).IsHomogeneous (homogeneousSubmodule σ k)) ∧
    -- (d)
    (∀ I : Ideal (MvPolynomial σ k), I.IsHomogeneous (homogeneousSubmodule σ k) →
      DirectSum.IsInternal (quotientPiece (homogeneousSubmodule σ k) I)) ∧
    -- (e)
    (∀ I : Ideal (MvPolynomial σ k), I.IsHomogeneous (homogeneousSubmodule σ k) →
      ∀ d, Module.Finite k (quotientPiece (homogeneousSubmodule σ k) I d)) ∧
    -- (f)
    (∀ (F : MvPolynomial (Fin 3) k) (m : ℕ) (hF : F.IsHomogeneous m), F ≠ 0 →
      (∀ n : ℕ,
        Function.Injective (((LinearMap.mulLeft k F).domRestrict
          (homogeneousSubmodule (Fin 3) k n)).codRestrict (homogeneousSubmodule (Fin 3) k (m + n))
            fun x ↦ SetLike.mul_mem_graded ((mem_homogeneousSubmodule m F).mpr hF) x.2) ∧
        Function.Exact (((LinearMap.mulLeft k F).domRestrict
          (homogeneousSubmodule (Fin 3) k n)).codRestrict (homogeneousSubmodule (Fin 3) k (m + n))
            fun x ↦ SetLike.mul_mem_graded ((mem_homogeneousSubmodule m F).mpr hF) x.2)
          ((Ideal.Quotient.mkₐ k (Ideal.span {F})).toLinearMap.submoduleMap
            (homogeneousSubmodule (Fin 3) k (m + n))) ∧
        Function.Surjective ((Ideal.Quotient.mkₐ k (Ideal.span {F})).toLinearMap.submoduleMap
            (homogeneousSubmodule (Fin 3) k (m + n)))) ∧
      (∀ d < m, Function.Bijective ((Ideal.Quotient.mkₐ k (Ideal.span {F})).toLinearMap.submoduleMap
            (homogeneousSubmodule (Fin 3) k d))) ∧
      ∀ d : ℕ, m ≤ d + 2 →
        (Module.finrank k (quotientPiece (homogeneousSubmodule (Fin 3) k) (Ideal.span {F}) d) : ℤ) =
          d * m - m * (m - 3) / 2) := by
  have hform {f : MvPolynomial σ k} :
      SetLike.IsHomogeneousElem (homogeneousSubmodule σ k) f ↔ ∃ d, f.IsHomogeneous d :=
    exists_congr fun d ↦ mem_homogeneousSubmodule d f
  refine ⟨fun I ↦ ⟨fun hI ↦ ?_, ?_⟩, fun I hI ↦ exists_finset_isHomogeneous_span_eq hI,
    fun I hI ↦ ?_, fun I J hI hJ ↦ ⟨hI.radical, hI.sup hJ, hI.inf hJ, hI.mul hJ⟩,
    fun I hI ↦ isInternal_quotientPiece _ I hI, fun I _ d ↦ inferInstance,
    fun F m hF hF₀ ↦ ⟨fun n ↦ ⟨fun x y h ↦ Subtype.ext
      (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hF₀ (congrArg Subtype.val h)),
      exact_mulLeft_submoduleMap_span_singleton _ ((mem_homogeneousSubmodule m F).mpr hF) n,
      LinearMap.submoduleMap_surjective _ _⟩,
      fun d hd ↦ bijective_submoduleMap_span_singleton_of_lt _
        ((mem_homogeneousSubmodule m F).mpr hF) hd,
      fun d hd ↦ finrank_quotientPiece_span_singleton_fin_three hF hF₀ hd⟩⟩
  · obtain ⟨s, hs, hspan⟩ := exists_finset_isHomogeneous_span_eq hI
    exact ⟨s, hs, hspan⟩
  · rintro ⟨S, hS, rfl⟩
    exact Ideal.homogeneous_span _ S fun f hf ↦ hform.mpr (hS f hf)
  · rw [hI.isPrime_iff]
    exact and_congr_right fun _ ↦ ⟨fun h F G hF hG ↦ h (hform.mpr hF) (hform.mpr hG),
      fun h F G hF hG ↦ h F G (hform.mp hF) (hform.mp hG)⟩

end MvPolynomial

end
