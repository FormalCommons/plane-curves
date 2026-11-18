/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import PlaneCurves.RingTheory.Regular.IsRelPrime
public import TauCeti.RingTheory.GradedAlgebra.HilbertSeries.RegularSequence
public import TauCeti.RingTheory.MvPolynomial.Finrank
public import TauCeti.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.LinearCombination

/-!
# Forms in the ideal of two relatively prime binary forms

Let `k` be a field and let `A`, `B` be relatively prime forms of degrees `m` and `n` in `k[X, Y]`.
Every form of degree `t ≥ m + n - 1` lies in the ideal `(A, B)`: it is `C A + D B` with forms `C`,
`D` of degrees `t - m` and `t - n`. This is the algebraic step in Fulton's proof that
`I_P^(m + n - 1) ⊆ (F, G)` when the leading forms of `F` and `G` have no common factor (Fulton,
§3.3, Lemma (a) of Property (5)), done over any field.

The proof counts dimensions: `A, B` is a regular sequence, so Tau Ceti's Hilbert series of a
quotient by a homogeneous regular sequence gives `dim_k (k[X, Y]/(A, B))_t =
(t + 1) - (t - m + 1) - (t - n + 1) + (t - m - n + 1) = 0`.

For forms that are not relatively prime, a common factor of positive degree gives the converse
tool of Lemma (b): forms `A'`, `B'` of degrees `m - 1`, `n - 1` with `B' ≠ 0` and `A B' = B A'`.

## Main results

* `MvPolynomial.finrank_quotientPiece_span_pair_fin_two`: the degree-`t` piece of
  `k[X, Y]/(A, B)` is zero for `t ≥ m + n - 1`.
* `MvPolynomial.homogeneousSubmodule_le_span_pair_fin_two`: the forms of degree `t` lie in
  `(A, B)`.
* `MvPolynomial.IsHomogeneous.exists_eq_mul_add_mul_of_isRelPrime`: a form `H` of degree `t` is
  `C A + D B` with `C`, `D` forms of degrees `t - m`, `t - n`.
* `MvPolynomial.IsHomogeneous.exists_mul_eq_mul_of_not_isRelPrime`: two nonzero forms with a
  common factor of positive degree satisfy `A B' = B A'` with forms `A'`, `B'` of degrees
  `m - 1`, `n - 1` and `B' ≠ 0`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.3, p. 39
-/

public section

open TauCeti.GradedAlgebra

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k]

/-- The number of monomials of degree `d - j` in two variables, read as `0` when `d < j`, is
`d - j + 1` whenever `j ≤ d + 1`. -/
private theorem ite_multichoose_two {d j : ℕ} (hj : j ≤ d + 1) :
    (if j ≤ d then ((2 : ℕ).multichoose (d - j) : ℤ) else 0) = (d : ℤ) - j + 1 := by
  split_ifs with h
  · rw [Nat.multichoose_two]
    push_cast [h]
    ring
  · rw [show j = d + 1 by omega]
    push_cast
    ring

/-- The dimension count for a nonzero first form. -/
private theorem finrank_quotientPiece_span_pair_fin_two_of_ne_zero
    {A B : MvPolynomial (Fin 2) k} {m n t : ℕ}
    (hA : A.IsHomogeneous m) (hB : B.IsHomogeneous n) (hA₀ : A ≠ 0) (hAB : IsRelPrime A B)
    (ht : m + n ≤ t + 1) :
    Module.finrank k (quotientPiece (homogeneousSubmodule (Fin 2) k) (Ideal.span {A, B}) t) =
      0 := by
  have h := mk_finrank_quotientPiece_of_isWeaklyRegular (S := ℤ) (homogeneousSubmodule (Fin 2) k)
    [(A, m), (B, n)] (by simpa [mem_homogeneousSubmodule] using ⟨hA, hB⟩)
    (by simpa using hAB.isWeaklyRegular hA₀)
  have hspan : Ideal.ofList ([(A, m), (B, n)].map Prod.fst) = Ideal.span {A, B} := by
    simp only [List.map_cons, List.map_nil, Ideal.ofList, List.mem_cons, List.not_mem_nil,
      or_false]
    rfl
  rw [hspan] at h
  have hc := congrArg (PowerSeries.coeff t) h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    PowerSeries.coeff_mk] at hc
  have hexp : ∀ p : PowerSeries ℤ, p * ((1 - PowerSeries.X ^ m) * (1 - PowerSeries.X ^ n)) =
      p - p * PowerSeries.X ^ m - p * PowerSeries.X ^ n + p * PowerSeries.X ^ (m + n) := by
    intro p
    ring
  rw [hexp] at hc
  simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
    TauCeti.finrank_homogeneousSubmodule_eq_multichoose, Fintype.card_fin] at hc
  have h₀ := ite_multichoose_two (d := t) (j := 0) (by omega)
  have h₁ := ite_multichoose_two (d := t) (j := m) (by omega)
  have h₂ := ite_multichoose_two (d := t) (j := n) (by omega)
  have h₃ := ite_multichoose_two (d := t) (j := m + n) (by omega)
  simp only [zero_le, ite_true, Nat.sub_zero] at h₀
  have : (Module.finrank k (quotientPiece (homogeneousSubmodule (Fin 2) k)
      (Ideal.span {A, B}) t) : ℤ) = 0 := by
    push_cast at h₀ h₃
    linear_combination hc + h₀ - h₁ - h₂ + h₃
  exact_mod_cast this

/-- If `A` and `B` are relatively prime forms of degrees `m` and `n` in `k[X, Y]`, the degree-`t`
piece of `k[X, Y]/(A, B)` is zero for every `t ≥ m + n - 1`. -/
theorem finrank_quotientPiece_span_pair_fin_two {A B : MvPolynomial (Fin 2) k} {m n t : ℕ}
    (hA : A.IsHomogeneous m) (hB : B.IsHomogeneous n) (hAB : IsRelPrime A B)
    (ht : m + n ≤ t + 1) :
    Module.finrank k (quotientPiece (homogeneousSubmodule (Fin 2) k) (Ideal.span {A, B}) t) =
      0 := by
  rcases eq_or_ne A 0 with rfl | hA₀
  · have hB₀ : B ≠ 0 := by
      rintro rfl
      exact not_isUnit_zero (isRelPrime_zero_left.mp hAB)
    rw [Set.pair_comm]
    exact finrank_quotientPiece_span_pair_fin_two_of_ne_zero hB hA hB₀ hAB.symm (by omega)
  · exact finrank_quotientPiece_span_pair_fin_two_of_ne_zero hA hB hA₀ hAB ht

/-- If `A` and `B` are relatively prime forms of degrees `m` and `n` in `k[X, Y]`, every form of
degree `t ≥ m + n - 1` lies in the ideal `(A, B)`. -/
theorem homogeneousSubmodule_le_span_pair_fin_two {A B : MvPolynomial (Fin 2) k} {m n t : ℕ}
    (hA : A.IsHomogeneous m) (hB : B.IsHomogeneous n) (hAB : IsRelPrime A B)
    (ht : m + n ≤ t + 1) :
    homogeneousSubmodule (Fin 2) k t ≤ (Ideal.span {A, B}).restrictScalars k := by
  have h := finrank_quotientPiece_span_pair_fin_two hA hB hAB ht
  rw [Submodule.finrank_eq_zero, quotientPiece_eq_bot_iff] at h
  exact h

/-- **Forms of degree at least `m + n - 1` lie in the ideal of two relatively prime binary
forms.** If `A` and `B` are relatively prime forms of degrees `m` and `n` in `k[X, Y]`, every form
`H` of degree `t ≥ m + n - 1` is `C A + D B` with `C`, `D` forms of degrees `t - m` and
`t - n`. -/
theorem IsHomogeneous.exists_eq_mul_add_mul_of_isRelPrime {A B H : MvPolynomial (Fin 2) k}
    {m n t : ℕ} (hA : A.IsHomogeneous m) (hB : B.IsHomogeneous n) (hAB : IsRelPrime A B)
    (hH : H.IsHomogeneous t) (ht : m + n ≤ t + 1) :
    ∃ C D : MvPolynomial (Fin 2) k, C.IsHomogeneous (t - m) ∧ D.IsHomogeneous (t - n) ∧
      H = C * A + D * B := by
  have hmem : H ∈ Ideal.span {A, B} :=
    homogeneousSubmodule_le_span_pair_fin_two hA hB hAB ht ((mem_homogeneousSubmodule _ _).mpr hH)
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hmem
  refine ⟨if m ≤ t then homogeneousComponent (t - m) a else 0,
    if n ≤ t then homogeneousComponent (t - n) b else 0, ?_, ?_, ?_⟩
  · split_ifs
    exacts [homogeneousComponent_isHomogeneous _ _, isHomogeneous_zero _ _ _]
  · split_ifs
    exacts [homogeneousComponent_isHomogeneous _ _, isHomogeneous_zero _ _ _]
  · have h := congrArg (homogeneousComponent t) hab
    rw [map_add, hA.homogeneousComponent_mul_right, hB.homogeneousComponent_mul_right,
      homogeneousComponent_eq_self hH] at h
    rw [← h]
    split_ifs <;> simp

/-- **Two forms with a common factor.** If `A` and `B` are nonzero forms of degrees `m` and `n`
that are not relatively prime, there are forms `A'`, `B'` of degrees `m - 1` and `n - 1`, with
`B' ≠ 0`, such that `A B' = B A'`. -/
theorem IsHomogeneous.exists_mul_eq_mul_of_not_isRelPrime {σ : Type*} {A B : MvPolynomial σ k}
    {m n : ℕ} (hA : A.IsHomogeneous m) (hB : B.IsHomogeneous n) (hA₀ : A ≠ 0) (hB₀ : B ≠ 0)
    (hAB : ¬IsRelPrime A B) :
    ∃ A' B' : MvPolynomial σ k, A'.IsHomogeneous (m - 1) ∧ B'.IsHomogeneous (n - 1) ∧
      B' ≠ 0 ∧ A * B' = B * A' := by
  simp only [IsRelPrime, not_forall] at hAB
  obtain ⟨e, ⟨A', rfl⟩, ⟨B', rfl⟩, he⟩ := hAB
  have he₀ : e ≠ 0 := left_ne_zero_of_mul hA₀
  have hA'₀ : A' ≠ 0 := right_ne_zero_of_mul hA₀
  have hB'₀ : B' ≠ 0 := right_ne_zero_of_mul hB₀
  -- The common factor is not a constant, so it has a monomial with some variable `i`.
  have hpos : 0 < e.totalDegree := by
    refine Nat.pos_of_ne_zero fun h ↦ he ?_
    rw [totalDegree_eq_zero_iff_eq_C] at h
    rw [h]
    exact isUnit_iff_ne_zero.mpr (by rwa [h, ne_eq, C_eq_zero] at he₀) |>.map C
  obtain ⟨s, -, hsd⟩ := Finset.exists_mem_eq_sup e.support (support_nonempty.mpr he₀)
    fun s ↦ s.sum fun _ e ↦ e
  obtain ⟨i, -⟩ : ∃ i, s i ≠ 0 := by
    by_contra! h
    have : s = 0 := Finsupp.ext h
    rw [show e.totalDegree = _ from hsd, this] at hpos
    simp at hpos
  have hmd := hA.totalDegree hA₀
  have hnd := hB.totalDegree hB₀
  rw [totalDegree_mul_of_isDomain he₀ hA'₀] at hmd
  rw [totalDegree_mul_of_isDomain he₀ hB'₀] at hnd
  set L : MvPolynomial σ k := X i ^ (e.totalDegree - 1)
  have hL : L.IsHomogeneous (e.totalDegree - 1) := by
    simpa using (isHomogeneous_X k i).pow (e.totalDegree - 1)
  refine ⟨A' * L, B' * L, ?_, ?_, mul_ne_zero hB'₀ (pow_ne_zero _ (X_ne_zero i)), by ring⟩
  · convert (IsHomogeneous.of_mul_right (hmd ▸ hA) he₀).mul hL using 1
    omega
  · convert (IsHomogeneous.of_mul_right (hnd ▸ hB) he₀).mul hL using 1
    omega

end MvPolynomial

end
