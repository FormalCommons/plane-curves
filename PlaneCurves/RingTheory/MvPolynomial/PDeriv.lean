/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.FieldTheory.Perfect
public import TauCeti.RingTheory.MvPolynomial.Cartier
public import TauCeti.RingTheory.MvPolynomial.Expand

/-!
# Polynomials whose partial derivatives vanish

A polynomial all of whose partial derivatives vanish is a constant in characteristic zero, and
the expansion `g(X ^ p)` of a polynomial `g` in characteristic `p`; over a perfect ring of
characteristic `p` it is a `p`-th power. Hence over a perfect field an irreducible polynomial has a
nonzero partial derivative, which it does not divide.

## Main results

* `MvPolynomial.coeff_eq_zero_of_pderiv_eq_zero`: if `∂f/∂Xᵢ = 0`, the coefficients of `f` at the
  exponents `m` with `(m i : R) ≠ 0` vanish.
* `MvPolynomial.eq_C_of_forall_pderiv_eq_zero`: in characteristic zero, a polynomial with all
  partial derivatives zero is constant.
* `MvPolynomial.exists_expand_eq_of_forall_pderiv_eq_zero`,
  `MvPolynomial.exists_pow_eq_of_forall_pderiv_eq_zero`: in characteristic `p`, it is an
  expansion `g(X ^ p)`, and a `p`-th power over a perfect ring.
* `MvPolynomial.totalDegree_pderiv_lt`, `MvPolynomial.pderiv_eq_zero_of_dvd`: a nonzero partial
  derivative has smaller total degree, so a polynomial divides its partial derivative only when
  that derivative is zero.
* `Irreducible.exists_pderiv_ne_zero`: over a perfect field, an irreducible polynomial has a
  nonzero partial derivative.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.1, Problem 3.10
-/

public section

namespace MvPolynomial

open Finsupp

variable {σ R : Type*}

section CommSemiring

variable [CommSemiring R] {f : MvPolynomial σ R}

/-- If `∂f/∂Xᵢ = 0`, then `f` has no monomial `X ^ m` with `(m i : R) ≠ 0`. -/
theorem coeff_eq_zero_of_pderiv_eq_zero [NoZeroDivisors R] {i : σ} (h : pderiv i f = 0)
    {m : σ →₀ ℕ} (hm : (m i : R) ≠ 0) : f.coeff m = 0 := by
  classical
  have hmi : m i ≠ 0 := by rintro h0; simp [h0] at hm
  have hm' : m - single i 1 + single i 1 = m := by
    ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [Ne.symm hj]
  have hc := coeff_pderiv (i := i) f (m - single i 1)
  have hcast : (((m - single i 1 : σ →₀ ℕ) i : ℕ) : R) + 1 = m i := by
    rw [tsub_apply, single_eq_same]
    norm_cast
    congr 1
    omega
  rw [h, hm', hcast] at hc
  simp only [AddMonoidAlgebra.coeff_zero] at hc
  exact (mul_eq_zero.1 hc.symm).resolve_right hm

/-- In characteristic zero, a polynomial all of whose partial derivatives vanish is constant. -/
theorem eq_C_of_forall_pderiv_eq_zero [NoZeroDivisors R] [CharZero R]
    (h : ∀ i, pderiv i f = 0) : f = C (f.coeff 0) := by
  classical
  ext m
  rw [coeff_C]
  split_ifs with hm
  · rw [hm]
  · obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra! h0
      exact hm (Finsupp.ext h0).symm
    exact coeff_eq_zero_of_pderiv_eq_zero (h i) (by exact_mod_cast hi)

/-- In characteristic `p > 0`, a polynomial all of whose partial derivatives vanish is the
expansion `g(X ^ p)` of a polynomial `g`. -/
theorem exists_expand_eq_of_forall_pderiv_eq_zero [NoZeroDivisors R] (p : ℕ) [NeZero p]
    [CharP R p] (h : ∀ i, pderiv i f = 0) : ∃ g, expand p g = f := by
  refine ⟨cartier R p 0 f, ?_⟩
  ext m
  by_cases hm : ∀ i, p ∣ m i
  · have hm' : p • m.mapRange (· / p) (Nat.zero_div p) = m := by
      ext i
      simp [Nat.mul_div_cancel' (hm i)]
    rw [← hm', coeff_expand_smul p (NeZero.ne p), coeff_cartier, add_zero]
  · push Not at hm
    obtain ⟨i, hi⟩ := hm
    rw [coeff_expand_of_not_dvd (h := hi), coeff_eq_zero_of_pderiv_eq_zero (h i)
      (by rwa [Ne, CharP.cast_eq_zero_iff R p])]

/-- Over a perfect ring of characteristic `p > 0`, a polynomial all of whose partial derivatives
vanish is a `p`-th power. -/
theorem exists_pow_eq_of_forall_pderiv_eq_zero [NoZeroDivisors R] (p : ℕ) [Fact p.Prime]
    [CharP R p] [PerfectRing R p] (h : ∀ i, pderiv i f = 0) : ∃ g, g ^ p = f := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨g, rfl⟩ := exists_expand_eq_of_forall_pderiv_eq_zero p h
  exact ⟨_, (expand_eq_map_frobeniusEquiv_symm_pow p g).symm⟩

/-- A nonzero partial derivative has smaller total degree than the polynomial. -/
theorem totalDegree_pderiv_lt {i : σ} (h : pderiv i f ≠ 0) :
    (pderiv i f).totalDegree < f.totalDegree := by
  classical
  have key : ∀ m ∈ (pderiv i f).support, m.degree < f.totalDegree := by
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    have hle : (m + single i 1).degree ≤ f.totalDegree :=
      le_totalDegree (mem_support_iff.2 (left_ne_zero_of_mul hm))
    rw [map_add, degree_single] at hle
    omega
  obtain ⟨m, hm⟩ := support_nonempty.2 h
  exact (Finset.sup_lt_iff ((Nat.zero_le _).trans_lt (key m hm))).2 key

end CommSemiring

section CommRing

variable [CommRing R] [IsDomain R] {f : MvPolynomial σ R}

/-- A polynomial over a domain divides one of its partial derivatives only when that derivative
is zero. -/
theorem pderiv_eq_zero_of_dvd {i : σ} (h : f ∣ pderiv i f) : pderiv i f = 0 := by
  by_contra hne
  exact (totalDegree_le_of_dvd_of_isDomain h hne).not_gt (totalDegree_pderiv_lt hne)

end CommRing

end MvPolynomial

open MvPolynomial in
/-- Over a perfect field, an irreducible polynomial has a nonzero partial derivative. This fails
over imperfect fields: `X ^ p - t Y ^ p` over `𝔽_p(t)` is irreducible, with both partial
derivatives zero. -/
theorem Irreducible.exists_pderiv_ne_zero {σ k : Type*} [Field k] [PerfectField k]
    {f : MvPolynomial σ k} (hf : Irreducible f) : ∃ i, pderiv i f ≠ 0 := by
  by_contra! h
  obtain ⟨p, hchar⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨g, rfl⟩ := exists_pow_eq_of_forall_pderiv_eq_zero p h
    exact not_irreducible_pow hp.ne_one hf
  · have : CharZero k := CharP.charP_to_charZero k
    rw [eq_C_of_forall_pderiv_eq_zero h] at hf
    by_cases hc : f.coeff 0 = 0
    · rw [hc, map_zero] at hf
      exact not_irreducible_zero hf
    · exact hf.not_isUnit ((Ne.isUnit hc).map C)

end
