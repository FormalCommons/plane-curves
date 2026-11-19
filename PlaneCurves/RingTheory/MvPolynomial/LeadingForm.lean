/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import TauCeti.RingTheory.MvPolynomial.OrderAt
public import PlaneCurves.RingTheory.MvPolynomial.LinearSubst
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.LinearCombination

/-!
# The leading form of a polynomial at a point

For a polynomial `p` and a point `a`, write the Taylor shift `p(X + a)` as a sum
`p_m + p_{m+1} + ⋯` of forms, `p_i` of degree `i`, with `m` the order of `p` at `a`
(Tau Ceti's `MvPolynomial.orderAt`). The *leading form* of `p` at `a` is `p_m`, the
lowest-degree nonzero form; it is `0` for `p = 0`. For a plane curve it is the product of the
tangent lines at the point.

## Main definitions

* `MvPolynomial.leadingFormAt p a`: the leading form of `p` at `a`.

## Main results

* `MvPolynomial.leadingFormAt_eq_zero_iff`: the leading form vanishes only for `p = 0`;
  `MvPolynomial.isUnit_leadingFormAt_iff`: over a domain it is a unit exactly when `p(a)` is.
* `MvPolynomial.le_orderAt_iff_homogeneousComponent`: the order is at least `n` exactly when the
  Taylor shift has no homogeneous components of degree below `n`.
* `MvPolynomial.leadingFormAt_of_eval_ne_zero`: away from the zeros of `p` the leading form
  is the constant `p(a)`; `MvPolynomial.leadingFormAt_eq_sum_pderiv`: at a point of order one it
  is the differential `∑ᵢ (∂p/∂Xᵢ)(a) Xᵢ`; `MvPolynomial.orderAt_eq_one_iff`: the order is one
  exactly at the zeros of `p` where some partial derivative does not vanish;
  `MvPolynomial.two_le_orderAt_iff`: it is at least two exactly where `p` and all its partial
  derivatives vanish.
* `MvPolynomial.leadingFormAt_mul`, `MvPolynomial.leadingFormAt_pow`,
  `MvPolynomial.leadingFormAt_prod`: over a domain, the leading form is multiplicative.
* `MvPolynomial.orderAt_mul_eq_one_iff`: over a domain, a product has order one exactly when
  one factor has order one and the other order zero.
* `MvPolynomial.leadingFormAt_rename`: leading forms commute with injective renamings.
* `MvPolynomial.orderAt_sub_one_le_orderAt_pderiv`: a partial derivative lowers the order by
  at most one, in every characteristic (Problem 5.6 of Fulton, in affine space).
* `MvPolynomial.orderAt_add_of_ne`, `MvPolynomial.orderAt_add_of_lt`,
  `MvPolynomial.orderAt_add_of_gt`: if `p` and `q` have different orders at `a`, `p + q` has
  the smaller one.
* `MvPolynomial.IsHomogeneous.orderAt_zero`: a nonzero form of degree `d` has order `d` at the
  origin.
* `MvPolynomial.IsHomogeneous.leadingFormAt_zero`: a form is its own leading form at the origin.
* `MvPolynomial.taylor_eq_leadingFormAt`: if the order at `a` is at least the total degree,
  `p(X + a)` is the leading form at `a`.
* `MvPolynomial.orderAt_taylor_sub_leadingFormAt`: `p(X + a)` minus the leading form has order
  greater than that of `p` at `a`.
* `MvPolynomial.orderAt_eq_and_leadingFormAt_eq_neg_of_orderAt_lt_orderAt_add`: if `p + q` has
  larger order than `p`, the leading forms of `p` and `q` cancel.
* `MvPolynomial.leadingFormAt_aeval`, `MvPolynomial.orderAt_aeval_eq`: if the leading form
  of `p` at `g(b)`, evaluated at the linear parts of `g` at `b`, is nonzero, then it is the
  leading form of `p(g)` at `b`, and the orders agree.
* `MvPolynomial.orderAt_aeval_eq_of_isUnit_det`,
  `MvPolynomial.leadingFormAt_aeval_of_isUnit_det`: Problem 3.8 of Fulton — the order is
  unchanged by a polynomial map with invertible Jacobian matrix at the point.
* `MvPolynomial.orderAt_linearSubst`, `MvPolynomial.leadingFormAt_linearSubst`: invertible
  linear changes of coordinates.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.1, §5.1 (Problem 5.6)
-/

public section

namespace MvPolynomial

open Matrix

variable {σ τ R : Type*}

section CommSemiring

variable [CommSemiring R] {p q : MvPolynomial σ R} {a : σ → R}

/-- The leading form of `p` at `a`: the homogeneous component of the Taylor shift `p(X + a)`
of degree the order of `p` at `a`. It is the lowest-degree nonzero form of `p(X + a)`, and `0`
when `p = 0`. -/
noncomputable def leadingFormAt (p : MvPolynomial σ R) (a : σ → R) : MvPolynomial σ R :=
  homogeneousComponent (p.orderAt a).toNat (taylor a p)

theorem leadingFormAt_def (p : MvPolynomial σ R) (a : σ → R) :
    p.leadingFormAt a = homogeneousComponent (p.orderAt a).toNat (taylor a p) :=
  (rfl)

/-- The leading form at `a` is a form of degree the order at `a`. -/
theorem isHomogeneous_leadingFormAt (p : MvPolynomial σ R) (a : σ → R) :
    (p.leadingFormAt a).IsHomogeneous (p.orderAt a).toNat :=
  homogeneousComponent_isHomogeneous _ _

@[simp]
theorem leadingFormAt_zero (a : σ → R) : (0 : MvPolynomial σ R).leadingFormAt a = 0 := by
  simp [leadingFormAt_def]

/-- If the Taylor coefficients of `p` at `a` vanish in degrees below `n` and its degree-`n`
component does not, then `p` has order `n` at `a`. -/
theorem orderAt_eq_of_homogeneousComponent_ne_zero {n : ℕ} (hn : n ≤ p.orderAt a)
    (h : homogeneousComponent n (taylor a p) ≠ 0) : p.orderAt a = n := by
  obtain ⟨d, hd⟩ := ne_zero_iff.1 h
  rw [coeff_homogeneousComponent] at hd
  split_ifs at hd with hdn
  · exact le_antisymm (hdn ▸ orderAt_le hd) hn
  · exact absurd rfl hd

/-- `p` has order at least `n` at `a` exactly when the homogeneous components of degree less
than `n` of its Taylor shift at `a` vanish. -/
theorem le_orderAt_iff_homogeneousComponent {n : ℕ} :
    n ≤ p.orderAt a ↔ ∀ i < n, homogeneousComponent i (taylor a p) = 0 := by
  rw [le_orderAt_iff]
  refine ⟨fun h i hi ↦ ?_, fun h d hd ↦ ?_⟩
  · ext d
    rw [coeff_homogeneousComponent]
    split_ifs with hd
    · exact h d (by rw [hd]; exact_mod_cast hi)
    · simp
  · simpa [coeff_homogeneousComponent] using
      congr($(h d.degree (by exact_mod_cast hd)).coeff d)

/-- The homogeneous components of the Taylor shift of `p` at `a` vanish below the order. -/
theorem homogeneousComponent_taylor_eq_zero_of_lt {i : ℕ} (hi : i < p.orderAt a) :
    homogeneousComponent i (taylor a p) = 0 :=
  le_orderAt_iff_homogeneousComponent.1 (Order.add_one_le_of_lt hi) i (Nat.lt_succ_self i)

/-- Every monomial of `p` has total degree at least the order of `p` at the origin. -/
theorem toNat_orderAt_zero_le_degree {d : σ →₀ ℕ} (hd : d ∈ p.support) :
    (p.orderAt 0).toNat ≤ d.degree :=
  ENat.toNat_le_of_le_natCast (orderAt_le (by rwa [taylor_zero, ← mem_support_iff]))

/-- If `p` vanishes at `a` to order at least its total degree, its Taylor shift `p(X + a)` is a
form: the leading form of `p` at `a`. -/
theorem taylor_eq_leadingFormAt (h : (p.totalDegree : ℕ∞) ≤ p.orderAt a) :
    taylor a p = p.leadingFormAt a := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  have hord : p.orderAt a = p.totalDegree := le_antisymm (orderAt_le_totalDegree hp a) h
  rw [leadingFormAt_def, hord, ENat.toNat_natCast]
  conv_lhs => rw [← sum_homogeneousComponent_of_totalDegree_le (totalDegree_taylor_le a p)]
  rw [Finset.sum_range_succ, Finset.sum_eq_zero fun i hi ↦
    homogeneousComponent_taylor_eq_zero_of_lt (by
      rw [hord]; exact_mod_cast Finset.mem_range.1 hi), zero_add]

/-- The leading form of `p` at `a` is zero only for `p = 0`. -/
@[simp]
theorem leadingFormAt_eq_zero_iff : p.leadingFormAt a = 0 ↔ p = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ leadingFormAt_zero a⟩
  by_contra hp
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (orderAt_eq_top_iff.not.2 hp)
  obtain ⟨⟨d, hd, hdn⟩, -⟩ := orderAt_eq_coe_iff.1 hn.symm
  rw [leadingFormAt_def, ← hn, ENat.toNat_natCast] at h
  have := coeff_homogeneousComponent (φ := taylor a p) (n := n) d
  exact hd (by simpa [h, hdn] using this.symm)

theorem leadingFormAt_ne_zero (hp : p ≠ 0) : p.leadingFormAt a ≠ 0 :=
  leadingFormAt_eq_zero_iff.not.2 hp

/-- Where `p` does not vanish, its leading form is the constant `p(a)`. -/
theorem leadingFormAt_of_eval_ne_zero (h : eval a p ≠ 0) : p.leadingFormAt a = C (eval a p) := by
  rw [leadingFormAt_def, orderAt_eq_zero_iff.2 h, ENat.toNat_zero, homogeneousComponent_zero,
    ← constantCoeff_eq, constantCoeff_taylor]

/-- The leading form of a constant is the constant. -/
@[simp]
theorem leadingFormAt_C (r : R) (a : σ → R) : (C r : MvPolynomial σ R).leadingFormAt a = C r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · rw [leadingFormAt_of_eval_ne_zero (by simpa using hr), eval_C]

@[simp]
theorem leadingFormAt_one (a : σ → R) : (1 : MvPolynomial σ R).leadingFormAt a = 1 := by
  simpa using leadingFormAt_C (1 : R) a

/-- At a point of order one, the leading form is the differential `∑ᵢ (∂p/∂Xᵢ)(a) Xᵢ`. -/
theorem leadingFormAt_eq_sum_pderiv [Fintype σ] (h : p.orderAt a = 1) :
    p.leadingFormAt a = ∑ i, eval a (pderiv i p) • X i := by
  rw [leadingFormAt_def, h, ENat.toNat_one, homogeneousComponent_one_taylor]

/-- A polynomial has order one at `a` exactly when it vanishes at `a` and some partial
derivative does not. -/
theorem orderAt_eq_one_iff [Finite σ] :
    p.orderAt a = 1 ↔ eval a p = 0 ∧ ∃ i, eval a (pderiv i p) ≠ 0 := by
  have := Fintype.ofFinite σ
  refine ⟨fun h ↦ ⟨orderAt_pos_iff.1 (by simp [h]), ?_⟩,
    fun ⟨h0, i, hi⟩ ↦ orderAt_eq_one_of_eval_pderiv_ne_zero h0 hi⟩
  by_contra! hd
  have hp : p ≠ 0 := by rintro rfl; simp at h
  apply leadingFormAt_ne_zero (a := a) hp
  simp [leadingFormAt_eq_sum_pderiv h, hd]

/-- A polynomial has order at least two at `a` exactly when it and all its partial derivatives
vanish at `a`. -/
theorem two_le_orderAt_iff [Finite σ] :
    2 ≤ p.orderAt a ↔ eval a p = 0 ∧ ∀ i, eval a (pderiv i p) = 0 := by
  have h : 2 ≤ p.orderAt a ↔ 0 < p.orderAt a ∧ p.orderAt a ≠ 1 := by
    generalize p.orderAt a = m
    cases m using ENat.recTopCoe with
    | top => simp
    | coe m =>
      norm_cast
      omega
  rw [h, orderAt_pos_iff, Ne, orderAt_eq_one_iff]
  grind

/-- The leading form of a Taylor shift is the leading form at the translated point. -/
@[simp]
theorem leadingFormAt_taylor (a b : σ → R) (p : MvPolynomial σ R) :
    (taylor a p).leadingFormAt b = p.leadingFormAt (b + a) := by
  rw [leadingFormAt_def, leadingFormAt_def, orderAt_taylor, taylor_taylor]

/-- Over a semiring without zero divisors, a product has order one at `a` exactly when one
factor has order one and the other order zero there. -/
theorem orderAt_mul_eq_one_iff [NoZeroDivisors R] :
    (p * q).orderAt a = 1 ↔
      p.orderAt a = 1 ∧ q.orderAt a = 0 ∨ p.orderAt a = 0 ∧ q.orderAt a = 1 := by
  rw [orderAt_mul]
  generalize p.orderAt a = m
  generalize q.orderAt a = n
  cases m using ENat.recTopCoe <;> cases n using ENat.recTopCoe <;> simp
  norm_cast
  omega

/-- Over a semiring without zero divisors, the leading form of a product is the product of the
leading forms. -/
theorem leadingFormAt_mul [NoZeroDivisors R] (p q : MvPolynomial σ R) (a : σ → R) :
    (p * q).leadingFormAt a = p.leadingFormAt a * q.leadingFormAt a := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (orderAt_eq_top_iff.not.2 hp : p.orderAt a ≠ ⊤)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (orderAt_eq_top_iff.not.2 hq : q.orderAt a ≠ ⊤)
  rw [leadingFormAt_def, leadingFormAt_def, leadingFormAt_def, orderAt_mul, ← hm, ← hn,
    ← Nat.cast_add, ENat.toNat_natCast, ENat.toNat_natCast, ENat.toNat_natCast, ← coe_inj, map_mul,
    coe_mul, coe_homogeneousComponent, coe_homogeneousComponent, coe_homogeneousComponent]
  simpa only [coe_mul] using MvPowerSeries.homogeneousComponent_mul_of_le_order
    (by rw [← orderAt_def, ← hm]) (by rw [← orderAt_def, ← hn])

/-- Over a semiring without zero divisors, the leading form of `c • p` is `c • ` the leading
form of `p`. -/
theorem leadingFormAt_smul [NoZeroDivisors R] (c : R) (p : MvPolynomial σ R) (a : σ → R) :
    (c • p).leadingFormAt a = c • p.leadingFormAt a := by
  rw [smul_eq_C_mul, smul_eq_C_mul, leadingFormAt_mul, leadingFormAt_C]

/-- Over a semiring without zero divisors, the leading form of `p ^ n` is the `n`-th power of
the leading form of `p`. -/
theorem leadingFormAt_pow [NoZeroDivisors R] (p : MvPolynomial σ R) (a : σ → R) (n : ℕ) :
    (p ^ n).leadingFormAt a = p.leadingFormAt a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, leadingFormAt_mul, ih, pow_succ]

/-- Over a semiring without zero divisors, the leading form of a finite product is the product
of the leading forms. -/
theorem leadingFormAt_prod [NoZeroDivisors R] {ι : Type*} (p : ι → MvPolynomial σ R)
    (s : Finset ι) (a : σ → R) :
    (∏ i ∈ s, p i).leadingFormAt a = ∏ i ∈ s, (p i).leadingFormAt a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, leadingFormAt_mul, ih]

/-- Renaming the variables along an injective map commutes with leading forms, with the point
pulled back along the renaming. -/
theorem leadingFormAt_rename {f : σ → τ} (hf : Function.Injective f) (p : MvPolynomial σ R)
    (b : τ → R) : (rename f p).leadingFormAt b = rename f (p.leadingFormAt (b ∘ f)) := by
  rw [leadingFormAt_def, leadingFormAt_def, orderAt_rename hf, taylor_rename,
    rename_homogeneousComponent]

/-- **A partial derivative lowers the order by at most one.** If `p` has order at least `n + 1`
at `a`, then `∂p/∂Xᵢ` has order at least `n` there, over every commutative semiring. -/
theorem le_orderAt_pderiv {n : ℕ∞} (h : n + 1 ≤ p.orderAt a) (i : σ) :
    n ≤ (pderiv i p).orderAt a := by
  rw [orderAt_def] at h ⊢
  rw [← pderiv_taylor, ← MvPowerSeries.pderiv_coe]
  exact MvPowerSeries.le_order_pderiv h i

/-- `ord_a(∂p/∂Xᵢ) ≥ ord_a(p) - 1`, over every commutative semiring (with `ord_a(0) = ⊤`). -/
theorem orderAt_sub_one_le_orderAt_pderiv (p : MvPolynomial σ R) (a : σ → R) (i : σ) :
    p.orderAt a - 1 ≤ (pderiv i p).orderAt a := by
  rcases eq_or_ne (p.orderAt a) 0 with h | h
  · simp [h]
  exact le_orderAt_pderiv (by rw [tsub_add_cancel_of_le (Order.one_le_iff_ne_zero.2 h)]) i

/-- If `p` and `q` have different orders at `a`, the order of `p + q` there is the smaller
one. -/
theorem orderAt_add_of_ne (h : p.orderAt a ≠ q.orderAt a) :
    (p + q).orderAt a = min (p.orderAt a) (q.orderAt a) := by
  rw [orderAt_def, orderAt_def] at h
  simpa [orderAt_def] using MvPowerSeries.order_add_of_order_ne h

/-- If `p` has smaller order at `a` than `q`, then `p + q` has the order of `p` there. -/
theorem orderAt_add_of_lt (h : p.orderAt a < q.orderAt a) :
    (p + q).orderAt a = p.orderAt a := by
  rw [orderAt_add_of_ne h.ne, min_eq_left h.le]

/-- If `q` has smaller order at `a` than `p`, then `p + q` has the order of `q` there. -/
theorem orderAt_add_of_gt (h : q.orderAt a < p.orderAt a) :
    (p + q).orderAt a = q.orderAt a := by
  rw [orderAt_add_of_ne h.ne', min_eq_right h.le]

/-- A form of degree `d` has order at least `d` at the origin. -/
theorem IsHomogeneous.natCast_le_orderAt_zero {d : ℕ} (hp : p.IsHomogeneous d) :
    (d : ℕ∞) ≤ p.orderAt 0 := by
  rw [le_orderAt_iff]
  intro e he
  rw [taylor_zero]
  exact hp.coeff_eq_zero (by exact_mod_cast he.ne)

/-- A nonzero form of degree `d` has order `d` at the origin. -/
theorem IsHomogeneous.orderAt_zero {d : ℕ} (hp : p.IsHomogeneous d) (hp₀ : p ≠ 0) :
    p.orderAt 0 = d := by
  refine le_antisymm ?_ hp.natCast_le_orderAt_zero
  obtain ⟨e, he⟩ := ne_zero_iff.1 hp₀
  have hed : e.degree = d := by
    by_contra h
    exact he (hp.coeff_eq_zero h)
  rw [← hed]
  exact orderAt_le (by rwa [taylor_zero])

/-- A form is its own leading form at the origin. -/
theorem IsHomogeneous.leadingFormAt_zero {d : ℕ} (hp : p.IsHomogeneous d) :
    p.leadingFormAt 0 = p := by
  rcases eq_or_ne p 0 with rfl | hp₀
  · exact MvPolynomial.leadingFormAt_zero 0
  rw [leadingFormAt_def, hp.orderAt_zero hp₀, ENat.toNat_natCast, taylor_zero]
  exact homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hp) |>.trans (ite_eq_left rfl)

end CommSemiring

section CommRing

variable [CommRing R]

/-- Removing the leading form from the Taylor shift `p(X + a)` leaves only terms of degree
greater than the order of `p` at `a`. -/
theorem orderAt_taylor_sub_leadingFormAt (p : MvPolynomial σ R) (a : σ → R) :
    ((p.orderAt a).toNat + 1 : ℕ∞) ≤ (taylor a p - p.leadingFormAt a).orderAt 0 := by
  rw [le_orderAt_iff]
  intro d hd
  rw [taylor_zero, coeff_sub, leadingFormAt_def, coeff_homogeneousComponent]
  split_ifs with h
  · exact sub_self _
  · rw [sub_zero]
    have hd' : d.degree < (p.orderAt a).toNat := by
      have : d.degree < (p.orderAt a).toNat + 1 := by exact_mod_cast hd
      omega
    exact le_orderAt_iff.1 le_rfl d
      ((Nat.cast_lt.2 hd').trans_le (ENat.natCast_toNat_le_self _))

/-- If `p + q` has larger order at `a` than `p`, the leading forms of `p` and `q` cancel: `q`
has the order of `p` at `a`, and the negative of its leading form. -/
theorem orderAt_eq_and_leadingFormAt_eq_neg_of_orderAt_lt_orderAt_add
    {p q : MvPolynomial σ R} {a : σ → R} (h : p.orderAt a < (p + q).orderAt a) :
    q.orderAt a = p.orderAt a ∧ q.leadingFormAt a = -p.leadingFormAt a := by
  have hp : p.orderAt a ≠ ⊤ := h.ne_top
  have hp₀ : p ≠ 0 := orderAt_eq_top_iff.not.1 hp
  have hle : p.orderAt a ≤ q.orderAt a := by
    have := min_orderAt_le_orderAt_add (p + q) (-p) a
    rwa [orderAt_neg, show p + q + -p = q by ring, min_eq_right h.le] at this
  have hc : homogeneousComponent (p.orderAt a).toNat (taylor a q) = -p.leadingFormAt a := by
    have := homogeneousComponent_taylor_eq_zero_of_lt (p := p + q)
      (i := (p.orderAt a).toNat) (by rwa [ENat.natCast_toNat hp])
    rw [map_add, map_add] at this
    rw [leadingFormAt_def]
    linear_combination this
  have hq : q.orderAt a = p.orderAt a := by
    rw [← ENat.natCast_toNat hp]
    exact orderAt_eq_of_homogeneousComponent_ne_zero (by rwa [ENat.natCast_toNat hp])
      (by rw [hc, neg_ne_zero]; exact leadingFormAt_ne_zero hp₀)
  refine ⟨hq, ?_⟩
  rw [leadingFormAt_def, hq, hc]

/-- Over a domain, the leading form of `p` at `a` is a unit exactly when `p(a)` is: a unit is a
form of degree zero. -/
theorem isUnit_leadingFormAt_iff [IsDomain R] {p : MvPolynomial σ R}
    {a : σ → R} : IsUnit (p.leadingFormAt a) ↔ IsUnit (eval a p) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hp : p ≠ 0 := by rintro rfl; simp at h
    have hd := (isHomogeneous_leadingFormAt p a).totalDegree (leadingFormAt_ne_zero hp)
    rw [(isUnit_iff_totalDegree_of_isReduced.1 h).2] at hd
    have h0 : p.orderAt a = 0 := by
      rw [← ENat.natCast_toNat (orderAt_eq_top_iff.not.2 hp), ← hd, Nat.cast_zero]
    rw [leadingFormAt_of_eval_ne_zero (orderAt_eq_zero_iff.1 h0)] at h
    simpa using h.map (constantCoeff (σ := σ) (R := R))
  · rw [leadingFormAt_of_eval_ne_zero h.ne_zero]
    exact h.map C

/-- The degree-`m` component of the Taylor shift of `p(g)` at `b`, for `m` the order of `p` at
the image point `a = g(b)`, is the leading form of `p` at `a` evaluated at the linear parts of
the `g i` at `b`. -/
theorem homogeneousComponent_taylor_aeval (g : σ → MvPolynomial τ R) (b : τ → R)
    (p : MvPolynomial σ R) :
    homogeneousComponent (p.orderAt fun i ↦ eval b (g i)).toNat (taylor b (aeval g p)) =
      aeval (fun i ↦ homogeneousComponent 1 (taylor b (g i)))
        (p.leadingFormAt fun i ↦ eval b (g i)) := by
  rw [taylor_aeval, homogeneousComponent_aeval_of_le_order
    (q := taylor (fun i ↦ eval b (g i)) p)
    (n := (p.orderAt fun i ↦ eval b (g i)).toNat)
    (by rw [← orderAt_def]; exact ENat.natCast_toNat_le_self _) fun i ↦ by simp,
    leadingFormAt_def]
  congr 2
  ext i : 1
  rw [map_sub, sub_eq_self]
  exact homogeneousComponent_eq_zero _ _ (by simp)

variable {g : σ → MvPolynomial τ R} {b : τ → R} {p : MvPolynomial σ R}

/-- If the leading form of `p` at `a = g(b)`, evaluated at the linear parts of the `g i` at
`b`, is nonzero, then `p(g)` has the same order at `b` as `p` at `a`. -/
theorem orderAt_aeval_eq
    (h : aeval (fun i ↦ homogeneousComponent 1 (taylor b (g i)))
      (p.leadingFormAt fun i ↦ eval b (g i)) ≠ 0) :
    (aeval g p).orderAt b = p.orderAt fun i ↦ eval b (g i) := by
  have hp : p ≠ 0 := by rintro rfl; simp at h
  have hfin : p.orderAt (fun i ↦ eval b (g i)) ≠ ⊤ := orderAt_eq_top_iff.not.2 hp
  rw [← ENat.natCast_toNat hfin]
  refine orderAt_eq_of_homogeneousComponent_ne_zero ?_
    (by rwa [homogeneousComponent_taylor_aeval])
  rw [ENat.natCast_toNat hfin]
  exact orderAt_le_orderAt_aeval g b p

/-- If the leading form of `p` at `a = g(b)`, evaluated at the linear parts of the `g i` at
`b`, is nonzero, then it is the leading form of `p(g)` at `b`. -/
theorem leadingFormAt_aeval
    (h : aeval (fun i ↦ homogeneousComponent 1 (taylor b (g i)))
      (p.leadingFormAt fun i ↦ eval b (g i)) ≠ 0) :
    (aeval g p).leadingFormAt b =
      aeval (fun i ↦ homogeneousComponent 1 (taylor b (g i)))
        (p.leadingFormAt fun i ↦ eval b (g i)) := by
  rw [leadingFormAt_def, orderAt_aeval_eq h, homogeneousComponent_taylor_aeval]

section Square

variable [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
/-- The linear parts at `b` of a polynomial map `g` are the linear change of variables along its
Jacobian matrix `(∂gᵢ/∂Xⱼ)(b)` at `b`. -/
theorem aeval_homogeneousComponent_one_taylor (g : σ → MvPolynomial σ R) (b : σ → R) :
    aeval (fun i ↦ homogeneousComponent 1 (taylor b (g i))) =
      linearSubst (Matrix.of fun i j ↦ eval b (pderiv j (g i))) := by
  rw [linearSubst_eq_aeval]
  congr 1
  ext i : 1
  simp [homogeneousComponent_one_taylor, smul_eq_C_mul]

variable {g : σ → MvPolynomial σ R} {b : σ → R} {p : MvPolynomial σ R}

/-- **Problem 3.8 of Fulton.** A polynomial map `g` whose Jacobian matrix at `b` is invertible
does not change the order: `p(g)` has the same order at `b` as `p` at `g(b)`. -/
theorem orderAt_aeval_eq_of_isUnit_det (hp : p ≠ 0)
    (hg : IsUnit (Matrix.of fun i j ↦ eval b (pderiv j (g i))).det) :
    (aeval g p).orderAt b = p.orderAt fun i ↦ eval b (g i) := by
  refine orderAt_aeval_eq ?_
  rw [aeval_homogeneousComponent_one_taylor, Ne, ← map_zero (linearSubst _),
    (linearSubst_injective hg).eq_iff]
  exact leadingFormAt_ne_zero hp

/-- Under a polynomial map `g` whose Jacobian matrix `J` at `b` is invertible, the leading form
of `p(g)` at `b` is the leading form of `p` at `g(b)` after the linear change of variables
along `J`. -/
theorem leadingFormAt_aeval_of_isUnit_det
    (hg : IsUnit (Matrix.of fun i j ↦ eval b (pderiv j (g i))).det) :
    (aeval g p).leadingFormAt b =
      linearSubst (Matrix.of fun i j ↦ eval b (pderiv j (g i)))
        (p.leadingFormAt fun i ↦ eval b (g i)) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rw [leadingFormAt_def, orderAt_aeval_eq_of_isUnit_det hp hg, homogeneousComponent_taylor_aeval,
    aeval_homogeneousComponent_one_taylor]

omit [DecidableEq σ] in
/-- The Jacobian matrix of the linear map `M` is `M`. -/
private theorem jacobian_linearSubst (M : Matrix σ σ R) (b : σ → R) :
    (Matrix.of fun i j ↦ eval b (pderiv j (linearSubst M (X i)))) = M := by
  classical
  ext i j
  simp [pderiv_X, Pi.single_apply]

omit [DecidableEq σ] in
private theorem eval_linearSubst_X (M : Matrix σ σ R) (b : σ → R) :
    (fun i ↦ eval b (linearSubst M (X i))) = M *ᵥ b := by
  ext i
  simp [Matrix.mulVec, dotProduct]

omit [DecidableEq σ] in
private theorem linearSubst_eq_aeval_X (M : Matrix σ σ R) :
    linearSubst M = aeval fun i ↦ linearSubst M (X i) := by
  ext i : 1
  simp

/-- An invertible linear change of variables preserves the order: `p(M X)` has order at `b`
the order of `p` at `M b`. -/
theorem orderAt_linearSubst {M : Matrix σ σ R} (hM : IsUnit M.det) (p : MvPolynomial σ R)
    (b : σ → R) : (linearSubst M p).orderAt b = p.orderAt (M *ᵥ b) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  conv_lhs => rw [linearSubst_eq_aeval_X]
  rw [orderAt_aeval_eq_of_isUnit_det hp (by rwa [jacobian_linearSubst]), eval_linearSubst_X]

/-- Under an invertible linear change of variables, the leading form of `p(M X)` at `b` is the
leading form of `p` at `M b`, with `M` substituted. -/
theorem leadingFormAt_linearSubst {M : Matrix σ σ R} (hM : IsUnit M.det) (p : MvPolynomial σ R)
    (b : σ → R) :
    (linearSubst M p).leadingFormAt b = linearSubst M (p.leadingFormAt (M *ᵥ b)) := by
  conv_lhs => rw [linearSubst_eq_aeval_X]
  rw [leadingFormAt_aeval_of_isUnit_det (by rwa [jacobian_linearSubst]), jacobian_linearSubst,
    eval_linearSubst_X]

end Square

end CommRing

end MvPolynomial

end
