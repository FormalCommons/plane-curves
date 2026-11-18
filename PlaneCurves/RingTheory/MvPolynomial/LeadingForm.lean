/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.RingTheory.MvPolynomial.OrderAt
public import PlaneCurves.RingTheory.MvPolynomial.LinearSubst

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

* `MvPolynomial.leadingFormAt_eq_zero_iff`: the leading form vanishes only for `p = 0`.
* `MvPolynomial.leadingFormAt_of_eval_ne_zero`: away from the zeros of `p` the leading form
  is the constant `p(a)`; `MvPolynomial.leadingFormAt_eq_sum_pderiv`: at a point of order one it
  is the differential `∑ᵢ (∂p/∂Xᵢ)(a) Xᵢ`.
* `MvPolynomial.leadingFormAt_mul`, `MvPolynomial.leadingFormAt_pow`,
  `MvPolynomial.leadingFormAt_prod`: over a domain, the leading form is multiplicative.
* `MvPolynomial.leadingFormAt_aeval`, `MvPolynomial.orderAt_aeval_eq`: if the leading form
  of `p` at `g(b)`, evaluated at the linear parts of `g` at `b`, is nonzero, then it is the
  leading form of `p(g)` at `b`, and the orders agree.
* `MvPolynomial.orderAt_aeval_eq_of_isUnit_det`,
  `MvPolynomial.leadingFormAt_aeval_of_isUnit_det`: Problem 3.8 of Fulton — the order is
  unchanged by a polynomial map with invertible Jacobian matrix at the point.
* `MvPolynomial.orderAt_linearSubst`, `MvPolynomial.leadingFormAt_linearSubst`: invertible
  linear changes of coordinates.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.1
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

/-- The leading form of a Taylor shift is the leading form at the translated point. -/
@[simp]
theorem leadingFormAt_taylor (a b : σ → R) (p : MvPolynomial σ R) :
    (taylor a p).leadingFormAt b = p.leadingFormAt (b + a) := by
  rw [leadingFormAt_def, leadingFormAt_def, orderAt_taylor, taylor_taylor]

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

end CommSemiring

section CommRing

variable [CommRing R]

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
