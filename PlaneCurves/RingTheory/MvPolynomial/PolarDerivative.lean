/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import PlaneCurves.RingTheory.MvPolynomial.LeadingForm
public import TauCeti.RingTheory.MvPolynomial.DirectionalOrder

/-!
# The polar derivative of a polynomial

For `v : σ → R`, the *polar derivative* of `F` in the direction `v` is
`D_v F = ∑ᵢ vᵢ ∂F/∂Xᵢ`, the derivative of `t ↦ F(X + t v)` at `t = 0`. It is linear in `v` and
in `F`, a derivation, it lowers the degree of a form by one, and it commutes with Taylor shifts
and, after transforming `v`, with linear changes of coordinates.

If `F` is a form of degree `n` and `G = F(X + v)` is its Taylor shift at `v`, Euler's identity
gives `∑ᵢ Xᵢ ∂G/∂Xᵢ + D_v G = n G`, so the degree-`j` Taylor component of `D_v F` at `v` is
`(n - j)` times that of `F`. Hence, when `F` has order `r` at `v` and `n - r` is nonzero in
`R`, `D_v F` also has order `r` at `v`, with leading form `(n - r)` times that of `F`; in
particular `D_v F ≠ 0`. In coordinates with `v = (0, 1, 0)` this is the remark in Fulton's
Problem 5.26 that the `Y^{n-r-1}` coefficient of `F_Y` is `(n - r) A_r`.

## Main definitions

* `MvPolynomial.polarDerivative v F`: `∑ᵢ vᵢ • ∂F/∂Xᵢ`.

## Main results

* `MvPolynomial.IsHomogeneous.polarDerivative`: `D_v` maps forms of degree `n` to forms of
  degree `n - 1`.
* `MvPolynomial.IsHomogeneous.eval_polarDerivative_self`: `(D_v F)(v) = n F(v)` (Euler).
* `MvPolynomial.taylor_polarDerivative`, `MvPolynomial.polarDerivative_linearSubst`: behaviour
  under Taylor shifts and linear substitutions.
* `MvPolynomial.IsHomogeneous.homogeneousComponent_taylor_polarDerivative`: the degree-`j`
  Taylor component of `D_v F` at `v` is `(n - j)` times that of `F`.
* `MvPolynomial.IsHomogeneous.orderAt_polarDerivative`,
  `MvPolynomial.IsHomogeneous.leadingFormAt_polarDerivative`,
  `MvPolynomial.IsHomogeneous.polarDerivative_ne_zero`: if `F` has order `r` at `v` and
  `(n - r : R) ≠ 0`, then `D_v F` has order `r` at `v` and is nonzero.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.1, Problem 5.26
-/

public section

namespace MvPolynomial

open Finset

variable {σ R : Type*}

section CommSemiring

variable [CommSemiring R]

/-- Euler's operator `∑ᵢ Xᵢ ∂/∂Xᵢ` multiplies the degree-`j` homogeneous component of a
polynomial by `j`. -/
theorem homogeneousComponent_sum_X_mul_pderiv [Fintype σ] (G : MvPolynomial σ R) (j : ℕ) :
    homogeneousComponent j (∑ i, X i * pderiv i G) = j • homogeneousComponent j G := by
  conv_lhs => rw [← sum_homogeneousComponent G]
  simp only [map_sum, mul_sum]
  rw [sum_comm]
  simp only [← map_sum, (homogeneousComponent_isHomogeneous _ G).sum_X_mul_pderiv, map_nsmul,
    homogeneousComponent_of_mem (homogeneousComponent_mem _ G)]
  rw [sum_eq_single j (fun m _ hm ↦ by simp [Ne.symm hm]) fun hj ↦ ?_]
  · simp
  · rw [mem_range, not_lt] at hj
    simp [homogeneousComponent_eq_zero _ _ (Nat.lt_of_succ_le hj)]

variable [Fintype σ]

/-- The *polar derivative* `D_v F = ∑ᵢ vᵢ ∂F/∂Xᵢ` of `F` in the direction `v`: the derivative
of `t ↦ F(X + t v)` at `t = 0`. -/
noncomputable def polarDerivative (v : σ → R) (F : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ i, v i • pderiv i F

theorem polarDerivative_def (v : σ → R) (F : MvPolynomial σ R) :
    polarDerivative v F = ∑ i, v i • pderiv i F :=
  (rfl)

theorem polarDerivative_eq_sum_C_mul (v : σ → R) (F : MvPolynomial σ R) :
    polarDerivative v F = ∑ i, C (v i) * pderiv i F := by
  simp [polarDerivative_def, smul_eq_C_mul]

@[simp]
theorem eval_polarDerivative (v w : σ → R) (F : MvPolynomial σ R) :
    eval w (polarDerivative v F) = ∑ i, v i * eval w (pderiv i F) := by
  simp [polarDerivative_eq_sum_C_mul]

/-! ### Linearity -/

@[simp]
theorem polarDerivative_zero_left (F : MvPolynomial σ R) : polarDerivative 0 F = 0 := by
  simp [polarDerivative_def]

theorem polarDerivative_add_left (v w : σ → R) (F : MvPolynomial σ R) :
    polarDerivative (v + w) F = polarDerivative v F + polarDerivative w F := by
  simp [polarDerivative_def, add_smul, sum_add_distrib]

theorem polarDerivative_smul_left (c : R) (v : σ → R) (F : MvPolynomial σ R) :
    polarDerivative (c • v) F = c • polarDerivative v F := by
  simp [polarDerivative_def, smul_sum, mul_smul]

@[simp]
theorem polarDerivative_zero_right (v : σ → R) : polarDerivative v (0 : MvPolynomial σ R) = 0 := by
  simp [polarDerivative_def]

theorem polarDerivative_add_right (v : σ → R) (F G : MvPolynomial σ R) :
    polarDerivative v (F + G) = polarDerivative v F + polarDerivative v G := by
  simp [polarDerivative_def, smul_add, sum_add_distrib]

theorem polarDerivative_smul_right (v : σ → R) (c : R) (F : MvPolynomial σ R) :
    polarDerivative v (c • F) = c • polarDerivative v F := by
  simp [polarDerivative_def, smul_sum, smul_comm c]

@[simp]
theorem polarDerivative_C (v : σ → R) (c : R) : polarDerivative v (C c) = 0 := by
  simp [polarDerivative_def]

@[simp]
theorem polarDerivative_X (v : σ → R) (j : σ) :
    polarDerivative v (X j) = C (v j) := by
  classical
  simp [polarDerivative_eq_sum_C_mul, pderiv_X, Pi.single_apply]

/-- The polar derivative is a derivation. -/
theorem polarDerivative_mul (v : σ → R) (F G : MvPolynomial σ R) :
    polarDerivative v (F * G) = polarDerivative v F * G + F * polarDerivative v G := by
  simp only [polarDerivative_eq_sum_C_mul, Derivation.leibniz, smul_eq_mul, sum_mul, mul_sum,
    ← sum_add_distrib]
  exact sum_congr rfl fun _ _ ↦ by ring

/-! ### Homogeneity, Taylor shifts and linear substitutions -/

/-- Euler's identity: `(D_v F)(v) = n F(v)` for a form `F` of degree `n`. -/
theorem IsHomogeneous.eval_polarDerivative_self {F : MvPolynomial σ R} {n : ℕ}
    (hF : F.IsHomogeneous n) (v : σ → R) : eval v (polarDerivative v F) = n * eval v F := by
  have he := congrArg (eval v) hF.sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, nsmul_eq_mul, map_natCast] at he
  rw [eval_polarDerivative, he]

/-- Taylor shifts commute with polar derivatives. -/
theorem taylor_polarDerivative (a v : σ → R) (F : MvPolynomial σ R) :
    taylor a (polarDerivative v F) = polarDerivative v (taylor a F) := by
  simp [polarDerivative_def]

/-- Under the linear substitution `F ↦ F(M X)`, the direction `v` becomes `M v`. -/
theorem polarDerivative_linearSubst (M : Matrix σ σ R) (v : σ → R) (F : MvPolynomial σ R) :
    polarDerivative v (linearSubst M F) = linearSubst M (polarDerivative (M.mulVec v) F) := by
  simp only [polarDerivative_eq_sum_C_mul, pderiv_linearSubst, mul_sum, map_sum, map_mul,
    algHom_C, algebraMap_eq, Matrix.mulVec, dotProduct, map_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ _ ↦ by ring

/-- Euler's identity after the Taylor shift at `v`: if `F` is a form of degree `n` and
`G = F(X + v)`, then `∑ᵢ Xᵢ ∂G/∂Xᵢ + D_v G = n G`. -/
theorem IsHomogeneous.sum_X_mul_pderiv_taylor_add_polarDerivative {F : MvPolynomial σ R}
    {n : ℕ} (hF : F.IsHomogeneous n) (v : σ → R) :
    ∑ i, X i * pderiv i (taylor v F) + polarDerivative v (taylor v F) = n • taylor v F := by
  have he := congrArg (taylor v) hF.sum_X_mul_pderiv
  simp only [map_sum, map_mul, taylor_X, map_nsmul, add_mul, sum_add_distrib] at he
  rw [polarDerivative_eq_sum_C_mul, ← he]
  simp

end CommSemiring

section CommRing

variable [CommRing R] [Fintype σ] {F : MvPolynomial σ R} {n : ℕ}

/-- If `F` is a form of degree `n`, the degree-`j` Taylor component of `D_v F` at `v` is
`(n - j)` times that of `F`. -/
theorem IsHomogeneous.homogeneousComponent_taylor_polarDerivative (hF : F.IsHomogeneous n)
    (v : σ → R) (j : ℕ) :
    homogeneousComponent j (taylor v (polarDerivative v F)) =
      (n - j) • homogeneousComponent j (taylor v F) := by
  have h := congrArg (homogeneousComponent j)
    (hF.sum_X_mul_pderiv_taylor_add_polarDerivative v)
  rw [map_add, homogeneousComponent_sum_X_mul_pderiv, map_nsmul, ← taylor_polarDerivative] at h
  rcases le_or_gt j n with hj | hj
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
    rw [add_nsmul] at h
    rw [add_tsub_cancel_left]
    exact add_left_cancel h
  · rw [homogeneousComponent_eq_zero _ _ ((totalDegree_taylor_le v F).trans_lt
      (hF.totalDegree_le.trans_lt hj)), smul_zero]
    rw [homogeneousComponent_eq_zero _ _ ((totalDegree_taylor_le v F).trans_lt
      (hF.totalDegree_le.trans_lt hj)), smul_zero] at h
    simpa using h

variable [NoZeroDivisors R] {v : σ → R} {r : ℕ}

/-- If the form `F` of degree `n` has order `r` at `v` and `n - r` is nonzero in `R`, then its
polar derivative `D_v F` also has order `r` at `v`. -/
theorem IsHomogeneous.orderAt_polarDerivative (hF : F.IsHomogeneous n) (hr : F.orderAt v = r)
    (hnr : ((n - r : ℕ) : R) ≠ 0) : (polarDerivative v F).orderAt v = r := by
  refine orderAt_eq_of_homogeneousComponent_ne_zero
    (le_orderAt_iff_homogeneousComponent.2 fun i hi ↦ ?_) ?_
  · rw [hF.homogeneousComponent_taylor_polarDerivative,
      homogeneousComponent_taylor_eq_zero_of_lt (by rw [hr]; exact_mod_cast hi), smul_zero]
  · rw [hF.homogeneousComponent_taylor_polarDerivative, nsmul_eq_mul, ← map_natCast C]
    exact mul_ne_zero (by rwa [Ne, C_eq_zero]) (homogeneousComponent_ne_zero_of_orderAt_eq _ _ hr)

/-- If the form `F` of degree `n` has order `r` at `v` and `n - r` is nonzero in `R`, the
leading form of `D_v F` at `v` is `(n - r)` times that of `F`. -/
theorem IsHomogeneous.leadingFormAt_polarDerivative (hF : F.IsHomogeneous n)
    (hr : F.orderAt v = r) (hnr : ((n - r : ℕ) : R) ≠ 0) :
    (polarDerivative v F).leadingFormAt v = (n - r) • F.leadingFormAt v := by
  rw [leadingFormAt_def, leadingFormAt_def, hF.orderAt_polarDerivative hr hnr, hr,
    ENat.toNat_natCast, hF.homogeneousComponent_taylor_polarDerivative]

/-- **Nonvanishing of the polar derivative.** If the form `F` of degree `n` has order `r` at
`v` and `n - r` is nonzero in `R`, then `D_v F ≠ 0`. -/
theorem IsHomogeneous.polarDerivative_ne_zero (hF : F.IsHomogeneous n) (hr : F.orderAt v = r)
    (hnr : ((n - r : ℕ) : R) ≠ 0) : polarDerivative v F ≠ 0 := by
  intro h
  have := hF.orderAt_polarDerivative hr hnr
  rw [h, MvPolynomial.orderAt_zero] at this
  exact ENat.top_ne_natCast r this

end CommRing

section Homogeneous

variable [CommSemiring R] [Fintype σ]

/-- The polar derivative of a form of degree `n` is a form of degree `n - 1`. -/
theorem IsHomogeneous.polarDerivative {F : MvPolynomial σ R} {n : ℕ} (hF : F.IsHomogeneous n)
    (v : σ → R) : (polarDerivative v F).IsHomogeneous (n - 1) := by
  rw [polarDerivative_eq_sum_C_mul]
  exact IsHomogeneous.sum _ _ _ fun i _ ↦ by
    simpa using (isHomogeneous_C σ (v i)).mul (hF.pderiv (i := i))

end Homogeneous

end MvPolynomial

end
