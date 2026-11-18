/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.OrderAt

/-!
# The Taylor shift as an algebra automorphism

Over a commutative ring `R`, the Taylor shift `MvPolynomial.taylor a : p ↦ p(X + a)` of Tau
Ceti is an `R`-algebra automorphism of `MvPolynomial σ R`, with inverse `taylor (-a)`. This file
packages it as an `AlgEquiv`, as Mathlib's `Polynomial.taylorEquiv` does in one variable.

## Main definitions

* `MvPolynomial.taylorAlgEquiv a`: the Taylor shift `p ↦ p(X + a)` as an `R`-algebra
  automorphism of `MvPolynomial σ R`.

## Main results

* `MvPolynomial.coe_taylorAlgEquiv`, `MvPolynomial.taylorAlgEquiv_symm`: it is `taylor a`, and
  its inverse is the Taylor shift at `-a`.
* `MvPolynomial.taylor_bijective`: the Taylor shift is bijective.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- The Taylor shift `p ↦ p(X + a)` as an `R`-algebra automorphism of `MvPolynomial σ R`; its
inverse is the Taylor shift at `-a`. -/
noncomputable def taylorAlgEquiv (a : σ → R) : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (taylor a) (taylor (-a))
    (algHom_ext fun i ↦ by simp [taylor_X]) (algHom_ext fun i ↦ by simp [taylor_X])

theorem taylorAlgEquiv_def (a : σ → R) :
    taylorAlgEquiv a = AlgEquiv.ofAlgHom (taylor a) (taylor (-a))
      (algHom_ext fun i ↦ by simp [taylor_X]) (algHom_ext fun i ↦ by simp [taylor_X]) :=
  (rfl)

@[simp]
theorem coe_taylorAlgEquiv (a : σ → R) : ⇑(taylorAlgEquiv a) = taylor a := by
  rw [taylorAlgEquiv_def]
  rfl

@[simp, norm_cast]
theorem toAlgHom_taylorAlgEquiv (a : σ → R) :
    (taylorAlgEquiv a : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) = taylor a :=
  AlgHom.coe_fn_injective (coe_taylorAlgEquiv a)

theorem taylorAlgEquiv_apply (a : σ → R) (p : MvPolynomial σ R) :
    taylorAlgEquiv a p = taylor a p := by
  rw [coe_taylorAlgEquiv]

@[simp]
theorem taylorAlgEquiv_symm (a : σ → R) :
    (taylorAlgEquiv a).symm = taylorAlgEquiv (-a) := by
  refine AlgEquiv.ext fun p ↦ ?_
  rw [AlgEquiv.symm_apply_eq, coe_taylorAlgEquiv, coe_taylorAlgEquiv, taylor_taylor,
    add_neg_cancel, taylor_zero]

theorem taylorAlgEquiv_symm_apply (a : σ → R) (p : MvPolynomial σ R) :
    (taylorAlgEquiv a).symm p = taylor (-a) p := by
  simp

@[simp]
theorem taylorAlgEquiv_zero : taylorAlgEquiv (0 : σ → R) = AlgEquiv.refl := by
  refine AlgEquiv.ext fun p ↦ ?_
  simp [taylor_zero]

theorem taylorAlgEquiv_trans (a b : σ → R) :
    (taylorAlgEquiv a).trans (taylorAlgEquiv b) = taylorAlgEquiv (a + b) := by
  refine AlgEquiv.ext fun p ↦ ?_
  simp [taylor_taylor, add_comm a b]

/-- Over a commutative ring, the Taylor shift is bijective. -/
theorem taylor_bijective (a : σ → R) : Function.Bijective (taylor a) := by
  rw [← coe_taylorAlgEquiv]
  exact (taylorAlgEquiv a).bijective

theorem taylor_surjective (a : σ → R) : Function.Surjective (taylor a) :=
  (taylor_bijective a).surjective

end MvPolynomial

end
