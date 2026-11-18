/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# Invertible linear changes of variables

Tau Ceti's `MvPolynomial.linearSubst M` is the change of variables `Xᵢ ↦ ∑ⱼ Mᵢⱼ Xⱼ` along a
square matrix `M`. When `M` is invertible it is an algebra automorphism of `R[X]`, with inverse
the change of variables along `M⁻¹`.

## Main definitions

* `MvPolynomial.linearSubstAlgEquiv M`: for `M` in `GL σ R`, the change of variables along `M`
  as an `R`-algebra automorphism of `MvPolynomial σ R`.

## Main results

* `MvPolynomial.linearSubst_nonsing_inv_linearSubst`,
  `MvPolynomial.linearSubst_linearSubst_nonsing_inv`: for `M` with invertible determinant, the
  changes of variables along `M` and `M⁻¹` are inverse to each other.
* `MvPolynomial.linearSubst_injective`: such a change of variables is injective.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [Fintype σ] [DecidableEq σ]

section CommSemiring

variable [CommSemiring R]

/-- The change of variables along `M⁻¹` undoes the change of variables along `M`, for `M` in
`GL σ R`. -/
@[simp]
theorem linearSubst_inv_linearSubst (M : Matrix.GeneralLinearGroup σ R) (p : MvPolynomial σ R) :
    linearSubst (M⁻¹ : Matrix.GeneralLinearGroup σ R).1 (linearSubst M.1 p) = p := by
  rw [← linearSubst_mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, linearSubst_one,
    AlgHom.id_apply]

/-- The change of variables along `M` undoes the change of variables along `M⁻¹`, for `M` in
`GL σ R`. -/
@[simp]
theorem linearSubst_linearSubst_inv (M : Matrix.GeneralLinearGroup σ R) (p : MvPolynomial σ R) :
    linearSubst M.1 (linearSubst (M⁻¹ : Matrix.GeneralLinearGroup σ R).1 p) = p := by
  rw [← linearSubst_mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, linearSubst_one,
    AlgHom.id_apply]

/-- The change of variables `Xᵢ ↦ ∑ⱼ Mᵢⱼ Xⱼ` along an invertible matrix `M`, as an `R`-algebra
automorphism of `MvPolynomial σ R`. Its inverse is the change of variables along `M⁻¹`. -/
noncomputable def linearSubstAlgEquiv (M : Matrix.GeneralLinearGroup σ R) :
    MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R :=
  AlgEquiv.ofAlgHom (linearSubst M.1) (linearSubst (M⁻¹ : Matrix.GeneralLinearGroup σ R).1)
    (AlgHom.ext (linearSubst_linearSubst_inv M)) (AlgHom.ext (linearSubst_inv_linearSubst M))

theorem linearSubstAlgEquiv_def (M : Matrix.GeneralLinearGroup σ R) :
    linearSubstAlgEquiv M =
      AlgEquiv.ofAlgHom (linearSubst M.1) (linearSubst (M⁻¹ : Matrix.GeneralLinearGroup σ R).1)
        (AlgHom.ext (linearSubst_linearSubst_inv M)) (AlgHom.ext (linearSubst_inv_linearSubst M)) :=
  (rfl)

@[simp]
theorem linearSubstAlgEquiv_apply (M : Matrix.GeneralLinearGroup σ R) (p : MvPolynomial σ R) :
    linearSubstAlgEquiv M p = linearSubst M.1 p :=
  (rfl)

@[simp]
theorem linearSubstAlgEquiv_symm_apply (M : Matrix.GeneralLinearGroup σ R)
    (p : MvPolynomial σ R) :
    (linearSubstAlgEquiv M).symm p = linearSubst (M⁻¹ : Matrix.GeneralLinearGroup σ R).1 p :=
  (rfl)

@[simp]
theorem toAlgHom_linearSubstAlgEquiv (M : Matrix.GeneralLinearGroup σ R) :
    (linearSubstAlgEquiv M : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) = linearSubst M.1 :=
  (rfl)

end CommSemiring

section CommRing

variable [CommRing R]

/-- The change of variables along `M⁻¹` undoes the change of variables along `M`, for a matrix
`M` with invertible determinant. -/
@[simp]
theorem linearSubst_nonsing_inv_linearSubst {M : Matrix σ σ R} (hM : IsUnit M.det)
    (p : MvPolynomial σ R) : linearSubst M⁻¹ (linearSubst M p) = p := by
  rw [← linearSubst_mul_apply, Matrix.mul_nonsing_inv _ hM, linearSubst_one, AlgHom.id_apply]

/-- The change of variables along `M` undoes the change of variables along `M⁻¹`, for a matrix
`M` with invertible determinant. -/
@[simp]
theorem linearSubst_linearSubst_nonsing_inv {M : Matrix σ σ R} (hM : IsUnit M.det)
    (p : MvPolynomial σ R) : linearSubst M (linearSubst M⁻¹ p) = p := by
  rw [← linearSubst_mul_apply, Matrix.nonsing_inv_mul _ hM, linearSubst_one, AlgHom.id_apply]

/-- A linear change of variables along a matrix with invertible determinant is injective. -/
theorem linearSubst_injective {M : Matrix σ σ R} (hM : IsUnit M.det) :
    Function.Injective (linearSubst M) :=
  Function.LeftInverse.injective (linearSubst_nonsing_inv_linearSubst hM)

end CommRing

end MvPolynomial

end
