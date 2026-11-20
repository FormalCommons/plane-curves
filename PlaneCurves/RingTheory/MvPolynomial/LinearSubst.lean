/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import TauCeti.Algebra.Squarefree
public import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# Invertible linear changes of variables

Tau Ceti's `MvPolynomial.linearSubst M` is the change of variables `Xᵢ ↦ ∑ⱼ Mᵢⱼ Xⱼ` along a
square matrix `M`. When `M` is invertible it is an algebra automorphism of `R[X]`, with inverse
the change of variables along `M⁻¹`.

## Main definitions

* `MvPolynomial.linearSubstAlgEquiv M`: for `M` in `GL σ R`, the change of variables along `M`
  as an `R`-algebra automorphism of `MvPolynomial σ R`.
* `MvPolynomial.linearSubstGradedRingHom M`: the change of variables along any square matrix `M`,
  as a graded ring hom for the grading of `MvPolynomial σ R` by total degree.

## Main results

* `MvPolynomial.linearSubst_nonsing_inv_linearSubst`,
  `MvPolynomial.linearSubst_linearSubst_nonsing_inv`: for `M` with invertible determinant, the
  changes of variables along `M` and `M⁻¹` are inverse to each other.
* `MvPolynomial.linearSubst_injective`, `MvPolynomial.irreducible_linearSubst_iff`,
  `MvPolynomial.squarefree_linearSubst_iff`, `MvPolynomial.isRelPrime_linearSubst_iff`: such a
  change of variables is injective and preserves irreducibility, being squarefree and being
  relatively prime.
* `MvPolynomial.totalDegree_linearSubst_le`, `MvPolynomial.totalDegree_linearSubst`: a change of
  variables does not raise the total degree, and preserves it when `M` is invertible.
* `MvPolynomial.linearSubst_toPEquiv_toMatrix`: renaming the variables along a permutation is the
  change of variables along its permutation matrix.
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

/-- The change of variables along a square matrix `M`, as a graded ring hom: it sends forms of
degree `d` to forms of degree `d`. -/
noncomputable def linearSubstGradedRingHom (M : Matrix σ σ R) :
    homogeneousSubmodule σ R →+*ᵍ homogeneousSubmodule σ R where
  toRingHom := (linearSubst M).toRingHom
  map_mem hp := (mem_homogeneousSubmodule _ _).2 <|
    ((mem_homogeneousSubmodule _ _).1 hp).linearSubst M

omit [DecidableEq σ] in
@[simp]
theorem coe_linearSubstGradedRingHom (M : Matrix σ σ R) :
    ⇑(linearSubstGradedRingHom M) = ⇑(linearSubst M) :=
  (rfl)

/-- Renaming the variables along a permutation `e` is the change of variables along the
permutation matrix of `e`. -/
theorem linearSubst_toPEquiv_toMatrix (e : Equiv.Perm σ) (p : MvPolynomial σ R) :
    linearSubst e.toPEquiv.toMatrix p = rename e p := by
  have h : linearSubst (R := R) e.toPEquiv.toMatrix = rename e :=
    algHom_ext fun i ↦ by simp [linearSubst_X, PEquiv.toMatrix_apply]
  exact DFunLike.congr_fun h p

omit [DecidableEq σ] in
/-- A linear change of variables does not raise the total degree. -/
theorem totalDegree_linearSubst_le (M : Matrix σ σ R) (p : MvPolynomial σ R) :
    (linearSubst M p).totalDegree ≤ p.totalDegree := by
  conv_lhs => rw [← sum_homogeneousComponent p]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun i hi ↦ ?_
  exact ((homogeneousComponent_isHomogeneous i p).linearSubst M).totalDegree_le.trans
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

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

/-- A linear change of variables along a matrix with invertible determinant preserves
irreducibility. -/
theorem irreducible_linearSubst_iff {M : Matrix σ σ R} (hM : IsUnit M.det)
    {p : MvPolynomial σ R} : Irreducible (linearSubst M p) ↔ Irreducible p := by
  simpa using MulEquiv.irreducible_iff
    (linearSubstAlgEquiv ((Matrix.isUnit_iff_isUnit_det M).2 hM).unit) (x := p)

/-- A linear change of variables along a matrix with invertible determinant preserves being
squarefree. -/
theorem squarefree_linearSubst_iff {M : Matrix σ σ R} (hM : IsUnit M.det)
    {p : MvPolynomial σ R} : Squarefree (linearSubst M p) ↔ Squarefree p := by
  simpa using TauCeti.squarefree_map_iff
    (linearSubstAlgEquiv ((Matrix.isUnit_iff_isUnit_det M).2 hM).unit) (a := p)

/-- A linear change of variables along a matrix with invertible determinant preserves being
relatively prime. -/
theorem isRelPrime_linearSubst_iff {M : Matrix σ σ R} (hM : IsUnit M.det)
    {p q : MvPolynomial σ R} :
    IsRelPrime (linearSubst M p) (linearSubst M q) ↔ IsRelPrime p q := by
  set e := linearSubstAlgEquiv ((Matrix.isUnit_iff_isUnit_det M).2 hM).unit
  have he (r : MvPolynomial σ R) : e r = linearSubst M r := rfl
  refine ⟨fun h ↦ IsRelPrime.of_map e (by simpa only [he] using h), fun h ↦ ?_⟩
  exact IsRelPrime.of_map e.symm (by simpa only [← he, AlgEquiv.symm_apply_apply] using h)

/-- A linear change of variables along a matrix with invertible determinant preserves the total
degree. -/
@[simp]
theorem totalDegree_linearSubst {M : Matrix σ σ R} (hM : IsUnit M.det) (p : MvPolynomial σ R) :
    (linearSubst M p).totalDegree = p.totalDegree := by
  refine (totalDegree_linearSubst_le M p).antisymm ?_
  conv_lhs => rw [← linearSubst_nonsing_inv_linearSubst hM p]
  exact totalDegree_linearSubst_le _ _

end CommRing

end MvPolynomial

end
