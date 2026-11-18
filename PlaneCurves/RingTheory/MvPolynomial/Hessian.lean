/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import TauCeti.RingTheory.LocalRing.Hessian
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization
public import TauCeti.RingTheory.MvPolynomial.LinearSubst

/-!
# The Hessian matrix of a polynomial

For a polynomial `F` in finitely many variables over a commutative ring, its Hessian matrix is
Tau Ceti's `TauCeti.hessian MvPolynomial.pderiv F`, the matrix of second partial derivatives
`Fᵢⱼ = ∂²F/∂Xᵢ∂Xⱼ`. This file proves its basic algebraic properties: symmetry, homogeneity of
the matrix and of its determinant for a form `F`, Euler's identity for the Hessian, its
behaviour under a linear change of variables, and its restriction to an affine chart.

## Main results

* `MvPolynomial.isSymm_hessian_pderiv`: the Hessian matrix is symmetric.
* `MvPolynomial.isHomogeneous_det`: a square matrix of forms of degree `d` has a determinant
  that is a form of degree `card ι * d`.
* `MvPolynomial.IsHomogeneous.det_hessian`: for a form `F` of degree `n` in `card σ`
  variables, the Hessian determinant is a form of degree `card σ * (n - 2)`.
* `MvPolynomial.IsHomogeneous.hessian_mulVec_X`: Euler's identity for the Hessian,
  `∑ⱼ Fᵢⱼ Xⱼ = (n - 1) Fᵢ`.
* `MvPolynomial.IsHomogeneous.sq_X_mul_det_hessian`: `Xⱼ² H` is `(n - 1)` times a bordered
  determinant whose `j`-th column is the gradient of `F` and whose `j`-th row is
  `((n - 1) F₀, …, n F, …, (n - 1) Fₘ)`.
* `MvPolynomial.det_hessian_linearSubst`: the Hessian determinant of `F` after the change of
  variables along `M` is `(det M)²` times the change of variables of the Hessian determinant.
* `MvPolynomial.hessian_dehomogenize`: the Hessian of a dehomogenization is the
  dehomogenization of the corresponding submatrix of the Hessian.

## References

* [W. Fulton, *Algebraic Curves: An Introduction to Algebraic Geometry*][Fulton2008],
  §5.3, Problem 5.23
-/

public section

namespace MvPolynomial

open Matrix

variable {R σ : Type*} [CommRing R]

/-- The Hessian matrix of a polynomial is symmetric. -/
theorem isSymm_hessian_pderiv (F : MvPolynomial σ R) :
    (TauCeti.hessian pderiv F).IsSymm :=
  Matrix.IsSymm.ext fun i j ↦ by simp [pderiv_comm]

/-- A square matrix whose entries are forms of degree `d` has as determinant a form of degree
`card ι * d`. -/
theorem isHomogeneous_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι (MvPolynomial σ R)} {d : ℕ} (h : ∀ i j, (M i j).IsHomogeneous d) :
    M.det.IsHomogeneous (Fintype.card ι * d) := by
  rw [Matrix.det_apply]
  refine IsHomogeneous.sum _ _ _ fun e _ ↦ ?_
  have hprod := IsHomogeneous.prod Finset.univ _ (fun _ ↦ d) fun i _ ↦ h (e i) i
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with he | he <;> simp [he, hprod, hprod.neg]

variable {F : MvPolynomial σ R} {n : ℕ}

/-- For a form `F` of degree `n`, the entries of its Hessian matrix are forms of degree
`n - 2`. -/
theorem IsHomogeneous.hessian_apply (hF : F.IsHomogeneous n) (i j : σ) :
    (TauCeti.hessian pderiv F i j).IsHomogeneous (n - 2) := by
  simpa [Nat.sub_sub] using hF.pderiv.pderiv (i := i)

/-- For a form `F` of degree `n` in `card σ` variables, the Hessian determinant is a form of
degree `card σ * (n - 2)`. -/
theorem IsHomogeneous.det_hessian [Fintype σ] [DecidableEq σ] (hF : F.IsHomogeneous n) :
    (TauCeti.hessian pderiv F).det.IsHomogeneous (Fintype.card σ * (n - 2)) :=
  isHomogeneous_det hF.hessian_apply

/-- **Euler's identity for the Hessian**: for a form `F` of degree `n`,
`∑ⱼ Fᵢⱼ Xⱼ = (n - 1) Fᵢ`. -/
theorem IsHomogeneous.hessian_mulVec_X [Fintype σ] (hF : F.IsHomogeneous n) :
    TauCeti.hessian pderiv F *ᵥ X = (n - 1) • fun i ↦ pderiv i F := by
  funext i
  simp only [mulVec, dotProduct, TauCeti.hessian_apply, Pi.smul_apply]
  rw [← (hF.pderiv (i := i)).sum_X_mul_pderiv]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [pderiv_comm, mul_comm]

/-- **Euler's identity for the Hessian**, on the other side: for a form `F` of degree `n`,
`∑ᵢ Xᵢ Fᵢⱼ = (n - 1) Fⱼ`. -/
theorem IsHomogeneous.X_vecMul_hessian [Fintype σ] (hF : F.IsHomogeneous n) :
    X ᵥ* TauCeti.hessian pderiv F = (n - 1) • fun i ↦ pderiv i F := by
  rw [← (isSymm_hessian_pderiv F).eq, vecMul_transpose, hF.hessian_mulVec_X]

/-- For a form `F` of degree `n`, `Xⱼ H = (n - 1) det H'`, where `H` is the Hessian determinant
and `H'` is the Hessian matrix with its `j`-th column replaced by the gradient of `F`. -/
theorem IsHomogeneous.X_mul_det_hessian [Fintype σ] [DecidableEq σ] (hF : F.IsHomogeneous n)
    (j : σ) :
    X j * (TauCeti.hessian pderiv F).det =
      (n - 1) • ((TauCeti.hessian pderiv F).updateCol j fun i ↦ pderiv i F).det := by
  have h := det_updateCol_sum (TauCeti.hessian pderiv F) j X
  have hcol : (fun k ↦ ∑ i, (X i : MvPolynomial σ R) • TauCeti.hessian pderiv F k i) =
      ((n - 1 : ℕ) : MvPolynomial σ R) • fun i ↦ pderiv i F := by
    rw [Nat.cast_smul_eq_nsmul, ← hF.hessian_mulVec_X]
    funext k
    simp [mulVec, dotProduct, mul_comm]
  rw [hcol, det_updateCol_smul, smul_eq_mul] at h
  rw [← h, nsmul_eq_mul]

/-- **The bordered Hessian**: for a form `F` of degree `n`, `Xⱼ² H` is `n - 1` times the
determinant of the Hessian matrix with its `j`-th column replaced by the gradient
`(F₀, …, Fₘ)` of `F` and then its `j`-th row by `((n - 1) F₀, …, n F, …, (n - 1) Fₘ)`, the entry
`n F` in the `j`-th place. -/
theorem IsHomogeneous.sq_X_mul_det_hessian [Fintype σ] [DecidableEq σ] (hF : F.IsHomogeneous n)
    (j : σ) :
    X j ^ 2 * (TauCeti.hessian pderiv F).det =
      (n - 1) • (((TauCeti.hessian pderiv F).updateCol j fun i ↦ pderiv i F).updateRow j
        fun k ↦ if k = j then n • F else (n - 1) • pderiv k F).det := by
  set A := (TauCeti.hessian pderiv F).updateCol j fun i ↦ pderiv i F
  have hrow : ∑ k, (X k : MvPolynomial σ R) • A k =
      fun l ↦ if l = j then n • F else (n - 1) • pderiv l F := by
    funext l
    simp only [A, Finset.sum_apply, Pi.smul_apply, updateCol_apply, smul_eq_mul]
    split_ifs
    · exact hF.sum_X_mul_pderiv
    · simpa [vecMul, dotProduct] using congrFun hF.X_vecMul_hessian l
  rw [sq, mul_assoc, hF.X_mul_det_hessian, mul_smul_comm, ← smul_eq_mul, ← det_updateRow_sum,
    hrow]

/-- **Covariance of the Hessian matrix**: after the change of variables along `M`, the Hessian
matrix of `F` is `Mᵀ (H ∘ M) M`, for `H` the Hessian matrix of `F`. -/
theorem hessian_linearSubst [Fintype σ] (M : Matrix σ σ R) (F : MvPolynomial σ R) :
    TauCeti.hessian pderiv (linearSubst M F) =
      (M.map C)ᵀ * (TauCeti.hessian pderiv F).map (linearSubst M) * M.map C := by
  refine Matrix.ext fun a b ↦ ?_
  simp only [TauCeti.hessian_apply, pderiv_linearSubst, map_sum, pderiv_C_mul, Finset.mul_sum]
  simp only [Matrix.mul_apply, transpose_apply, map_apply, TauCeti.hessian_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring

/-- **Covariance of the Hessian**: after the change of variables along `M`, the Hessian
determinant of `F` is `(det M)²` times the change of variables of the Hessian determinant. -/
theorem det_hessian_linearSubst [Fintype σ] [DecidableEq σ] (M : Matrix σ σ R)
    (F : MvPolynomial σ R) :
    (TauCeti.hessian pderiv (linearSubst M F)).det =
      C (M.det ^ 2) * linearSubst M (TauCeti.hessian pderiv F).det := by
  have hC : (M.map C).det = C M.det := (RingHom.map_det (C : R →+* MvPolynomial σ R) M).symm
  have hL : ((TauCeti.hessian pderiv F).map (linearSubst M)).det =
      linearSubst M (TauCeti.hessian pderiv F).det := (AlgHom.map_det _ _).symm
  rw [hessian_linearSubst, det_mul, det_mul, det_transpose, hC, hL, map_pow]
  ring

/-- **Covariance of the Hessian at a point**: the Hessian determinant of `F` after the change of
variables along `M`, at `v`, is `(det M)²` times the Hessian determinant of `F` at `M v`. -/
theorem eval_det_hessian_linearSubst [Fintype σ] [DecidableEq σ] (M : Matrix σ σ R)
    (F : MvPolynomial σ R) (v : σ → R) :
    eval v (TauCeti.hessian pderiv (linearSubst M F)).det =
      M.det ^ 2 * eval (M *ᵥ v) (TauCeti.hessian pderiv F).det := by
  rw [det_hessian_linearSubst, eval_mul, eval_C, eval_linearSubst]

/-- **The Hessian in an affine chart**: the Hessian matrix of the dehomogenization of `F` at the
`i`-th variable is the dehomogenization of the Hessian matrix of `F` with the `i`-th row and
column removed. -/
theorem hessian_dehomogenize {m : ℕ} (i : Fin (m + 1)) (F : MvPolynomial (Fin (m + 1)) R) :
    TauCeti.hessian pderiv (TauCeti.dehomogenize i F) =
      ((TauCeti.hessian pderiv F).submatrix i.succAbove i.succAbove).map
        (TauCeti.dehomogenize i) := by
  refine Matrix.ext fun a b ↦ ?_
  simp [TauCeti.pderiv_dehomogenize]

end MvPolynomial
