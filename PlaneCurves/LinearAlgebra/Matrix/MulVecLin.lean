/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Injectivity of `Matrix.mulVecLin`

The injectivity of the linear map `v ↦ M *ᵥ v` is the usual way to state that a square matrix
`M` is an invertible change of coordinates. This file relates it to the determinant.

## Main results

* `Matrix.mulVecLin_injective_iff_isUnit_det`: over a field, `M.mulVecLin` is injective exactly
  when `M.det` is a unit.
* `Matrix.isUnit_det_of_mulVecLin_injective`: its forward direction.
* `Matrix.mulVecLin_mul_injective`: over a commutative semiring, the product of two matrices
  whose `mulVecLin` are injective has an injective `mulVecLin`.
-/

public section

namespace Matrix

variable {l m n K R : Type*}

/-- Over a field, the linear map `v ↦ M *ᵥ v` of a square matrix is injective exactly when the
determinant of `M` is a unit. -/
theorem mulVecLin_injective_iff_isUnit_det [Fintype n] [DecidableEq n] [Field K]
    {M : Matrix n n K} : Function.Injective M.mulVecLin ↔ IsUnit M.det := by
  rw [coe_mulVecLin, mulVec_injective_iff_isUnit, isUnit_iff_isUnit_det]

/-- Over a field, if the linear map `v ↦ M *ᵥ v` of a square matrix is injective, then the
determinant of `M` is a unit. -/
theorem isUnit_det_of_mulVecLin_injective [Fintype n] [DecidableEq n] [Field K]
    {M : Matrix n n K} (hM : Function.Injective M.mulVecLin) : IsUnit M.det :=
  mulVecLin_injective_iff_isUnit_det.1 hM

/-- If the linear maps `v ↦ M *ᵥ v` and `v ↦ N *ᵥ v` are injective, then so is
`v ↦ (M * N) *ᵥ v`. -/
theorem mulVecLin_mul_injective [Fintype m] [Fintype n] [CommSemiring R]
    {M : Matrix l m R} {N : Matrix m n R} (hM : Function.Injective M.mulVecLin)
    (hN : Function.Injective N.mulVecLin) : Function.Injective (M * N).mulVecLin := by
  rw [mulVecLin_mul, LinearMap.coe_comp]
  exact hM.comp hN

end Matrix

end
