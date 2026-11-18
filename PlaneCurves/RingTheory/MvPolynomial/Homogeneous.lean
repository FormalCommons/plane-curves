/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.RingTheory.MvPolynomial.Homogenize.Basic

/-!
# Scaling the arguments of a form

A form `F` of degree `d` satisfies `F(c x₁, …, c xₙ) = c ^ d F(x₁, …, xₙ)` for every `c` in any
commutative algebra, not only for `c` in the base ring as in Mathlib's
`MvPolynomial.IsHomogeneous.aeval_smul`. In two variables, a binary form `F` is determined by
`F(1, Y)`, kept as a polynomial in the variable `Y = X 1`.

## Main results

* `MvPolynomial.IsHomogeneous.eval₂_mul_left`, `MvPolynomial.IsHomogeneous.aeval_mul_left`:
  `F(c x) = c ^ d F(x)` for a form `F` of degree `d`.
* `MvPolynomial.IsHomogeneous.aeval_one_X_eq_zero_iff`: a binary form `F` vanishes exactly when
  `F(1, Y)` does.
-/

public section

namespace MvPolynomial

open TauCeti

variable {σ R S : Type*} [CommSemiring R] [CommSemiring S] {F : MvPolynomial σ R} {d : ℕ}

/-- Multiplying every argument of a form of degree `d` by `c` multiplies its value by `c ^ d`. -/
theorem IsHomogeneous.eval₂_mul_left (hF : F.IsHomogeneous d) (f : R →+* S) (c : S)
    (p : σ → S) : F.eval₂ f (fun i ↦ c * p i) = c ^ d * F.eval₂ f p := by
  simp only [eval₂_eq, Finset.mul_sum, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  congr! 1 with x hx
  rw [hF.degree_eq_sum_deg_support hx, mul_left_comm]

/-- Multiplying every argument of a form of degree `d` by `c` multiplies its value by `c ^ d`. -/
theorem IsHomogeneous.aeval_mul_left [Algebra R S] (hF : F.IsHomogeneous d) (c : S)
    (p : σ → S) : MvPolynomial.aeval (fun i ↦ c * p i) F = c ^ d * MvPolynomial.aeval p F :=
  hF.eval₂_mul_left _ c p

/-- `F(1, Y)` is the dehomogenization of `F` in the first variable, renamed to `Y = X 1`. -/
theorem aeval_one_X_eq_rename_dehomogenize (F : MvPolynomial (Fin 2) R) :
    aeval ![1, (X 1 : MvPolynomial (Fin 2) R)] F = rename (fun _ ↦ 1) (dehomogenize 0 F) := by
  rw [← AlgHom.comp_apply]
  congr 1
  ext j
  fin_cases j <;> simp

/-- A binary form `F` is zero exactly when `F(1, Y)` is. -/
theorem IsHomogeneous.aeval_one_X_eq_zero_iff {F : MvPolynomial (Fin 2) R}
    (hF : F.IsHomogeneous d) :
    MvPolynomial.aeval ![1, (X 1 : MvPolynomial (Fin 2) R)] F = 0 ↔ F = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [aeval_one_X_eq_rename_dehomogenize, ← map_zero (rename fun _ : Fin 1 ↦ (1 : Fin 2)),
    (rename_injective _ fun _ _ _ ↦ Subsingleton.elim _ _).eq_iff] at h
  rw [← homogenize_dehomogenize (i := 0) hF, h, map_zero]

end MvPolynomial

end
