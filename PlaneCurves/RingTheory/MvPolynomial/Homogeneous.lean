/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.RingTheory.MvPolynomial.Homogenize.Basic

/-!
# Scaling the arguments of a form, and dividing by a form

A form `F` of degree `d` satisfies `F(c x₁, …, c xₙ) = c ^ d F(x₁, …, xₙ)` for every `c` in any
commutative algebra, not only for `c` in the base ring as in Mathlib's
`MvPolynomial.IsHomogeneous.aeval_smul`. In two variables, a binary form `F` is determined by
`F(1, Y)`, kept as a polynomial in the variable `Y = X 1`. A form that divides a polynomial divides
each of its homogeneous components.

## Main results

* `MvPolynomial.IsHomogeneous.eval₂_mul_left`, `MvPolynomial.IsHomogeneous.aeval_mul_left`:
  `F(c x) = c ^ d F(x)` for a form `F` of degree `d`.
* `MvPolynomial.IsHomogeneous.aeval_one_X_eq_zero_iff`: a binary form `F` vanishes exactly when
  `F(1, Y)` does, and `MvPolynomial.IsHomogeneous.aeval_one_polynomial_X_eq_zero_iff` the same
  for `F(1, T)` as a polynomial in one variable.
* `MvPolynomial.IsHomogeneous.dvd_homogeneousComponent`: a form dividing a polynomial divides
  each of its homogeneous components.
* `MvPolynomial.IsHomogeneous.exists_isHomogeneous_of_dvd`: over a field, a divisor of a nonzero
  form that is not a unit is a form of positive degree.
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

/-- A binary form `F` is zero exactly when the polynomial `F(1, T)` in one variable is. -/
theorem IsHomogeneous.aeval_one_polynomial_X_eq_zero_iff {F : MvPolynomial (Fin 2) R}
    (hF : F.IsHomogeneous d) :
    (MvPolynomial.aeval ![1, Polynomial.X] F : Polynomial R) = 0 ↔ F = 0 := by
  refine ⟨fun h ↦ hF.aeval_one_X_eq_zero_iff.1 ?_, fun h ↦ by simp [h]⟩
  have h' := congr(Polynomial.aeval (X 1 : MvPolynomial (Fin 2) R) $h)
  rw [← AlgHom.comp_apply, comp_aeval, map_zero] at h'
  rw [← h']
  congr 1
  ext i : 1
  fin_cases i <;> simp

/-- A form that divides a polynomial divides each of its homogeneous components. -/
theorem IsHomogeneous.dvd_homogeneousComponent {P : MvPolynomial σ R} (hF : F.IsHomogeneous d)
    (h : F ∣ P) (j : ℕ) : F ∣ homogeneousComponent j P := by
  obtain ⟨K, rfl⟩ := h
  rw [mul_comm, hF.homogeneousComponent_mul_right]
  split_ifs
  exacts [dvd_mul_left _ _, dvd_zero _]

/-- Over a field, a divisor of a nonzero form that is not a unit is a form of positive
degree. -/
theorem IsHomogeneous.exists_isHomogeneous_of_dvd {k : Type*} [Field k]
    {F H : MvPolynomial σ k} (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) (hHF : H ∣ F)
    (hH : ¬IsUnit H) : ∃ e ≠ 0, H.IsHomogeneous e := by
  obtain ⟨c, rfl⟩ := hHF
  refine ⟨H.totalDegree, fun h0 ↦ hH ?_, hF.of_mul_left (right_ne_zero_of_mul hF0)⟩
  rw [totalDegree_eq_zero_iff_eq_C.1 h0, isUnit_map_iff, isUnit_iff_ne_zero]
  rintro hc
  rw [totalDegree_eq_zero_iff_eq_C.1 h0, hc, map_zero, zero_mul] at hF0
  exact hF0 rfl

end MvPolynomial

end
