/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Singular
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.LinearSubvariety
public import PlaneCurves.RingTheory.MvPolynomial.LinearSubst
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Irreducible conics

A conic is a form of degree two in `k[X, Y, Z]`. Over an algebraically closed field `k`, every
irreducible conic is projectively equivalent to `YZ = X²`, and so is nonsingular (Fulton,
Problem 5.9), in every characteristic. The proof puts a point of the conic at `[0 : 1 : 0]`, so
that the form is `Y ℓ(X, Z) + q(X, Z)`; irreducibility forces `ℓ ≠ 0`, a change of coordinates
in `X, Z` makes `ℓ = Z`, a substitution `Y ↦ Y + αX + βZ` removes all of `q` but its
`X²` term, which irreducibility makes nonzero, and a rescaling of `X` normalizes it.

Changes of coordinates are Tau Ceti's `MvPolynomial.linearSubst M`, `F ↦ F(M X)`, along a matrix
`M` with `M.mulVecLin` injective, as in the rest of the library.

## Main results

* `MvPolynomial.IsHomogeneous.eq_of_fin_three_two`: a form of degree two in three variables is
  `a X² + b Y² + c Z² + d XY + e XZ + f YZ`.
* `PlaneCurves.Projective.isNonsingular_X_mul_X_sub_X_sq`,
  `PlaneCurves.Projective.irreducible_X_mul_X_sub_X_sq`: the conic `YZ - X²` is nonsingular,
  and irreducible over an algebraically closed field.
* `PlaneCurves.Projective.exists_linearSubst_eq_X_mul_X_sub_X_sq`: an irreducible conic over an
  algebraically closed field is carried to `YZ - X²` by a change of coordinates.
* `PlaneCurves.Projective.isNonsingular_of_irreducible_of_isHomogeneous_two`: irreducible conics
  are nonsingular.
* `PlaneCurves.Projective.irreducible_iff_exists_linearSubst_eq_X_mul_X_sub_X_sq`: a conic is
  irreducible exactly when it is projectively equivalent to `YZ - X²`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.1, Problem 5.9
-/

public section

namespace MvPolynomial

variable {k : Type*} [CommSemiring k]

/-- A form of degree two in three variables is `a X² + b Y² + c Z² + d XY + e XZ + f YZ`, with
its coefficients `a, …, f`. -/
theorem IsHomogeneous.eq_of_fin_three_two {F : MvPolynomial (Fin 3) k} (hF : F.IsHomogeneous 2) :
    F = C (F.coeff (Finsupp.single 0 2)) * X 0 ^ 2 + C (F.coeff (Finsupp.single 1 2)) * X 1 ^ 2 +
      C (F.coeff (Finsupp.single 2 2)) * X 2 ^ 2 +
      C (F.coeff (Finsupp.single 0 1 + Finsupp.single 1 1)) * (X 0 * X 1) +
      C (F.coeff (Finsupp.single 0 1 + Finsupp.single 2 1)) * (X 0 * X 2) +
      C (F.coeff (Finsupp.single 1 1 + Finsupp.single 2 1)) * (X 1 * X 2) := by
  ext n
  simp only [X_pow_eq_monomial]
  simp only [X, monomial_mul_monomial, C_mul_monomial, AddMonoidAlgebra.coeff_add, Finsupp.coe_add,
    Pi.add_apply, coeff_monomial, mul_one]
  by_cases h : n.degree = 2
  · have e : n = Finsupp.single 0 (n 0) + Finsupp.single 1 (n 1) + Finsupp.single 2 (n 2) := by
      ext i; fin_cases i <;> simp
    have hs : n 0 + n 1 + n 2 = 2 := by
      simpa [Finsupp.degree_eq_sum, Fin.sum_univ_three] using h
    generalize n 0 = a, n 1 = b, n 2 = c at e hs
    subst e
    have : a ≤ 2 := by omega
    have : b ≤ 2 := by omega
    have : c ≤ 2 := by omega
    interval_cases a <;> interval_cases b <;> interval_cases c <;> simp at hs <;>
      simp [Finsupp.ext_iff, Fin.forall_fin_succ, Finsupp.single_apply]
  · have : F.coeff n = 0 := by
      by_contra h'
      exact h (by rw [Finsupp.degree_eq_weight_one]; exact hF h')
    rw [this]
    have hm : ∀ m : Fin 3 →₀ ℕ, m.degree = 2 → m ≠ n := fun m hm e ↦ h (e ▸ hm)
    simp [hm, Finsupp.degree_single]

end MvPolynomial

namespace PlaneCurves.Projective

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization Matrix

variable {k : Type*} [Field k]

/-- A product of two polynomials that vanish at the origin is not irreducible. -/
private theorem not_irreducible_mul {p q : MvPolynomial (Fin 3) k} (hp : eval 0 p = 0)
    (hq : eval 0 q = 0) : ¬Irreducible (p * q) := fun h ↦ by
  rcases h.isUnit_or_isUnit rfl with h | h
  · exact (h.map (eval 0)).ne_zero hp
  · exact (h.map (eval 0)).ne_zero hq

private theorem isUnit_det_of_injective {M : Matrix (Fin 3) (Fin 3) k}
    (hM : Function.Injective M.mulVecLin) : IsUnit M.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]; exact hM

private theorem injective_mulVecLin {M : Matrix (Fin 3) (Fin 3) k} (hM : M.det ≠ 0) :
    Function.Injective M.mulVecLin := by
  rw [Matrix.coe_mulVecLin, Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]
  exact hM.isUnit

private theorem injective_mulVecLin_mul {M N : Matrix (Fin 3) (Fin 3) k}
    (hM : Function.Injective M.mulVecLin) (hN : Function.Injective N.mulVecLin) :
    Function.Injective (M * N).mulVecLin := by
  rw [Matrix.mulVecLin_mul, LinearMap.coe_comp]
  exact hM.comp hN

/-- The conic `YZ - X²` is nonsingular, in every characteristic. -/
theorem isNonsingular_X_mul_X_sub_X_sq :
    IsNonsingular (X 1 * X 2 - X 0 ^ 2 : MvPolynomial (Fin 3) k) := by
  rw [isNonsingular_def]
  intro v hv h0
  by_cases h2 : v 2 = 0
  · by_cases h1 : v 1 = 0
    · refine absurd (funext fun i ↦ ?_) hv
      have : v 0 = 0 := by simpa [h1] using h0
      fin_cases i <;> simp [*]
    · exact ⟨2, by simpa [pderiv_X] using h1⟩
  · exact ⟨1, by simpa [pderiv_X] using h2⟩

variable [IsAlgClosed k]

/-- Over an algebraically closed field a binary quadratic form `a X² + e XZ + c Z²` is a product
of two linear forms, so it is not irreducible. -/
private theorem not_irreducible_binary (a e c : k) :
    ¬Irreducible (C a * X 0 ^ 2 + C e * (X 0 * X 2) + C c * X 2 ^ 2 : MvPolynomial (Fin 3) k) := by
  by_cases ha : a = 0
  · have : (C a * X 0 ^ 2 + C e * (X 0 * X 2) + C c * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
        X 2 * (C e * X 0 + C c * X 2) := by
      subst ha; simp; ring
    rw [this]
    exact not_irreducible_mul (by simp) (by simp)
  · obtain ⟨t, ht⟩ := IsAlgClosed.exists_root (Polynomial.C a * Polynomial.X ^ 2 +
      Polynomial.C e * Polynomial.X + Polynomial.C c) (by rw [Polynomial.degree_quadratic ha]; simp)
    have ht : a * t ^ 2 + e * t + c = 0 := by simpa using ht
    have : (C a * X 0 ^ 2 + C e * (X 0 * X 2) + C c * X 2 ^ 2 : MvPolynomial (Fin 3) k) =
        (X 0 - C t * X 2) * (C a * X 0 + C (e + a * t) * X 2) := by
      refine MvPolynomial.funext fun x ↦ ?_
      simp only [map_add, map_mul, map_sub, map_pow, eval_C, eval_X]
      linear_combination (x 2 ^ 2) * ht
    rw [this]
    exact not_irreducible_mul (by simp) (by simp)

/-- An irreducible form `YZ + a X² + e XZ + c Z²` is carried to `YZ - X²` by a change of
coordinates. -/
private theorem exists_linearSubst_eq_of_mul_add {a e c : k}
    (h : Irreducible (X 1 * X 2 + C a * X 0 ^ 2 + C e * (X 0 * X 2) + C c * X 2 ^ 2 :
      MvPolynomial (Fin 3) k)) :
    ∃ M : Matrix (Fin 3) (Fin 3) k, Function.Injective M.mulVecLin ∧
      linearSubst M (X 1 * X 2 + C a * X 0 ^ 2 + C e * (X 0 * X 2) + C c * X 2 ^ 2) =
        X 1 * X 2 - X 0 ^ 2 := by
  have ha : a ≠ 0 := by
    rintro rfl
    refine not_irreducible_mul (p := X 2) (q := X 1 + C e * X 0 + C c * X 2) (by simp) (by simp) ?_
    convert h using 1
    simp; ring
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (-a⁻¹) two_pos
  have hs' : a * s ^ 2 = -1 := by rw [hs]; field_simp
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs'
  refine ⟨!![s, 0, 0; -e * s, 1, -c; 0, 0, 1], injective_mulVecLin (by simp [Matrix.det_fin_three,
    hs0]), MvPolynomial.funext fun x ↦ ?_⟩
  simp [Fin.sum_univ_three]
  linear_combination (x 0 ^ 2) * hs'

/-- An irreducible form `a X² + c Z² + d XY + e XZ + f YZ`, one that vanishes at `[0 : 1 : 0]`, is
carried to `YZ - X²` by a change of coordinates. -/
private theorem exists_linearSubst_eq_of_coeff_eq_zero {a c d e f : k}
    (h : Irreducible (C a * X 0 ^ 2 + C c * X 2 ^ 2 + C d * (X 0 * X 1) + C e * (X 0 * X 2) +
      C f * (X 1 * X 2) : MvPolynomial (Fin 3) k)) :
    ∃ M : Matrix (Fin 3) (Fin 3) k, Function.Injective M.mulVecLin ∧
      linearSubst M (C a * X 0 ^ 2 + C c * X 2 ^ 2 + C d * (X 0 * X 1) + C e * (X 0 * X 2) +
        C f * (X 1 * X 2)) = X 1 * X 2 - X 0 ^ 2 := by
  set G : MvPolynomial (Fin 3) k :=
    C a * X 0 ^ 2 + C c * X 2 ^ 2 + C d * (X 0 * X 1) + C e * (X 0 * X 2) + C f * (X 1 * X 2)
  -- First carry `G` to `YZ + a' X² + e' XZ + c' Z²`.
  obtain ⟨M, hM, a', e', c', hMG⟩ : ∃ M : Matrix (Fin 3) (Fin 3) k,
      Function.Injective M.mulVecLin ∧
      ∃ a' e' c' : k, linearSubst M G =
        X 1 * X 2 + C a' * X 0 ^ 2 + C e' * (X 0 * X 2) + C c' * X 2 ^ 2 := by
    by_cases hf : f = 0
    · by_cases hd : d = 0
      · refine absurd h ?_
        convert not_irreducible_binary a e c using 2
        simp [G, hf, hd]; ring
      refine ⟨!![0, 0, 1 / d; 0, 1, 0; 1, 0, 0], injective_mulVecLin (by
        simp [Matrix.det_fin_three, hd]), c, e / d, a / d ^ 2, MvPolynomial.funext fun x ↦ ?_⟩
      simp [G, hf, Fin.sum_univ_three]
      field_simp
      ring
    · refine ⟨!![1, 0, 0; 0, 1, 0; -d / f, 0, 1 / f], injective_mulVecLin (by
        simp [Matrix.det_fin_three, hf]), a - e * d / f + c * d ^ 2 / f ^ 2,
        e / f - 2 * c * d / f ^ 2, c / f ^ 2, MvPolynomial.funext fun x ↦ ?_⟩
      simp [G, Fin.sum_univ_three]
      field_simp
      ring
  -- Then normalize it.
  have hG : Irreducible (linearSubst M G) :=
    (irreducible_linearSubst_iff (isUnit_det_of_injective hM)).2 h
  rw [hMG] at hG
  obtain ⟨N, hN, hNG⟩ := exists_linearSubst_eq_of_mul_add hG
  exact ⟨M * N, injective_mulVecLin_mul hM hN, by rw [linearSubst_mul_apply, hMG, hNG]⟩

/-- The conic `YZ - X²` is irreducible, over an algebraically closed field. -/
theorem irreducible_X_mul_X_sub_X_sq :
    Irreducible (X 1 * X 2 - X 0 ^ 2 : MvPolynomial (Fin 3) k) :=
  isNonsingular_X_mul_X_sub_X_sq.irreducible
    (((isHomogeneous_X k 1).mul (isHomogeneous_X k 2)).sub ((isHomogeneous_X k 0).pow 2))
    two_ne_zero

/-- **Normal form of an irreducible conic.** Over an algebraically closed field, an irreducible
form `F` of degree two is projectively equivalent to `YZ - X²`: some invertible change of
coordinates carries `F` to `YZ - X²` exactly (Fulton, Problem 5.9; every characteristic). -/
theorem exists_linearSubst_eq_X_mul_X_sub_X_sq {F : MvPolynomial (Fin 3) k}
    (hF : F.IsHomogeneous 2) (h : Irreducible F) :
    ∃ M : Matrix (Fin 3) (Fin 3) k, Function.Injective M.mulVecLin ∧
      linearSubst M F = X 1 * X 2 - X 0 ^ 2 := by
  -- Move a point of `F` to `[0 : 1 : 0]`.
  obtain ⟨P, hP⟩ := zeroLocus_singleton_nonempty (n := 2) two_ne_zero hF two_ne_zero
  have he : (Pi.single 1 1 : Fin 3 → k) ≠ 0 := by simp
  obtain ⟨M, hM, hMP⟩ := exists_mulVecLin_map_eq (mk k _ he) P
  rw [← hMP, map_mk, mk_mem_zeroLocus_iff (by simpa using ⟨2, hF⟩)] at hP
  have h0 : eval (M *ᵥ Pi.single 1 1) F = 0 := by simpa using hP
  set G := linearSubst M F with hGdef
  have hG : G.IsHomogeneous 2 := hF.linearSubst M
  have hGe := hG.eq_of_fin_three_two
  -- There `G` has no `Y²` term.
  have hb : G.coeff (Finsupp.single 1 2) = 0 := by
    have : eval (Pi.single 1 1) G = G.coeff (Finsupp.single 1 2) := by
      conv_lhs => rw [hGe]
      simp
    rw [← this, hGdef, eval_linearSubst, h0]
  rw [hb, map_zero, zero_mul, add_zero] at hGe
  have hGe' : G = C (G.coeff (Finsupp.single 0 2)) * X 0 ^ 2 +
      C (G.coeff (Finsupp.single 2 2)) * X 2 ^ 2 +
      C (G.coeff (Finsupp.single 0 1 + Finsupp.single 1 1)) * (X 0 * X 1) +
      C (G.coeff (Finsupp.single 0 1 + Finsupp.single 2 1)) * (X 0 * X 2) +
      C (G.coeff (Finsupp.single 1 1 + Finsupp.single 2 1)) * (X 1 * X 2) := hGe
  have hGi : Irreducible G := (irreducible_linearSubst_iff (isUnit_det_of_injective hM)).2 h
  rw [hGe'] at hGi
  obtain ⟨N, hN, hNG⟩ := exists_linearSubst_eq_of_coeff_eq_zero hGi
  refine ⟨M * N, injective_mulVecLin_mul hM hN, ?_⟩
  rw [linearSubst_mul_apply, ← hGdef, hGe', hNG]

/-- **Irreducible conics are nonsingular.** Over an algebraically closed field, an irreducible
form of degree two is nonsingular (Fulton, Problem 5.9; every characteristic). -/
theorem isNonsingular_of_irreducible_of_isHomogeneous_two {F : MvPolynomial (Fin 3) k}
    (hF : F.IsHomogeneous 2) (h : Irreducible F) : IsNonsingular F := by
  obtain ⟨M, hM, hMF⟩ := exists_linearSubst_eq_X_mul_X_sub_X_sq hF h
  rw [← isNonsingular_linearSubst_iff hM, hMF]
  exact isNonsingular_X_mul_X_sub_X_sq

/-- Over an algebraically closed field, a form of degree two is irreducible exactly when some
invertible change of coordinates carries it to `YZ - X²`. -/
theorem irreducible_iff_exists_linearSubst_eq_X_mul_X_sub_X_sq {F : MvPolynomial (Fin 3) k}
    (hF : F.IsHomogeneous 2) :
    Irreducible F ↔ ∃ M : Matrix (Fin 3) (Fin 3) k, Function.Injective M.mulVecLin ∧
      linearSubst M F = X 1 * X 2 - X 0 ^ 2 := by
  refine ⟨exists_linearSubst_eq_X_mul_X_sub_X_sq hF, fun ⟨M, hM, hMF⟩ ↦ ?_⟩
  rw [← irreducible_linearSubst_iff (isUnit_det_of_injective hM), hMF]
  exact irreducible_X_mul_X_sub_X_sq

end PlaneCurves.Projective

end
