/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Multiplicity

/-!
# Fundamental points and the standard quadratic transformation

The standard quadratic transformation of `ℙ²` is `[x : y : z] ↦ [yz : xz : xy]`. It is defined
off the three *fundamental points* `[1 : 0 : 0]`, `[0 : 1 : 0]`, `[0 : 0 : 1]`, and is an
involution off the *fundamental triangle* `xyz = 0`. On polynomials it is the substitution
`F ↦ F^Q = F(YZ, XZ, XY)`, a ring map that doubles degrees, with `(F^Q)^Q = (XYZ)^n F` for a form
`F` of degree `n`.

## Main definitions

* `PlaneCurves.Projective.fundamentalPoint i`: the point `[eᵢ]` of `ℙ²`.
* `PlaneCurves.Projective.fundamentalTriangle`: the union `V(XYZ)` of the three exceptional
  lines `V(Xᵢ)`.
* `PlaneCurves.Projective.quadraticTransform`: the algebra map `F ↦ F^Q`, over any commutative
  semiring.

## Main results

* `PlaneCurves.Projective.mult_fundamentalPoint_eq_orderAt`: the multiplicity of a form at
  `fundamentalPoint i` is the order at `0` of its dehomogenization at `i`.
* `PlaneCurves.Projective.mult_rename_fundamentalPoint`: permuting the variables moves the
  fundamental points along, with the same multiplicities.
* `PlaneCurves.Projective.IsHomogeneous.quadraticTransform`: `F^Q` is a form of degree `2n`.
* `PlaneCurves.Projective.quadraticTransform_quadraticTransform`: `(F^Q)^Q = (XYZ)^n F`.
* `PlaneCurves.Projective.quadraticTransform_injective`,
  `PlaneCurves.Projective.quadraticTransform_eq_zero_iff`: `F^Q = 0` only for `F = 0`.
* `PlaneCurves.Projective.quadraticTransform_rename`: `F ↦ F^Q` commutes with permutations of
  the variables.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.4
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

section FundamentalPoint

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {n : ℕ}

/-- The fundamental point `[eᵢ]` of `ℙ²`: Fulton's `P'' = [1 : 0 : 0]`, `P' = [0 : 1 : 0]` and
`P = [0 : 0 : 1]` are `fundamentalPoint 0`, `fundamentalPoint 1` and `fundamentalPoint 2`. -/
noncomputable def fundamentalPoint (i : Fin 3) : ℙ k (Fin 3 → k) :=
  mk k (Pi.single i 1) (by simp)

theorem fundamentalPoint_def (i : Fin 3) :
    fundamentalPoint (k := k) i = mk k (Pi.single i 1) (by simp) :=
  (rfl)

theorem fundamentalPoint_injective : Function.Injective (fundamentalPoint (k := k)) :=
  mk_single_injective

@[simp]
theorem fundamentalPoint_inj {i j : Fin 3} :
    fundamentalPoint (k := k) i = fundamentalPoint j ↔ i = j :=
  fundamentalPoint_injective.eq_iff

/-- The fundamental point `[eᵢ]` lies on the exceptional line `V(Xⱼ)` exactly when `i ≠ j`. -/
@[simp]
theorem fundamentalPoint_mem_zeroLocus_X_iff {i j : Fin 3} :
    fundamentalPoint (k := k) i ∈ zeroLocus {X j} ↔ i ≠ j := by
  rw [fundamentalPoint_def, mk_mem_zeroLocus_iff (by simpa using ⟨1, isHomogeneous_X k j⟩)]
  simp [Pi.single_apply, eq_comm]

/-- The fundamental point `[eᵢ]` lies in the standard affine open `Xⱼ ≠ 0` exactly when
`i = j`. -/
@[simp]
theorem fundamentalPoint_mem_affineOpen_iff {i j : Fin 3} :
    fundamentalPoint (k := k) i ∈ affineOpen j ↔ i = j :=
  (mk_single_mem_affineOpen_iff i j).trans eq_comm

/-- The fundamental point `[eᵢ]` is the centre of the standard affine chart at `i`. -/
@[simp]
theorem affineChart_fundamentalPoint (i : Fin 3) :
    affineChart i (fundamentalPoint (k := k) i) = 0 :=
  affineChart_mk_single i

/-- The multiplicity of a form at the fundamental point `[eᵢ]` is the order at the origin of its
dehomogenization at `i`. -/
theorem mult_fundamentalPoint_eq_orderAt (hF : F.IsHomogeneous n) (i : Fin 3) :
    mult F (fundamentalPoint i) = (dehomogenize i F).orderAt 0 := by
  rw [mult_eq_orderAt_dehomogenize hF (fundamentalPoint_mem_affineOpen_iff.2 rfl),
    affineChart_fundamentalPoint]

/-- Renaming the variables by a permutation `σ` moves the fundamental point `[eᵢ]` to
`[e_{σ i}]`, with the same multiplicity. -/
theorem mult_rename_fundamentalPoint (hF : F.IsHomogeneous n) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) : mult (rename σ F) (fundamentalPoint (σ i)) = mult F (fundamentalPoint i) := by
  rw [fundamentalPoint_def, fundamentalPoint_def, mult_mk hF.rename_isHomogeneous, mult_mk hF,
    orderAt_rename σ.injective]
  congr 1
  funext j
  simp [Pi.single_apply, σ.injective.eq_iff]

/-- The fundamental triangle `V(XYZ)`: the union of the three exceptional lines `V(Xᵢ)`, the
points with a zero coordinate. -/
noncomputable def fundamentalTriangle : Set (ℙ k (Fin 3 → k)) :=
  zeroLocus {X 0 * X 1 * X 2}

theorem fundamentalTriangle_def :
    fundamentalTriangle (k := k) = zeroLocus {X 0 * X 1 * X 2} :=
  (rfl)

private theorem isHomogeneous_X_mul_X_mul_X :
    (X 0 * X 1 * X 2 : MvPolynomial (Fin 3) k).IsHomogeneous 3 :=
  ((isHomogeneous_X k 0).mul (isHomogeneous_X k 1)).mul (isHomogeneous_X k 2)

theorem mk_mem_fundamentalTriangle_iff (v : Fin 3 → k) (hv : v ≠ 0) :
    mk k v hv ∈ fundamentalTriangle ↔ ∃ i, v i = 0 := by
  rw [fundamentalTriangle_def,
    mk_mem_zeroLocus_iff (by simpa using ⟨3, isHomogeneous_X_mul_X_mul_X⟩)]
  simp [Fin.exists_fin_succ, or_assoc]

/-- A point lies on the fundamental triangle exactly when one of its coordinates is zero. -/
theorem mem_fundamentalTriangle_iff {P : ℙ k (Fin 3 → k)} :
    P ∈ fundamentalTriangle ↔ ∃ i, P.rep i = 0 := by
  conv_lhs => rw [← P.mk_rep]
  exact mk_mem_fundamentalTriangle_iff _ _

theorem fundamentalPoint_mem_fundamentalTriangle (i : Fin 3) :
    fundamentalPoint (k := k) i ∈ fundamentalTriangle := by
  rw [fundamentalPoint_def, mk_mem_fundamentalTriangle_iff]
  fin_cases i
  exacts [⟨1, by simp⟩, ⟨0, by simp⟩, ⟨0, by simp⟩]

/-- The fundamental triangle is the union of the three exceptional lines. -/
theorem fundamentalTriangle_eq_iUnion :
    fundamentalTriangle (k := k) = ⋃ i, zeroLocus {X i} := by
  ext P
  simp only [Set.mem_iUnion, mem_fundamentalTriangle_iff]
  refine exists_congr fun i ↦ ?_
  rw [mem_zeroLocus_iff_eval_rep (by simpa using ⟨1, isHomogeneous_X k i⟩)]
  simp

end FundamentalPoint

section QuadraticTransform

variable {R : Type*} [CommSemiring R] {F : MvPolynomial (Fin 3) R} {n : ℕ}

/-- The standard quadratic transformation of polynomials, `F ↦ F^Q = F(YZ, XZ, XY)`: the
substitution of `X 1 * X 2`, `X 0 * X 2`, `X 0 * X 1` for `X 0`, `X 1`, `X 2`. -/
noncomputable def quadraticTransform : MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R :=
  bind₁ ![X 1 * X 2, X 0 * X 2, X 0 * X 1]

theorem quadraticTransform_def :
    quadraticTransform (R := R) = bind₁ ![X 1 * X 2, X 0 * X 2, X 0 * X 1] :=
  (rfl)

@[simp]
theorem quadraticTransform_X_zero : quadraticTransform (X 0 : MvPolynomial (Fin 3) R) = X 1 * X 2 :=
  by simp [quadraticTransform_def]

@[simp]
theorem quadraticTransform_X_one : quadraticTransform (X 1 : MvPolynomial (Fin 3) R) = X 0 * X 2 :=
  by simp [quadraticTransform_def]

@[simp]
theorem quadraticTransform_X_two : quadraticTransform (X 2 : MvPolynomial (Fin 3) R) = X 0 * X 1 :=
  by simp [quadraticTransform_def]

/-- `X i ^ Q` is the product of the other two variables. -/
theorem quadraticTransform_X (i : Fin 3) :
    quadraticTransform (X i : MvPolynomial (Fin 3) R) = ∏ j ∈ {i}ᶜ, X j := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  · rw [show ({0}ᶜ : Finset (Fin 3)) = {1, 2} by decide, Finset.prod_pair (by decide)]
    exact quadraticTransform_X_zero
  · rw [show ({1}ᶜ : Finset (Fin 3)) = {0, 2} by decide, Finset.prod_pair (by decide)]
    exact quadraticTransform_X_one
  · rw [show ({2}ᶜ : Finset (Fin 3)) = {0, 1} by decide, Finset.prod_pair (by decide)]
    exact quadraticTransform_X_two

@[simp]
theorem quadraticTransform_C (r : R) : quadraticTransform (C r : MvPolynomial (Fin 3) R) = C r :=
  AlgHom.commutes _ r

/-- Evaluating `F^Q` at `v = (x, y, z)` is evaluating `F` at `(yz, xz, xy)`. -/
theorem eval_quadraticTransform (v : Fin 3 → R) (F : MvPolynomial (Fin 3) R) :
    eval v (quadraticTransform F) = eval ![v 1 * v 2, v 0 * v 2, v 0 * v 1] F := by
  change eval₂Hom (RingHom.id R) v _ = eval₂Hom (RingHom.id R) _ F
  rw [quadraticTransform_def, eval₂Hom_bind₁]
  congr 2
  funext i
  fin_cases i <;> simp

/-- The quadratic transform of a form of degree `n` is a form of degree `2n`. -/
theorem IsHomogeneous.quadraticTransform (hF : F.IsHomogeneous n) :
    (quadraticTransform F).IsHomogeneous (2 * n) := by
  refine hF.aeval _ fun i ↦ ?_
  fin_cases i <;> exact (isHomogeneous_X R _).mul (isHomogeneous_X R _)

private theorem monomial_eq_fin_three (d : Fin 3 →₀ ℕ) (r : R) :
    monomial d r = C r * X 0 ^ d 0 * X 1 ^ d 1 * X 2 ^ d 2 := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_three]
  ring

/-- The quadratic transform of the monomial `X^a Y^b Z^c` is `X^(b+c) Y^(a+c) Z^(a+b)`. -/
theorem quadraticTransform_monomial (d : Fin 3 →₀ ℕ) (r : R) :
    quadraticTransform (monomial d r) =
      monomial (Finsupp.equivFunOnFinite.symm ![d 1 + d 2, d 0 + d 2, d 0 + d 1]) r := by
  rw [monomial_eq_fin_three, monomial_eq_fin_three]
  simp only [map_mul, map_pow, quadraticTransform_C, quadraticTransform_X_zero,
    quadraticTransform_X_one, quadraticTransform_X_two, Finsupp.coe_equivFunOnFinite_symm]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

private theorem injective_quadraticExponent :
    Function.Injective fun d : Fin 3 →₀ ℕ ↦
      Finsupp.equivFunOnFinite.symm ![d 1 + d 2, d 0 + d 2, d 0 + d 1] := by
  intro d d' h
  have h0 := congrArg (· 0) h
  have h1 := congrArg (· 1) h
  have h2 := congrArg (· 2) h
  simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  ext i
  fin_cases i <;> simp <;> omega

/-- The coefficient of `X^(b+c) Y^(a+c) Z^(a+b)` in `F^Q` is the coefficient of `X^a Y^b Z^c`
in `F`. -/
theorem coeff_quadraticTransform (d : Fin 3 →₀ ℕ) (F : MvPolynomial (Fin 3) R) :
    (quadraticTransform F).coeff
        (Finsupp.equivFunOnFinite.symm ![d 1 + d 2, d 0 + d 2, d 0 + d 1]) =
      F.coeff d := by
  conv_lhs => rw [F.as_sum]
  simp only [map_sum, quadraticTransform_monomial, coeff_sum, coeff_monomial,
    injective_quadraticExponent.eq_iff]
  simp [eq_comm]

theorem quadraticTransform_injective :
    Function.Injective (quadraticTransform : MvPolynomial (Fin 3) R → MvPolynomial (Fin 3) R) :=
  fun F G h ↦ ext _ _ fun d ↦ by rw [← coeff_quadraticTransform, h, coeff_quadraticTransform]

@[simp]
theorem quadraticTransform_eq_zero_iff : quadraticTransform F = 0 ↔ F = 0 :=
  map_eq_zero_iff _ quadraticTransform_injective

/-- **The quadratic transformation is an involution on forms**: for a form `F` of degree `n`,
`(F^Q)^Q = (XYZ)^n F`. -/
theorem quadraticTransform_quadraticTransform (hF : F.IsHomogeneous n) :
    quadraticTransform (quadraticTransform F) = (X 0 * X 1 * X 2) ^ n * F := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, quadraticTransform_monomial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hn := hF (mem_support_iff.1 hd)
  simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one] at hn
  rw [Finsupp.sum_fintype _ _ fun _ ↦ rfl, Fin.sum_univ_three] at hn
  subst hn
  rw [monomial_eq_fin_three, monomial_eq_fin_three]
  simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The quadratic transformation commutes with every permutation of the variables. -/
theorem quadraticTransform_rename (σ : Equiv.Perm (Fin 3)) (F : MvPolynomial (Fin 3) R) :
    quadraticTransform (rename σ F) = rename σ (quadraticTransform F) := by
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  refine algHom_ext fun i ↦ ?_
  simp only [AlgHom.comp_apply, rename_X, quadraticTransform_X, map_prod]
  exact (Finset.prod_equiv σ (by simp) fun _ _ ↦ rfl).symm

/-- The identity `(F^Q)^Q = (XYZ) F` for the line `F = X + Y + Z`. -/
example :
    quadraticTransform (quadraticTransform (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) ℚ)) =
      X 0 * X 1 * X 2 * (X 0 + X 1 + X 2) := by
  simp only [map_add, quadraticTransform_X_zero, quadraticTransform_X_one,
    quadraticTransform_X_two, map_mul]
  ring

end QuadraticTransform

end PlaneCurves.Projective

end
