/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.Monad
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Multiplicity
public import PlaneCurves.RingTheory.MvPolynomial.Homogeneous

/-!
# Fundamental points and the standard quadratic transformation

The standard quadratic transformation of `ℙ²` is `[x : y : z] ↦ [yz : xz : xy]`. It is defined
off the three *fundamental points* `[1 : 0 : 0]`, `[0 : 1 : 0]`, `[0 : 0 : 1]`, and is an
involution off the *fundamental triangle* `xyz = 0`. On polynomials it is the substitution
`F ↦ F^Q = F(YZ, XZ, XY)`, a ring map that doubles degrees, with `(F^Q)^Q = (XYZ)^n F` for a form
`F` of degree `n`.

Fulton's step (1): `F^Q = X^r₀ Y^r₁ Z^r₂ F'`, where `rᵢ` is the multiplicity of `F` at the
fundamental point `[eᵢ]` and no `Xᵢ` divides the *proper transform* `F'`. It holds for every
nonzero form. It is proved at `Z` from the expansion `F^Q = ∑ⱼ Z^j Gⱼ(Y, X) (XY)^(n - j)`, and at
the other two lines by permuting the variables.

Steps (2) and (3), for a form with no exceptional component, compare the powers of each `Xᵢ` in
`X^r₀ Y^r₁ Z^r₂ (F')^Q = (F^Q)^Q = (XYZ)^n F`: the multiplicity of `F'` at `[eᵢ]` is
`n - rⱼ - rₗ`, and cancelling the monomials gives `(F')' = F`.

## Main definitions

* `PlaneCurves.Projective.fundamentalPoint i`: the point `[eᵢ]` of `ℙ²`.
* `PlaneCurves.Projective.fundamentalTriangle`: the union `V(XYZ)` of the three exceptional
  lines `V(Xᵢ)`.
* `PlaneCurves.Projective.quadraticTransform`: the algebra map `F ↦ F^Q`, over any commutative
  semiring.
* `PlaneCurves.Projective.exceptionalExponent`: the exponents `(r₀, r₁, r₂)` of the exceptional
  factor of `F^Q`.
* `PlaneCurves.Projective.properTransform`: the proper transform `F' = F^Q / (X^r₀ Y^r₁ Z^r₂)`.

## Main results

* `PlaneCurves.Projective.mult_fundamentalPoint_eq_orderAt`: the multiplicity of a form at
  `fundamentalPoint i` is the order at `0` of its dehomogenization at `i`.
* `PlaneCurves.Projective.mult_rename_fundamentalPoint`: permuting the variables moves the
  fundamental points along, with the same multiplicities.
* `MvPolynomial.IsHomogeneous.quadraticTransform`: `F^Q` is a form of degree `2n`.
* `PlaneCurves.Projective.quadraticTransform_quadraticTransform`: `(F^Q)^Q = (XYZ)^n F`.
* `PlaneCurves.Projective.quadraticTransform_injective`,
  `PlaneCurves.Projective.quadraticTransform_eq_zero_iff`: `F^Q = 0` only for `F = 0`.
* `PlaneCurves.Projective.quadraticTransform_rename`: `F ↦ F^Q` commutes with permutations of
  the variables.
* `PlaneCurves.Projective.quadraticTransform_eq_sum`: the expansion of `F^Q` at `Z`.
* `PlaneCurves.Projective.multiplicity_X_quadraticTransform`,
  `PlaneCurves.Projective.not_X_dvd_properTransform`,
  `PlaneCurves.Projective.quadraticTransform_eq`:
  step (1), `F^Q = X^r₀ Y^r₁ Z^r₂ F'` with `X^rᵢ` the exact power of `Xᵢ` dividing `F^Q`.
* `MvPolynomial.IsHomogeneous.properTransform`: `F'` is a form of degree `2n - r₀ - r₁ - r₂`.
* `PlaneCurves.Projective.properTransform_mul`, `PlaneCurves.Projective.properTransform_rename`:
  the proper transform is multiplicative on forms and commutes with permutations of the variables.
* `PlaneCurves.Projective.aeval_X_two_eq_zero_properTransform`: the restriction of `F'` to the
  line `Z = 0`, in terms of the tangent cone of `F` at `[0 : 0 : 1]`.
* `PlaneCurves.Projective.quadraticTransform_properTransform`,
  `PlaneCurves.Projective.properTransform_properTransform`: step (2) for a form `F` with no
  exceptional component, `(F')^Q = X^(n - r₁ - r₂) Y^(n - r₀ - r₂) Z^(n - r₀ - r₁) F` and
  `(F')' = F`.
* `PlaneCurves.Projective.irreducible_properTransform`,
  `PlaneCurves.Projective.dvd_quadraticTransform_iff`: for `F` irreducible as well, `F'` is
  irreducible, and `F' ∣ H^Q ↔ F ∣ H`.
* `PlaneCurves.Projective.mult_properTransform_fundamentalPoint_add`,
  `PlaneCurves.Projective.mult_properTransform_fundamentalPoint`: step (3),
  `m_{[eᵢ]}(F') = n - m_{[eⱼ]}(F) - m_{[eₗ]}(F)`.

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

/-- The class of `v` is the fundamental point `[eᵢ]` exactly when every other coordinate of `v`
is zero. -/
theorem mk_eq_fundamentalPoint_iff (v : Fin 3 → k) (hv : v ≠ 0) (i : Fin 3) :
    mk k v hv = fundamentalPoint i ↔ ∀ j, j ≠ i → v j = 0 := by
  rw [fundamentalPoint_def, mk_eq_mk_iff']
  refine ⟨fun ⟨a, ha⟩ j hj ↦ by simp [← ha, hj], fun h ↦ ⟨v i, ?_⟩⟩
  funext j
  by_cases hj : j = i
  · simp [hj]
  · simp [hj, h j hj]

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
theorem _root_.MvPolynomial.IsHomogeneous.quadraticTransform (hF : F.IsHomogeneous n) :
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

/-- The component of degree `2e` of `H^Q` is the quadratic transform of the component of degree
`e` of `H`. -/
theorem homogeneousComponent_quadraticTransform (e : ℕ) (H : MvPolynomial (Fin 3) R) :
    homogeneousComponent (2 * e) (quadraticTransform H) =
      quadraticTransform (homogeneousComponent e H) := by
  conv_lhs => rw [← sum_homogeneousComponent H]
  rw [map_sum, map_sum]
  have hc (j : ℕ) := homogeneousComponent_of_mem (m := 2 * e)
    ((homogeneousComponent_isHomogeneous j H).quadraticTransform)
  simp only [hc, mul_right_inj' two_ne_zero, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [homogeneousComponent_eq_zero _ _ (by omega), map_zero]

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

section Expansion

variable {R : Type*} [CommSemiring R] {F : MvPolynomial (Fin 3) R} {n : ℕ}

/-- For a binary form `G(X, Y)` of degree `j`, `G(X, Y)^Q = G(YZ, XZ) = Z ^ j G(Y, X)`. -/
theorem quadraticTransform_rename_succAbove_two {G : MvPolynomial (Fin 2) R} {j : ℕ}
    (hG : G.IsHomogeneous j) :
    quadraticTransform (rename (Fin.succAbove 2) G) = X 2 ^ j * rename ![1, 0] G := by
  have h : quadraticTransform.comp (rename (Fin.succAbove (2 : Fin 3))) =
      aeval fun i ↦ X 2 * (X (![1, 0] i) : MvPolynomial (Fin 3) R) := by
    refine algHom_ext fun i ↦ ?_
    fin_cases i <;> simp [mul_comm, Fin.succAbove, Fin.lt_def]
  rw [← AlgHom.comp_apply, h, hG.aeval_mul_left, ← aeval_X_left_apply (rename _ G), aeval_rename]
  rfl

/-- **The expansion of `F^Q` at `Z`.** Writing a form `F` of degree `n` as
`F = ∑ⱼ Gⱼ(X, Y) Z^(n - j)` with `Gⱼ` the degree `j` part of `F(X, Y, 1)`, its quadratic
transform is `F^Q = ∑ⱼ Z^j Gⱼ(Y, X) (XY)^(n - j)`. -/
theorem quadraticTransform_eq_sum (hF : F.IsHomogeneous n) :
    quadraticTransform F = ∑ j ∈ Finset.range (n + 1), X 2 ^ j *
      rename ![1, 0] (homogeneousComponent j (dehomogenize 2 F)) * (X 0 * X 1) ^ (n - j) := by
  conv_lhs => rw [← homogenize_dehomogenize (i := 2) hF, homogenize_def]
  simp only [map_sum, map_mul, map_pow, ← rename_homogeneousComponent]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [quadraticTransform_rename_succAbove_two (homogeneousComponent_isHomogeneous j _),
    quadraticTransform_X_two]

end Expansion

section ProperTransform

variable {k : Type*} [Field k] {F G : MvPolynomial (Fin 3) k} {n m : ℕ}

/-- The multiplicity of the line `V(Xᵢ)` at the fundamental point `[eⱼ]` is `0` for `j = i`
and `1` otherwise. -/
theorem mult_X_fundamentalPoint (i j : Fin 3) :
    mult (X i : MvPolynomial (Fin 3) k) (fundamentalPoint j) = if j = i then 0 else 1 := by
  split_ifs with h
  · subst h
    exact (mult_eq_zero_iff (isHomogeneous_X k j)).2 (by simp)
  · refine le_antisymm (by simpa using mult_le_degree (isHomogeneous_X k i) (X_ne_zero i) _) ?_
    exact Order.one_le_iff_pos.2 ((mult_pos_iff (isHomogeneous_X k i)).2 (by simpa using h))

private theorem aeval_X_two_zero_rename (p : MvPolynomial (Fin 2) k) :
    aeval (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) (rename ![1, 0] p) =
      rename ![1, 0] p := by
  have h : (aeval (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k)).comp (rename ![1, 0]) =
      rename (R := k) (![1, 0] : Fin 2 → Fin 3) :=
    algHom_ext fun i ↦ by fin_cases i <;> simp
  simpa using AlgHom.congr_fun h p

/-- `F^Q = Z ^ r H`, with `r` the multiplicity of `F` at `[0 : 0 : 1]` and
`H(X, Y, 0) = (XY)^(n - r) G_r(Y, X)` for the leading form `G_r` of `F(X, Y, 1)` at `0`. -/
private theorem exists_quadraticTransform_eq_X_two_pow_mul (hF : F.IsHomogeneous n)
    (hF0 : F ≠ 0) :
    ∃ H, quadraticTransform F = X 2 ^ (mult F (fundamentalPoint 2)).toNat * H ∧
      aeval (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) H =
        (X 0 * X 1) ^ (n - (mult F (fundamentalPoint 2)).toNat) *
          rename ![1, 0] (leadingFormAt (dehomogenize 2 F) 0) := by
  set r := (mult F (fundamentalPoint 2)).toNat with hr
  have hrn : r ≤ n := ENat.toNat_le_of_le_natCast (mult_le_degree hF hF0 _)
  have hr' : (r : ℕ∞) = (dehomogenize 2 F).orderAt 0 := by
    rw [hr, ENat.natCast_toNat (mult_eq_top_iff.not.2 hF0), mult_fundamentalPoint_eq_orderAt hF]
  have hlt : ∀ j < r, homogeneousComponent j (dehomogenize 2 F) = 0 := fun j hj ↦ by
    simpa [taylor_zero] using le_orderAt_iff_homogeneousComponent.1 hr'.le j hj
  refine ⟨∑ j ∈ Finset.Ico r (n + 1), X 2 ^ (j - r) *
    rename ![1, 0] (homogeneousComponent j (dehomogenize 2 F)) * (X 0 * X 1) ^ (n - j), ?_, ?_⟩
  · rw [quadraticTransform_eq_sum hF, ← Finset.sum_range_add_sum_Ico _ (by omega : r ≤ n + 1),
      Finset.sum_eq_zero fun j hj ↦ by rw [hlt j (Finset.mem_range.1 hj)]; simp, zero_add,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [← mul_assoc, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' (Finset.mem_Ico.1 hj).1]
  · rw [map_sum, Finset.sum_eq_single_of_mem r (by simp; omega)]
    · simp only [map_mul, map_pow, aeval_X_two_zero_rename]
      simp [leadingFormAt_def, taylor_zero, ← hr', mul_comm]
    · intro j hj hjr
      have : j - r ≠ 0 := by simp at hj; omega
      simp [zero_pow this]

private theorem emultiplicity_X_two_quadraticTransform (hF : F.IsHomogeneous n) (hF0 : F ≠ 0) :
    emultiplicity (X 2) (quadraticTransform F) = (mult F (fundamentalPoint 2)).toNat := by
  obtain ⟨H, hFH, hH⟩ := exists_quadraticTransform_eq_X_two_pow_mul hF hF0
  refine emultiplicity_eq_of_dvd_of_not_dvd (hFH ▸ dvd_mul_right _ _) ?_
  rw [hFH, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ (X_ne_zero _))]
  have hne : (X 0 * X 1 : MvPolynomial (Fin 3) k) ^ (n - (mult F (fundamentalPoint 2)).toNat) *
      rename ![1, 0] (leadingFormAt (dehomogenize 2 F) 0) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (mul_ne_zero (X_ne_zero _) (X_ne_zero _)))
      ((map_ne_zero_iff _ (rename_injective _ (by decide))).2
        (leadingFormAt_ne_zero (dehomogenize_ne_zero_of_isHomogeneous 2 hF hF0)))
  rintro ⟨K, rfl⟩
  apply hne
  rw [← hH]
  simp

/-- **(1), the exact power**, as an `emultiplicity`: the largest power of `Xᵢ` dividing the
quadratic transform of a nonzero form is its multiplicity at the fundamental point `[eᵢ]`. -/
theorem emultiplicity_X_quadraticTransform (hF : F.IsHomogeneous n) (hF0 : F ≠ 0) (i : Fin 3) :
    emultiplicity (X i) (quadraticTransform F) = (mult F (fundamentalPoint i)).toNat := by
  have hσ : Equiv.swap i 2 i = 2 := Equiv.swap_apply_left _ _
  have hm := mult_rename_fundamentalPoint hF (Equiv.swap i 2) i
  rw [hσ] at hm
  have h := emultiplicity_X_two_quadraticTransform (hF.rename_isHomogeneous (f := Equiv.swap i 2))
    ((map_ne_zero_iff _ (rename_injective _ (Equiv.injective _))).2 hF0)
  rw [quadraticTransform_rename, hm, ← hσ, ← rename_X, hσ] at h
  have he := emultiplicity_map_eq (renameEquiv k (Equiv.swap i 2)) (a := X i)
    (b := quadraticTransform F)
  rwa [renameEquiv_apply, renameEquiv_apply, h, eq_comm] at he

/-- **(1), the exact power.** The largest power of `Xᵢ` dividing the quadratic transform of a
nonzero form is its multiplicity at the fundamental point `[eᵢ]`. -/
theorem multiplicity_X_quadraticTransform (hF : F.IsHomogeneous n) (hF0 : F ≠ 0) (i : Fin 3) :
    multiplicity (X i) (quadraticTransform F) = (mult F (fundamentalPoint i)).toNat :=
  multiplicity_eq_of_emultiplicity_eq_some (emultiplicity_X_quadraticTransform hF hF0 i)

/-- `Xᵢ ^ rᵢ` divides the quadratic transform of a form, `rᵢ` its multiplicity at `[eᵢ]`. -/
theorem X_pow_dvd_quadraticTransform (hF : F.IsHomogeneous n) (i : Fin 3) :
    X i ^ (mult F (fundamentalPoint i)).toNat ∣ quadraticTransform F := by
  obtain rfl | hF0 := eq_or_ne F 0
  · simp
  exact pow_dvd_of_le_emultiplicity (emultiplicity_X_quadraticTransform hF hF0 i).ge

/-- The exponents of the exceptional factor of `F^Q`: the exponent of `Xᵢ` is the multiplicity
of `F` at the fundamental point `[eᵢ]` off the line `V(Xᵢ)`. -/
noncomputable def exceptionalExponent (F : MvPolynomial (Fin 3) k) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i ↦ (mult F (fundamentalPoint i)).toNat

theorem exceptionalExponent_def (F : MvPolynomial (Fin 3) k) :
    exceptionalExponent F =
      Finsupp.equivFunOnFinite.symm fun i ↦ (mult F (fundamentalPoint i)).toNat :=
  (rfl)

@[simp]
theorem exceptionalExponent_apply (F : MvPolynomial (Fin 3) k) (i : Fin 3) :
    exceptionalExponent F i = (mult F (fundamentalPoint i)).toNat := by
  simp [exceptionalExponent_def]

/-- The exceptional monomial is `X^r₀ Y^r₁ Z^r₂`. -/
theorem monomial_exceptionalExponent (F : MvPolynomial (Fin 3) k) :
    monomial (exceptionalExponent F) (1 : k) =
      X 0 ^ (mult F (fundamentalPoint 0)).toNat * X 1 ^ (mult F (fundamentalPoint 1)).toNat *
        X 2 ^ (mult F (fundamentalPoint 2)).toNat := by
  simp [monomial_eq_fin_three]

/-- The exceptional exponents of a product of nonzero polynomials add up. -/
theorem exceptionalExponent_mul (hF0 : F ≠ 0) (hG0 : G ≠ 0) :
    exceptionalExponent (F * G) = exceptionalExponent F + exceptionalExponent G := by
  ext i
  simp [mult_mul, ENat.toNat_add (mult_eq_top_iff.not.2 hF0) (mult_eq_top_iff.not.2 hG0)]

/-- Renaming the variables by `σ` permutes the exceptional exponents along. -/
theorem exceptionalExponent_rename (hF : F.IsHomogeneous n) (σ : Equiv.Perm (Fin 3)) :
    exceptionalExponent (rename σ F) = (exceptionalExponent F).mapDomain σ := by
  ext j
  obtain ⟨i, rfl⟩ := σ.surjective j
  rw [Finsupp.mapDomain_apply_of_injective σ.injective, exceptionalExponent_apply,
    exceptionalExponent_apply, mult_rename_fundamentalPoint hF]

private theorem isRelPrime_X {i j : Fin 3} (h : i ≠ j) :
    IsRelPrime (X i : MvPolynomial (Fin 3) k) (X j) :=
  (prime_X (R := k) (σ := Fin 3) (i := i)).irreducible.isRelPrime_iff_not_dvd.2
    (by rwa [X_dvd_X])

/-- The exceptional monomial `X^r₀ Y^r₁ Z^r₂` divides the quadratic transform of a form. -/
theorem monomial_exceptionalExponent_dvd (hF : F.IsHomogeneous n) :
    monomial (exceptionalExponent F) 1 ∣ quadraticTransform F := by
  rw [monomial_exceptionalExponent]
  refine IsRelPrime.mul_dvd ?_ (IsRelPrime.mul_dvd ?_ ?_ ?_) (X_pow_dvd_quadraticTransform hF 2)
  · exact (isRelPrime_X (by decide)).pow.mul_left (isRelPrime_X (by decide)).pow
  · exact (isRelPrime_X (by decide)).pow
  exacts [X_pow_dvd_quadraticTransform hF 0, X_pow_dvd_quadraticTransform hF 1]

/-- The proper transform `F'` of a form `F`: its quadratic transform `F^Q` divided by
`X^r₀ Y^r₁ Z^r₂`, where `rᵢ` is the multiplicity of `F` at the fundamental point `[eᵢ]`. This
is the largest monomial dividing `F^Q` (`multiplicity_X_quadraticTransform`). The value is not
meaningful for a polynomial that is not homogeneous. -/
noncomputable def properTransform (F : MvPolynomial (Fin 3) k) : MvPolynomial (Fin 3) k :=
  divMonomial (quadraticTransform F) (exceptionalExponent F)

theorem properTransform_def (F : MvPolynomial (Fin 3) k) :
    properTransform F = divMonomial (quadraticTransform F) (exceptionalExponent F) :=
  (rfl)

/-- If `F^Q` is the exceptional monomial times `G`, then `G` is the proper transform of `F`. -/
theorem properTransform_eq_of_quadraticTransform_eq
    (h : quadraticTransform F = monomial (exceptionalExponent F) 1 * G) : properTransform F = G :=
  by rw [properTransform_def, h, divMonomial_monomial_mul]

/-- `F^Q` is the exceptional monomial `X^r₀ Y^r₁ Z^r₂` times the proper transform `F'`. -/
theorem quadraticTransform_eq_monomial_mul_properTransform (hF : F.IsHomogeneous n) :
    quadraticTransform F = monomial (exceptionalExponent F) 1 * properTransform F := by
  obtain ⟨G, hG⟩ := monomial_exceptionalExponent_dvd hF
  rw [properTransform_eq_of_quadraticTransform_eq hG, ← hG]

/-- **Fulton's (1)**: `F^Q = X^r₀ Y^r₁ Z^r₂ F'`, with `rᵢ` the multiplicity of `F` at the
fundamental point `[eᵢ]`. -/
theorem quadraticTransform_eq (hF : F.IsHomogeneous n) :
    quadraticTransform F =
      X 0 ^ (mult F (fundamentalPoint 0)).toNat * X 1 ^ (mult F (fundamentalPoint 1)).toNat *
        X 2 ^ (mult F (fundamentalPoint 2)).toNat * properTransform F := by
  rw [quadraticTransform_eq_monomial_mul_properTransform hF, monomial_exceptionalExponent]

/-- **(1)**: no exceptional line divides the proper transform of a nonzero form. -/
theorem not_X_dvd_properTransform (hF : F.IsHomogeneous n) (hF0 : F ≠ 0) (i : Fin 3) :
    ¬ X i ∣ properTransform F := by
  rintro ⟨K, hK⟩
  have hdvd : X i ^ ((mult F (fundamentalPoint i)).toNat + 1) ∣ quadraticTransform F := by
    rw [quadraticTransform_eq_monomial_mul_properTransform hF, hK, pow_succ]
    refine mul_dvd_mul ?_ (dvd_mul_right _ _)
    rw [X_pow_eq_monomial, monomial_one_dvd_monomial_one, Finsupp.single_le_iff,
      exceptionalExponent_apply]
  have := (pow_dvd_iff_le_emultiplicity.1 hdvd).trans_eq
    (emultiplicity_X_quadraticTransform hF hF0 i)
  norm_cast at this
  omega

@[simp]
theorem properTransform_zero : properTransform (0 : MvPolynomial (Fin 3) k) = 0 := by
  simp [properTransform_def, zero_divMonomial]

theorem properTransform_eq_zero_iff (hF : F.IsHomogeneous n) : properTransform F = 0 ↔ F = 0 := by
  refine ⟨fun h ↦ ?_, by rintro rfl; exact properTransform_zero⟩
  rw [← quadraticTransform_eq_zero_iff, quadraticTransform_eq_monomial_mul_properTransform hF, h,
    mul_zero]

/-- The proper transform of a form `F` of degree `n` is a form of degree `2n - r₀ - r₁ - r₂`. -/
theorem _root_.MvPolynomial.IsHomogeneous.properTransform (hF : F.IsHomogeneous n) :
    (PlaneCurves.Projective.properTransform F).IsHomogeneous
      (2 * n - ∑ i, (mult F (fundamentalPoint i)).toNat) := by
  obtain rfl | hF0 := eq_or_ne F 0
  · simpa using isHomogeneous_zero _ _ _
  have hm0 : monomial (exceptionalExponent F) (1 : k) ≠ 0 := by simp
  have hP0 : PlaneCurves.Projective.properTransform F ≠ 0 :=
    (properTransform_eq_zero_iff hF).not.2 hF0
  have h := hF.quadraticTransform
  rw [quadraticTransform_eq_monomial_mul_properTransform hF] at h
  convert h.of_mul_right hm0 using 1
  have := h.totalDegree (mul_ne_zero hm0 hP0)
  rw [totalDegree_mul_of_isDomain hm0 hP0, totalDegree_monomial _ one_ne_zero,
    Finsupp.sum_fintype _ _ fun _ ↦ rfl] at this
  simp only [exceptionalExponent_apply] at this
  omega

/-- **Multiplicativity**: `(FG)' = F'G'` for forms `F` and `G`. -/
theorem properTransform_mul (hF : F.IsHomogeneous n) (hG : G.IsHomogeneous m) :
    properTransform (F * G) = properTransform F * properTransform G := by
  obtain rfl | hF0 := eq_or_ne F 0
  · simp
  obtain rfl | hG0 := eq_or_ne G 0
  · simp
  refine properTransform_eq_of_quadraticTransform_eq ?_
  have hm : monomial (exceptionalExponent F + exceptionalExponent G) (1 : k) =
      monomial (exceptionalExponent F) 1 * monomial (exceptionalExponent G) 1 := by
    rw [monomial_mul_monomial, mul_one]
  rw [map_mul, quadraticTransform_eq_monomial_mul_properTransform hF,
    quadraticTransform_eq_monomial_mul_properTransform hG, exceptionalExponent_mul hF0 hG0,
    hm]
  ring

@[simp]
theorem properTransform_C (c : k) : properTransform (C c : MvPolynomial (Fin 3) k) = C c := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  refine properTransform_eq_of_quadraticTransform_eq ?_
  have h : exceptionalExponent (C c : MvPolynomial (Fin 3) k) = 0 := by
    ext i
    have h0 : mult (C c : MvPolynomial (Fin 3) k) (fundamentalPoint i) = 0 := by
      by_contra h
      exact hc (by simpa using mult_pos_iff_eval_rep.1 (pos_iff_ne_zero.2 h))
    simp [h0]
  simp [h]

@[simp]
theorem properTransform_one : properTransform (1 : MvPolynomial (Fin 3) k) = 1 := by
  simpa using properTransform_C (1 : k)

theorem properTransform_smul (hF : F.IsHomogeneous n) (c : k) :
    properTransform (c • F) = c • properTransform F := by
  rw [smul_eq_C_mul, smul_eq_C_mul, properTransform_mul (isHomogeneous_C _ c) hF,
    properTransform_C]

theorem properTransform_pow (hF : F.IsHomogeneous n) (e : ℕ) :
    properTransform (F ^ e) = properTransform F ^ e := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, properTransform_mul (hF.pow e) hF, ih, pow_succ]

theorem properTransform_prod {ι : Type*} (s : Finset ι) {F : ι → MvPolynomial (Fin 3) k}
    {n : ι → ℕ} (hF : ∀ i ∈ s, (F i).IsHomogeneous (n i)) :
    properTransform (∏ i ∈ s, F i) = ∏ i ∈ s, properTransform (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      properTransform_mul (hF a (by simp))
        (IsHomogeneous.prod _ _ _ fun i hi ↦ hF i (by simp [hi])),
      ih fun i hi ↦ hF i (by simp [hi])]

/-- The proper transform of an exceptional line is `1`: `X^Q = YZ` is all exceptional. -/
@[simp]
theorem properTransform_X (i : Fin 3) : properTransform (X i : MvPolynomial (Fin 3) k) = 1 := by
  refine properTransform_eq_of_quadraticTransform_eq ?_
  rw [mul_one, monomial_exceptionalExponent]
  fin_cases i <;> simp [mult_X_fundamentalPoint]

/-- Proper transforms commute with permutations of the variables. -/
theorem properTransform_rename (hF : F.IsHomogeneous n) (σ : Equiv.Perm (Fin 3)) :
    properTransform (rename σ F) = rename σ (properTransform F) := by
  refine properTransform_eq_of_quadraticTransform_eq ?_
  rw [quadraticTransform_rename, quadraticTransform_eq_monomial_mul_properTransform hF, map_mul,
    rename_monomial, exceptionalExponent_rename hF]

/-- **The restriction of `F'` to `Z = 0`.** For a nonzero form `F` of degree `n`,
`X^r₀ Y^r₁ F'(X, Y, 0) = (XY)^(n - r₂) G(Y, X)`, where `G` is the leading form of `F(X, Y, 1)`
at the origin, the tangent cone of `F` at `[0 : 0 : 1]`. -/
theorem aeval_X_two_eq_zero_properTransform (hF : F.IsHomogeneous n) (hF0 : F ≠ 0) :
    X 0 ^ (mult F (fundamentalPoint 0)).toNat * X 1 ^ (mult F (fundamentalPoint 1)).toNat *
        aeval (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) (properTransform F) =
      (X 0 * X 1) ^ (n - (mult F (fundamentalPoint 2)).toNat) *
        rename ![1, 0] (leadingFormAt (dehomogenize 2 F) 0) := by
  obtain ⟨H, hFH, hH⟩ := exists_quadraticTransform_eq_X_two_pow_mul hF hF0
  have h := quadraticTransform_eq hF
  rw [hFH, mul_comm _ (X 2 ^ _), mul_assoc, mul_right_inj' (pow_ne_zero _ (X_ne_zero _))] at h
  rw [← hH, h]
  simp

/-- The line `X + Y + Z` passes through no fundamental point, so its proper transform is its
quadratic transform, the conic `YZ + XZ + XY`. -/
example :
    properTransform (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) ℚ) = X 1 * X 2 + X 0 * X 2 + X 0 * X 1
    := by
  refine properTransform_eq_of_quadraticTransform_eq ?_
  have hL : (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) ℚ).IsHomogeneous 1 :=
    ((isHomogeneous_X ℚ 0).add (isHomogeneous_X ℚ 1)).add (isHomogeneous_X ℚ 2)
  have h (i : Fin 3) : mult (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) ℚ) (fundamentalPoint i) = 0 :=
    by
    rw [fundamentalPoint_def, mult_mk hL, orderAt_eq_zero_iff]
    fin_cases i <;> simp
  simp [monomial_exceptionalExponent, h]

/-- The conic `YZ + XZ + XY` passes simply through the three fundamental points, and its proper
transform is the line `X + Y + Z`. -/
example :
    properTransform (X 1 * X 2 + X 0 * X 2 + X 0 * X 1 : MvPolynomial (Fin 3) ℚ) =
      X 0 + X 1 + X 2 := by
  refine properTransform_eq_of_quadraticTransform_eq ?_
  have hC : (X 1 * X 2 + X 0 * X 2 + X 0 * X 1 : MvPolynomial (Fin 3) ℚ).IsHomogeneous 2 :=
    (((isHomogeneous_X ℚ 1).mul (isHomogeneous_X ℚ 2)).add
      ((isHomogeneous_X ℚ 0).mul (isHomogeneous_X ℚ 2))).add
      ((isHomogeneous_X ℚ 0).mul (isHomogeneous_X ℚ 1))
  have h (i : Fin 3) :
      mult (X 1 * X 2 + X 0 * X 2 + X 0 * X 1 : MvPolynomial (Fin 3) ℚ) (fundamentalPoint i) = 1 :=
    by
    rw [fundamentalPoint_def, mult_mk hC, orderAt_eq_one_iff]
    fin_cases i
    · exact ⟨by simp, 1, by simp⟩
    · exact ⟨by simp, 0, by simp⟩
    · exact ⟨by simp, 0, by simp⟩
  simp only [monomial_exceptionalExponent, h, map_add, map_mul, quadraticTransform_X_zero,
    quadraticTransform_X_one, quadraticTransform_X_two]
  simp
  ring

end ProperTransform

section Involution

variable {k : Type*} [Field k] {F H : MvPolynomial (Fin 3) k} {n : ℕ}

private theorem X_mul_quadraticTransform_X (i : Fin 3) :
    (X i * quadraticTransform (X i) : MvPolynomial (Fin 3) k) = X 0 * X 1 * X 2 := by
  fin_cases i <;> simp <;> ring

private theorem not_X_dvd_quadraticTransform_X (i : Fin 3) :
    ¬ X i ∣ (quadraticTransform (X i) : MvPolynomial (Fin 3) k) := by
  fin_cases i <;> simp [prime_X.dvd_mul, X_dvd_X]

/-- If the exceptional line `V(Xᵢ)` is not a component of a form `F` of degree `n`, then `F^Q`
has multiplicity `n` at the fundamental point `[eᵢ]`. -/
theorem mult_quadraticTransform_fundamentalPoint (hF : F.IsHomogeneous n) {i : Fin 3}
    (hXi : ¬ X i ∣ F) : mult (quadraticTransform F) (fundamentalPoint i) = n := by
  have hF0 : F ≠ 0 := by rintro rfl; exact hXi (dvd_zero _)
  have hQ0 : quadraticTransform F ≠ 0 := quadraticTransform_eq_zero_iff.not.2 hF0
  have h := emultiplicity_X_quadraticTransform hF.quadraticTransform hQ0 i
  rw [quadraticTransform_quadraticTransform hF, ← X_mul_quadraticTransform_X i, mul_pow,
    mul_assoc, emultiplicity_mul prime_X, emultiplicity_pow_self_of_prime prime_X,
    emultiplicity_mul prime_X, emultiplicity_pow prime_X,
    emultiplicity_eq_zero.2 (not_X_dvd_quadraticTransform_X i), emultiplicity_eq_zero.2 hXi]
    at h
  rw [← ENat.natCast_toNat (mult_eq_top_iff.not.2 hQ0)]
  simpa using h.symm

/-- **Fulton's (3)**, as a sum: if `V(Xᵢ)` is not a component of a form `F` of degree `n`, and
`i, j, l` are the three indices, then `m_{[eᵢ]}(F') + m_{[eⱼ]}(F) + m_{[eₗ]}(F) = n`. -/
theorem mult_properTransform_fundamentalPoint_add (hF : F.IsHomogeneous n) {i j l : Fin 3}
    (hXi : ¬ X i ∣ F) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    mult (properTransform F) (fundamentalPoint i) + mult F (fundamentalPoint j) +
      mult F (fundamentalPoint l) = n := by
  have hF0 : F ≠ 0 := by rintro rfl; exact hXi (dvd_zero _)
  have hc (m : Fin 3) :
      ((mult F (fundamentalPoint m)).toNat : ℕ∞) = mult F (fundamentalPoint m) :=
    ENat.natCast_toNat (mult_eq_top_iff.not.2 hF0)
  have h := mult_quadraticTransform_fundamentalPoint hF hXi
  rw [quadraticTransform_eq hF] at h
  simp only [mult_mul, mult_pow, mult_X_fundamentalPoint, nsmul_eq_mul] at h
  rw [← h]
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp [hc] at hij hil hjl ⊢ <;> ring

/-- If `V(Xᵢ)` is not a component of a form `F` of degree `n`, then the multiplicities of `F` at
the two fundamental points on `V(Xᵢ)` add up to at most `n`. -/
theorem mult_fundamentalPoint_add_le (hF : F.IsHomogeneous n) {i j l : Fin 3}
    (hXi : ¬ X i ∣ F) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    mult F (fundamentalPoint j) + mult F (fundamentalPoint l) ≤ n := by
  rw [← mult_properTransform_fundamentalPoint_add hF hXi hij hil hjl, add_assoc]
  exact le_add_self

/-- **Fulton's (3)**: if `V(Xᵢ)` is not a component of a form `F` of degree `n`, and `i, j, l`
are the three indices, then `m_{[eᵢ]}(F') = n - m_{[eⱼ]}(F) - m_{[eₗ]}(F)`. -/
theorem mult_properTransform_fundamentalPoint (hF : F.IsHomogeneous n) {i j l : Fin 3}
    (hXi : ¬ X i ∣ F) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    mult (properTransform F) (fundamentalPoint i) =
      (n - (mult F (fundamentalPoint j)).toNat - (mult F (fundamentalPoint l)).toNat : ℕ) := by
  have hF0 : F ≠ 0 := by rintro rfl; exact hXi (dvd_zero _)
  have hF0' : properTransform F ≠ 0 := (properTransform_eq_zero_iff hF).not.2 hF0
  have h := mult_properTransform_fundamentalPoint_add hF hXi hij hil hjl
  rw [← ENat.natCast_toNat (mult_eq_top_iff.not.2 hF0'),
    ← ENat.natCast_toNat (mult_eq_top_iff.not.2 hF0 : mult F (fundamentalPoint j) ≠ ⊤),
    ← ENat.natCast_toNat (mult_eq_top_iff.not.2 hF0 : mult F (fundamentalPoint l) ≠ ⊤)] at h
  rw [← ENat.natCast_toNat (mult_eq_top_iff.not.2 hF0')]
  norm_cast at h ⊢
  omega

/-- **Fulton's (3)** at `fundamentalPoint 0`. -/
theorem mult_properTransform_fundamentalPoint_zero (hF : F.IsHomogeneous n) (hX0 : ¬ X 0 ∣ F) :
    mult (properTransform F) (fundamentalPoint 0) =
      (n - (mult F (fundamentalPoint 1)).toNat - (mult F (fundamentalPoint 2)).toNat : ℕ) :=
  mult_properTransform_fundamentalPoint hF hX0 (by decide) (by decide) (by decide)

/-- **Fulton's (3)** at `fundamentalPoint 1`. -/
theorem mult_properTransform_fundamentalPoint_one (hF : F.IsHomogeneous n) (hX1 : ¬ X 1 ∣ F) :
    mult (properTransform F) (fundamentalPoint 1) =
      (n - (mult F (fundamentalPoint 0)).toNat - (mult F (fundamentalPoint 2)).toNat : ℕ) :=
  mult_properTransform_fundamentalPoint hF hX1 (by decide) (by decide) (by decide)

/-- **Fulton's (3)** at `fundamentalPoint 2`. -/
theorem mult_properTransform_fundamentalPoint_two (hF : F.IsHomogeneous n) (hX2 : ¬ X 2 ∣ F) :
    mult (properTransform F) (fundamentalPoint 2) =
      (n - (mult F (fundamentalPoint 0)).toNat - (mult F (fundamentalPoint 1)).toNat : ℕ) :=
  mult_properTransform_fundamentalPoint hF hX2 (by decide) (by decide) (by decide)

/-- **The quadratic transformation inverts the proper transform**: for a form `F` of degree `n`
with no exceptional component, `(F')^Q = X^(n - r₁ - r₂) Y^(n - r₀ - r₂) Z^(n - r₀ - r₁) F`,
where `rᵢ` is the multiplicity of `F` at `[eᵢ]`. -/
theorem quadraticTransform_properTransform (hF : F.IsHomogeneous n) (hX : ∀ i, ¬ X i ∣ F) :
    quadraticTransform (properTransform F) =
      X 0 ^ (n - (mult F (fundamentalPoint 1)).toNat - (mult F (fundamentalPoint 2)).toNat) *
        X 1 ^ (n - (mult F (fundamentalPoint 0)).toNat - (mult F (fundamentalPoint 2)).toNat) *
        X 2 ^ (n - (mult F (fundamentalPoint 0)).toNat - (mult F (fundamentalPoint 1)).toNat) *
        F := by
  have hF0 : F ≠ 0 := by rintro rfl; exact hX 0 (dvd_zero _)
  have hle {i j l : Fin 3} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
      (mult F (fundamentalPoint j)).toNat + (mult F (fundamentalPoint l)).toNat ≤ n := by
    have h := mult_fundamentalPoint_add_le hF (hX i) hij hil hjl
    rw [← ENat.natCast_toNat (mult_eq_top_iff.not.2 hF0 : mult F (fundamentalPoint j) ≠ ⊤),
      ← ENat.natCast_toNat (mult_eq_top_iff.not.2 hF0 : mult F (fundamentalPoint l) ≠ ⊤)] at h
    exact_mod_cast h
  have e (i : Fin 3) {a b : ℕ} (hab : a + b ≤ n) :
      (X i : MvPolynomial (Fin 3) k) ^ n = X i ^ (a + b) * X i ^ (n - a - b) := by
    rw [← pow_add]
    congr 1
    omega
  have h := quadraticTransform_quadraticTransform hF
  rw [quadraticTransform_eq hF] at h
  simp only [map_mul, map_pow, quadraticTransform_X_zero, quadraticTransform_X_one,
    quadraticTransform_X_two] at h
  refine mul_left_cancel₀ (by simp [X_ne_zero]) (h.trans ?_)
  rw [mul_pow, mul_pow, e 0 (hle (i := 0) (j := 1) (l := 2) (by decide) (by decide) (by decide)),
    e 1 (hle (i := 1) (j := 0) (l := 2) (by decide) (by decide) (by decide)),
    e 2 (hle (i := 2) (j := 0) (l := 1) (by decide) (by decide) (by decide))]
  ring

/-- **Fulton's (2)**, the involution: `(F')' = F` for a form `F` with no exceptional
component. -/
theorem properTransform_properTransform (hF : F.IsHomogeneous n) (hX : ∀ i, ¬ X i ∣ F) :
    properTransform (properTransform F) = F := by
  refine properTransform_eq_of_quadraticTransform_eq ?_
  rw [monomial_exceptionalExponent, mult_properTransform_fundamentalPoint_zero hF (hX 0),
    mult_properTransform_fundamentalPoint_one hF (hX 1),
    mult_properTransform_fundamentalPoint_two hF (hX 2), ENat.toNat_natCast, ENat.toNat_natCast,
    ENat.toNat_natCast]
  exact quadraticTransform_properTransform hF hX

/-- Without its hypothesis, `properTransform_properTransform` fails: the proper transform of the
exceptional line `X` is `1`, and so is that of `1`. -/
example : properTransform (properTransform (X 0 : MvPolynomial (Fin 3) ℚ)) ≠ X 0 := by
  rw [properTransform_X, properTransform_one]
  intro h
  simpa using congrArg totalDegree h

private theorem isUnit_of_isUnit_properTransform (hF : F.IsHomogeneous n) (hX : ∀ i, ¬ X i ∣ F)
    (h : IsUnit (properTransform F)) : IsUnit F := by
  obtain ⟨c, hc, h⟩ := isUnit_iff_eq_C_of_isReduced.1 h
  rw [← properTransform_properTransform hF hX, h, properTransform_C]
  exact hc.map C

/-- **Fulton's (2)**: the proper transform of an irreducible form with no exceptional
component is irreducible. -/
theorem irreducible_properTransform (hF : F.IsHomogeneous n) (hirr : Irreducible F)
    (hX : ∀ i, ¬ X i ∣ F) : Irreducible (properTransform F) := by
  have hF0 := hirr.ne_zero
  refine ⟨fun h ↦ hirr.not_isUnit (isUnit_of_isUnit_properTransform hF hX h), fun G H hGH ↦ ?_⟩
  have hP0 : properTransform F ≠ 0 := (properTransform_eq_zero_iff hF).not.2 hF0
  have hGH0 := hGH ▸ hP0
  have hP := hGH ▸ hF.properTransform
  have hG := hP.of_mul_left (right_ne_zero_of_mul hGH0)
  have hH := hP.of_mul_right (left_ne_zero_of_mul hGH0)
  have hXG (i : Fin 3) : ¬ X i ∣ G := fun hi ↦
    not_X_dvd_properTransform hF hF0 i (hGH ▸ dvd_mul_of_dvd_left hi _)
  have hXH (i : Fin 3) : ¬ X i ∣ H := fun hi ↦
    not_X_dvd_properTransform hF hF0 i (hGH ▸ dvd_mul_of_dvd_right hi _)
  have h := properTransform_properTransform hF hX
  rw [hGH, properTransform_mul hG hH] at h
  exact (hirr.isUnit_or_isUnit h.symm).imp (isUnit_of_isUnit_properTransform hG hXG)
    (isUnit_of_isUnit_properTransform hH hXH)

private theorem dvd_of_properTransform_dvd_of_isHomogeneous (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) (hX : ∀ i, ¬ X i ∣ F) {m : ℕ} (hH : H.IsHomogeneous m)
    (h : properTransform F ∣ quadraticTransform H) : F ∣ H := by
  have h1 : F ∣ (X 0 * X 1 * X 2) ^ m * H := by
    rw [← quadraticTransform_quadraticTransform hH]
    refine dvd_trans ?_ (map_dvd quadraticTransform h)
    rw [quadraticTransform_properTransform hF hX]
    exact dvd_mul_left _ _
  have hp := hirr.prime
  have hXF (i : Fin 3) : ¬ F ∣ X i := fun h ↦ hX i (hirr.dvd_symm prime_X.irreducible h)
  refine (hp.dvd_or_dvd h1).resolve_left fun h2 ↦ ?_
  simpa [hp.dvd_mul, hXF] using hp.dvd_of_dvd_pow h2

/-- For an irreducible form `F` with no exceptional component, `F'` divides `H^Q` exactly when
`F` divides `H`. -/
theorem dvd_quadraticTransform_iff (hF : F.IsHomogeneous n) (hirr : Irreducible F)
    (hX : ∀ i, ¬ X i ∣ F) : properTransform F ∣ quadraticTransform H ↔ F ∣ H := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← sum_homogeneousComponent H]
    refine Finset.dvd_sum fun e _ ↦ dvd_of_properTransform_dvd_of_isHomogeneous hF hirr hX
      (homogeneousComponent_isHomogeneous e H) ?_
    rw [← homogeneousComponent_quadraticTransform]
    exact hF.properTransform.dvd_homogeneousComponent h _
  · refine dvd_trans ?_ (map_dvd quadraticTransform h)
    rw [quadraticTransform_eq hF]
    exact dvd_mul_left _ _

end Involution

end PlaneCurves.Projective

end
