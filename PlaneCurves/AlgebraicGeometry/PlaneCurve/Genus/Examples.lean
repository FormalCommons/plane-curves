/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
public import PlaneCurves.Algebra.Polynomial.Bivariate
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Genus.VirtualGenus

/-!
# A plane curve of genus two

Over an algebraically closed field `k` with `2 ≠ 0`, the quartic `C : Y²XZ = X⁴ + Z⁴` is
irreducible, and its only multiple point is the node `[0 : 1 : 0]`, with tangents `X = 0` and
`Z = 0`. By the genus formula it has genus `3 - 1 = 2`, so it is not birationally equivalent to
any nonsingular plane curve, whose genus is `(n - 1)(n - 2)/2 ∈ {0, 1, 3, 6, …}`.

The example printed in Fulton (§8.3, p. 104), `Y²XZ = X⁴ + Y⁴`, has a non-ordinary triple point
at `[0 : 0 : 1]` and is rational; `Y²XZ = X⁴ + Z⁴` is a correct example. In characteristic two
it has further singular points, such as `[1 : 0 : 1]`.

## Main definitions

* `PlaneCurves.Projective.nodalQuartic`: the form `Y²XZ - X⁴ - Z⁴`.

## Main results

* `PlaneCurves.Projective.irreducible_nodalQuartic`: it is irreducible.
* `PlaneCurves.Projective.isOrdinaryMultiplePoint_nodalQuartic`,
  `PlaneCurves.Projective.mult_nodalQuartic`,
  `PlaneCurves.Projective.eq_of_isMultiplePoint_nodalQuartic`: `[0 : 1 : 0]` is a node, and the
  only multiple point.
* `PlaneCurves.Projective.genus_functionField_nodalQuartic`: the curve has genus two.
* `PlaneCurves.Projective.isEmpty_algEquiv_nodalQuartic`: it is not birationally equivalent to
  any nonsingular plane curve.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §8.3, Examples
-/

public section

section Bivariate

open Polynomial

/-- `Y ↦ X Y² - (X⁴ + 1)` in `k[X][Y]`, the dehomogenization of `Y²XZ - X⁴ - Z⁴` at `Z`. -/
private theorem irreducible_bivariate {k : Type*} [Field k] [IsAlgClosed k] (h2 : (2 : k) ≠ 0) :
    Irreducible (C X * X ^ 2 - C (X ^ 4 + 1) : k[X][X]) := by
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : k) (by norm_num : 0 < 4)
  have hζ0 : ζ ≠ 0 := by rintro rfl; norm_num at hζ
  set c : k[X] := X ^ 4 + 1
  set f : k[X][X] := C X * X ^ 2 - C c
  have hX0 : (X : k[X]) ≠ 0 := X_ne_zero
  have hdeg2 : (C X * X ^ 2 : k[X][X]).degree = 2 := by
    rw [degree_C_mul_X_pow 2 hX0]; rfl
  have hdeg : f.degree = 2 := by
    rw [degree_sub_C (by rw [hdeg2]; norm_num), hdeg2]
  have hnat : f.natDegree = 2 := natDegree_eq_of_degree_eq_some hdeg
  have hc2 : f.coeff 2 = X := by simp [f]
  have hc1 : f.coeff 1 = 0 := by simp [f]
  have hc0 : f.coeff 0 = -c := by simp [f, coeff_C]
  have hlc : f.leadingCoeff = X := by rw [leadingCoeff, hnat, hc2]
  set P : Ideal k[X] := Ideal.span {X - C ζ}
  have hP : P.IsPrime := (Ideal.span_singleton_prime (X_sub_C_ne_zero ζ)).2 (prime_X_sub_C ζ)
  have hmem (q : k[X]) : q ∈ P ↔ q.IsRoot ζ := by
    rw [Ideal.mem_span_singleton, dvd_iff_isRoot]
  have hc : c.IsRoot ζ := by simp [c, hζ]
  refine irreducible_of_eisenstein_criterion hP ?_ ?_ (by rw [hdeg]; norm_num) ?_ ?_
  · rw [hlc, hmem]
    simpa using hζ0
  · intro n hn
    rw [hdeg] at hn
    have hn : n < 2 := by exact_mod_cast hn
    interval_cases n
    · rw [hc0]; exact P.neg_mem ((hmem c).2 hc)
    · rw [hc1]; exact P.zero_mem
  · rw [hc0, Ideal.span_singleton_pow, Ideal.neg_mem_iff, Ideal.mem_span_singleton]
    rintro ⟨q, hq⟩
    have h := congrArg (fun p ↦ (derivative p).eval ζ) hq
    replace h : (4 : k) = 0 ∨ ζ = 0 := by simpa [c, derivative_mul, derivative_pow] using h
    have h4 : (4 : k) ≠ 0 := by
      rw [show (4 : k) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    exact h.elim h4 hζ0
  · intro r hr
    rw [C_dvd_iff_dvd_coeff] at hr
    have h0 := hr 0
    have h2' := hr 2
    rw [hc2] at h2'
    rw [hc0, dvd_neg] at h0
    refine isUnit_of_dvd_one ?_
    have : (1 : k[X]) = c - X ^ 3 * X := by simp only [c]; ring
    rw [this]
    exact dvd_sub h0 (h2'.mul_left _)

end Bivariate

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti
open TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace PlaneCurves.Projective

variable (k : Type*) [Field k]

/-- The quartic form `Y²XZ - X⁴ - Z⁴`, with `X, Y, Z` the variables `X 0, X 1, X 2`. -/
noncomputable def nodalQuartic : MvPolynomial (Fin 3) k :=
  X 1 ^ 2 * X 0 * X 2 - X 0 ^ 4 - X 2 ^ 4

theorem nodalQuartic_def : nodalQuartic k = X 1 ^ 2 * X 0 * X 2 - X 0 ^ 4 - X 2 ^ 4 :=
  (rfl)

/-- `Y²XZ - X⁴ - Z⁴` is a form of degree four. -/
theorem isHomogeneous_nodalQuartic : (nodalQuartic k).IsHomogeneous 4 := by
  have h := fun i : Fin 3 ↦ isHomogeneous_X k i
  exact ((((h 1).pow 2).mul (h 0)).mul (h 2)).sub ((h 0).pow 4) |>.sub ((h 2).pow 4)

variable {k}

/-! ### Irreducibility -/

/-- `Y²XZ - X⁴ - Z⁴` is not divisible by `Z`: it is `-1` at `[1 : 0 : 0]`. -/
private theorem not_X_two_dvd_nodalQuartic : ¬ X 2 ∣ nodalQuartic k := by
  rintro ⟨G, hG⟩
  have := congrArg (eval ![1, 0, 0]) hG
  simp [nodalQuartic_def] at this

/-- **`Y²XZ = X⁴ + Z⁴` is irreducible**, over an algebraically closed field with `2 ≠ 0`: its
dehomogenization `XY² - (X⁴ + 1)` is irreducible by Eisenstein's criterion at `X - ζ`, `ζ⁴ = -1`,
as a polynomial in `Y` over `k[X]`. -/
theorem irreducible_nodalQuartic [IsAlgClosed k] (h2 : (2 : k) ≠ 0) :
    Irreducible (nodalQuartic k) := by
  refine (irreducible_dehomogenize_iff (isHomogeneous_nodalQuartic k)
    not_X_two_dvd_nodalQuartic).1 ?_
  have h := (MulEquiv.irreducible_iff
    (Polynomial.Bivariate.equivMvPolynomial k).toMulEquiv).2 (irreducible_bivariate h2)
  convert h using 1
  have e0 : dehomogenize 2 (X 0 : MvPolynomial (Fin 3) k) = X 0 := by rw [dehomogenize_X]; rfl
  have e1 : dehomogenize 2 (X 1 : MvPolynomial (Fin 3) k) = X 1 := by rw [dehomogenize_X]; rfl
  have e2 : dehomogenize 2 (X 2 : MvPolynomial (Fin 3) k) = 1 := by rw [dehomogenize_X]; rfl
  simp [nodalQuartic_def, e0, e1, e2]
  ring

/-! ### The multiple points -/

/-- `4 a³ = 0` forces `a = 0` when `2 ≠ 0`. -/
private theorem eq_zero_of_four_mul_pow_three (h2 : (2 : k) ≠ 0) {a : k} (h : 4 * a ^ 3 = 0) :
    a = 0 := by
  have h4 : (4 : k) ≠ 0 := by
    rw [show (4 : k) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1 ((mul_eq_zero.1 h).resolve_left h4)

/-- **The only multiple point of `Y²XZ = X⁴ + Z⁴` is `[0 : 1 : 0]`**, when `2 ≠ 0`: the partial
derivatives `Y²Z - 4X³`, `2XYZ` and `Y²X - 4Z³` vanish together only there. -/
theorem eq_of_isMultiplePoint_nodalQuartic (h2 : (2 : k) ≠ 0) {Q : ℙ k (Fin 3 → k)}
    (hQ : IsMultiplePoint (nodalQuartic k) Q) : Q = mk k ![0, 1, 0] (by simp) := by
  induction Q using Projectivization.ind with | h v hv =>
  rw [isMultiplePoint_iff_eval_pderiv (isHomogeneous_nodalQuartic k)] at hQ
  obtain ⟨-, hd⟩ := hQ
  have hX : 4 * v 0 ^ 3 = v 1 ^ 2 * v 2 := by
    have := hd 0
    simp [nodalQuartic_def, pderiv_X] at this
    linear_combination -this
  have hY : v 0 = 0 ∨ v 1 = 0 ∨ v 2 = 0 := by
    have := hd 1
    simp [nodalQuartic_def, pderiv_X] at this
    tauto
  have hZ : 4 * v 2 ^ 3 = v 1 ^ 2 * v 0 := by
    have := hd 2
    simp [nodalQuartic_def, pderiv_X] at this
    linear_combination -this
  have h02 : v 0 = 0 ∧ v 2 = 0 := by
    rcases hY with h | h | h
    · exact ⟨h, eq_zero_of_four_mul_pow_three h2 (by rw [hZ, h, mul_zero])⟩
    · exact ⟨eq_zero_of_four_mul_pow_three h2 (by rw [hX, h]; ring),
        eq_zero_of_four_mul_pow_three h2 (by rw [hZ, h]; ring)⟩
    · exact ⟨eq_zero_of_four_mul_pow_three h2 (by rw [hX, h, mul_zero]), h⟩
  have h1 : v 1 ≠ 0 := fun h1 ↦ hv (funext fun i ↦ by fin_cases i <;> simp [h02.1, h02.2, h1])
  rw [mk_eq_mk_iff]
  refine ⟨Units.mk0 (v 1) h1, funext fun i ↦ ?_⟩
  fin_cases i <;> simp [h02.1, h02.2]

/-- The order at `(0, 1, 0)` of `X 0` and `X 2`, and their leading forms there. -/
private theorem orderAt_X_and_leadingFormAt_X {j : Fin 3} (hj : (![0, 1, 0] : Fin 3 → k) j = 0) :
    (X j : MvPolynomial (Fin 3) k).orderAt ![0, 1, 0] = 1 ∧
      (X j : MvPolynomial (Fin 3) k).leadingFormAt ![0, 1, 0] = X j := by
  refine ⟨by simpa [hj] using orderAt_X_sub_C (R := k) ![0, 1, 0] j, ?_⟩
  have h := leadingFormAt_taylor ![0, 1, 0] 0 (X j : MvPolynomial (Fin 3) k)
  rwa [zero_add, taylor_X, hj, C_0, add_zero, (isHomogeneous_X k j).leadingFormAt_zero,
    eq_comm] at h

/-- At `(0, 1, 0)`, `Y²XZ - X⁴ - Z⁴` has order two and leading form `XZ`. -/
private theorem orderAt_and_leadingFormAt_nodalQuartic :
    (nodalQuartic k).orderAt ![0, 1, 0] = 2 ∧
      (nodalQuartic k).leadingFormAt ![0, 1, 0] = X 0 * X 2 := by
  obtain ⟨hX0, hL0⟩ := orderAt_X_and_leadingFormAt_X (k := k) (j := 0) rfl
  obtain ⟨hX2, hL2⟩ := orderAt_X_and_leadingFormAt_X (k := k) (j := 2) rfl
  have hX1 : eval ![0, 1, 0] (X 1 : MvPolynomial (Fin 3) k) ≠ 0 := by simp
  have hp : (X 1 ^ 2 * X 0 * X 2 : MvPolynomial (Fin 3) k).orderAt ![0, 1, 0] = 2 := by
    rw [orderAt_mul, orderAt_mul, orderAt_pow, orderAt_eq_zero_iff.2 hX1, hX0, hX2]
    norm_num
  have hq : 2 < (-(X 0 ^ 4 + X 2 ^ 4) : MvPolynomial (Fin 3) k).orderAt ![0, 1, 0] := by
    rw [orderAt_neg]
    refine lt_of_lt_of_le ?_ (min_orderAt_le_orderAt_add _ _ _)
    rw [orderAt_pow, orderAt_pow, hX0, hX2]
    norm_num
  have hF : nodalQuartic k = X 1 ^ 2 * X 0 * X 2 + -(X 0 ^ 4 + X 2 ^ 4) := by
    rw [nodalQuartic_def]; ring
  rw [← hp] at hq
  rw [hF, orderAt_add_of_lt hq, leadingFormAt_add_of_lt hq, hp, leadingFormAt_mul,
    leadingFormAt_mul, leadingFormAt_pow, leadingFormAt_of_eval_ne_zero hX1, hL0, hL2]
  simp

/-- `[0 : 1 : 0]` is a double point of `Y²XZ = X⁴ + Z⁴`. -/
theorem mult_nodalQuartic : mult (nodalQuartic k) (mk k ![0, 1, 0] (by simp)) = 2 := by
  rw [mult_mk (isHomogeneous_nodalQuartic k)]
  exact orderAt_and_leadingFormAt_nodalQuartic.1

/-- **`[0 : 1 : 0]` is a node of `Y²XZ = X⁴ + Z⁴`**: a double point with the two distinct
tangents `X = 0` and `Z = 0`. -/
theorem isOrdinaryMultiplePoint_nodalQuartic :
    IsOrdinaryMultiplePoint (nodalQuartic k) (mk k ![0, 1, 0] (by simp)) := by
  refine isOrdinaryMultiplePoint_def.2 ⟨isMultiplePoint_def.2 (by rw [mult_nodalQuartic]), ?_⟩
  rw [(associated_leadingForm_mk (isHomogeneous_nodalQuartic k) _ (by simp)).squarefree_iff,
    orderAt_and_leadingFormAt_nodalQuartic.2, squarefree_mul_iff,
    (prime_X : Prime (X 0 : MvPolynomial (Fin 3) k)).irreducible.isRelPrime_iff_not_dvd, X_dvd_X]
  exact ⟨by decide, prime_X.squarefree, prime_X.squarefree⟩

/-! ### The genus -/

variable [IsAlgClosed k]

/-- **`Y²XZ = X⁴ + Z⁴` has genus two**, over an algebraically closed field with `2 ≠ 0`: it is an
irreducible quartic whose only multiple point is a node, so `g = 3 - 1`. -/
theorem genus_functionField_nodalQuartic (h2 : (2 : k) ≠ 0) :
    haveI := Fact.mk (irreducible_nodalQuartic h2)
    genus k (functionField (isHomogeneous_nodalQuartic k)) = 2 :=
  haveI := Fact.mk (irreducible_nodalQuartic h2)
  genus_eq_two_of_isOrdinaryMultiplePoint _ isOrdinaryMultiplePoint_nodalQuartic
    mult_nodalQuartic fun _ hQ ↦ eq_of_isMultiplePoint_nodalQuartic h2 hQ

/-- **`Y²XZ = X⁴ + Z⁴` is not birationally equivalent to any nonsingular plane curve**, over an
algebraically closed field with `2 ≠ 0`. -/
theorem isEmpty_algEquiv_nodalQuartic (h2 : (2 : k) ≠ 0) {G : MvPolynomial (Fin 3) k} {m : ℕ}
    (hG : G.IsHomogeneous m) [Fact (Irreducible G)] (hns : IsNonsingular G) :
    haveI := Fact.mk (irreducible_nodalQuartic h2)
    IsEmpty (functionField (isHomogeneous_nodalQuartic k) ≃ₐ[k] functionField hG) :=
  haveI := Fact.mk (irreducible_nodalQuartic h2)
  isEmpty_algEquiv_of_genus_eq_two (genus_functionField_nodalQuartic h2) hG hns

end PlaneCurves.Projective

end
