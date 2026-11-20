/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.Line
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Cubic.GroupLaw
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Cubic.NormalForm
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Hessian.Flex
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.IntersectionCycle
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Singular
public import PlaneCurves.Data.Finsupp.Multiset
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Collinear
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.CoordinateRing
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Prime
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Projectivization

/-!
# The Weierstrass cubic as a projective plane curve

Let `W` be a Weierstrass curve over a field `k`, and `F = W.polynomial` its cubic form
`Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³)`. This file compares the plane curve `F`
with Mathlib's points of `W`: the simple points of `F` are exactly Mathlib's nonsingular
points, so that Mathlib's `W.Point` is in bijection with the simple points of `F`, the point at
infinity going to `O = [0 : 1 : 0]`; and over a perfect field `F` is a nonsingular curve exactly
when the discriminant of `W` is nonzero. The tangent line of `F` at `O` is the line `Z = 0`
(`WeierstrassCurve.Projective.tangentLine_polynomial_zero`, in `Cubic/NormalForm.lean`), and
`F` is irreducible by Tau Ceti's `WeierstrassCurve.Projective.prime_polynomial`.

The file then computes the intersection cycle `L • F` of each kind of line `L` with `F`: the
line at infinity `Z = 0` meets `F` only at `O`, three times, so that `O` is a flex; a vertical
line `X = xZ` through an affine point `(x, y)` meets `F` at `O`, `[x : y : 1]` and
`[x : negY x y : 1]`; and a non-vertical line `Y = ℓX + νZ` meets `F` at the points
`[x : ℓx + ν : 1]`, for the roots `x` of `W(X, ℓX + ν)`, counted with multiplicity.
The lines other than `Z = 0`, and the fact that `Z = 0` is the tangent line at `O`, are handled
over any field; the cycle of `Z = 0` itself, and so the flex, uses Bézout's theorem, over an
algebraically closed field. The affine points are read off from the restriction of `F` to the
line (Problem 3.21 of Fulton, `PlaneCurves.Affine.intersectionNumber_line_eq_rootMultiplicity`).

Finally, these computations show that three points of `W` add to zero exactly when a line cuts
them out of `F`, so that Fulton's third point `φ(P, Q)` of the chord through `P` and `Q` is
`-(P + Q)`, and Mathlib's group `W.Point` is isomorphic to Fulton's chord–tangent group
`CubicGroup F O` of the simple points of `F` with zero `O`, through the bijection above. No group
axiom is proved again: the isomorphism only has to preserve addition.

Through this isomorphism, Mathlib's addition formulas give Fulton's formulas for `P₁ ⊕ P₂`
on a cubic `Y²Z = X³ + aX²Z + bXZ² + cZ³` (Problem 5.38), and Mathlib's points over a subfield
`k₀` give the subgroup of `k₀`-rational points (Problem 5.40). Together these are the milestone
`WeierstrassCurve.Projective.chordTangentAddition_eq_add`.

Last, for any irreducible cubic `F` with a flex `O`, a projective change of coordinates carries
`F` to a multiple of a Weierstrass cubic `W.polynomial` and `[0 : 1 : 0]` to `O` (Fulton's
Problem 5.24 (a)); it also carries third points to third points, so that the chord–tangent group
`CubicGroup F O` is isomorphic to Mathlib's group `W.Point`.

## Main results

* `WeierstrassCurve.Projective.isSimplePoint_polynomial_mk_iff`: `[v]` is a simple point of `F`
  exactly when `v` is a nonsingular point of `W`.
* `WeierstrassCurve.Projective.Point.mem_range_toProjectivization_iff_isSimplePoint`: the simple
  points of `F` are the images of the points of `W`.
* `WeierstrassCurve.Projective.Point.toSimplePoint`: the bijection between `W.Point` and the
  simple points of `F`.
* `WeierstrassCurve.Projective.isNonsingular_polynomial_iff`: over a perfect field, `F` is
  nonsingular exactly when `W.Δ ≠ 0`.
* `WeierstrassCurve.Projective.isRelPrime_polynomial`: no line is a component of `F`.
* `WeierstrassCurve.Projective.isTangentAt_zero_X_two`: the tangent line of `F` at `O` is
  `Z = 0`.
* `WeierstrassCurve.Projective.intersectionCycle_X_two`: `Z • F = 3 O`.
* `WeierstrassCurve.Projective.isFlex_zero`: `O` is a flex of `F`.
* `WeierstrassCurve.Projective.intersectionCycle_X_zero_sub`: the cycle of a vertical line.
* `WeierstrassCurve.Projective.intersectionCycle_X_one_sub`: the cycle of a non-vertical line.
* `WeierstrassCurve.Projective.Point.add_add_eq_zero_iff`: `P + Q + R = 0` iff a line meets `F`
  in `P + Q + R`.
* `WeierstrassCurve.Projective.Point.thirdPoint_toProjectivization`: `φ(P, Q) = -(P + Q)`.
* `WeierstrassCurve.Projective.Point.toCubicGroup`: the isomorphism `W.Point ≃+ CubicGroup F O`.
* `WeierstrassCurve.Projective.add_coords_of_a₁_eq_zero_of_a₃_eq_zero`: the addition formulas
  when `a₁ = a₃ = 0` (Problem 5.38).
* `WeierstrassCurve.Projective.rationalPoints`, `mem_rationalPoints_iff`,
  `chord_mem_rationalPoints`: the subgroup of `k₀`-rational points (Problem 5.40).
* `WeierstrassCurve.Projective.chordTangentAddition_eq_add`: chord–tangent addition on a
  Weierstrass cubic agrees with Mathlib's group law.
* `PlaneCurves.Projective.exists_addEquiv_weierstrass_of_isFlex`: the group of an irreducible
  cubic with zero at a flex is the group of a Weierstrass curve, with `Δ ≠ 0` when the cubic is
  nonsingular.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.3, Problem 3.21, Problem 5.24, and §5.6,
  Problems 5.38 and 5.40
-/

public section

open MvPolynomial PlaneCurves.Projective Projectivization TauCeti
open Finsupp (single)

open scoped LinearAlgebra.Projectivization

namespace WeierstrassCurve.Projective

variable {k : Type*} [Field k] {W : WeierstrassCurve.Projective k}

/-- A point `[v]` of the plane is a simple point of the Weierstrass cubic `W.polynomial` exactly
when `v` is a nonsingular point of `W` in Mathlib's sense. -/
theorem isSimplePoint_polynomial_mk_iff {v : Fin 3 → k} (hv : v ≠ 0) :
    IsSimplePoint W.polynomial (Projectivization.mk k v hv) ↔ W.Nonsingular v := by
  rw [isSimplePoint_mk_iff W.isHomogeneous_polynomial, Nonsingular, Equation, polynomialX,
    polynomialY, polynomialZ, Fin.exists_fin_succ, Fin.exists_fin_succ, Fin.exists_fin_one]
  rfl

/-- A point of the plane is a simple point of `W.polynomial` exactly when its chosen
representative is a nonsingular point of `W`. -/
theorem isSimplePoint_polynomial_iff (P : ℙ k (Fin 3 → k)) :
    IsSimplePoint W.polynomial P ↔ W.Nonsingular P.rep := by
  conv_lhs => rw [← P.mk_rep]
  exact isSimplePoint_polynomial_mk_iff _

/-- **The Weierstrass cubic over a perfect field is nonsingular exactly when its discriminant is
nonzero.** Over a perfect field `k`, the projective plane curve `W.polynomial` has no multiple
point if and only if `W.Δ ≠ 0`. -/
theorem isNonsingular_polynomial_iff [PerfectField k] :
    IsNonsingular W.polynomial ↔ W.Δ ≠ 0 := by
  have key : IsNonsingular W.polynomial ↔ ∀ v : Fin 3 → k, v ≠ 0 → W.Equation v →
      W.Nonsingular v := by
    rw [isNonsingular_def]
    refine forall₂_congr fun v hv ↦ ?_
    rw [← isSimplePoint_polynomial_mk_iff hv, isSimplePoint_mk_iff W.isHomogeneous_polynomial,
      Equation]
    exact ⟨fun h hW ↦ ⟨hW, h hW⟩, fun h hW ↦ (h hW).2⟩
  rw [key]
  refine ⟨fun h hΔ ↦ ?_, fun hΔ v hv ↦ (equation_iff_nonsingular_of_Δ_ne_zero_of_ne_zero hΔ hv).1⟩
  obtain ⟨x, y, hxy⟩ := Affine.exists_isSingular_of_Δ_eq_zero W.toAffine hΔ
  rw [Affine.isSingular_iff_equation_and_not_nonsingular] at hxy
  refine hxy.2 ((nonsingular_some x y).1 (h _ (fun h0 ↦ ?_) ((equation_some x y).2 hxy.1)))
  simpa using congrFun h0 2

namespace Point

/-- The simple points of the Weierstrass cubic `W.polynomial` are exactly the points of the
plane that come from points of `W`. -/
theorem mem_range_toProjectivization_iff_isSimplePoint (P : ℙ k (Fin 3 → k)) :
    P ∈ Set.range (toProjectivization : W.Point → _) ↔ IsSimplePoint W.polynomial P := by
  rw [mem_range_toProjectivization_iff, isSimplePoint_polynomial_iff]

/-- The point of the plane given by a point of `W` is a simple point of `W.polynomial`. -/
theorem isSimplePoint_toProjectivization (P : W.Point) :
    IsSimplePoint W.polynomial P.toProjectivization :=
  (mem_range_toProjectivization_iff_isSimplePoint _).1 ⟨P, rfl⟩

/-- The bijection between Mathlib's points of `W` and the simple points of the plane curve
`W.polynomial`, sending a point to its line in `ℙ²`. -/
noncomputable def toSimplePoint :
    W.Point ≃ {P : ℙ k (Fin 3 → k) // IsSimplePoint W.polynomial P} :=
  Equiv.ofBijective (fun P ↦ ⟨P.toProjectivization, P.isSimplePoint_toProjectivization⟩)
    ⟨fun _ _ h ↦ toProjectivization_injective (congrArg Subtype.val h), fun P ↦
      ((mem_range_toProjectivization_iff_isSimplePoint P.1).2 P.2).imp fun _ h ↦
        Subtype.ext h⟩

/-- `toSimplePoint` sends a point of `W` to its line in `ℙ²`. -/
@[simp]
theorem coe_toSimplePoint_apply (P : W.Point) :
    (toSimplePoint P : ℙ k (Fin 3 → k)) = P.toProjectivization :=
  (rfl)

/-- The point at infinity of `W` goes to the point `O = [0 : 1 : 0]`. -/
theorem toSimplePoint_zero :
    (toSimplePoint (0 : W.Point) : ℙ k (Fin 3 → k)) =
      Projectivization.mk k ![0, 1, 0] (by simp) := by
  simp

/-- A point of `W` whose line in `ℙ²` is `[x : y : 1]` is the affine point `(x, y)` of `W`. -/
theorem exists_eq_fromAffine_some_of_toProjectivization_eq {P : W.Point} {x y : k}
    {hv : ![x, y, 1] ≠ 0} (h : P.toProjectivization = Projectivization.mk k ![x, y, 1] hv) :
    ∃ hxy : W.toAffine.Nonsingular x y, P = fromAffine (.some x y hxy) := by
  have hxy := (nonsingular_some x y).1 ((exists_toProjectivization_eq_mk_iff _ hv).1 ⟨P, h⟩)
  exact ⟨hxy, toProjectivization_injective (by rw [h, toProjectivization_fromAffine_some])⟩

end Point

/-! ### The chart `Z = 1` -/

section CommRing

variable {R : Type*} [CommRing R] (W' : WeierstrassCurve.Projective R)

@[simp]
private theorem insertNth_two_X_zero :
    Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin 2) R) 2 1 X 0 = X 0 :=
  (rfl)

@[simp]
private theorem insertNth_two_X_one :
    Fin.insertNth (α := fun _ ↦ MvPolynomial (Fin 2) R) 2 1 X 1 = X 1 :=
  (rfl)

/-- In the chart `Z = 1`, the Weierstrass cubic is the affine Weierstrass polynomial
`Y² + a₁XY + a₃Y - (X³ + a₂X² + a₄X + a₆)`. -/
theorem dehomogenize_two_polynomial :
    dehomogenize 2 W'.polynomial = X 1 ^ 2 + C W'.a₁ * X 0 * X 1 + C W'.a₃ * X 1 -
      (X 0 ^ 3 + C W'.a₂ * X 0 ^ 2 + C W'.a₄ * X 0 + C W'.a₆) := by
  simp [polynomial, dehomogenize_X]

end CommRing

/-- `[a : b : 1]` is the point of the chart `Z = 1` with affine coordinates `(a, b)`. -/
private theorem mk_eq_mk_insertNth_two (a b : k) :
    Projectivization.mk k ![a, b, 1] (by simp) =
      Projectivization.mk k (Fin.insertNth (α := fun _ ↦ k) 2 1 ![a, b])
        (Fin.insertNth_one_ne_zero 2 _) := by
  congr 1
  funext j
  fin_cases j <;> rfl

private theorem mk_mem_affineOpen (a b : k) :
    Projectivization.mk k ![a, b, 1] (by simp) ∈ affineOpen 2 := by
  simp [mk_mem_affineOpen_iff]

private theorem rep_two_eq_zero {P : ℙ k (Fin 3 → k)} (hP : P ∉ affineOpen 2) :
    P.rep 2 = 0 := by
  simpa [mem_affineOpen_iff] using hP

private theorem mk_zero_ne_mk (a b : k) :
    Projectivization.mk k ![0, 1, 0] (by simp) ≠ Projectivization.mk k ![a, b, 1] (by simp) := by
  intro h
  have := mk_mem_affineOpen a b
  rw [← h, mk_mem_affineOpen_iff] at this
  simp at this

private theorem rep_mk_zero_zero :
    (Projectivization.mk k (![0, 1, 0] : Fin 3 → k) (by simp)).rep 0 = 0 := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep k (![0, 1, 0] : Fin 3 → k) (by simp)
  rw [← ha]
  simp

/-- The only point of `W.polynomial` on the line `Z = 0` is `O = [0 : 1 : 0]`. -/
private theorem eq_mk_zero_of_rep_two_eq_zero {P : ℙ k (Fin 3 → k)} (hP : P.rep 2 = 0)
    (hF : eval P.rep W.polynomial = 0) : P = Projectivization.mk k ![0, 1, 0] (by simp) := by
  have h0 : P.rep 0 = 0 := X_eq_zero_of_Z_eq_zero (W' := W) hF hP
  rw [← Projectivization.mk_rep P, mk_eq_mk_iff']
  refine ⟨P.rep 1, ?_⟩
  funext j
  fin_cases j <;> simp [h0, hP]

/-- At a point `[a : b : 1]`, the intersection number with `W.polynomial` is computed in the chart
`Z = 1`. -/
private theorem intersectionNumber_mk_two {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1)
    (a b : k) :
    intersectionNumber (Projectivization.mk k ![a, b, 1] (by simp)) L W.polynomial =
      PlaneCurves.Affine.intersectionNumber ![a, b] (dehomogenize 2 L)
        (dehomogenize 2 W.polynomial) := by
  rw [intersectionNumber_eq_affine hL W.isHomogeneous_polynomial (mk_mem_affineOpen a b),
    mk_eq_mk_insertNth_two, affineChart_mk_insertNth_one]

/-- **No line is a component of the Weierstrass cubic**: every nonzero linear form `L` is
relatively prime to `W.polynomial`. -/
theorem isRelPrime_polynomial {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1)
    (hL0 : L ≠ 0) : IsRelPrime L W.polynomial :=
  (W.isHomogeneous_polynomial.isRelPrime_of_irreducible (prime_polynomial W).irreducible hL hL0
    (by norm_num)).symm

/-- On the vertical line through a point `(x, y)` of the affine curve, `W(x, Y)` is
`(Y - y)(Y - negY x y)`. -/
private theorem aeval_dehomogenize_two_polynomial_vertical {x y : k}
    (h : W.toAffine.Equation x y) :
    aeval (fun i ↦ Polynomial.C (![x, 0] i) + Polynomial.C (![0, 1] i) * Polynomial.X)
      (dehomogenize 2 W.polynomial) =
      (Polynomial.X - Polynomial.C y) * (Polynomial.X - Polynomial.C (W.toAffine.negY x y)) := by
  rw [WeierstrassCurve.Affine.equation_iff, ← Polynomial.C_inj] at h
  simp only [map_add, map_mul, map_pow] at h
  simp only [dehomogenize_two_polynomial, WeierstrassCurve.Affine.negY]
  simp
  linear_combination h

/-- On the line `Y = ℓX + ν`, the restriction of `W` is `W(X, ℓX + ν)`. -/
private theorem aeval_dehomogenize_two_polynomial_line (ℓ ν : k) :
    aeval (fun i ↦ Polynomial.C (![0, ν] i) + Polynomial.C (![1, ℓ] i) * Polynomial.X)
      (dehomogenize 2 W.polynomial) =
      W.toAffine.polynomial.eval (Polynomial.C ℓ * Polynomial.X + Polynomial.C ν) := by
  simp [dehomogenize_two_polynomial, WeierstrassCurve.Affine.polynomial]
  ring

/-! ### Lines and the cubic -/

/-- The point `O = [0 : 1 : 0]` is a simple point of `W.polynomial`. -/
theorem isSimplePoint_polynomial_zero :
    IsSimplePoint W.polynomial (Projectivization.mk k ![0, 1, 0] (by simp)) := by
  have := Point.isSimplePoint_toProjectivization (0 : W.Point)
  rwa [Point.toProjectivization_zero] at this

/-- **A non-vertical line meets the Weierstrass cubic at the points above the roots of `W` on the
line**: the line `Y = ℓX + νZ` meets `W.polynomial` in `∑ [x : ℓx + ν : 1]`, the sum over the
roots `x` of `W(X, ℓX + ν)`, counted with multiplicity. It does not pass through `O`. -/
theorem intersectionCycle_X_one_sub (ℓ ν : k) :
    intersectionCycle (X 1 - C ℓ * X 0 - C ν * X 2) W.polynomial =
      ((W.toAffine.polynomial.eval (Polynomial.C ℓ * Polynomial.X + Polynomial.C ν)).roots.map
        fun x ↦ single (Projectivization.mk k ![x, ℓ * x + ν, 1] (by simp)) 1).sum := by
  classical
  have hF := W.isHomogeneous_polynomial
  set L : MvPolynomial (Fin 3) k := C ℓ * X 0 - X 1 + C ν * X 2 with hLdef
  have hLs : L = ∑ i, C (![ℓ, -1, ν] i) * X i := by
    simp [hLdef, Fin.sum_univ_three]
    ring
  have hL : L.IsHomogeneous 1 := hLs ▸ isHomogeneous_sum_C_mul_X _
  have hL0 : L ≠ 0 := hLs ▸ sum_C_mul_X_ne_zero (fun h ↦ by simpa using congrFun h 1)
  have hrel := isRelPrime_polynomial (W := W) hL hL0
  have hneg : (X 1 - C ℓ * X 0 - C ν * X 2 : MvPolynomial (Fin 3) k) = (-1 : k) • L := by
    rw [hLdef, smul_eq_C_mul]
    simp
    ring
  have hdL : dehomogenize 2 L = C ((![1, ℓ] : Fin 2 → k) 1) * (X 0 - C (![0, ν] 0)) -
      C ((![1, ℓ] : Fin 2 → k) 0) * (X 1 - C (![0, ν] 1)) := by
    simp [hLdef]
    ring
  set G := W.toAffine.polynomial.eval (Polynomial.C ℓ * Polynomial.X + Polynomial.C ν)
  have hG0 : G ≠ 0 := by
    have : G = W.toAffine.addPolynomial 0 ν ℓ := by
      simp [G, WeierstrassCurve.Affine.addPolynomial, WeierstrassCurve.Affine.linePolynomial]
    rw [this, WeierstrassCurve.Affine.addPolynomial_eq, neg_ne_zero]
    exact Cubic.ne_zero_of_a_ne_zero one_ne_zero
  have hg : Function.Injective fun x : k ↦ Projectivization.mk k ![x, ℓ * x + ν, 1] (by simp) :=
    fun x x' h ↦ by
      simp only [mk_eq_mk_insertNth_two, mk_insertNth_one_inj, Matrix.vecCons_inj] at h
      exact h.1
  rw [hneg, intersectionCycle_smul_left (by norm_num), Multiset.sum_map_single_eq_toFinsupp]
  ext P
  apply Nat.cast_injective (R := ℕ∞)
  rw [intersectionCycle_apply hL hF hrel, Multiset.toFinsupp_apply]
  by_cases hP : P ∈ affineOpen 2
  · obtain ⟨a, b, rfl⟩ : ∃ a b : k, P = Projectivization.mk k ![a, b, 1] (by simp) := by
      refine ⟨affineChart 2 P 0, affineChart 2 P 1, (eq_mk_insertNth_affineChart hP).trans ?_⟩
      rw [mk_eq_mk_insertNth_two, mk_insertNth_one_inj]
      ext j; fin_cases j <;> rfl
    rw [intersectionNumber_mk_two hL]
    by_cases hb : b = ℓ * a + ν
    · subst hb
      have hab : ![a, ℓ * a + ν] = ![0, ν] + a • ![1, ℓ] := by
        ext j; fin_cases j <;> simp [add_comm, mul_comm]
      rw [Multiset.count_map_eq_count' _ _ hg, Polynomial.count_roots, hdL, hab,
        PlaneCurves.Affine.intersectionNumber_line_eq_rootMultiplicity (by simp)
          (by rwa [aeval_dehomogenize_two_polynomial_line]), aeval_dehomogenize_two_polynomial_line]
    · rw [PlaneCurves.Affine.intersectionNumber_eq_zero_of_eval_ne_zero_left,
        Multiset.count_eq_zero.2]
      · simp
      · simp only [Multiset.mem_map, not_exists, not_and]
        intro x _ h
        obtain ⟨rfl, rfl⟩ : x = a ∧ ℓ * x + ν = b := by simpa [mk_eq_mk_insertNth_two] using h
        exact hb rfl
      · simp only [hLdef, map_add, map_sub, map_mul, eval_C, eval_X, algHom_C, algebraMap_eq,
          dehomogenize_X, insertNth_two_X_zero, insertNth_two_X_one]
        simp only [Fin.insertNth_apply_same, map_one, Matrix.cons_val_zero, Matrix.cons_val_one,
          mul_one]
        intro h
        exact hb (by linear_combination -h)
  · have h2 := rep_two_eq_zero hP
    rw [Multiset.count_eq_zero.2, (intersectionNumber_eq_zero_iff hL hF).2]
    · simp
    · by_contra hc
      push Not at hc
      have h0 : P.rep 0 = 0 := X_eq_zero_of_Z_eq_zero (W' := W) hc.2 h2
      have h1 : P.rep 1 = 0 := by simpa [hLdef, h0, h2] using hc.1
      exact P.rep_ne_zero (by funext j; fin_cases j <;> simp [h0, h1, h2])
    · simp only [Multiset.mem_map, not_exists, not_and]
      intro x _ h
      exact hP (h ▸ mk_mem_affineOpen _ _)

/-- The tangent line of `W.polynomial` at `O = [0 : 1 : 0]` is the line at infinity `Z = 0`. -/
theorem isTangentAt_zero_X_two :
    IsTangentAt W.polynomial (Projectivization.mk k ![0, 1, 0] (by simp)) (X 2) := by
  have hT :=
    isSimplePoint_polynomial_zero.isTangentAt_tangentLine W.isHomogeneous_polynomial
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep k (![0, 1, 0] : Fin 3 → k) (by simp)
  rw [← ha, tangentLine_def] at hT
  simp only [Fin.sum_univ_three, polynomial] at hT
  refine isTangentAt_def.2 ⟨isHomogeneous_X k 2, X_ne_zero 2, by simp [← ha],
    dvd_of_mul_left_dvd (a := C ((a : k) ^ 2)) ?_⟩
  simpa [polynomial, pderiv_X, Pi.single_apply, Units.smul_def] using
    (isTangentAt_def.1 hT).2.2.2

/-- A line through `O` other than the line at infinity meets `W.polynomial` at `O` once. -/
private theorem intersectionNumber_zero_eq_one {L : MvPolynomial (Fin 3) k}
    (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0)
    (hLO : eval (Projectivization.mk k ![0, 1, 0] (by simp)).rep L = 0)
    (hLX : ¬Associated L (X 2)) :
    intersectionNumber (Projectivization.mk k ![0, 1, 0] (by simp)) L W.polynomial = 1 := by
  have hF := W.isHomogeneous_polynomial
  have hs := isSimplePoint_polynomial_zero (W := W)
  refine le_antisymm ?_ (one_le_intersectionNumber hL hF hLO hs.eval_rep_eq_zero)
  by_contra hlt
  rw [not_le, intersectionNumber_comm, ← isSimplePoint_def.1 hs,
    ← isTangentAt_iff_mult_lt_intersectionNumber hF (prime_polynomial W).ne_zero hL hL0 hLO]
    at hlt
  exact hLX ((hs.associated_tangentLine_of_isTangentAt hF hlt).trans
    (hs.associated_tangentLine_of_isTangentAt hF isTangentAt_zero_X_two).symm)

/-- **A vertical line meets the Weierstrass cubic at `O` and at the two points above `x`**: for a
point `(x, y)` of the affine curve, `(X - xZ) • W.polynomial = O + [x : y : 1] + [x : y' : 1]`,
where `y' = W.toAffine.negY x y` is the other root of `W(x, Y)`. When `y = y'` the line is
tangent there and the point is counted twice. -/
theorem intersectionCycle_X_zero_sub {x y : k} (h : W.toAffine.Equation x y) :
    intersectionCycle (X 0 - C x * X 2) W.polynomial =
      single (Projectivization.mk k ![0, 1, 0] (by simp)) 1 +
        single (Projectivization.mk k ![x, y, 1] (by simp)) 1 +
        single (Projectivization.mk k ![x, W.toAffine.negY x y, 1] (by simp)) 1 := by
  have hF := W.isHomogeneous_polynomial
  have hLs : (X 0 - C x * X 2 : MvPolynomial (Fin 3) k) = ∑ i, C (![1, 0, -x] i) * X i := by
    simp [Fin.sum_univ_three]
    ring
  have hL : (X 0 - C x * X 2 : MvPolynomial (Fin 3) k).IsHomogeneous 1 :=
    hLs ▸ isHomogeneous_sum_C_mul_X _
  have hL0 : (X 0 - C x * X 2 : MvPolynomial (Fin 3) k) ≠ 0 :=
    hLs ▸ sum_C_mul_X_ne_zero (fun h ↦ by simpa using congrFun h 0)
  have hrel := isRelPrime_polynomial (W := W) hL hL0
  have hdL : dehomogenize 2 (X 0 - C x * X 2 : MvPolynomial (Fin 3) k) =
      C ((![0, 1] : Fin 2 → k) 1) * (X 0 - C (![x, 0] 0)) -
        C ((![0, 1] : Fin 2 → k) 0) * (X 1 - C (![x, 0] 1)) := by
    simp [dehomogenize_X]
  have hG0 := aeval_dehomogenize_two_polynomial_vertical h
  have hGne : (Polynomial.X - Polynomial.C y) *
      (Polynomial.X - Polynomial.C (W.toAffine.negY x y)) ≠ 0 :=
    mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _)
  classical
  ext P
  apply Nat.cast_injective (R := ℕ∞)
  rw [intersectionCycle_apply hL hF hrel]
  by_cases hP : P ∈ affineOpen 2
  · obtain ⟨a, b, rfl⟩ : ∃ a b : k, P = Projectivization.mk k ![a, b, 1] (by simp) := by
      refine ⟨affineChart 2 P 0, affineChart 2 P 1, (eq_mk_insertNth_affineChart hP).trans ?_⟩
      rw [mk_eq_mk_insertNth_two, mk_insertNth_one_inj]
      ext j; fin_cases j <;> rfl
    rw [intersectionNumber_mk_two hL]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
      ite_eq_right_iff.2 (fun h ↦ absurd h (mk_zero_ne_mk a b))]
    simp only [mk_eq_mk_insertNth_two, mk_insertNth_one_inj, Matrix.vecCons_inj, and_true]
    by_cases ha : x = a
    · subst ha
      have hab : ![x, b] = ![x, 0] + b • ![0, 1] := by
        ext j; fin_cases j <;> simp
      rw [hdL, hab, PlaneCurves.Affine.intersectionNumber_line_eq_rootMultiplicity (by simp)
        (hG0 ▸ hGne), hG0, Polynomial.rootMultiplicity_mul hGne,
        Polynomial.rootMultiplicity_X_sub_C, Polynomial.rootMultiplicity_X_sub_C]
      simp [eq_comm]
    · rw [PlaneCurves.Affine.intersectionNumber_eq_zero_of_eval_ne_zero_left]
      · simp [ha]
      · simpa [sub_eq_zero] using Ne.symm ha
  · have h2 := rep_two_eq_zero hP
    have hne : ∀ a b : k, Projectivization.mk k ![a, b, 1] (by simp) ≠ P := fun a b h ↦
      hP (h ▸ mk_mem_affineOpen a b)
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, hne, ↓reduceIte]
    by_cases hPO : Projectivization.mk k ![0, 1, 0] (by simp) = P
    · subst hPO
      rw [intersectionNumber_zero_eq_one hL hL0 (by simp [rep_mk_zero_zero, h2])]
      · simp
      · rintro ⟨u, hu⟩
        have := congrArg (eval ![1, 0, 0]) hu
        simp only [eval_mul, eval_sub, eval_X, eval_C] at this
        simpa using (u.isUnit.map (eval ![1, 0, 0])).ne_zero (by simpa using this)
    · rw [(intersectionNumber_eq_zero_iff hL hF).2]
      · simp [hPO]
      by_contra hc
      push Not at hc
      exact hPO (eq_mk_zero_of_rep_two_eq_zero h2 hc.2).symm

/-! ### Collinearity and the chord–tangent group -/

/-- `W.polynomial` is a cubic form, as an instance for the chord–tangent group `CubicGroup`. -/
instance fact_isHomogeneous_polynomial : Fact (W.polynomial.IsHomogeneous 3) :=
  ⟨W.isHomogeneous_polynomial⟩

/-- `W.polynomial` is irreducible, as an instance for the chord–tangent group `CubicGroup`. -/
instance fact_irreducible_polynomial : Fact (Irreducible W.polynomial) :=
  ⟨W.prime_polynomial.irreducible⟩

/-- `O = [0 : 1 : 0]` is a simple point of `W.polynomial`, as an instance for the chord–tangent
group `CubicGroup` with zero `O`. -/
instance fact_isSimplePoint_toProjectivization_zero :
    Fact (IsSimplePoint W.polynomial (0 : W.Point).toProjectivization) :=
  ⟨Point.isSimplePoint_toProjectivization 0⟩

/-- The line `X - xZ` is a nonzero linear form. -/
private theorem isHomogeneous_X_zero_sub (x : k) :
    (X 0 - C x * X 2 : MvPolynomial (Fin 3) k).IsHomogeneous 1 :=
  (isHomogeneous_X k 0).sub (isHomogeneous_C_mul_X x 2)

private theorem X_zero_sub_ne_zero (x : k) : (X 0 - C x * X 2 : MvPolynomial (Fin 3) k) ≠ 0 :=
  fun h ↦ by simpa using congrArg (eval ![1, 0, 0]) h

/-- The line `Y - ℓX - νZ` is a nonzero linear form. -/
private theorem isHomogeneous_X_one_sub (ℓ ν : k) :
    (X 1 - C ℓ * X 0 - C ν * X 2 : MvPolynomial (Fin 3) k).IsHomogeneous 1 :=
  ((isHomogeneous_X k 1).sub (isHomogeneous_C_mul_X ℓ 0)).sub (isHomogeneous_C_mul_X ν 2)

private theorem X_one_sub_ne_zero (ℓ ν : k) :
    (X 1 - C ℓ * X 0 - C ν * X 2 : MvPolynomial (Fin 3) k) ≠ 0 :=
  fun h ↦ by simpa using congrArg (eval ![0, 1, 0]) h

section IsAlgClosed

variable [IsAlgClosed k]

/-- **The line at infinity meets the Weierstrass cubic only at `O`, three times**:
`Z • W.polynomial = 3 O`, for `O = [0 : 1 : 0]`. -/
theorem intersectionCycle_X_two :
    intersectionCycle (X 2) W.polynomial =
      single (Projectivization.mk k ![0, 1, 0] (by simp)) 3 := by
  have hL : (X 2 : MvPolynomial (Fin 3) k).IsHomogeneous 1 := isHomogeneous_X k 2
  have hrel := isRelPrime_polynomial (W := W) hL (X_ne_zero 2)
  have hsupp : (intersectionCycle (X 2) W.polynomial).support ⊆
      {Projectivization.mk k ![0, 1, 0] (by simp)} := by
    intro P hP
    rw [mem_support_intersectionCycle_iff hL W.isHomogeneous_polynomial hrel, eval_X] at hP
    exact Finset.mem_singleton.2 (eq_mk_zero_of_rep_two_eq_zero hP.1 hP.2)
  rw [Finsupp.support_subset_singleton] at hsupp
  have hdeg := degree_intersectionCycle hL W.isHomogeneous_polynomial hrel
  rw [hsupp, Finsupp.degree_single] at hdeg
  rw [hsupp, hdeg]

/-- **`O = [0 : 1 : 0]` is a flex of the Weierstrass cubic**: its tangent line `Z = 0` meets
`W.polynomial` there three times. -/
theorem isFlex_zero : IsFlex W.polynomial (Projectivization.mk k ![0, 1, 0] (by simp)) := by
  rw [isFlex_iff_of_isTangentAt W.isHomogeneous_polynomial isSimplePoint_polynomial_zero
    isTangentAt_zero_X_two, intersectionNumber_comm, ← intersectionCycle_apply
    (isHomogeneous_X k 2) W.isHomogeneous_polynomial
    (isRelPrime_polynomial (isHomogeneous_X k 2) (X_ne_zero 2)), intersectionCycle_X_two,
    Finsupp.single_eq_same]
  norm_num

namespace Point

/-- `O`, `P` and `-P` are the intersection of a line with `W.polynomial`: the line at infinity if
`P = 0`, and a vertical line otherwise. -/
private theorem exists_line_zero_neg (P : W.Point) :
    ∃ L : MvPolynomial (Fin 3) k, L.IsHomogeneous 1 ∧ L ≠ 0 ∧
      intersectionCycle L W.polynomial = single (0 : W.Point).toProjectivization 1 +
        single P.toProjectivization 1 + single (-P).toProjectivization 1 := by
  classical
  obtain ⟨A, rfl⟩ := (toAffineAddEquiv W).symm.surjective P
  rw [← map_neg, toAffineAddEquiv_symm_apply, toAffineAddEquiv_symm_apply]
  rcases A with _ | ⟨x, y, h⟩
  · refine ⟨X 2, isHomogeneous_X k 2, X_ne_zero 2, ?_⟩
    rw [← Affine.Point.zero_def, neg_zero, fromAffine_zero, intersectionCycle_X_two,
      toProjectivization_zero, ← Finsupp.single_add, ← Finsupp.single_add]
  · refine ⟨X 0 - C x * X 2, isHomogeneous_X_zero_sub x, X_zero_sub_ne_zero x, ?_⟩
    rw [Affine.Point.neg_some, toProjectivization_fromAffine_some,
      toProjectivization_fromAffine_some, toProjectivization_zero,
      intersectionCycle_X_zero_sub h.1]

omit [IsAlgClosed k] in
/-- Three nonzero points of `W` that add to zero are the intersection of a non-vertical line with
`W.polynomial`. -/
private theorem exists_line_of_add_add_eq_zero_of_ne_zero {P Q R : W.Point} (h : P + Q + R = 0)
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hR : R ≠ 0) :
    ∃ L : MvPolynomial (Fin 3) k, L.IsHomogeneous 1 ∧ L ≠ 0 ∧
      intersectionCycle L W.polynomial = single P.toProjectivization 1 +
        single Q.toProjectivization 1 + single R.toProjectivization 1 := by
  classical
  obtain ⟨A, rfl⟩ := (toAffineAddEquiv W).symm.surjective P
  obtain ⟨B, rfl⟩ := (toAffineAddEquiv W).symm.surjective Q
  obtain ⟨C', rfl⟩ := (toAffineAddEquiv W).symm.surjective R
  rw [← map_add, ← map_add, AddEquivClass.map_eq_zero_iff] at h
  simp only [toAffineAddEquiv_symm_apply] at hP hQ hR ⊢
  rcases A with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd (by rw [← Affine.Point.zero_def, fromAffine_zero]) hP
  rcases B with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd (by rw [← Affine.Point.zero_def, fromAffine_zero]) hQ
  rcases C' with _ | ⟨x₃, y₃, h₃⟩
  · exact absurd (by rw [← Affine.Point.zero_def, fromAffine_zero]) hR
  obtain ⟨ℓ, ν, rfl, rfl, rfl, hW⟩ := (Affine.Point.some_add_some_add_some_eq_zero_iff h₁ h₂ h₃).1 h
  refine ⟨_, isHomogeneous_X_one_sub ℓ ν, X_one_sub_ne_zero ℓ ν, ?_⟩
  have hne : ∀ x : k, Polynomial.X - Polynomial.C x ≠ 0 := Polynomial.X_sub_C_ne_zero
  rw [intersectionCycle_X_one_sub, hW, Polynomial.roots_neg,
    Polynomial.roots_mul (mul_ne_zero (mul_ne_zero (hne _) (hne _)) (hne _)),
    Polynomial.roots_mul (mul_ne_zero (hne _) (hne _))]
  simp [toProjectivization_fromAffine_some, add_assoc]

/-- Three points of `W` that add to zero are the intersection of a line with `W.polynomial`. -/
private theorem exists_line_of_add_add_eq_zero {P Q R : W.Point} (h : P + Q + R = 0) :
    ∃ L : MvPolynomial (Fin 3) k, L.IsHomogeneous 1 ∧ L ≠ 0 ∧
      intersectionCycle L W.polynomial = single P.toProjectivization 1 +
        single Q.toProjectivization 1 + single R.toProjectivization 1 := by
  by_cases hP : P = 0
  · subst hP
    rw [zero_add, add_eq_zero_iff_neg_eq] at h
    subst h
    exact exists_line_zero_neg Q
  by_cases hQ : Q = 0
  · subst hQ
    rw [add_zero, add_eq_zero_iff_neg_eq] at h
    subst h
    obtain ⟨L, hL, hL0, hc⟩ := exists_line_zero_neg P
    exact ⟨L, hL, hL0, by rw [hc]; abel⟩
  by_cases hR : R = 0
  · subst hR
    rw [add_zero, add_eq_zero_iff_neg_eq] at h
    subst h
    obtain ⟨L, hL, hL0, hc⟩ := exists_line_zero_neg P
    exact ⟨L, hL, hL0, by rw [hc]; abel⟩
  exact exists_line_of_add_add_eq_zero_of_ne_zero h hP hQ hR

/-- **Fulton's third point on a Weierstrass cubic**: the third point `φ(P, Q)` of the chord through
the points of `W.polynomial` given by `P` and `Q` is the point given by `-(P + Q)`. -/
theorem thirdPoint_toProjectivization (P Q : W.Point) :
    thirdPoint W.polynomial P.toProjectivization Q.toProjectivization =
      (-(P + Q)).toProjectivization := by
  obtain ⟨L, hL, hL0, h⟩ := exists_line_of_add_add_eq_zero (add_neg_cancel (P + Q))
  exact (eq_thirdPoint_of_intersectionCycle_eq W.isHomogeneous_polynomial
    W.prime_polynomial.irreducible P.isSimplePoint_toProjectivization
    Q.isSimplePoint_toProjectivization hL hL0 h).symm

/-- **Three points of a Weierstrass curve add to zero exactly when they are collinear**: for
points `P`, `Q`, `R` of `W`, `P + Q + R = 0` if and only if some line `L` meets the cubic
`W.polynomial` in `L • W.polynomial = P + Q + R`, counted with multiplicity. -/
theorem add_add_eq_zero_iff (P Q R : W.Point) :
    P + Q + R = 0 ↔ ∃ L : MvPolynomial (Fin 3) k, L.IsHomogeneous 1 ∧ L ≠ 0 ∧
      intersectionCycle L W.polynomial = single P.toProjectivization 1 +
        single Q.toProjectivization 1 + single R.toProjectivization 1 := by
  refine ⟨exists_line_of_add_add_eq_zero, fun ⟨L, hL, hL0, h⟩ ↦ ?_⟩
  have hR := eq_thirdPoint_of_intersectionCycle_eq W.isHomogeneous_polynomial
    W.prime_polynomial.irreducible P.isSimplePoint_toProjectivization
    Q.isSimplePoint_toProjectivization hL hL0 h
  rw [thirdPoint_toProjectivization] at hR
  rw [toProjectivization_injective hR, add_neg_cancel]

/-- **Mathlib's group law on a Weierstrass curve is Fulton's chord–tangent group law**: the
bijection `toSimplePoint` between the points of `W` and the simple points of `W.polynomial` is an
isomorphism from `W.Point` to the chord–tangent group `CubicGroup W.polynomial O` with zero
`O = [0 : 1 : 0]`. -/
noncomputable def toCubicGroup :
    W.Point ≃+ CubicGroup W.polynomial (0 : W.Point).toProjectivization :=
  AddEquiv.mk' (toSimplePoint.trans CubicGroup.equivSubtype.symm) fun P Q ↦ by
    refine CubicGroup.ext ?_
    simp only [Equiv.trans_apply, CubicGroup.point_equivSubtype_symm_apply,
      coe_toSimplePoint_apply, CubicGroup.point_add]
    rw [thirdPoint_toProjectivization, thirdPoint_toProjectivization, zero_add, neg_neg]

/-- `toCubicGroup` sends a point of `W` to its line in `ℙ²`. -/
@[simp]
theorem point_toCubicGroup_apply (P : W.Point) :
    (toCubicGroup P).point = P.toProjectivization :=
  CubicGroup.point_equivSubtype_symm_apply (toSimplePoint P)

end Point

/-! ### Problems 5.38 and 5.40 -/

/-- A point of the chord–tangent group of `W.polynomial` whose line is `[x : y : 1]` is the affine
point `(x, y)` of `W`, through `toCubicGroup` and Mathlib's `toAffineAddEquiv`. -/
private theorem exists_toAffineAddEquiv_eq_some [DecidableEq k]
    {A : CubicGroup W.polynomial (0 : W.Point).toProjectivization} {x y : k} {hv : ![x, y, 1] ≠ 0}
    (h : A.point = Projectivization.mk k ![x, y, 1] hv) :
    ∃ hxy : W.toAffine.Nonsingular x y,
      Point.toAffineAddEquiv W (Point.toCubicGroup.symm A) = .some x y hxy := by
  obtain ⟨hxy, hP⟩ := Point.exists_eq_fromAffine_some_of_toProjectivization_eq
    (P := Point.toCubicGroup.symm A) (by rw [← Point.point_toCubicGroup_apply,
      AddEquiv.apply_symm_apply, h])
  exact ⟨hxy, by rw [hP, ← Point.toAffineAddEquiv_symm_apply, AddEquiv.apply_symm_apply]⟩

/-- **Addition formulas on the cubic `Y²Z = X³ + aX²Z + bXZ² + cZ³`** (Problem 5.38 of Fulton).
Let `W` have `a₁ = a₃ = 0`, so that `W.polynomial` is this cubic with `a = a₂`, `b = a₄`,
`c = a₆`, and let `P₁ ⊕ P₂ = P₃` in the chord–tangent group with zero `O = [0 : 1 : 0]`, where
`Pᵢ = [xᵢ : yᵢ : 1]`. If either `x₁ ≠ x₂` and `λ = (y₁ - y₂) / (x₁ - x₂)`, or `P₁ = P₂` and
`λ = (3x₁² + 2ax₁ + b) / (2y₁)`, then, with `μ = y₁ - λx₁`, `x₃ = λ² - a - x₁ - x₂` and
`y₃ = -λx₃ - μ`. No hypothesis on the characteristic is needed. -/
theorem add_coords_of_a₁_eq_zero_of_a₃_eq_zero (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {A₁ A₂ A₃ : CubicGroup W.polynomial (0 : W.Point).toProjectivization}
    {x₁ y₁ x₂ y₂ x₃ y₃ ℓ : k} {hv₁ : ![x₁, y₁, 1] ≠ 0} {hv₂ : ![x₂, y₂, 1] ≠ 0}
    {hv₃ : ![x₃, y₃, 1] ≠ 0} (h₁ : A₁.point = Projectivization.mk k ![x₁, y₁, 1] hv₁)
    (h₂ : A₂.point = Projectivization.mk k ![x₂, y₂, 1] hv₂)
    (h₃ : A₃.point = Projectivization.mk k ![x₃, y₃, 1] hv₃) (hA : A₁ + A₂ = A₃)
    (hℓ : x₁ ≠ x₂ ∧ ℓ = (y₁ - y₂) / (x₁ - x₂) ∨
      x₁ = x₂ ∧ y₁ = y₂ ∧ ℓ = (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄) / (2 * y₁)) :
    x₃ = ℓ ^ 2 - W.a₂ - x₁ - x₂ ∧ y₃ = -ℓ * x₃ - (y₁ - ℓ * x₁) := by
  classical
  obtain ⟨hp₁, e₁⟩ := exists_toAffineAddEquiv_eq_some h₁
  obtain ⟨hp₂, e₂⟩ := exists_toAffineAddEquiv_eq_some h₂
  obtain ⟨hp₃, e₃⟩ := exists_toAffineAddEquiv_eq_some h₃
  have hsum : Affine.Point.some x₁ y₁ hp₁ + .some x₂ y₂ hp₂ = .some x₃ y₃ hp₃ := by
    rw [← e₁, ← e₂, ← e₃, ← map_add, ← map_add, hA]
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) := fun hxy ↦
    Affine.Point.some_ne_zero hp₃ (by rw [← hsum, Affine.Point.add_of_Y_eq hxy.1 hxy.2])
  rw [Affine.Point.add_some hxy, Affine.Point.some.injEq] at hsum
  obtain ⟨rfl, rfl⟩ := hsum
  have hslope : W.toAffine.slope x₁ x₂ y₁ y₂ = ℓ := by
    rcases hℓ with ⟨hx, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Affine.slope_of_X_ne hx
    · rw [Affine.slope_of_Y_ne rfl fun h ↦ hxy ⟨rfl, h⟩]
      simp only [Affine.negY, ha₁, ha₃]
      congr 1 <;> ring
  subst hslope
  simp only [Affine.addX, Affine.addY, Affine.negAddY, Affine.negY, ha₁, ha₃]
  constructor <;> ring

section RationalPoints

variable (k₀ : Type*) [Field k₀] [Algebra k₀ k] (W₀ : WeierstrassCurve k₀)

open Classical in
/-- **The `k₀`-rational points of a Weierstrass cubic** (Problem 5.40 of Fulton). For a
Weierstrass curve `W₀` over a subfield `k₀` of `k`, the points of the cubic of `W₀` over `k` with
coordinates in `k₀` form a subgroup of its chord–tangent group with zero `O = [0 : 1 : 0]`
(`mem_rationalPoints_iff`). It is the image of Mathlib's points of `W₀` over `k₀`. -/
noncomputable def rationalPoints :
    AddSubgroup (CubicGroup (W₀.baseChange k).toProjective.polynomial
      (0 : (W₀.baseChange k).toProjective.Point).toProjectivization) :=
  ((Point.toCubicGroup.toAddMonoidHom.comp
    (Point.toAffineAddEquiv (W₀.baseChange k).toProjective).symm.toAddMonoidHom).comp
      (Affine.Point.map (W' := W₀) (Algebra.ofId k₀ k))).range

open Classical in
/-- `rationalPoints k₀ W₀` is the image of Mathlib's points of `W₀` over `k₀`. -/
theorem rationalPoints_def : rationalPoints k₀ W₀ =
    ((Point.toCubicGroup.toAddMonoidHom.comp
      (Point.toAffineAddEquiv (W₀.baseChange k).toProjective).symm.toAddMonoidHom).comp
        (Affine.Point.map (W' := W₀) (Algebra.ofId k₀ k))).range :=
  (rfl)

variable {k₀ W₀}

/-- **The `k₀`-rational points of a Weierstrass cubic**: a point of the chord–tangent group of the
cubic of `W₀` over `k` is in `rationalPoints k₀ W₀` exactly when it has homogeneous coordinates
in `k₀`. -/
theorem mem_rationalPoints_iff {A : CubicGroup (W₀.baseChange k).toProjective.polynomial
      (0 : (W₀.baseChange k).toProjective.Point).toProjectivization} :
    A ∈ rationalPoints k₀ W₀ ↔ ∃ (v : Fin 3 → k₀) (hv : algebraMap k₀ k ∘ v ≠ 0),
      A.point = Projectivization.mk k (algebraMap k₀ k ∘ v) hv := by
  classical
  have hmk : ∀ {u w : Fin 3 → k} (hu : u ≠ 0) (hw : w ≠ 0), u = w →
      Projectivization.mk k u hu = Projectivization.mk k w hw := by
    rintro _ _ _ _ rfl
    rfl
  rw [rationalPoints_def, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨B, rfl⟩
    rcases B with _ | ⟨x, y, h⟩
    · refine ⟨![0, 1, 0], fun h ↦ by simpa using congrFun h 1, ?_⟩
      rw [← Affine.Point.zero_def, map_zero, CubicGroup.point_zero, Point.toProjectivization_zero]
      exact hmk _ _ (by ext i; fin_cases i <;> simp)
    · refine ⟨![x, y, 1], fun h ↦ by simpa using congrFun h 2, ?_⟩
      simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, Affine.Point.map_some,
        Point.toAffineAddEquiv_symm_apply, Point.point_toCubicGroup_apply,
        Point.toProjectivization_fromAffine_some]
      exact hmk _ _ (by ext i; fin_cases i <;> simp)
  · rintro ⟨v, hv, h⟩
    by_cases hz : v 2 = 0
    · have hns : (W₀.baseChange k).toProjective.Nonsingular (algebraMap k₀ k ∘ v) :=
        (Point.exists_toProjectivization_eq_mk_iff _ hv).1 ⟨Point.toCubicGroup.symm A, by
          rw [← Point.point_toCubicGroup_apply, AddEquiv.apply_symm_apply, h]⟩
      have h0 : algebraMap k₀ k (v 0) = 0 := X_eq_zero_of_Z_eq_zero hns.1 (by simp [hz])
      refine ⟨0, CubicGroup.ext ?_⟩
      symm
      rw [h, map_zero, CubicGroup.point_zero, Point.toProjectivization_zero, mk_eq_mk_iff']
      exact ⟨algebraMap k₀ k (v 1), by ext i; fin_cases i <;> simp [h0, hz]⟩
    · set x := v 0 / v 2
      set y := v 1 / v 2
      have hA : A.point = Projectivization.mk k ![algebraMap k₀ k x, algebraMap k₀ k y, 1]
          (fun h ↦ by simpa using congrFun h 2) := by
        rw [h, mk_eq_mk_iff']
        refine ⟨algebraMap k₀ k (v 2), ?_⟩
        ext i
        fin_cases i <;>
          simp [x, y, mul_div_cancel₀ _ ((map_ne_zero (algebraMap k₀ k)).2 hz)]
      obtain ⟨hxy, -⟩ := Point.exists_eq_fromAffine_some_of_toProjectivization_eq
        (P := Point.toCubicGroup.symm A) (by
          rw [← Point.point_toCubicGroup_apply, AddEquiv.apply_symm_apply, hA])
      have h₀ := (Affine.baseChange_nonsingular (W := W₀) (Algebra.ofId k₀ k).injective x y).1 hxy
      refine ⟨.some x y h₀, CubicGroup.ext ?_⟩
      simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, Affine.Point.map_some,
        Point.toAffineAddEquiv_symm_apply, Point.point_toCubicGroup_apply,
        Point.toProjectivization_fromAffine_some, hA]
      rfl

/-- **Fulton's third point of two `k₀`-rational points is `k₀`-rational** (Problem 5.40 of
Fulton): the third point `φ(A, B)` of the chord through two points of `rationalPoints k₀ W₀` is in
`rationalPoints k₀ W₀`. -/
theorem chord_mem_rationalPoints {A B : CubicGroup (W₀.baseChange k).toProjective.polynomial
      (0 : (W₀.baseChange k).toProjective.Point).toProjectivization}
    (hA : A ∈ rationalPoints k₀ W₀) (hB : B ∈ rationalPoints k₀ W₀) :
    CubicGroup.chord A B ∈ rationalPoints k₀ W₀ := by
  have h0 : CubicGroup.chord (0 : CubicGroup (W₀.baseChange k).toProjective.polynomial
      (0 : (W₀.baseChange k).toProjective.Point).toProjectivization) 0 = 0 := by
    refine CubicGroup.ext ?_
    rw [CubicGroup.point_chord, CubicGroup.point_zero, Point.thirdPoint_toProjectivization,
      add_zero, neg_zero]
  rw [CubicGroup.chord_eq_sub, h0, zero_sub]
  exact sub_mem (neg_mem hA) hB

end RationalPoints

/-- **Chord–tangent addition on a Weierstrass cubic agrees with Mathlib's group law.** Let `W` be a
Weierstrass curve over an algebraically closed field `k`, `F = W.polynomial` its cubic and
`O = [0 : 1 : 0]`. Then
1. `F` is irreducible;
2. `O` is a simple point and a flex of `F`, with tangent line `Z = 0`;
3. `F` is nonsingular exactly when `W.Δ ≠ 0`;
4. the simple points of `F` are exactly the points of `W`;
5. Fulton's third point of the chord through `P` and `Q` is `-(P + Q)`;
6. Fulton's sum `P ⊕ Q` with zero `O` is Mathlib's `P + Q`, through `toCubicGroup`;
7. the addition formulas of Problem 5.38 hold when `a₁ = a₃ = 0`;
8. if `W` comes from a Weierstrass curve `W₀` over a subfield `k₀`, the points of `F` with
   coordinates in `k₀` form a subgroup of the chord–tangent group, closed under the third point
   (Problem 5.40).

Milestone: *Chord–tangent addition on a Weierstrass cubic agrees with Mathlib's group law*. -/
theorem chordTangentAddition_eq_add :
    Irreducible W.polynomial ∧
    (IsSimplePoint W.polynomial (Projectivization.mk k ![0, 1, 0] (by simp)) ∧
      IsFlex W.polynomial (Projectivization.mk k ![0, 1, 0] (by simp)) ∧
      tangentLine W.polynomial ![0, 1, 0] = X 2) ∧
    (IsNonsingular W.polynomial ↔ W.Δ ≠ 0) ∧
    (∀ P, IsSimplePoint W.polynomial P ↔ P ∈ Set.range (Point.toProjectivization (W := W))) ∧
    (∀ P Q : W.Point, thirdPoint W.polynomial P.toProjectivization Q.toProjectivization =
      (-(P + Q)).toProjectivization) ∧
    (∀ P Q : W.Point, Point.toCubicGroup (P + Q) = Point.toCubicGroup P + Point.toCubicGroup Q) ∧
    (W.a₁ = 0 → W.a₃ = 0 →
      ∀ {A₁ A₂ A₃ : CubicGroup W.polynomial (0 : W.Point).toProjectivization}
        {x₁ y₁ x₂ y₂ x₃ y₃ ℓ : k} {hv₁ : ![x₁, y₁, 1] ≠ 0} {hv₂ : ![x₂, y₂, 1] ≠ 0}
        {hv₃ : ![x₃, y₃, 1] ≠ 0}, A₁.point = Projectivization.mk k ![x₁, y₁, 1] hv₁ →
        A₂.point = Projectivization.mk k ![x₂, y₂, 1] hv₂ →
        A₃.point = Projectivization.mk k ![x₃, y₃, 1] hv₃ → A₁ + A₂ = A₃ →
        (x₁ ≠ x₂ ∧ ℓ = (y₁ - y₂) / (x₁ - x₂) ∨
          x₁ = x₂ ∧ y₁ = y₂ ∧ ℓ = (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄) / (2 * y₁)) →
        x₃ = ℓ ^ 2 - W.a₂ - x₁ - x₂ ∧ y₃ = -ℓ * x₃ - (y₁ - ℓ * x₁)) ∧
    (∀ (k₀ : Type*) [Field k₀] [Algebra k₀ k] (W₀ : WeierstrassCurve k₀),
      W₀.baseChange k = W →
      ∃ H : AddSubgroup (CubicGroup W.polynomial (0 : W.Point).toProjectivization),
        (∀ A, A ∈ H ↔ ∃ (v : Fin 3 → k₀) (hv : algebraMap k₀ k ∘ v ≠ 0),
          A.point = Projectivization.mk k (algebraMap k₀ k ∘ v) hv) ∧
        ∀ A ∈ H, ∀ B ∈ H, CubicGroup.chord A B ∈ H) := by
  refine ⟨W.prime_polynomial.irreducible, ⟨isSimplePoint_polynomial_zero, isFlex_zero,
    tangentLine_polynomial_zero W⟩, isNonsingular_polynomial_iff,
    fun P ↦ (Point.mem_range_toProjectivization_iff_isSimplePoint P).symm,
    Point.thirdPoint_toProjectivization, fun P Q ↦ map_add _ P Q,
    fun ha₁ ha₃ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ hA hℓ ↦
      add_coords_of_a₁_eq_zero_of_a₃_eq_zero ha₁ ha₃ h₁ h₂ h₃ hA hℓ, ?_⟩
  rintro k₀ _ _ W₀ rfl
  exact ⟨rationalPoints k₀ W₀, fun _ ↦ mem_rationalPoints_iff,
    fun _ hA _ hB ↦ chord_mem_rationalPoints hA hB⟩

end IsAlgClosed

end WeierstrassCurve.Projective

/-! ### Cubics with a flex -/

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k}
  {O : ℙ k (Fin 3 → k)}

open WeierstrassCurve.Projective

/-- Addition of points of `W` under a change of coordinates that carries an irreducible cubic `F`
to `c • W.polynomial`: if `T` is the projective change of coordinates of `M`, then
`T(P + Q) = φ(T(O'), φ(T(P), T(Q)))` on `F`, for `O' = [0 : 1 : 0]`. -/
private theorem map_toProjectivization_add {W : WeierstrassCurve k} (hF : F.IsHomogeneous 3)
    (hirr : Irreducible F) (M : GL (Fin 3) k) {c : k} (hc : c ≠ 0)
    (hMF : linearSubst M.1 F = c • W.toProjective.polynomial) (P Q : W.toProjective.Point) :
    map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) (P + Q).toProjectivization =
      thirdPoint F
        (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit)
          (0 : W.toProjective.Point).toProjectivization)
        (thirdPoint F (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit)
          P.toProjectivization)
          (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit)
            Q.toProjectivization)) := by
  have hs (R : W.toProjective.Point) :
      IsSimplePoint (linearSubst M.1 F) R.toProjectivization := by
    rw [hMF, isSimplePoint_smul_iff hc]
    exact R.isSimplePoint_toProjectivization
  rw [← thirdPoint_linearSubst hF hirr M (hs P) (hs Q), hMF, thirdPoint_smul hc,
    Point.thirdPoint_toProjectivization, ← thirdPoint_linearSubst hF hirr M (hs 0) (hs _), hMF,
    thirdPoint_smul hc, Point.thirdPoint_toProjectivization, zero_add, neg_neg]

/-- **The group of a cubic with a flex is the group of a Weierstrass curve.** For an irreducible
cubic `F` over an algebraically closed field and a flex `O` of `F`, the chord–tangent group
`CubicGroup F O` of the simple points of `F` with zero `O` is isomorphic to Mathlib's group of
points of a Weierstrass curve `W`, and `W.Δ ≠ 0` when `F` is nonsingular. The isomorphism is
the projective change of coordinates that carries `F` to a multiple of `W.polynomial` and
`[0 : 1 : 0]` to `O` ([Fulton2008], Problem 5.24 (a)), composed with
`WeierstrassCurve.Projective.Point.toCubicGroup`. -/
theorem exists_addEquiv_weierstrass_of_isFlex [hF : Fact (F.IsHomogeneous 3)]
    [hirr : Fact (Irreducible F)] [Fact (IsSimplePoint F O)] (hO : IsFlex F O) :
    ∃ W : WeierstrassCurve k, (IsNonsingular F → W.Δ ≠ 0) ∧
      Nonempty (CubicGroup F O ≃+ W.toProjective.Point) := by
  obtain ⟨T, c, W, hT, hc, hTO, hTF, -⟩ :=
    hO.exists_linearSubst_eq_smul_polynomial hF.out hirr.out
  obtain ⟨M, rfl⟩ : ∃ M : GL (Fin 3) k, M.1 = T :=
    ⟨_, ((Matrix.isUnit_iff_isUnit_det T).2
      (Matrix.isUnit_det_of_mulVecLin_injective hT)).unit_spec⟩
  have hb := ProjectiveSpace.bijective_map_mulVecLin M
  have hMO : map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit)
      (0 : W.toProjective.Point).toProjectivization = O := by
    rw [Point.toProjectivization_zero]
    erw [map_mk]
    simp only [Matrix.mulVecLin_apply, hTO, mk_rep]
  have hs (P : W.toProjective.Point) : IsSimplePoint F
      (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) P.toProjectivization) := by
    rw [← isSimplePoint_linearSubst_iff hF.out hT, hTF, isSimplePoint_smul_iff hc]
    exact P.isSimplePoint_toProjectivization
  let e : W.toProjective.Point ≃ CubicGroup F O := Equiv.ofBijective (fun P ↦ ⟨_, hs P⟩)
    ⟨fun P Q h ↦ Point.toProjectivization_injective (hb.1 (congrArg CubicGroup.point h)),
      fun A ↦ by
        obtain ⟨R, hR⟩ := hb.2 A.point
        have hRs : IsSimplePoint W.toProjective.polynomial R := by
          rw [← isSimplePoint_smul_iff hc, ← hTF, isSimplePoint_linearSubst_iff hF.out hT, hR]
          exact A.isSimplePoint
        obtain ⟨P, rfl⟩ := (Point.mem_range_toProjectivization_iff_isSimplePoint R).2 hRs
        exact ⟨P, CubicGroup.ext hR⟩⟩
  refine ⟨W, fun hns ↦ ?_, ⟨(AddEquiv.mk' e fun P Q ↦ CubicGroup.ext ?_).symm⟩⟩
  · rw [← isNonsingular_linearSubst_iff hT, hTF, isNonsingular_smul_iff hc] at hns
    exact isNonsingular_polynomial_iff.1 hns
  · rw [CubicGroup.point_add]
    refine (map_toProjectivization_add hF.out hirr.out M hc hTF P Q).trans ?_
    rw [hMO]
    rfl

end PlaneCurves.Projective

end
