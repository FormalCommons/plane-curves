/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.Line
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Hessian.Flex
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.IntersectionCycle
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Singular
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

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.3, Problem 3.21, and §5.6
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

/-- A point of the plane off the line `Z = 0` is `[a : b : 1]`. -/
private theorem exists_eq_mk {P : ℙ k (Fin 3 → k)} (hP : P ∈ affineOpen 2) :
    ∃ a b : k, P = Projectivization.mk k ![a, b, 1] (by simp) := by
  refine ⟨affineChart 2 P 0, affineChart 2 P 1, ?_⟩
  calc P = (affineChart 2).symm (affineChart 2 P) :=
        ((affineChart 2).left_inv (by rwa [affineChart_source])).symm
    _ = _ := by
      rw [affineChart_symm_apply]
      congr 1
      funext j
      fin_cases j <;> rfl

private theorem mk_mem_affineOpen (a b : k) :
    Projectivization.mk k ![a, b, 1] (by simp) ∈ affineOpen 2 := by
  simp [mk_mem_affineOpen_iff]

private theorem affineChart_mk_two (a b : k) :
    affineChart 2 (Projectivization.mk k ![a, b, 1] (by simp)) = ![a, b] := by
  funext j
  fin_cases j <;> simp [Fin.succAbove, Fin.lt_def]

private theorem mk_eq_mk_iff_two {a b a' b' : k} :
    Projectivization.mk k ![a, b, 1] (by simp) = Projectivization.mk k ![a', b', 1] (by simp) ↔
      a = a' ∧ b = b' := by
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2⟩ ↦ by subst h1 h2; rfl⟩
  have := congrArg (affineChart 2) h
  rw [affineChart_mk_two, affineChart_mk_two] at this
  exact ⟨by simpa using congrFun this 0, by simpa using congrFun this 1⟩

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
    affineChart_mk_two]

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

private theorem sum_map_single_eq_toFinsupp {α β : Type*} [DecidableEq β] (g : α → β)
    (s : Multiset α) : (s.map fun x ↦ single (g x) 1).sum = Multiset.toFinsupp (s.map g) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.map_cons, ← Multiset.singleton_add,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

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
    fun x x' h ↦ (mk_eq_mk_iff_two.1 h).1
  rw [hneg, intersectionCycle_smul_left (by norm_num), sum_map_single_eq_toFinsupp]
  ext P
  apply Nat.cast_injective (R := ℕ∞)
  rw [intersectionCycle_apply hL hF hrel, Multiset.toFinsupp_apply]
  by_cases hP : P ∈ affineOpen 2
  · obtain ⟨a, b, rfl⟩ := exists_eq_mk hP
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
        obtain ⟨rfl, rfl⟩ := mk_eq_mk_iff_two.1 h
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
  · obtain ⟨a, b, rfl⟩ := exists_eq_mk hP
    rw [intersectionNumber_mk_two hL]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, mk_eq_mk_iff_two,
      ite_eq_right_iff.2 (fun h ↦ absurd h (mk_zero_ne_mk a b))]
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

end IsAlgClosed

end WeierstrassCurve.Projective

end
