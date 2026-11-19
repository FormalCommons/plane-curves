/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Singular
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.CoordinateRing
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

## Main results

* `WeierstrassCurve.Projective.isSimplePoint_polynomial_mk_iff`: `[v]` is a simple point of `F`
  exactly when `v` is a nonsingular point of `W`.
* `WeierstrassCurve.Projective.Point.mem_range_toProjectivization_iff_isSimplePoint`: the simple
  points of `F` are the images of the points of `W`.
* `WeierstrassCurve.Projective.Point.toSimplePoint`: the bijection between `W.Point` and the
  simple points of `F`.
* `WeierstrassCurve.Projective.isNonsingular_polynomial_iff`: over a perfect field, `F` is
  nonsingular exactly when `W.Δ ≠ 0`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.6
-/

public section

open MvPolynomial PlaneCurves.Projective

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

end WeierstrassCurve.Projective

end
