/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Cubic.DivisorClass
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Cubic.Weierstrass
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.ChangeOfCoordinates
public import PlaneCurves.FieldTheory.FunctionField.PlaneModel
public import PlaneCurves.FieldTheory.FunctionField.Rational
public import PlaneCurves.RingTheory.MvPolynomial.Homogenize.Factorization
public import TauCeti.AlgebraicGeometry.Curves.ProjectiveLine
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GeneratedByY
public import TauCeti.FieldTheory.FunctionField.Elliptic.Weierstrass.Model

/-!
# Curves of genus zero and one and their plane models

Let `k` be algebraically closed and `K / k` a function field of one variable, the function field
of a curve `C` with nonsingular model `X`.

* `C` has genus zero exactly when it is rational, `K ≅ k(t)`, and then the regular proper curves
  over `k` with function field `K` are `ℙ¹` (Fulton, §8.2, Corollary to Proposition 4; the
  function-field criteria are `TauCeti.tfae_genus_eq_zero_of_isAlgClosed`).
* `C` has genus one exactly when it is birationally equivalent to a nonsingular plane cubic; the
  cubic can be taken in Weierstrass form, and, when `2 ≠ 0` in `k`, as
  `Y²Z = (X - α₁Z)(X - α₂Z)(X - α₃Z)` with distinct `αᵢ` (Fulton, §8.3, Examples (1) and (2),
  Problem 8.21).

The link between a Weierstrass equation and the plane curve it defines is
`WeierstrassCurve.Projective.functionFieldEquiv`: the function field of the projective plane
cubic `W.polynomial` is Mathlib's function field `W.FunctionField` of the Weierstrass curve `W`.
With it, Tau Ceti's Weierstrass coordinates of a function field of genus one
(`TauCeti.Place.exists_isWeierstrassCoordinates_isElliptic_of_genus_eq_one`) give the plane
model, and the genus formula for nonsingular plane curves gives the converse.

## Main results

* `AlgebraicGeometry.Scheme.nonempty_iso_projectiveLine_iff`: a regular proper curve over `k` is
  isomorphic to `ℙ¹` exactly when its function field is rational.
* `WeierstrassCurve.Projective.functionFieldEquiv`: `k(W.polynomial) ≃ₐ[k] k(W)`.
* `WeierstrassCurve.Projective.genus_functionField`: an elliptic Weierstrass cubic has genus one.
* `PlaneCurves.Projective.genus_eq_one_of_algEquiv`: a curve birational to a nonsingular plane
  cubic has genus one.
* `PlaneCurves.Projective.exists_isElliptic_algEquiv_of_genus_eq_one`: a curve of genus one is
  birational to an elliptic Weierstrass cubic.
* `PlaneCurves.Projective.exists_injective_algEquiv_of_genus_eq_one`: if `2 ≠ 0`, to a cubic
  `Y²Z = (X - α₁Z)(X - α₂Z)(X - α₃Z)` with distinct `αᵢ`.
* `PlaneCurves.Projective.tfae_genus_eq_zero_and_genus_eq_one_iff`: the milestone.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §8.2, Corollary to Proposition 4, §8.3,
  Examples (1) and (2), Problems 8.21 and 8.35 (a)
-/

public section

open CategoryTheory MvPolynomial PlaneCurves PlaneCurves.Projective TauCeti
  TauCeti.AlgebraicGeometry
open scoped IntermediateField

/-! ### Curves isomorphic to the projective line -/

namespace AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsIntegral X]
  [IsProper (X ↘ Spec (.of k))]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]

/-- **A regular proper curve is the projective line exactly when it is rational**: an integral
scheme `X` proper over `k` whose local rings at codimension-one points are discrete valuation
rings is isomorphic to `ℙ¹_k` over `k` if and only if its function field is `k`-isomorphic to
`k(t)`. -/
theorem nonempty_iso_projectiveLine_iff :
    (∃ e : X ≅ projectiveLine k, e.hom.IsOver (Spec (.of k))) ↔
      Nonempty (X.functionField ≃ₐ[k] RatFunc k) := by
  refine ⟨fun ⟨e, he⟩ ↦ ⟨(AlgEquiv.ofAlgHom (e.inv.functionFieldAlgHom k)
    (e.hom.functionFieldAlgHom k) ?_ ?_).trans (projectiveLine.functionFieldEquiv k)⟩,
    fun ⟨e⟩ ↦ ⟨X.isoProjectiveLine e.symm, inferInstance⟩⟩
  · rw [← Scheme.Hom.functionFieldAlgHom_comp]
    simp
  · rw [← Scheme.Hom.functionFieldAlgHom_comp]
    simp

end AlgebraicGeometry.Scheme

/-! ### The function field of a Weierstrass cubic -/

namespace WeierstrassCurve.Projective

variable {k : Type*} [Field k] (W : WeierstrassCurve.Projective k)

/-- The Weierstrass cubic `W.polynomial` is not divisible by `Z`: it is `-X³` on `Z = 0`. -/
theorem not_X_two_dvd_polynomial : ¬ X 2 ∣ W.polynomial := by
  rintro ⟨G, hG⟩
  have := congrArg (eval ![1, 0, 0]) hG
  simp [WeierstrassCurve.Projective.polynomial] at this

/-- The line `Z = 0` is not a multiple of the Weierstrass cubic `W.polynomial`. -/
theorem not_dvd_X_two_polynomial : ¬ W.polynomial ∣ X 2 := fun h ↦
  W.not_X_two_dvd_polynomial (W.prime_polynomial.irreducible.dvd_symm
    (prime_X : Prime (X 2 : MvPolynomial (Fin 3) k)).irreducible h)

/-- The affine Weierstrass polynomial `Y² + a₁XY + a₃Y - (X³ + a₂X² + a₄X + a₆)`, the
dehomogenization of `W.polynomial` at `Z`, is irreducible in `k[X, Y]`. -/
theorem irreducible_dehomogenize_two_polynomial : Irreducible (dehomogenize 2 W.polynomial) :=
  (irreducible_dehomogenize_iff W.isHomogeneous_polynomial W.not_X_two_dvd_polynomial).2
    W.prime_polynomial.irreducible

/-- The generic point `(x, y)` of `W` satisfies the affine Weierstrass polynomial, the
dehomogenization of `W.polynomial` at `Z`. -/
theorem aeval_genericX_genericY_dehomogenize_two_polynomial :
    aeval ![W.toAffine.genericX, W.toAffine.genericY] (dehomogenize 2 W.polynomial) = 0 := by
  have h := (WeierstrassCurve.Affine.equation_iff' _ _).1
    W.toAffine.equation_genericX_genericY
  rw [dehomogenize_two_polynomial]
  simpa [Algebra.smul_def] using h

/-- **The relations of the generic point of a Weierstrass curve**: the polynomials in `k[X, Y]`
vanishing at the generic point `(x, y)` of `W` are the multiples of the affine Weierstrass
polynomial. -/
theorem ker_aeval_genericX_genericY :
    RingHom.ker (aeval ![W.toAffine.genericX, W.toAffine.genericY] :
      MvPolynomial (Fin 2) k →ₐ[k] W.toAffine.FunctionField) =
      Ideal.span {dehomogenize 2 W.polynomial} := by
  have hx := W.toAffine.transcendental_genericX
  have := W.toAffine.isFunctionField.finiteDimensional_adjoin hx
  obtain ⟨G, hG, hker, -⟩ := exists_irreducible_ker_aeval_eq_span_singleton hx
    W.toAffine.adjoin_genericX_genericY_eq_top
  have hmem : dehomogenize 2 W.polynomial ∈ Ideal.span {G} := by
    rw [← hker, RingHom.mem_ker]
    exact W.aeval_genericX_genericY_dehomogenize_two_polynomial
  rw [hker, Ideal.span_singleton_eq_span_singleton]
  exact hG.associated_of_dvd W.irreducible_dehomogenize_two_polynomial
    (Ideal.mem_span_singleton.1 hmem)

/-- **The function field of a Weierstrass cubic**: the function field of the projective plane
curve `W.polynomial = 0` is Mathlib's function field `k(W)` of the Weierstrass curve `W`. The
isomorphism sends `X / Z` and `Y / Z` to the generic coordinates `x` and `y` of `W`: it is the
chart isomorphism at `Z` followed by `X ↦ x`, `Y ↦ y`. -/
noncomputable def functionFieldEquiv :
    functionField W.isHomogeneous_polynomial ≃ₐ[k] W.toAffine.FunctionField :=
  haveI := isPrime_span_dehomogenize W.isHomogeneous_polynomial W.not_dvd_X_two_polynomial
  (functionField.chartEquiv W.isHomogeneous_polynomial 2 W.not_dvd_X_two_polynomial).trans
    (fractionRingAlgEquivOfKerAevalEq W.toAffine.adjoin_genericX_genericY_eq_top
      W.ker_aeval_genericX_genericY)

theorem functionFieldEquiv_def :
    haveI := isPrime_span_dehomogenize W.isHomogeneous_polynomial W.not_dvd_X_two_polynomial
    W.functionFieldEquiv =
      (functionField.chartEquiv W.isHomogeneous_polynomial 2 W.not_dvd_X_two_polynomial).trans
        (fractionRingAlgEquivOfKerAevalEq W.toAffine.adjoin_genericX_genericY_eq_top
          W.ker_aeval_genericX_genericY) :=
  (rfl)

/-- **An elliptic Weierstrass cubic has genus one**: over an algebraically closed field, the
plane curve `W.polynomial = 0` of an elliptic curve `W` is a nonsingular cubic. -/
theorem genus_functionField [IsAlgClosed k] [W.IsElliptic] :
    genus k (functionField W.isHomogeneous_polynomial) = 1 := by
  rw [genus_functionField_of_isNonsingular W.isHomogeneous_polynomial
    (isNonsingular_polynomial_iff.2 W.isUnit_Δ.ne_zero)]

end WeierstrassCurve.Projective

/-! ### Plane models of curves of genus one -/

namespace PlaneCurves.Projective

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A change of the equation of a plane curve to an equal one changes nothing: the curve keeps
its function field, irreducibility and nonsingularity. -/
private theorem exists_of_eq {F G : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d)
    [Fact (Irreducible F)] (h : F = G) :
    ∃ (hG : G.IsHomogeneous d) (_ : Fact (Irreducible G)), (IsNonsingular F → IsNonsingular G) ∧
      Nonempty (functionField hF ≃ₐ[k] functionField hG) := by
  subst h
  exact ⟨hF, inferInstance, id, ⟨AlgEquiv.refl⟩⟩

variable [IsAlgClosed k]

/-- **A curve birational to a nonsingular plane cubic has genus one.** -/
theorem genus_eq_one_of_algEquiv {F : MvPolynomial (Fin 3) k} {hF : F.IsHomogeneous 3}
    [Fact (Irreducible F)] (hns : IsNonsingular F) (e : K ≃ₐ[k] functionField hF) :
    genus k K = 1 := by
  rw [← genus_eq_of_ringEquiv (RingEquiv.refl k) e.toRingEquiv fun c ↦ by simp,
    genus_functionField_of_isNonsingular hF hns]

/-- **A curve of genus one is birational to an elliptic Weierstrass cubic**: if the function
field `K / k` has genus one, it is the function field of the plane cubic `W.polynomial = 0` of
an elliptic curve `W` over `k`, in every characteristic. -/
theorem exists_isElliptic_algEquiv_of_genus_eq_one (hK : IsFunctionField k K)
    (hg : genus k K = 1) : ∃ W : WeierstrassCurve k, W.IsElliptic ∧
      Nonempty (K ≃ₐ[k] functionField W.toProjective.isHomogeneous_polynomial) := by
  obtain ⟨P, hP⟩ := (Place.infinite_setOf_degree_eq_one hK).nonempty
  obtain ⟨W, x, y, hW, h⟩ := Place.exists_isWeierstrassCoordinates_isElliptic_of_genus_eq_one hK
    isIntegrallyClosedIn_of_isAlgClosed hg hP
  exact ⟨W, hW, ⟨(W.toAffine.functionFieldEquivOfAdjoinEqTop h.equation h.transcendental_x
    (h.adjoin_eq_top hK hP)).symm.trans W.toProjective.functionFieldEquiv.symm⟩⟩

/-- **A curve of genus one is birational to a cubic `Y²Z = (X - α₁Z)(X - α₂Z)(X - α₃Z)`**: if
`2 ≠ 0` in `k` and the function field `K / k` has genus one, it is the function field of such a
cubic with distinct `α₁, α₂, α₃`, which is nonsingular. One can take `α = (0, 1, λ)`, the
Legendre form. -/
theorem exists_injective_algEquiv_of_genus_eq_one (h2 : (2 : k) ≠ 0) (hK : IsFunctionField k K)
    (hg : genus k K = 1) : ∃ α : Fin 3 → k, Function.Injective α ∧
      ∃ (hF : (X 1 ^ 2 * X 2 - (X 0 - C (α 0) * X 2) * (X 0 - C (α 1) * X 2) *
          (X 0 - C (α 2) * X 2) : MvPolynomial (Fin 3) k).IsHomogeneous 3)
        (_ : Fact (Irreducible (X 1 ^ 2 * X 2 - (X 0 - C (α 0) * X 2) * (X 0 - C (α 1) * X 2) *
          (X 0 - C (α 2) * X 2) : MvPolynomial (Fin 3) k))),
        IsNonsingular (X 1 ^ 2 * X 2 - (X 0 - C (α 0) * X 2) * (X 0 - C (α 1) * X 2) *
          (X 0 - C (α 2) * X 2) : MvPolynomial (Fin 3) k) ∧
        Nonempty (K ≃ₐ[k] functionField hF) := by
  obtain ⟨W, hW, ⟨e⟩⟩ := exists_isElliptic_algEquiv_of_genus_eq_one hK hg
  have hG := W.toProjective.isHomogeneous_polynomial
  have hns : IsNonsingular W.toProjective.polynomial :=
    WeierstrassCurve.Projective.isNonsingular_polynomial_iff.2 W.isUnit_Δ.ne_zero
  obtain ⟨M, l, hM, hl0, hl1, hML⟩ := IsNonsingular.exists_linearSubst_eq_legendre h2 hG hns
  let M' := Matrix.GeneralLinearGroup.mkOfDetNeZero M
    ((Matrix.mulVecLin_injective_iff_isUnit_det).1 hM).ne_zero
  have hM' : linearSubst M'.1 W.toProjective.polynomial = X 1 ^ 2 * X 2 -
      (X 0 - C ((![0, 1, l] : Fin 3 → k) 0) * X 2) *
        (X 0 - C ((![0, 1, l] : Fin 3 → k) 1) * X 2) *
        (X 0 - C ((![0, 1, l] : Fin 3 → k) 2) * X 2) := by
    rw [show M'.1 = M from rfl, hML]
    simp
  obtain ⟨hF, hirr, hnsF, ⟨e'⟩⟩ := exists_of_eq (hG.linearSubst M'.1) hM'
  have hinj : Function.Injective (![0, 1, l] : Fin 3 → k) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> grind
  exact ⟨![0, 1, l], hinj, hF, hirr, hnsF ((isNonsingular_linearSubst_iff hM).2 hns),
    ⟨(e.trans (functionField.linearSubstEquiv hG M')).trans e'⟩⟩

/-! ### The milestone -/

universe u v

/-- **Curves of genus zero and one and their plane models** (Fulton, §8.2, Corollary to
Proposition 4; §8.3, Examples (1) and (2); Problem 8.21). Let `k` be algebraically closed and
`K / k` the function field of a curve `C`, with genus `g`.

1. The following are equivalent: `C` is rational (`K ≅ k(t)`); some `x ∈ K` has a zero divisor
   `(x)₀` of degree one; `l(P) > 1` for some point `P` of the nonsingular model; `g = 0`; the
   group `C⁰` of divisor classes of degree zero is trivial.
2. When `g = 0`, and only then, every regular proper curve `X` over `k` with function field `K`
   (the nonsingular model of `C` as a scheme) is isomorphic to `ℙ¹` over `k`.
3. `g = 1` if and only if `C` is birationally equivalent to a nonsingular plane cubic;
4. the cubic can be taken in Weierstrass form, the plane cubic of an elliptic curve `W`, in
   every characteristic;
5. and, if `2 ≠ 0` in `k`, as `Y²Z = (X - α₁Z)(X - α₂Z)(X - α₃Z)` with distinct `αᵢ`.

Milestone: *Curves of genus zero and one and their plane models*. -/
theorem tfae_genus_eq_zero_and_genus_eq_one_iff {k : Type u} {K : Type v} [Field k]
    [IsAlgClosed k] [Field K] [Algebra k K] (hK : IsFunctionField k K) :
    List.TFAE [Nonempty (K ≃ₐ[k] RatFunc k),
      ∃ x : Kˣ, Divisor.degree (Divisor.zeros hK x) = 1,
      ∃ P : Place k K, 1 < Divisor.dim (WeilDivisor.ofPoint P : Divisor k K),
      genus k K = 0,
      (Divisor.degreeClass hK).ker = ⊥] ∧
    (∀ (Y : AlgebraicGeometry.Scheme.{u}) [Y.Over (AlgebraicGeometry.Spec (.of k))]
      [AlgebraicGeometry.IsIntegral Y]
      [AlgebraicGeometry.IsProper (Y ↘ AlgebraicGeometry.Spec (.of k))]
      [∀ p : CodimensionOnePoint Y,
        IsDiscreteValuationRing (Y.presheaf.stalk (p : Y))],
      Nonempty (Y.functionField ≃ₐ[k] K) →
        ((∃ e : Y ≅ projectiveLine k, e.hom.IsOver (AlgebraicGeometry.Spec (.of k))) ↔
          genus k K = 0)) ∧
    (genus k K = 1 ↔ ∃ (F : MvPolynomial (Fin 3) k) (hF : F.IsHomogeneous 3)
      (_ : Fact (Irreducible F)), IsNonsingular F ∧ Nonempty (K ≃ₐ[k] functionField hF)) ∧
    (genus k K = 1 ↔ ∃ W : WeierstrassCurve k, W.IsElliptic ∧
      Nonempty (K ≃ₐ[k] functionField W.toProjective.isHomogeneous_polynomial)) ∧
    ((2 : k) ≠ 0 → (genus k K = 1 ↔ ∃ α : Fin 3 → k, Function.Injective α ∧
      ∃ (hF : (X 1 ^ 2 * X 2 - (X 0 - C (α 0) * X 2) * (X 0 - C (α 1) * X 2) *
          (X 0 - C (α 2) * X 2) : MvPolynomial (Fin 3) k).IsHomogeneous 3)
        (_ : Fact (Irreducible (X 1 ^ 2 * X 2 - (X 0 - C (α 0) * X 2) * (X 0 - C (α 1) * X 2) *
          (X 0 - C (α 2) * X 2) : MvPolynomial (Fin 3) k))),
        IsNonsingular (X 1 ^ 2 * X 2 - (X 0 - C (α 0) * X 2) * (X 0 - C (α 1) * X 2) *
          (X 0 - C (α 2) * X 2) : MvPolynomial (Fin 3) k) ∧
        Nonempty (K ≃ₐ[k] functionField hF))) := by
  have h0 := tfae_genus_eq_zero_of_isAlgClosed hK
  refine ⟨h0, fun Y _ _ _ _ ⟨e⟩ ↦ ?_, ⟨fun hg ↦ ?_, fun ⟨F, hF, _, hns, ⟨e⟩⟩ ↦
    genus_eq_one_of_algEquiv hns e⟩, ⟨exists_isElliptic_algEquiv_of_genus_eq_one hK,
    fun ⟨W, _, ⟨e⟩⟩ ↦ genus_eq_one_of_algEquiv
      (WeierstrassCurve.Projective.isNonsingular_polynomial_iff.2 W.isUnit_Δ.ne_zero) e⟩,
    fun h2 ↦ ⟨exists_injective_algEquiv_of_genus_eq_one h2 hK,
      fun ⟨_, _, _, _, hns, ⟨e⟩⟩ ↦ genus_eq_one_of_algEquiv hns e⟩⟩
  · have h14 : Nonempty (K ≃ₐ[k] RatFunc k) ↔ genus k K = 0 := h0.out 1 4
    rw [Y.nonempty_iso_projectiveLine_iff, ← h14]
    exact ⟨fun ⟨f⟩ ↦ ⟨e.symm.trans f⟩, fun ⟨f⟩ ↦ ⟨e.trans f⟩⟩
  · obtain ⟨W, _, he⟩ := exists_isElliptic_algEquiv_of_genus_eq_one hK hg
    exact ⟨_, _, inferInstance,
      WeierstrassCurve.Projective.isNonsingular_polynomial_iff.2 W.isUnit_Δ.ne_zero, he⟩

end PlaneCurves.Projective

end
