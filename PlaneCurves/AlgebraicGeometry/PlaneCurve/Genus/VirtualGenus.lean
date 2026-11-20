/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Genus.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Resolution
public import PlaneCurves.FieldTheory.FunctionField.Rational
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Equiv

/-!
# The genus of a plane curve is at most its virtual genus

Let `k` be an algebraically closed field and `C : F = 0` an irreducible projective plane curve of
degree `n` with arbitrary singularities, `r_P = m_P(C)`. Its genus `g` is at most the virtual
genus `g*(C) = (n - 1)(n - 2)/2 - ∑_P r_P (r_P - 1)/2`. The proof is the book's: a sequence of
quadratic transformations carries `C` to a birationally equivalent curve `C'` with only ordinary
multiple points and `g*(C') ≤ g*(C)`, and the genus formula gives `g = g*(C')`.

Hence a curve with `g* = 0`, for instance an irreducible cubic with a multiple point, is rational.
Since a nonsingular plane curve of degree `n` has genus `(n - 1)(n - 2)/2`, which takes the values
`0, 0, 1, 3, 6, …`, a curve of genus two is not birationally equivalent to any nonsingular plane
curve; an irreducible quartic whose only multiple point is a node has genus two.

## Main results

* `PlaneCurves.Projective.genus_eq_virtualGenus`: `g = g*` when every multiple point is ordinary.
* `PlaneCurves.Projective.genus_le_virtualGenus`: `g ≤ g*`.
* `PlaneCurves.Projective.nonempty_algEquiv_ratFunc_of_virtualGenus_eq_zero`: a curve with
  `g* = 0` is rational.
* `PlaneCurves.Projective.nonempty_algEquiv_ratFunc_of_isMultiplePoint`: an irreducible cubic
  with a multiple point is rational.
* `PlaneCurves.Projective.isEmpty_algEquiv_of_genus_eq_two`: a curve of genus two is not
  birationally equivalent to a nonsingular plane curve.
* `PlaneCurves.Projective.genus_eq_two_of_isOrdinaryMultiplePoint`: an irreducible quartic whose
  only multiple point is a node has genus two.
* `PlaneCurves.Projective.genus_le_virtualGenus_spec`: the milestone.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §8.3, Corollaries 1 and 2 to Proposition 5 and the
  Examples after them
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti
open TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}

/-- `((a (a - 1) : ℕ) : ℤ) = a (a - 1)`, the subtraction on the left being truncated. -/
private theorem natCast_mul_sub_one (a : ℕ) :
    ((a * (a - 1) : ℕ) : ℤ) = (a : ℤ) * ((a : ℤ) - 1) := by
  rcases a with _ | a <;> simp

/-- **The genus of a curve with only ordinary multiple points is its virtual genus**: if every
multiple point of the irreducible plane curve `C : F = 0` is ordinary, then `g = g*(F)`. -/
theorem genus_eq_virtualGenus (hF : F.IsHomogeneous d) [Fact (Irreducible F)]
    (hord : ∀ P, IsMultiplePoint F P → IsOrdinaryMultiplePoint F P) :
    (genus k (functionField hF) : ℤ) = virtualGenus F := by
  have hirr : Irreducible F := Fact.out
  have h1 := two_mul_genus_eq hF hord
  have h2 := two_mul_virtualGenus hF hirr.ne_zero (hF.degree_ne_zero_of_irreducible hirr)
  simp only [natCast_mul_sub_one] at h1
  linarith

/-- **The genus is at most the virtual genus** (Fulton, §8.3, Corollary 1 to Proposition 5): for
an irreducible plane curve `C : F = 0` over an algebraically closed field, `g ≤ g*(F)`. -/
theorem genus_le_virtualGenus (hF : F.IsHomogeneous d) [Fact (Irreducible F)] :
    (genus k (functionField hF) : ℤ) ≤ virtualGenus F := by
  obtain ⟨G, m, hG, hirrG, hord, hle, ⟨e⟩⟩ := exists_ordinary_model hF Fact.out
  have := Fact.mk hirrG
  rw [← genus_eq_of_ringEquiv (RingEquiv.refl k) e.toRingEquiv fun c ↦ by simp,
    genus_eq_virtualGenus hG hord]
  exact hle

/-- **A curve of virtual genus zero is rational** (Fulton, §8.3, Corollary 2 to Proposition 5):
if `g*(F) = 0`, the function field of the irreducible plane curve `F = 0` is `k(t)`. -/
theorem nonempty_algEquiv_ratFunc_of_virtualGenus_eq_zero (hF : F.IsHomogeneous d)
    [Fact (Irreducible F)] (h : virtualGenus F = 0) :
    Nonempty (functionField hF ≃ₐ[k] RatFunc k) :=
  ((tfae_genus_eq_zero_of_isAlgClosed (functionField.isFunctionField hF)).out 1 4).2 (by
    have := genus_le_virtualGenus hF
    omega)

/-- **A singular cubic is rational** (Fulton, §8.3, Examples): an irreducible plane cubic with a
multiple point has function field `k(t)`. -/
theorem nonempty_algEquiv_ratFunc_of_isMultiplePoint (hF : F.IsHomogeneous 3)
    [Fact (Irreducible F)] {P : ℙ k (Fin 3 → k)} (hP : IsMultiplePoint F P) :
    Nonempty (functionField hF ≃ₐ[k] RatFunc k) :=
  nonempty_algEquiv_ratFunc_of_virtualGenus_eq_zero hF
    (virtualGenus_eq_zero_of_isMultiplePoint hF Fact.out hP)

/-- `(d - 1)(d - 2)/2` is never `2`: the genera of nonsingular plane curves are
`0, 0, 1, 3, 6, …`. -/
private theorem sub_one_mul_sub_two_div_two_ne_two (d : ℕ) : (d - 1) * (d - 2) / 2 ≠ 2 := by
  rcases le_or_gt d 4 with hd | hd
  · interval_cases d <;> decide
  · have : 4 * 3 ≤ (d - 1) * (d - 2) := Nat.mul_le_mul (by omega) (by omega)
    omega

/-- **A curve of genus two is not birationally equivalent to a nonsingular plane curve**
(Fulton, §8.3, Examples): a function field of genus two is not the function field of any
nonsingular plane curve. -/
theorem isEmpty_algEquiv_of_genus_eq_two {K : Type*} [Field K] [Algebra k K]
    (hK : genus k K = 2) {G : MvPolynomial (Fin 3) k} {m : ℕ} (hG : G.IsHomogeneous m)
    [Fact (Irreducible G)] (hns : IsNonsingular G) : IsEmpty (K ≃ₐ[k] functionField hG) := by
  refine ⟨fun e ↦ sub_one_mul_sub_two_div_two_ne_two m ?_⟩
  rw [← genus_functionField_of_isNonsingular hG hns,
    genus_eq_of_ringEquiv (RingEquiv.refl k) e.toRingEquiv fun c ↦ by simp, hK]

/-- **A nodal quartic has genus two** (Fulton, §8.3, Examples): an irreducible plane quartic
whose only multiple point `P` is an ordinary double point has genus two. -/
theorem genus_eq_two_of_isOrdinaryMultiplePoint (hF : F.IsHomogeneous 4) [Fact (Irreducible F)]
    {P : ℙ k (Fin 3 → k)} (hP : IsOrdinaryMultiplePoint F P) (hP2 : mult F P = 2)
    (honly : ∀ Q, IsMultiplePoint F Q → Q = P) :
    genus k (functionField hF) = 2 := by
  have hirr : Irreducible F := Fact.out
  have hg := genus_eq_virtualGenus hF fun Q hQ ↦ honly Q hQ ▸ hP
  rw [virtualGenus_def, hF.totalDegree hirr.ne_zero, finsum_eq_single _ P fun Q hQ ↦
    choose_two_toNat_mult_eq_zero (not_lt.1 fun h ↦ hQ (honly Q (isMultiplePoint_def.2
      (Order.add_one_le_of_lt h))))] at hg
  rw [hP2] at hg
  norm_num at hg
  omega

/-- **The genus is at most the virtual genus** (Fulton, §8.3, Corollaries 1 and 2 to
Proposition 5 and the Examples). Let `k` be algebraically closed and `C : F = 0` an irreducible
projective plane curve of degree `n`, with arbitrary singularities and `r_P = m_P(C)`.

1. Its genus satisfies `g ≤ g*(C) = (n - 1)(n - 2)/2 - ∑_P r_P (r_P - 1)/2`.
2. If `∑_P r_P (r_P - 1)/2 = (n - 1)(n - 2)/2`, that is `g*(C) = 0`, then `C` is rational.
3. In particular every irreducible cubic with a multiple point is rational.
4. A curve of genus two is not birationally equivalent to any nonsingular plane curve.
5. An irreducible quartic whose only multiple point is a node has genus two; an example is
   `PlaneCurves.Projective.genus_functionField_nodalQuartic`.

Milestone: *Genus bound by the virtual genus of a plane curve*. -/
theorem genus_le_virtualGenus_spec (hF : F.IsHomogeneous d) [Fact (Irreducible F)] :
    (genus k (functionField hF) : ℤ) ≤ virtualGenus F ∧
    (virtualGenus F = 0 → Nonempty (functionField hF ≃ₐ[k] RatFunc k)) ∧
    (∀ {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous 3) [Fact (Irreducible G)]
      {P : ℙ k (Fin 3 → k)}, IsMultiplePoint G P → Nonempty (functionField hG ≃ₐ[k] RatFunc k)) ∧
    (∀ {K : Type*} [Field K] [Algebra k K], genus k K = 2 →
      ∀ {G : MvPolynomial (Fin 3) k} {m : ℕ} (hG : G.IsHomogeneous m) [Fact (Irreducible G)],
        IsNonsingular G → IsEmpty (K ≃ₐ[k] functionField hG)) ∧
    (∀ {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous 4) [Fact (Irreducible G)]
      {P : ℙ k (Fin 3 → k)}, IsOrdinaryMultiplePoint G P → mult G P = 2 →
        (∀ Q, IsMultiplePoint G Q → Q = P) → genus k (functionField hG) = 2) :=
  ⟨genus_le_virtualGenus hF, nonempty_algEquiv_ratFunc_of_virtualGenus_eq_zero hF,
    fun hG _ _ hP ↦ nonempty_algEquiv_ratFunc_of_isMultiplePoint hG hP,
    fun hK _ _ hG _ hns ↦ isEmpty_algEquiv_of_genus_eq_two hK hG hns,
    fun hG _ _ hP hP2 honly ↦ genus_eq_two_of_isOrdinaryMultiplePoint hG hP hP2 honly⟩

end PlaneCurves.Projective

end
