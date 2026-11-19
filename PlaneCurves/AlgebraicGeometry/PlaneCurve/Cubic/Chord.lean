/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Combinatorics.Configuration
public import Mathlib.LinearAlgebra.Projectivization.Constructions
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Singular
public import PlaneCurves.RingTheory.MvPolynomial.Homogeneous
public import PlaneCurves.RingTheory.MvPolynomial.LinearForm

/-!
# Chord lines of a plane curve

For two points `P`, `Q` of the projective plane and a form `F`, the *chord line*
`chordLine F P Q` is the line through `P` and `Q` if `P ≠ Q`, and the tangent line of `F` at
`P` if `P = Q`. It is the line of Fulton's chord–tangent construction on a cubic (§5.6): for
simple points `P`, `Q` of an irreducible cubic `F`, it meets `F` in `P`, `Q` and a third point.

For `P ≠ Q` the chord line is the linear form `∑ i, C (a i) * X i` whose coefficient vector `a`
represents the point `Projectivization.cross P Q` of the dual plane, the point orthogonal to `P`
and `Q`.

## Main definitions

* `PlaneCurves.Projective.chordLine`: the line through `P` and `Q`, or the tangent at `P = Q`.

## Main results

* `PlaneCurves.Projective.isHomogeneous_chordLine`, `PlaneCurves.Projective.chordLine_ne_zero`:
  the chord line is a line.
* `PlaneCurves.Projective.eval_chordLine_left`, `PlaneCurves.Projective.eval_chordLine_right`:
  it passes through `P` and `Q`.
* `PlaneCurves.Projective.chordLine_eq_smul_of_eval_eq_zero`: for `P ≠ Q`, every line through
  `P` and `Q` is a nonzero multiple of it.
* `PlaneCurves.Projective.isRelPrime_chordLine`: it is not a component of an irreducible form of
  degree at least two.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.6
-/

public section

namespace Projectivization

open scoped LinearAlgebra.Projectivization Matrix

variable {K : Type*} [Field K] {m : Type*} [Fintype m]

/-- Two points of projective space are orthogonal iff their representatives are. -/
theorem orthogonal_iff_dotProduct_rep {v w : ℙ K (m → K)} :
    v.orthogonal w ↔ v.rep ⬝ᵥ w.rep = 0 := by
  simpa using orthogonal_mk (F := K) v.rep_ne_zero w.rep_ne_zero

end Projectivization

namespace PlaneCurves.Projective

open MvPolynomial Projectivization
open scoped LinearAlgebra.Projectivization Matrix

variable {k : Type*} [Field k] {F L : MvPolynomial (Fin 3) k} {P Q : ℙ k (Fin 3 → k)} {d : ℕ}

open Classical in
/-- The *chord line* of `F` through `P` and `Q`: for `P ≠ Q`, the line through `P` and `Q`, the
linear form whose coefficients represent the point `cross P Q` of the dual plane; for `P = Q`,
the tangent line `tangentLine F P.rep` of `F` at `P`. -/
noncomputable def chordLine (F : MvPolynomial (Fin 3) k) (P Q : ℙ k (Fin 3 → k)) :
    MvPolynomial (Fin 3) k :=
  if P = Q then tangentLine F P.rep else ∑ i, C ((cross P Q).rep i) * X i

open Classical in
theorem chordLine_def (F : MvPolynomial (Fin 3) k) (P Q : ℙ k (Fin 3 → k)) :
    chordLine F P Q =
      if P = Q then tangentLine F P.rep else ∑ i, C ((cross P Q).rep i) * X i :=
  (rfl)

open Classical in
/-- The chord line through two distinct points is the line through them. -/
theorem chordLine_of_ne (F : MvPolynomial (Fin 3) k) (h : P ≠ Q) :
    chordLine F P Q = ∑ i, C ((cross P Q).rep i) * X i := by
  simp [chordLine_def, h]

/-- The chord line through `P` and `P` is the tangent line at `P`. -/
@[simp]
theorem chordLine_self (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k)) :
    chordLine F P P = tangentLine F P.rep := by
  simp [chordLine_def]

theorem chordLine_comm (F : MvPolynomial (Fin 3) k) (P Q : ℙ k (Fin 3 → k)) :
    chordLine F P Q = chordLine F Q P := by
  classical
  by_cases h : P = Q
  · rw [h]
  · rw [chordLine_of_ne F h, chordLine_of_ne F (Ne.symm h), cross_comm]

/-- The chord line is a linear form. -/
theorem isHomogeneous_chordLine (F : MvPolynomial (Fin 3) k) (P Q : ℙ k (Fin 3 → k)) :
    (chordLine F P Q).IsHomogeneous 1 := by
  by_cases h : P = Q
  · rw [h, chordLine_self]
    exact isHomogeneous_tangentLine F _
  · rw [chordLine_of_ne F h]
    exact isHomogeneous_sum_C_mul_X _

/-- The chord line through two distinct points, or through a simple point and itself, is
nonzero. -/
theorem chordLine_ne_zero (hF : F.IsHomogeneous d) (h : P ≠ Q ∨ IsSimplePoint F P) :
    chordLine F P Q ≠ 0 := by
  by_cases hPQ : P = Q
  · subst hPQ
    rw [chordLine_self]
    have hP := h.resolve_left (not_not.2 rfl)
    rw [← mk_rep P] at hP
    exact hP.tangentLine_ne_zero hF
  · rw [chordLine_of_ne F hPQ]
    exact sum_C_mul_X_ne_zero (Projectivization.rep_ne_zero _)

/-- The chord line through two distinct points passes through the first. -/
theorem eval_chordLine_left_of_ne (F : MvPolynomial (Fin 3) k) (h : P ≠ Q) :
    eval P.rep (chordLine F P Q) = 0 := by
  classical
  rw [chordLine_of_ne F h, eval_sum_C_mul_X, ← orthogonal_iff_dotProduct_rep]
  exact cross_orthogonal_left h

/-- The chord line through two distinct points passes through the second. -/
theorem eval_chordLine_right_of_ne (F : MvPolynomial (Fin 3) k) (h : P ≠ Q) :
    eval Q.rep (chordLine F P Q) = 0 := by
  rw [chordLine_comm]
  exact eval_chordLine_left_of_ne F (Ne.symm h)

/-- The chord line of a form `F` through a point `P` of `F` and any point passes through `P`. -/
theorem eval_chordLine_left (hF : F.IsHomogeneous d) (hP : eval P.rep F = 0)
    (Q : ℙ k (Fin 3 → k)) : eval P.rep (chordLine F P Q) = 0 := by
  by_cases h : P = Q
  · rw [← h, chordLine_self]
    exact eval_tangentLine_self hF hP
  · exact eval_chordLine_left_of_ne F h

/-- The chord line of a form `F` through any point and a point `Q` of `F` passes through `Q`. -/
theorem eval_chordLine_right (hF : F.IsHomogeneous d) (P : ℙ k (Fin 3 → k))
    (hQ : eval Q.rep F = 0) : eval Q.rep (chordLine F P Q) = 0 := by
  rw [chordLine_comm]
  exact eval_chordLine_left hF hQ P

/-- **The line through two points.** For `P ≠ Q`, every line through `P` and `Q` is a nonzero
multiple of the chord line through them. -/
theorem chordLine_eq_smul_of_eval_eq_zero (F : MvPolynomial (Fin 3) k) (h : P ≠ Q)
    (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) (hLP : eval P.rep L = 0)
    (hLQ : eval Q.rep L = 0) : ∃ c : k, c ≠ 0 ∧ L = c • chordLine F P Q := by
  classical
  set b : Fin 3 → k := fun i ↦ L.coeff (Finsupp.single i 1)
  have hLb : L = ∑ i, C (b i) * X i := hL.eq_sum_C_mul_X
  have hb : b ≠ 0 := by
    rintro hb
    rw [hLb, hb] at hL0
    simp at hL0
  have horth : ∀ R : ℙ k (Fin 3 → k), eval R.rep L = 0 → (mk k b hb).orthogonal R := by
    intro R hR
    rw [hLb, eval_sum_C_mul_X] at hR
    simpa using (orthogonal_mk hb R.rep_ne_zero).2 hR
  have heq := (Configuration.ofField.eq_or_eq_of_orthogonal (horth P hLP)
    (cross_orthogonal_left h) (horth Q hLQ) (cross_orthogonal_right h)).resolve_right h
  rw [← mk_rep (cross P Q), mk_eq_mk_iff] at heq
  obtain ⟨a, ha⟩ := heq
  refine ⟨a, a.ne_zero, ?_⟩
  rw [chordLine_of_ne F h, hLb, ← ha, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Pi.smul_apply, Units.smul_def, smul_eq_mul, map_mul, smul_eq_C_mul, mul_assoc]

/-- The chord line through two distinct points, or through a simple point and itself, is not a
component of an irreducible form of degree at least two. -/
theorem isRelPrime_chordLine (hF : F.IsHomogeneous d) (hirr : Irreducible F) (hd : 2 ≤ d)
    (h : P ≠ Q ∨ IsSimplePoint F P) : IsRelPrime (chordLine F P Q) F :=
  (hF.isRelPrime_of_irreducible hirr (isHomogeneous_chordLine F P Q) (chordLine_ne_zero hF h)
    (by omega)).symm

/-- Multiplying `F` by a nonzero constant multiplies its chord lines by nonzero constants. -/
theorem chordLine_smul {c : k} (hc : c ≠ 0) (F : MvPolynomial (Fin 3) k)
    (P Q : ℙ k (Fin 3 → k)) : ∃ a : k, a ≠ 0 ∧ chordLine (c • F) P Q = a • chordLine F P Q := by
  by_cases h : P = Q
  · exact ⟨c, hc, by rw [h, chordLine_self, chordLine_self, tangentLine_smul]⟩
  · exact ⟨1, one_ne_zero, by rw [chordLine_of_ne _ h, chordLine_of_ne _ h, one_smul]⟩

end PlaneCurves.Projective

end
