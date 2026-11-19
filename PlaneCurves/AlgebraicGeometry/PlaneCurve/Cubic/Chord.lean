/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.Combinatorics.Configuration
public import Mathlib.LinearAlgebra.Projectivization.Constructions
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.IntersectionCycle
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

For simple points `P`, `Q` of an irreducible cubic `F` over an algebraically closed field,
Bézout's theorem gives `L • F = P + Q + R` for `L = chordLine F P Q` and a unique point `R`, the
*third point* `thirdPoint F P Q`, Fulton's `φ(P, Q)`.

## Main definitions

* `PlaneCurves.Projective.chordLine`: the line through `P` and `Q`, or the tangent at `P = Q`.
* `PlaneCurves.Projective.thirdPoint`: the third point `φ(P, Q)` of the chord through `P`, `Q`.

## Main results

* `PlaneCurves.Projective.isHomogeneous_chordLine`, `PlaneCurves.Projective.chordLine_ne_zero`:
  the chord line is a line.
* `PlaneCurves.Projective.eval_chordLine_left`, `PlaneCurves.Projective.eval_chordLine_right`:
  it passes through `P` and `Q`.
* `PlaneCurves.Projective.chordLine_eq_smul_of_eval_eq_zero`: for `P ≠ Q`, every line through
  `P` and `Q` is a nonzero multiple of it.
* `PlaneCurves.Projective.isRelPrime_chordLine`: it is not a component of an irreducible form of
  degree at least two.
* `PlaneCurves.Projective.intersectionCycle_chordLine`: `L • F = P + Q + φ(P, Q)`.
* `PlaneCurves.Projective.eq_smul_chordLine_of_intersectionCycle_eq`,
  `PlaneCurves.Projective.eq_thirdPoint_of_intersectionCycle_eq`: a line `L` with
  `L • F = P + Q + R` is a nonzero multiple of the chord line, and `R = φ(P, Q)`.
* `PlaneCurves.Projective.isSimplePoint_thirdPoint`, `PlaneCurves.Projective.thirdPoint_comm`,
  `PlaneCurves.Projective.thirdPoint_thirdPoint`: `φ(P, Q)` is simple, `φ(P, Q) = φ(Q, P)` and
  `φ(P, φ(P, Q)) = Q`.

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

namespace Finsupp

/-- A finitely supported function to `ℕ` has degree one iff it is `single a 1` for some `a`. -/
theorem degree_eq_one_iff {σ : Type*} {f : σ →₀ ℕ} : f.degree = 1 ↔ ∃ a, f = single a 1 := by
  refine ⟨fun h ↦ ?_, by rintro ⟨a, rfl⟩; exact degree_single a 1⟩
  obtain ⟨a, ha⟩ : f.support.Nonempty := by
    rw [support_nonempty_iff]
    rintro rfl
    simp at h
  have hle : single a 1 ≤ f := single_le_iff.2 (Nat.one_le_iff_ne_zero.2 (mem_support_iff.1 ha))
  have h' := congrArg degree (add_tsub_cancel_of_le hle)
  rw [map_add, degree_single, h] at h'
  refine ⟨a, ?_⟩
  rw [← add_tsub_cancel_of_le hle, (degree_eq_zero_iff (f - single a 1)).1 (by omega), add_zero]

end Finsupp

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

/-! ### The third point -/

open Finsupp (single)

variable {R : ℙ k (Fin 3 → k)}

open Classical in
/-- The *third point* `φ(P, Q)` of the chord through `P` and `Q` on a cubic `F`: the point `R`
with `chordLine F P Q • F = P + Q + R`, if there is one, and `P` otherwise. For simple points
`P`, `Q` of an irreducible cubic there is exactly one (`intersectionCycle_chordLine`). -/
noncomputable def thirdPoint (F : MvPolynomial (Fin 3) k) (P Q : ℙ k (Fin 3 → k)) :
    ℙ k (Fin 3 → k) :=
  if h : ∃ R, intersectionCycle (chordLine F P Q) F = single P 1 + single Q 1 + single R 1 then
    h.choose
  else P

open Classical in
theorem thirdPoint_def (F : MvPolynomial (Fin 3) k) (P Q : ℙ k (Fin 3 → k)) :
    thirdPoint F P Q =
      if h : ∃ R, intersectionCycle (chordLine F P Q) F = single P 1 + single Q 1 + single R 1
      then h.choose
      else P :=
  (rfl)

/-- Multiplying `F` by a nonzero constant does not change its third points. -/
@[simp]
theorem thirdPoint_smul {c : k} (hc : c ≠ 0) (F : MvPolynomial (Fin 3) k)
    (P Q : ℙ k (Fin 3 → k)) : thirdPoint (c • F) P Q = thirdPoint F P Q := by
  obtain ⟨a, ha, h⟩ := chordLine_smul hc F P Q
  have hZ : intersectionCycle (chordLine (c • F) P Q) (c • F) =
      intersectionCycle (chordLine F P Q) F := by
    rw [h, intersectionCycle_smul_left ha, intersectionCycle_smul_right hc]
  rw [thirdPoint_def, thirdPoint_def, hZ]

section IsAlgClosed

variable [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The chord line through simple points `P`, `Q` of an irreducible form of degree at least two
meets it in `P + Q` at least: at `P` and `Q` if `P ≠ Q`, and twice at `P` if `P = Q`. -/
theorem single_add_single_le_intersectionCycle_chordLine (hF : F.IsHomogeneous d)
    (hirr : Irreducible F) (hd : 2 ≤ d) (hP : IsSimplePoint F P) (hQ : IsSimplePoint F Q) :
    single P 1 + single Q 1 ≤ intersectionCycle (chordLine F P Q) F := by
  have hrel := isRelPrime_chordLine (Q := Q) hF hirr hd (Or.inr hP)
  have hL := isHomogeneous_chordLine F P Q
  by_cases hPQ : P = Q
  · subst hPQ
    rw [← Finsupp.single_add, Finsupp.single_le_iff]
    have ht := (isTangentAt_iff_mult_lt_intersectionNumber hF hirr.ne_zero hL
      (chordLine_ne_zero hF (Or.inr hP)) (eval_chordLine_left hF hP.eval_rep_eq_zero P)).1
      (by rw [chordLine_self]; exact hP.isTangentAt_tangentLine hF)
    rw [isSimplePoint_def.1 hP, intersectionNumber_comm, ← intersectionCycle_apply hL hF hrel]
      at ht
    exact_mod_cast Order.add_one_le_of_lt ht
  · have hmem : ∀ S, IsSimplePoint F S → eval S.rep (chordLine F P Q) = 0 →
        1 ≤ intersectionCycle (chordLine F P Q) F S := fun S hS hSL ↦ by
      rw [Nat.one_le_iff_ne_zero, ← Finsupp.mem_support_iff,
        mem_support_intersectionCycle_iff hL hF hrel]
      exact ⟨hSL, hS.eval_rep_eq_zero⟩
    intro S
    simp only [Finsupp.coe_add, Pi.add_apply]
    by_cases hS : P = S
    · subst hS
      simpa [hPQ] using hmem P hP (eval_chordLine_left_of_ne F hPQ)
    · by_cases hS' : Q = S
      · subst hS'
        simpa [hS] using hmem Q hQ (eval_chordLine_right_of_ne F hPQ)
      · simp [hS, hS']

/-- **The third point** ([Fulton2008], §5.6). The chord line `L` through simple points `P`, `Q` of
an irreducible cubic `F` meets it in `L • F = P + Q + φ(P, Q)`. -/
theorem intersectionCycle_chordLine (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hP : IsSimplePoint F P) (hQ : IsSimplePoint F Q) :
    intersectionCycle (chordLine F P Q) F =
      single P 1 + single Q 1 + single (thirdPoint F P Q) 1 := by
  have hex : ∃ R, intersectionCycle (chordLine F P Q) F =
      single P 1 + single Q 1 + single R 1 := by
    have hle := single_add_single_le_intersectionCycle_chordLine hF hirr (by norm_num) hP hQ
    have hdeg := degree_intersectionCycle (isHomogeneous_chordLine F P Q) hF
      (isRelPrime_chordLine hF hirr (by norm_num) (Or.inr hP))
    have h := congrArg Finsupp.degree (add_tsub_cancel_of_le hle)
    rw [map_add, map_add, Finsupp.degree_single, Finsupp.degree_single, hdeg] at h
    obtain ⟨R, hR⟩ := Finsupp.degree_eq_one_iff.1 (show
      (intersectionCycle (chordLine F P Q) F - (single P 1 + single Q 1)).degree = 1 by omega)
    exact ⟨R, by rw [← hR, add_tsub_cancel_of_le hle]⟩
  rw [thirdPoint_def, dite_eq_left_of_eq_true (eq_true hex)]
  exact hex.choose_spec

omit [IsAlgClosed k] in
/-- **Uniqueness of the chord line.** A line `L` that meets an irreducible cubic `F` in
`L • F = P + Q + R`, for simple points `P`, `Q` of `F`, is a nonzero multiple of the chord line
through `P` and `Q`: of the line through them if `P ≠ Q`, and of the tangent at `P` if
`P = Q`. -/
theorem eq_smul_chordLine_of_intersectionCycle_eq (hF : F.IsHomogeneous 3)
    (hirr : Irreducible F) (hP : IsSimplePoint F P) (hQ : IsSimplePoint F Q)
    (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0)
    (h : intersectionCycle L F = single P 1 + single Q 1 + single R 1) :
    ∃ c : k, c ≠ 0 ∧ L = c • chordLine F P Q := by
  have hrel : IsRelPrime L F := (hF.isRelPrime_of_irreducible hirr hL hL0 (by norm_num)).symm
  have hev : ∀ S, S = P ∨ S = Q → eval S.rep L = 0 := by
    intro S hS
    refine ((mem_support_intersectionCycle_iff hL hF hrel).1 ?_).1
    rw [h]
    rcases hS with rfl | rfl <;> simp
  by_cases hPQ : P = Q
  · subst hPQ
    have h2 : (2 : ℕ∞) ≤ intersectionNumber P F L := by
      rw [intersectionNumber_comm, ← intersectionCycle_apply hL hF hrel, h]
      norm_cast
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same]
      omega
    have ht := (isTangentAt_iff_mult_lt_intersectionNumber hF hirr.ne_zero hL hL0
      (hev P (Or.inl rfl))).2 (by rw [isSimplePoint_def.1 hP]; exact lt_of_lt_of_le (by simp) h2)
    obtain ⟨u, hu⟩ := (hP.associated_tangentLine_of_isTangentAt hF ht).symm
    obtain ⟨r, hr, hur⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
    refine ⟨r, hr.ne_zero, ?_⟩
    rw [chordLine_self, smul_eq_C_mul, ← hur, ← hu, mul_comm]
  · exact chordLine_eq_smul_of_eval_eq_zero F hPQ hL hL0 (hev P (Or.inl rfl))
      (hev Q (Or.inr rfl))

/-- **Uniqueness of the third point.** If a line `L` meets an irreducible cubic `F` in
`L • F = P + Q + R`, for simple points `P`, `Q` of `F`, then `R = φ(P, Q)`. -/
theorem eq_thirdPoint_of_intersectionCycle_eq (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hP : IsSimplePoint F P) (hQ : IsSimplePoint F Q) (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0)
    (h : intersectionCycle L F = single P 1 + single Q 1 + single R 1) :
    R = thirdPoint F P Q := by
  obtain ⟨c, hc, rfl⟩ := eq_smul_chordLine_of_intersectionCycle_eq hF hirr hP hQ hL hL0 h
  rw [intersectionCycle_smul_left hc, intersectionCycle_chordLine hF hirr hP hQ] at h
  exact (Finsupp.single_left_injective one_ne_zero (add_left_cancel h)).symm

/-- The third point `φ(P, Q)` is `R` iff some line `L` meets the irreducible cubic `F` in
`L • F = P + Q + R`, for simple points `P`, `Q` of `F`. -/
theorem thirdPoint_eq_iff (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hP : IsSimplePoint F P) (hQ : IsSimplePoint F Q) :
    thirdPoint F P Q = R ↔ ∃ L : MvPolynomial (Fin 3) k, L.IsHomogeneous 1 ∧ L ≠ 0 ∧
      intersectionCycle L F = single P 1 + single Q 1 + single R 1 := by
  refine ⟨?_, fun ⟨L, hL, hL0, h⟩ ↦ (eq_thirdPoint_of_intersectionCycle_eq hF hirr hP hQ hL hL0
    h).symm⟩
  rintro rfl
  exact ⟨chordLine F P Q, isHomogeneous_chordLine F P Q, chordLine_ne_zero hF (Or.inr hP),
    intersectionCycle_chordLine hF hirr hP hQ⟩

/-- The third point `φ(P, Q)` of simple points `P`, `Q` of an irreducible cubic is simple: a
multiple point would meet the chord line at least twice. -/
theorem isSimplePoint_thirdPoint (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hP : IsSimplePoint F P) (hQ : IsSimplePoint F Q) : IsSimplePoint F (thirdPoint F P Q) := by
  have hZ := intersectionCycle_chordLine hF hirr hP hQ
  generalize thirdPoint F P Q = S at hZ ⊢
  have hL := isHomogeneous_chordLine F P Q
  have hL0 := chordLine_ne_zero (Q := Q) hF (Or.inr hP)
  have hrel := isRelPrime_chordLine (Q := Q) hF hirr (by norm_num) (Or.inr hP)
  have hS := (mem_support_intersectionCycle_iff (P := S) hL hF hrel).1 (by rw [hZ]; simp)
  by_contra hns
  have hSP : P ≠ S := fun h ↦ hns (h ▸ hP)
  have hSQ : Q ≠ S := fun h ↦ hns (h ▸ hQ)
  have h2 : (2 : ℕ∞) ≤ intersectionCycle (chordLine F P Q) F S := by
    rw [intersectionCycle_apply hL hF hrel]
    refine le_trans ?_ (mul_mult_le_intersectionNumber hL hF)
    rw [mult_eq_one_of_isHomogeneous_one hL hL0 hS.1, one_mul]
    exact isMultiplePoint_def.1 (isMultiplePoint_iff_not_isSimplePoint.2 ⟨hS.2, hns⟩)
  rw [hZ] at h2
  norm_cast at h2
  simp [hSP, hSQ] at h2

/-- `φ(P, Q) = φ(Q, P)`, for simple points `P`, `Q` of an irreducible cubic. -/
theorem thirdPoint_comm (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hP : IsSimplePoint F P) (hQ : IsSimplePoint F Q) : thirdPoint F P Q = thirdPoint F Q P :=
  eq_thirdPoint_of_intersectionCycle_eq hF hirr hQ hP (isHomogeneous_chordLine F P Q)
    (chordLine_ne_zero hF (Or.inr hP))
    (by rw [intersectionCycle_chordLine hF hirr hP hQ, add_comm (single P 1)])

/-- `φ(P, φ(P, Q)) = Q`, for simple points `P`, `Q` of an irreducible cubic. -/
@[simp]
theorem thirdPoint_thirdPoint (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hP : IsSimplePoint F P) (hQ : IsSimplePoint F Q) :
    thirdPoint F P (thirdPoint F P Q) = Q :=
  (eq_thirdPoint_of_intersectionCycle_eq hF hirr hP (isSimplePoint_thirdPoint hF hirr hP hQ)
    (isHomogeneous_chordLine F P Q) (chordLine_ne_zero hF (Or.inr hP))
    (by rw [intersectionCycle_chordLine hF hirr hP hQ, add_right_comm])).symm

/-- `φ(φ(P, Q), Q) = P`, for simple points `P`, `Q` of an irreducible cubic. -/
@[simp]
theorem thirdPoint_thirdPoint' (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hP : IsSimplePoint F P) (hQ : IsSimplePoint F Q) :
    thirdPoint F (thirdPoint F P Q) Q = P :=
  (eq_thirdPoint_of_intersectionCycle_eq hF hirr (isSimplePoint_thirdPoint hF hirr hP hQ) hQ
    (isHomogeneous_chordLine F P Q) (chordLine_ne_zero hF (Or.inr hP))
    (by rw [intersectionCycle_chordLine hF hirr hP hQ]; abel)).symm

end IsAlgClosed

end PlaneCurves.Projective

end
