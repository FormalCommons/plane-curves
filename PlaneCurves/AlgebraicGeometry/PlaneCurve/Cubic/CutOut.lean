/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Cubic.Flex

/-!
# Points of a cubic cut out by a curve of degree `m`

Let `F` be an irreducible cubic over an algebraically closed field and `O` a simple point of `F`,
the zero of the chord–tangent group `CubicGroup F O`. A multiset `s` of `3m` simple points of `F`
is the intersection `G • F` of `F` with a form `G` of degree `m`, not a multiple of `F`, iff
`∑ s = m • φ(O, O)` in the group ([Fulton2008], §5.6, Problem 5.41). If `O` is a flex, then
`φ(O, O) = O` and the condition is `∑ s = 0`: this is Abel's theorem for plane cubics.
Consequently, if `G • F = D + P` and `H • F = D + Q` for forms `G`, `H` of the same degree that
are not multiples of `F`, then `P = Q` (Problem 5.42).

Both directions are proved by induction on `m`, following Fulton's hint. For `m = 1` this is the
collinearity criterion `CubicGroup.exists_line_iff_add_add_eq`. For `m ≥ 2` write
`s = A₁ + A₂ + A₃ + A₄ + t` and let `L₁`, `L₂`, `L₃` be the chord lines through `A₁, A₂`, through
`A₃, A₄` and through `R₁ = φ(A₁, A₂)`, `R₂ = φ(A₃, A₄)`, with third point `R₃ = φ(R₁, R₂)`.
All their intersections with `F` are simple points, so the residual intersection
(`exists_isHomogeneous_intersectionCycle_eq_sub_of_isSimplePoint`) passes between a form `G'` of
degree `m - 1` with `G' • F = R₃ + t` and a form `G` of degree `m` with `G • F = s`: from `G'` to
`G` as the residual of `L₃` in `L₁ L₂ G'`, and from `G` to `G'` as the residual of `L₁ L₂` in
`L₃ G`. In the group, `R₃ = A₁ + A₂ + A₃ + A₄ - φ(O, O)`.

Zero-cycles of points of the group are written `(s.map fun A ↦ single A.point 1).sum`.

## Main results

* `PlaneCurves.Projective.CubicGroup.sum_eq_nsmul_of_intersectionCycle_eq`: points cut out by a
  form of degree `m` add up to `m • φ(O, O)`.
* `PlaneCurves.Projective.CubicGroup.exists_intersectionCycle_eq_of_sum_eq_nsmul`: conversely,
  `3m` points that add up to `m • φ(O, O)` are cut out by a form of degree `m`.
* `PlaneCurves.Projective.CubicGroup.exists_intersectionCycle_eq_iff_sum_eq_zero`: the criterion
  for a flex as base point (Problem 5.41).
* `PlaneCurves.Projective.CubicGroup.eq_of_intersectionCycle_eq_add_single`: Problem 5.42.
* `PlaneCurves.Projective.intersectionCycle_cubicGroup_sum_spec`: both, for a nonsingular cubic.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.6, Problems 5.41 and 5.42
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization
open Finsupp (single)
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F G H : MvPolynomial (Fin 3) k} {O : ℙ k (Fin 3 → k)}

namespace CubicGroup

/-! ### Zero-cycles of points of the group -/

/-- The zero-cycle of a multiset of points of the group has degree its cardinality. -/
@[simp]
theorem degree_sum_map_single (s : Multiset (CubicGroup F O)) :
    (s.map fun A ↦ single A.point 1).sum.degree = Multiset.card s := by
  rw [map_multiset_sum, Multiset.map_map]
  simp [Finsupp.degree_single]

/-- A point in the support of the zero-cycle of a multiset of points of the group is one of
them. -/
theorem exists_mem_of_sum_map_single_apply_ne_zero {s : Multiset (CubicGroup F O)}
    {P : ℙ k (Fin 3 → k)} (h : (s.map fun A ↦ single A.point 1).sum P ≠ 0) :
    ∃ A ∈ s, A.point = P := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp at h
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Finsupp.add_apply] at h
    by_cases ha : a.point = P
    · exact ⟨a, Multiset.mem_cons_self _ _, ha⟩
    · rw [Finsupp.single_eq_of_ne (Ne.symm ha), zero_add] at h
      obtain ⟨A, hA, rfl⟩ := ih h
      exact ⟨A, Multiset.mem_cons_of_mem hA, rfl⟩

/-- If a form `G` meets `F` in the zero-cycle of a multiset of points of the group, then every
point of `V(F) ∩ V(G)` is a simple point of `F`. -/
theorem isSimplePoint_of_intersectionCycle_eq {d e : ℕ} (hG : G.IsHomogeneous e)
    (hF : F.IsHomogeneous d) (hGF : IsRelPrime G F) {s : Multiset (CubicGroup F O)}
    (h : intersectionCycle G F = (s.map fun A ↦ single A.point 1).sum) {P : ℙ k (Fin 3 → k)}
    (hPG : eval P.rep G = 0) (hPF : eval P.rep F = 0) : IsSimplePoint F P := by
  have hP := (mem_support_intersectionCycle_iff hG hF hGF).2 ⟨hPG, hPF⟩
  rw [h, Finsupp.mem_support_iff] at hP
  obtain ⟨A, -, rfl⟩ := exists_mem_of_sum_map_single_apply_ne_zero hP
  exact A.isSimplePoint

private theorem exists_eq_cons_cons_cons_cons {α : Type*} {s : Multiset α}
    (hs : 4 ≤ Multiset.card s) : ∃ a b c d t, s = a ::ₘ b ::ₘ c ::ₘ d ::ₘ t := by
  have hpos {u : Multiset α} (hu : 0 < Multiset.card u) : ∃ a t, u = a ::ₘ t := by
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 hu
    exact ⟨a, Multiset.exists_cons_of_mem ha⟩
  obtain ⟨a, s, rfl⟩ := hpos (u := s) (by omega)
  obtain ⟨b, s, rfl⟩ := hpos (u := s) (by simp at hs; omega)
  obtain ⟨c, s, rfl⟩ := hpos (u := s) (by simp at hs; omega)
  obtain ⟨d, t, rfl⟩ := hpos (u := s) (by simp at hs; omega)
  exact ⟨a, b, c, d, t, rfl⟩

variable [IsAlgClosed k] [hF : Fact (F.IsHomogeneous 3)] [hirr : Fact (Irreducible F)]

/-- The chord line through points `A`, `B` of the group meets `F` in `A + B + φ(A, B)`. -/
theorem intersectionCycle_chordLine_eq (A B : CubicGroup F O) :
    intersectionCycle (chordLine F A.point B.point) F =
      (({A, B, chord A B} : Multiset (CubicGroup F O)).map fun A ↦ single A.point 1).sum := by
  rw [intersectionCycle_chordLine hF.out hirr.out A.isSimplePoint B.isSimplePoint]
  simp [add_assoc]

omit [IsAlgClosed k] in
/-- The chord line through two points of the group is not a component of `F`. -/
theorem isRelPrime_chordLine (A B : CubicGroup F O) :
    IsRelPrime F (chordLine F A.point B.point) :=
  (Projective.isRelPrime_chordLine hF.out hirr.out (by norm_num) (Or.inr A.isSimplePoint)).symm

/-- The product of the chord lines through `A₁, A₂` and through `A₃, A₄` meets `F` in
`A₁ + A₂ + φ(A₁, A₂) + A₃ + A₄ + φ(A₃, A₄)`. -/
theorem intersectionCycle_chordLine_mul_chordLine_eq (A₁ A₂ A₃ A₄ : CubicGroup F O) :
    intersectionCycle (chordLine F A₁.point A₂.point * chordLine F A₃.point A₄.point) F =
      (({A₁, A₂, chord A₁ A₂} + {A₃, A₄, chord A₃ A₄} : Multiset (CubicGroup F O)).map
        fun A ↦ single A.point 1).sum := by
  rw [intersectionCycle_mul_left (isHomogeneous_chordLine F _ _) (isHomogeneous_chordLine F _ _)
    hF.out (isRelPrime_chordLine A₁ A₂).symm (isRelPrime_chordLine A₃ A₄).symm,
    intersectionCycle_chordLine_eq, intersectionCycle_chordLine_eq, Multiset.map_add,
    Multiset.sum_add]

/-! ### Points cut out by a curve of degree `m` -/

variable [hO : Fact (IsSimplePoint F O)]

/-- The sum of four points of the group in terms of the third point of the chord through
`φ(A₁, A₂)` and `φ(A₃, A₄)`. -/
private theorem add_add_add_eq (A₁ A₂ A₃ A₄ : CubicGroup F O) :
    A₁ + A₂ + A₃ + A₄ = chord (chord A₁ A₂) (chord A₃ A₄) + chord 0 0 := by
  rw [chord_eq_sub (chord A₁ A₂), chord_eq_sub A₁, chord_eq_sub A₃]
  abel

/-- **Points cut out by a curve of degree `m` add up to `m • φ(O, O)`** ([Fulton2008], §5.6,
Problem 5.41). If a form `G` of degree `m`, not a multiple of the irreducible cubic `F`, meets `F`
in the points of a multiset `s` of the group with zero `O`, then `∑ s = m • φ(O, O)`. -/
theorem sum_eq_nsmul_of_intersectionCycle_eq {m : ℕ} (hG : G.IsHomogeneous m) (hFG : ¬F ∣ G)
    {s : Multiset (CubicGroup F O)}
    (h : intersectionCycle G F = (s.map fun A ↦ single A.point 1).sum) :
    s.sum = m • chord 0 0 := by
  induction m using Nat.strong_induction_on generalizing G s with | _ m ih =>
  have hGF : IsRelPrime G F := (hirr.out.isRelPrime_iff_not_dvd.2 hFG).symm
  have hcard : Multiset.card s = m * 3 := by
    rw [← degree_sum_map_single, ← h, degree_intersectionCycle hG hF.out hGF]
  obtain _ | _ | n := m
  · simp [Multiset.card_eq_zero.1 hcard]
  · obtain ⟨A, B, C, rfl⟩ := Multiset.card_eq_three.1 hcard
    have hG0 : G ≠ 0 := by
      rintro rfl
      exact hFG (dvd_zero F)
    have := (exists_line_iff_add_add_eq A B C).1 ⟨G, hG, hG0, by rw [h]; simp [add_assoc]⟩
    simpa [add_assoc] using this
  obtain ⟨A₁, A₂, A₃, A₄, t, rfl⟩ := exists_eq_cons_cons_cons_cons (s := s) (by omega)
  -- the residual of `L₁ L₂` in `L₃ G` cuts out `R₃ + t`
  obtain ⟨-, B, hB, -, hFB, hBF⟩ := exists_isHomogeneous_intersectionCycle_eq_sub_of_isSimplePoint
    hF.out ((isHomogeneous_chordLine F A₁.point A₂.point).mul
      (isHomogeneous_chordLine F A₃.point A₄.point))
    ((isHomogeneous_chordLine F (chord A₁ A₂).point (chord A₃ A₄).point).mul hG) (by norm_num)
    ((isRelPrime_chordLine A₁ A₂).mul_right (isRelPrime_chordLine A₃ A₄))
    ((isRelPrime_chordLine _ _).mul_right hGF.symm)
    (fun P hPF hPG ↦ isSimplePoint_of_intersectionCycle_eq
      ((isHomogeneous_chordLine F _ _).mul (isHomogeneous_chordLine F _ _)) hF.out
      ((isRelPrime_chordLine A₁ A₂).mul_right (isRelPrime_chordLine A₃ A₄)).symm
      (intersectionCycle_chordLine_mul_chordLine_eq A₁ A₂ A₃ A₄) hPG hPF)
    (by
      rw [intersectionCycle_chordLine_mul_chordLine_eq, intersectionCycle_mul_left
        (isHomogeneous_chordLine F _ _) hG hF.out (isRelPrime_chordLine _ _).symm hGF,
        intersectionCycle_chordLine_eq, h]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_add, Multiset.sum_add,
        Finsupp.le_def, Finsupp.coe_add, Pi.add_apply]
      intro P
      omega)
  have hBt : intersectionCycle B F =
      ((chord (chord A₁ A₂) (chord A₃ A₄) ::ₘ t).map fun A ↦ single A.point 1).sum := by
    rw [hBF, intersectionCycle_chordLine_mul_chordLine_eq, intersectionCycle_mul_left
      (isHomogeneous_chordLine F _ _) hG hF.out (isRelPrime_chordLine _ _).symm hGF,
      intersectionCycle_chordLine_eq, h]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_add, Multiset.sum_add]
    ext P
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    omega
  have := ih (n + 1) (by omega) (by convert hB using 1; omega)
    (fun h ↦ hirr.out.not_isUnit (hFB dvd_rfl h)) hBt
  rw [Multiset.sum_cons] at this
  simp only [Multiset.sum_cons, ← add_assoc]
  rw [add_add_add_eq A₁ A₂ A₃ A₄, succ_nsmul, ← this]
  abel

/-- **Points adding up to `m • φ(O, O)` are cut out by a curve of degree `m`** ([Fulton2008],
§5.6, Problem 5.41). If a multiset `s` of `3m` points of the group of the irreducible cubic `F`
with zero `O` has `∑ s = m • φ(O, O)`, then there is a form `G` of degree `m`, not a multiple of
`F`, that meets `F` in the points of `s`. -/
theorem exists_intersectionCycle_eq_of_sum_eq_nsmul {m : ℕ} {s : Multiset (CubicGroup F O)}
    (hs : Multiset.card s = 3 * m) (h : s.sum = m • chord 0 0) :
    ∃ G : MvPolynomial (Fin 3) k, G.IsHomogeneous m ∧ ¬F ∣ G ∧
      intersectionCycle G F = (s.map fun A ↦ single A.point 1).sum := by
  induction m using Nat.strong_induction_on generalizing s with | _ m ih =>
  obtain _ | _ | n := m
  · refine ⟨1, isHomogeneous_one _ _, fun h ↦ hirr.out.not_isUnit (isUnit_of_dvd_one h), ?_⟩
    rw [Multiset.card_eq_zero.1 hs, ← C_1, intersectionCycle_C_left one_ne_zero]
    simp
  · obtain ⟨A, B, C, rfl⟩ := Multiset.card_eq_three.1 hs
    obtain ⟨L, hL, hL0, hLF⟩ := (exists_line_iff_add_add_eq A B C).2 (by simpa [add_assoc] using h)
    exact ⟨L, hL, fun h ↦ hirr.out.not_isUnit
      ((hF.out.isRelPrime_of_irreducible hirr.out hL hL0 (by norm_num)) dvd_rfl h),
      by rw [hLF]; simp [add_assoc]⟩
  obtain ⟨A₁, A₂, A₃, A₄, t, rfl⟩ := exists_eq_cons_cons_cons_cons (s := s) (by omega)
  -- a form `G'` of degree `m - 1` with `G' • F = R₃ + t`
  obtain ⟨G', hG', hFG', hG'F⟩ := ih (n + 1) (by omega)
    (s := chord (chord A₁ A₂) (chord A₃ A₄) ::ₘ t) (by simp at hs ⊢; omega) (by
      simp only [Multiset.sum_cons, ← add_assoc] at h ⊢
      rw [add_add_add_eq A₁ A₂ A₃ A₄, succ_nsmul] at h
      rw [add_right_comm] at h
      exact add_right_cancel h)
  have hFG'r : IsRelPrime F G' := hirr.out.isRelPrime_iff_not_dvd.2 hFG'
  -- the residual of `L₃` in `L₁ L₂ G'` cuts out `s`
  have hL₃ := intersectionCycle_chordLine_eq (chord A₁ A₂) (chord A₃ A₄)
  obtain ⟨-, B, hB, -, hFB, hBF⟩ := exists_isHomogeneous_intersectionCycle_eq_sub_of_isSimplePoint
    hF.out (isHomogeneous_chordLine F (chord A₁ A₂).point (chord A₃ A₄).point)
    (((isHomogeneous_chordLine F A₁.point A₂.point).mul
      (isHomogeneous_chordLine F A₃.point A₄.point)).mul hG') (by norm_num)
    (isRelPrime_chordLine _ _)
    (((isRelPrime_chordLine A₁ A₂).mul_right (isRelPrime_chordLine A₃ A₄)).mul_right hFG'r)
    (fun P hPF hPG ↦ isSimplePoint_of_intersectionCycle_eq (isHomogeneous_chordLine F _ _)
      hF.out (isRelPrime_chordLine _ _).symm hL₃ hPG hPF)
    (by
      rw [intersectionCycle_mul_left ((isHomogeneous_chordLine F _ _).mul
        (isHomogeneous_chordLine F _ _)) hG' hF.out
        ((isRelPrime_chordLine A₁ A₂).mul_right (isRelPrime_chordLine A₃ A₄)).symm hFG'r.symm,
        intersectionCycle_chordLine_mul_chordLine_eq, hL₃, hG'F]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_add, Multiset.sum_add,
        Finsupp.le_def, Finsupp.coe_add, Pi.add_apply]
      intro P
      omega)
  refine ⟨B, by convert hB using 1; omega, fun h ↦ hirr.out.not_isUnit (hFB dvd_rfl h), ?_⟩
  rw [hBF, intersectionCycle_mul_left ((isHomogeneous_chordLine F _ _).mul
    (isHomogeneous_chordLine F _ _)) hG' hF.out
    ((isRelPrime_chordLine A₁ A₂).mul_right (isRelPrime_chordLine A₃ A₄)).symm hFG'r.symm,
    intersectionCycle_chordLine_mul_chordLine_eq, hL₃, hG'F]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
    Multiset.map_singleton, Multiset.sum_singleton, Multiset.map_add, Multiset.sum_add]
  ext P
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
  omega

/-- **Points of an irreducible cubic cut out by a curve of degree `m`** ([Fulton2008], §5.6,
Problem 5.41). A multiset `s` of `3m` points of the group of the irreducible cubic `F` with
zero `O` is the intersection of `F` with a form of degree `m`, not a multiple of `F`, iff
`∑ s = m • φ(O, O)`. -/
theorem exists_intersectionCycle_eq_iff {m : ℕ} {s : Multiset (CubicGroup F O)}
    (hs : Multiset.card s = 3 * m) :
    (∃ G : MvPolynomial (Fin 3) k, G.IsHomogeneous m ∧ ¬F ∣ G ∧
      intersectionCycle G F = (s.map fun A ↦ single A.point 1).sum) ↔ s.sum = m • chord 0 0 :=
  ⟨fun ⟨_, hG, hFG, h⟩ ↦ sum_eq_nsmul_of_intersectionCycle_eq hG hFG h,
    exists_intersectionCycle_eq_of_sum_eq_nsmul hs⟩

/-- **Points of a cubic cut out by a curve of degree `m`, with a flex as base point**
([Fulton2008], §5.6, Problem 5.41). If the zero `O` of the group of the irreducible cubic `F` is
a flex, then a multiset `s` of `3m` points of the group is the intersection of `F` with a form of
degree `m`, not a multiple of `F`, iff `∑ s = 0`. -/
theorem exists_intersectionCycle_eq_iff_sum_eq_zero (hO' : IsFlex F O) {m : ℕ}
    {s : Multiset (CubicGroup F O)} (hs : Multiset.card s = 3 * m) :
    (∃ G : MvPolynomial (Fin 3) k, G.IsHomogeneous m ∧ ¬F ∣ G ∧
      intersectionCycle G F = (s.map fun A ↦ single A.point 1).sum) ↔ s.sum = 0 := by
  rw [exists_intersectionCycle_eq_iff hs, chord_zero_zero_of_isFlex hO', nsmul_zero]

/-- **The last point of an intersection with a curve of degree `m` is determined by the others**
([Fulton2008], §5.6, Problem 5.42). Let `G` and `H` be forms of the same degree, not multiples of
the irreducible cubic `F`. If `G • F = D + A` and `H • F = D + B`, where `D` is the zero-cycle of a
multiset `s` of simple points of `F`, and `A`, `B` are simple points, then `A = B`. -/
theorem eq_of_intersectionCycle_eq_add_single {m : ℕ} (hG : G.IsHomogeneous m)
    (hH : H.IsHomogeneous m) (hFG : ¬F ∣ G) (hFH : ¬F ∣ H) {s : Multiset (CubicGroup F O)}
    {A B : CubicGroup F O}
    (hGF : intersectionCycle G F = (s.map fun A ↦ single A.point 1).sum + single A.point 1)
    (hHF : intersectionCycle H F = (s.map fun A ↦ single A.point 1).sum + single B.point 1) :
    A = B := by
  have hA := sum_eq_nsmul_of_intersectionCycle_eq hG hFG (s := A ::ₘ s)
    (by rw [hGF, Multiset.map_cons, Multiset.sum_cons, add_comm])
  have hB := sum_eq_nsmul_of_intersectionCycle_eq hH hFH (s := B ::ₘ s)
    (by rw [hHF, Multiset.map_cons, Multiset.sum_cons, add_comm])
  rw [← hB, Multiset.sum_cons, Multiset.sum_cons] at hA
  exact add_right_cancel hA

end CubicGroup

/-- **Points of a nonsingular cubic cut out by a curve of degree `m`** ([Fulton2008], §5.6,
Problems 5.41, 5.42). Let `k` be algebraically closed, `F` a nonsingular cubic and `O` a flex of
`F`, the zero of the group `CubicGroup F O`.

* (a) A multiset `s` of `3m` points of `F` is the intersection `G • F` of `F` with a form `G` of
  degree `m`, not a multiple of `F`, iff `∑ s = 0` in the group.
* (b) If `G` and `H` are forms of degree `m`, not multiples of `F`, with `G • F = D + A` and
  `H • F = D + B`, where `D` is the zero-cycle of a multiset of points of `F`, then `A = B`.

Every point of `F` is simple (`isNonsingular_iff_forall_isSimplePoint`), and
`CubicGroup.equivZeroLocus` identifies the carrier of the group with the curve.

Milestone: *Points of a nonsingular cubic cut out by a curve of degree m*. -/
theorem intersectionCycle_cubicGroup_sum_spec [IsAlgClosed k] (hF : F.IsHomogeneous 3)
    (hns : IsNonsingular F) (hO : IsFlex F O) :
    letI : Fact (F.IsHomogeneous 3) := ⟨hF⟩
    letI : Fact (Irreducible F) := ⟨hns.irreducible hF three_ne_zero⟩
    letI : Fact (IsSimplePoint F O) := ⟨hO.isSimplePoint⟩
    (∀ (m : ℕ) (s : Multiset (CubicGroup F O)), Multiset.card s = 3 * m →
      ((∃ G : MvPolynomial (Fin 3) k, G.IsHomogeneous m ∧ ¬F ∣ G ∧
        intersectionCycle G F = (s.map fun A ↦ single A.point 1).sum) ↔ s.sum = 0)) ∧
    ∀ (m : ℕ) (G H : MvPolynomial (Fin 3) k) (s : Multiset (CubicGroup F O))
      (A B : CubicGroup F O), G.IsHomogeneous m → H.IsHomogeneous m → ¬F ∣ G → ¬F ∣ H →
      intersectionCycle G F = (s.map fun A ↦ single A.point 1).sum + single A.point 1 →
      intersectionCycle H F = (s.map fun A ↦ single A.point 1).sum + single B.point 1 →
      A = B := by
  let : Fact (F.IsHomogeneous 3) := ⟨hF⟩
  let : Fact (Irreducible F) := ⟨hns.irreducible hF three_ne_zero⟩
  let : Fact (IsSimplePoint F O) := ⟨hO.isSimplePoint⟩
  exact ⟨fun m s hs ↦ CubicGroup.exists_intersectionCycle_eq_iff_sum_eq_zero hO hs,
    fun m G H s A B hG hH hFG hFH hGF hHF ↦
      CubicGroup.eq_of_intersectionCycle_eq_add_single hG hH hFG hFH hGF hHF⟩

end PlaneCurves.Projective

end
