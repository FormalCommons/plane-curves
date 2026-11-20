/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.TerriblePoint
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Finiteness
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.LinearSubvariety

/-!
# Transverse position of a plane curve

A plane curve `F` of degree `n` is in *transverse position* if the line `Z = 0` meets it
transversally, `I(Q, F ∩ Z) = 1` at each common point `Q`, the point `[1 : 0 : 0]` is not on `F`,
and no tangent at a multiple point of `F` passes through `[1 : 0 : 0]`. These are the coordinates
in which Fulton computes the divisor of the differential `dx / f_y` (§8.5): the points of `F` on
`Z = 0` are then `n` simple points `[a : 1 : 0]`, and the partial derivatives `F_X` and `F_Y` are
nonzero (the second for `n ≥ 2`), in every characteristic.

## Main definitions

* `PlaneCurves.Projective.IsTransversePosition F`: `F` is in transverse position.

## Main results

* `PlaneCurves.Projective.IsTransversePosition.isSimplePoint`,
  `PlaneCurves.Projective.IsTransversePosition.eval_one_ne_zero`: the points of `F` on `Z = 0` are
  simple and of the form `[a : 1 : 0]`.
* `PlaneCurves.Projective.IsTransversePosition.ncard_zeroLocus_X_two`: there are `n` of them.
* `PlaneCurves.Projective.IsTransversePosition.eval_pderiv_zero_ne_zero`: `F_X` does not vanish
  at them.
* `PlaneCurves.Projective.IsTransversePosition.pderiv_zero_ne_zero`,
  `PlaneCurves.Projective.IsTransversePosition.pderiv_one_ne_zero`: `F_X ≠ 0`, and `F_Y ≠ 0` for
  `n ≥ 2`.
* `PlaneCurves.Projective.IsTransversePosition.not_dvd_pderiv_zero`,
  `PlaneCurves.Projective.IsTransversePosition.not_dvd_pderiv_one`,
  `PlaneCurves.Projective.IsTransversePosition.not_dvd_X`: `F` divides none of `F_X`, `F_Y` and,
  for `n ≥ 2`, the coordinates `X`, `Y`, `Z`.
* `PlaneCurves.Projective.exists_isTransversePosition`: over an algebraically closed field every
  irreducible curve is in transverse position after a projective change of coordinates.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §8.5 and Appendix A
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization Matrix

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {Q : ℙ k (Fin 3 → k)} {n : ℕ}

/-- A point lies on the curve of a form `G` exactly when `G` vanishes at its coordinates. -/
private theorem mem_zeroLocus_singleton_iff {G : MvPolynomial (Fin 3) k} {d : ℕ}
    (hG : G.IsHomogeneous d) {P : ℙ k (Fin 3 → k)} : P ∈ zeroLocus {G} ↔ eval P.rep G = 0 := by
  rw [mem_zeroLocus_iff_eval_rep (by simpa using ⟨d, hG⟩)]
  simp

/-- A plane curve `F` is in *transverse position* if the line `Z = 0` meets it transversally,
`[1 : 0 : 0]` is not on it, and no tangent line at a multiple point of `F` passes through
`[1 : 0 : 0]`. -/
structure IsTransversePosition (F : MvPolynomial (Fin 3) k) : Prop where
  /-- The line `Z = 0` meets `F` transversally: `I(Q, F ∩ Z) = 1` at each common point. -/
  intersectionNumber_X_two : ∀ Q ∈ zeroLocus {F, X 2}, intersectionNumber Q F (X 2) = 1
  /-- The point `[1 : 0 : 0]` is not on `F`. -/
  eval_ne_zero : eval ![1, 0, 0] F ≠ 0
  /-- No tangent line at a multiple point of `F` passes through `[1 : 0 : 0]`. -/
  not_isTangentAt : ∀ P, IsMultiplePoint F P → ∀ L, IsTangentAt F P L → eval ![1, 0, 0] L ≠ 0

namespace IsTransversePosition

variable (h : IsTransversePosition F)
include h

theorem ne_zero : F ≠ 0 := fun h0 ↦ h.eval_ne_zero (by simp [h0])

/-- The line `Z = 0` is not a component of a curve in transverse position. -/
theorem not_X_two_dvd : ¬X 2 ∣ F := fun ⟨G, hG⟩ ↦ h.eval_ne_zero (by simp [hG])

omit h in
private theorem eval_X_two_eq_zero (hQ : Q ∈ zeroLocus {F, X 2}) : eval Q.rep (X 2) = 0 := by
  simpa using mem_zeroLocus_X_iff.1 (mem_zeroLocus_pair_iff.1 hQ).2

/-- The points of `F` on `Z = 0` are simple points of `F`. -/
theorem isSimplePoint (hF : F.IsHomogeneous n) (hQ : Q ∈ zeroLocus {F, X 2}) :
    IsSimplePoint F Q :=
  ((intersectionNumber_eq_one_iff hF (isHomogeneous_X k 2) (X_ne_zero 2)
    (eval_X_two_eq_zero hQ)).1 (h.intersectionNumber_X_two Q hQ)).1

/-- The line `Z = 0` is not tangent to `F` at its points on `F`. -/
theorem not_isTangentAt_X_two (hF : F.IsHomogeneous n) (hQ : Q ∈ zeroLocus {F, X 2}) :
    ¬IsTangentAt F Q (X 2) :=
  ((intersectionNumber_eq_one_iff hF (isHomogeneous_X k 2) (X_ne_zero 2)
    (eval_X_two_eq_zero hQ)).1 (h.intersectionNumber_X_two Q hQ)).2

/-- The points of `F` on `Z = 0` are of the form `[a : 1 : 0]`: their `Y`-coordinate is
nonzero, since `[1 : 0 : 0]` is not on `F`. -/
theorem eval_one_ne_zero (hF : F.IsHomogeneous n) (hQ : Q ∈ zeroLocus {F, X 2}) :
    Q.rep 1 ≠ 0 := by
  intro h1
  rw [mem_zeroLocus_pair_iff, mem_zeroLocus_singleton_iff hF, mem_zeroLocus_X_iff] at hQ
  have hv : Q.rep = Q.rep 0 • ![1, 0, 0] := funext fun i ↦ by fin_cases i <;> simp [h1, hQ.2]
  have h0 : Q.rep 0 ≠ 0 := fun h0 ↦ Q.rep_ne_zero (by rw [hv, h0, zero_smul])
  have hQF := hQ.1
  rw [hv, hF.eval_smul, mul_eq_zero] at hQF
  exact hQF.elim (pow_ne_zero _ h0) h.eval_ne_zero

/-- **`F_X` at the points of `Z = 0`.** At a point `Q = [a : 1 : 0]` of `F` on `Z = 0`,
`F_X(Q) ≠ 0`. Otherwise Euler's identity `a F_X(Q) + F_Y(Q) = 0` gives `F_Y(Q) = 0` too, and the
tangent line `F_X(Q) X + F_Y(Q) Y + F_Z(Q) Z` at the simple point `Q` is `Z = 0`, which meets
`F` transversally. -/
theorem eval_pderiv_zero_ne_zero (hF : F.IsHomogeneous n) (hQ : Q ∈ zeroLocus {F, X 2}) :
    eval Q.rep (pderiv 0 F) ≠ 0 := by
  intro h0
  have hs := h.isSimplePoint hF hQ
  have h2 : Q.rep 2 = 0 := mem_zeroLocus_X_iff.1 (mem_zeroLocus_pair_iff.1 hQ).2
  have hE := eval_tangentLine_self hF hs.eval_rep_eq_zero
  simp only [eval_tangentLine, Fin.sum_univ_three, h0, h2, zero_mul, mul_zero, zero_add,
    add_zero] at hE
  have h1 : eval Q.rep (pderiv 1 F) = 0 :=
    (mul_eq_zero.1 hE).resolve_right (h.eval_one_ne_zero hF hQ)
  have hTL : tangentLine F Q.rep = C (eval Q.rep (pderiv 2 F)) * X 2 := by
    simp [tangentLine_def, Fin.sum_univ_three, h0, h1]
  refine h.not_isTangentAt_X_two hF hQ
    (isTangentAt_def.2 ⟨isHomogeneous_X k 2, X_ne_zero 2, eval_X_two_eq_zero hQ, ?_⟩)
  exact (dvd_mul_left _ _).trans
    (hTL ▸ (isTangentAt_def.1 (hs.isTangentAt_tangentLine hF)).2.2.2)

/-- **`Z = 0` meets `F` in `n` points.** Over an algebraically closed field, a curve of degree
`n` in transverse position meets the line `Z = 0` in exactly `n` points. -/
theorem ncard_zeroLocus_X_two [IsAlgClosed k] (hF : F.IsHomogeneous n) :
    (zeroLocus {F, X 2}).ncard = n := by
  have hP : eval (Projectivization.mk k ![(1 : k), 0, 0] (by simp)).rep F ≠ 0 := by
    rw [Ne, hF.eval_rep_mk_eq_zero_iff]
    exact h.eval_ne_zero
  have h0 : intersectionNumber (Projectivization.mk k ![(1 : k), 0, 0] (by simp)) F (X 2) =
      ((0 : ℕ) : ℕ∞) := by
    rw [Nat.cast_zero, intersectionNumber_eq_zero_iff hF (isHomogeneous_X k 2)]
    exact .inl hP
  have := ncard_zeroLocus_pair_diff hF (isHomogeneous_X k 2) (X_ne_zero 2) h.not_X_two_dvd h0
    fun Q hQ _ ↦ h.intersectionNumber_X_two Q hQ
  rwa [Set.sdiff_singleton_eq_self fun hQ ↦ hP ((mem_zeroLocus_singleton_iff hF).1
    (mem_zeroLocus_pair_iff.1 hQ).1), Nat.sub_zero] at this

/-- Over an algebraically closed field, `F_X ≠ 0` for a curve of positive degree in transverse
position. -/
theorem pderiv_zero_ne_zero [IsAlgClosed k] (hF : F.IsHomogeneous n) (hn : n ≠ 0) :
    pderiv 0 F ≠ 0 := by
  obtain ⟨Q, hQ⟩ := Set.nonempty_of_ncard_ne_zero (h.ncard_zeroLocus_X_two hF ▸ hn)
  exact fun h0 ↦ h.eval_pderiv_zero_ne_zero hF hQ (by rw [h0, map_zero])

/-- Over an algebraically closed field, `F_Y ≠ 0` for a curve of degree `n ≥ 2` in transverse
position. Otherwise Euler's identity `a F_X(Q) = 0` at the points `Q = [a : 1 : 0]` of `F` on
`Z = 0` forces all of them to be `[0 : 1 : 0]`, but there are `n ≥ 2` of them. -/
theorem pderiv_one_ne_zero [IsAlgClosed k] (hF : F.IsHomogeneous n) (hn : 2 ≤ n) :
    pderiv 1 F ≠ 0 := by
  intro h1
  have hcard := h.ncard_zeroLocus_X_two hF
  have key (Q) (hQ : Q ∈ zeroLocus {F, X 2}) :
      Q = Projectivization.mk k ![(0 : k), 1, 0] (by simp) := by
    have h2 : Q.rep 2 = 0 := mem_zeroLocus_X_iff.1 (mem_zeroLocus_pair_iff.1 hQ).2
    have hE := eval_tangentLine_self hF (h.isSimplePoint hF hQ).eval_rep_eq_zero
    simp only [eval_tangentLine, Fin.sum_univ_three, h1, h2, map_zero, zero_mul, mul_zero,
      add_zero] at hE
    have h0 : Q.rep 0 = 0 := (mul_eq_zero.1 hE).resolve_left (h.eval_pderiv_zero_ne_zero hF hQ)
    rw [← Q.mk_rep, mk_eq_mk_iff']
    exact ⟨Q.rep 1, funext fun i ↦ by fin_cases i <;> simp [h0, h2]⟩
  have hlt : 1 < (zeroLocus {F, X 2}).ncard := by omega
  obtain ⟨Q, hQ, Q', hQ', hne⟩ :=
    (Set.one_lt_ncard (Set.finite_of_ncard_ne_zero (Nat.ne_zero_of_lt hlt))).1 hlt
  exact hne ((key Q hQ).trans (key Q' hQ').symm)

/-- `F` does not divide `F_X`. -/
theorem not_dvd_pderiv_zero [IsAlgClosed k] (hF : F.IsHomogeneous n) (hn : n ≠ 0) :
    ¬F ∣ pderiv 0 F :=
  fun hd ↦ h.pderiv_zero_ne_zero hF hn (pderiv_eq_zero_of_dvd hd)

/-- `F` does not divide `F_Y`, for `n ≥ 2`. -/
theorem not_dvd_pderiv_one [IsAlgClosed k] (hF : F.IsHomogeneous n) (hn : 2 ≤ n) :
    ¬F ∣ pderiv 1 F :=
  fun hd ↦ h.pderiv_one_ne_zero hF hn (pderiv_eq_zero_of_dvd hd)

/-- For `n ≥ 2`, `F` divides none of the coordinates `X`, `Y`, `Z`. -/
theorem not_dvd_X (hF : F.IsHomogeneous n) (hn : 2 ≤ n) (i : Fin 3) : ¬F ∣ X i := fun hd ↦ by
  have hle := totalDegree_le_of_dvd_of_isDomain hd (X_ne_zero i)
  rw [hF.totalDegree h.ne_zero, totalDegree_X] at hle
  omega

end IsTransversePosition

/-! ### Existence of transverse position -/

/-- Two distinct points of the dual plane give linearly independent coefficient vectors. -/
private theorem linearIndependent_rep_pair {c c' : ℙ k (Fin 3 → k)} (hne : c ≠ c') :
    LinearIndependent k ![c.rep, c'.rep] := by
  rw [← crossProduct_ne_zero_iff_linearIndependent]
  refine mt (mk_eq_mk_iff_crossProduct_eq_zero c.rep_ne_zero c'.rep_ne_zero).mpr ?_
  simpa using hne

/-- **Existence of transverse position.** Let `k` be algebraically closed and `F` an irreducible
form. Then there is a projective change of coordinates, given by an invertible matrix `M`, that
puts `F(M X)` in transverse position.

By part (d) of the terrible-point theorem there is a line `L` through no multiple point of `F`
that meets `F` transversally in `n` points. Each of the finitely many tangents at the multiple
points meets `L` in one point, so some point `v` of `L` is off `F` and off all these tangents;
`M` moves `L` to `Z = 0` and `v` to `[1 : 0 : 0]`. -/
theorem exists_isTransversePosition [IsAlgClosed k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) : ∃ M : GL (Fin 3) k, IsTransversePosition (linearSubst M.1 F) := by
  classical
  set S := {P | IsMultiplePoint F P}
  have hS : S.Finite := finite_setOf_isMultiplePoint_of_irreducible hF hirr
  obtain ⟨c, hcS, hcard, hI⟩ := exists_ncard_zeroLocus_pair_sum_C_mul_X_eq hF hirr hS
  set L := ∑ i, C (c.rep i) * X i
  have hL : L.IsHomogeneous 1 := isHomogeneous_sum_C_mul_X _
  have hn : n ≠ 0 := hF.degree_ne_zero_of_irreducible hirr
  -- The lines tangent to `F` at a multiple point; none of them is `L`.
  set T := {c' : ℙ k (Fin 3 → k) | ∃ P ∈ S, IsTangentAt F P (∑ i, C (c'.rep i) * X i)}
  have hT : T.Finite := (hS.biUnion fun P _ ↦ finite_setOf_isTangentAt hirr.ne_zero P).subset
    fun c' ⟨P, hP, hc'⟩ ↦ Set.mem_biUnion hP hc'
  have hcT (c') (hc' : c' ∈ T) : c ≠ c' := by
    rintro rfl
    obtain ⟨P, hP, hcP⟩ := hc'
    exact hcS P hP (isTangentAt_def.1 hcP).2.2.1
  -- A point `v` of `L` off `F` and off these tangents.
  set B := zeroLocus {F, L} ∪ ⋃ c' ∈ T, zeroLocus {L, ∑ i, C (c'.rep i) * X i}
  have hB : B.Finite := (Set.finite_of_ncard_ne_zero (hcard ▸ hn)).union
    (hT.biUnion fun c' hc' ↦ by
      rw [zeroLocus_pair_sum_C_mul_X (linearIndependent_rep_pair (hcT c' hc'))]
      exact Set.finite_singleton _)
  obtain ⟨v, hvL, hvB⟩ :=
    ((zeroLocus_singleton_infinite (n := 2) le_rfl hL one_ne_zero).sdiff hB).nonempty
  simp only [B, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hvB
  -- A second line through `v`, and a change of coordinates moving the two lines to `Y` and `Z`.
  obtain ⟨c₁, hc₁v, hc₁c⟩ :=
    ((infinite_setOf_eval_sum_C_mul_X_eq_zero v).sdiff (Set.finite_singleton c)).nonempty
  have hind := linearIndependent_rep_pair (by simpa using hc₁c : c₁ ≠ c)
  obtain ⟨M, hM, hMa⟩ := exists_linearSubst_sum_C_mul_X_eq_X hind (τ := ![1, 2])
    (by intro i j h; fin_cases i <;> fin_cases j <;> simp_all)
  have hU : IsUnit M := Matrix.mulVec_injective_iff_isUnit.1 hM
  set N := hU.unit
  have hML : linearSubst N.1 L = X 2 := by
    rw [hU.unit_spec]
    simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] using hMa 1
  have hM₁ : linearSubst N.1 (∑ i, C (c₁.rep i) * X i) = X 1 := by
    rw [hU.unit_spec]
    simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] using hMa 0
  have hdet : IsUnit N.1.det := (Matrix.isUnit_iff_isUnit_det _).1 N.isUnit
  have hN : Function.Injective N.1.mulVecLin := Matrix.mulVec_injective_of_isUnit N.isUnit
  set τ := map N.1.mulVecLin hN
  have hev {G : MvPolynomial (Fin 3) k} {d : ℕ} (hG : G.IsHomogeneous d) :
      eval (τ (mk k ![1, 0, 0] (by simp))).rep G = 0 ↔ eval ![1, 0, 0] (linearSubst N.1 G) = 0 := by
    rw [← eval_rep_linearSubst_eq_zero_iff N hG, (hG.linearSubst _).eval_rep_mk_eq_zero_iff]
  have hτ : τ (mk k ![1, 0, 0] (by simp)) = v := by
    have hmem (P : ℙ k (Fin 3 → k)) (h₁ : eval P.rep (∑ i, C (c₁.rep i) * X i) = 0)
        (h₂ : eval P.rep L = 0) : P ∈ zeroLocus {∑ i, C (c₁.rep i) * X i, L} :=
      mem_zeroLocus_pair_iff.2 ⟨(mem_zeroLocus_singleton_iff (isHomogeneous_sum_C_mul_X _)).2 h₁,
        (mem_zeroLocus_singleton_iff hL).2 h₂⟩
    have h₁ := hmem _ ((hev (isHomogeneous_sum_C_mul_X _)).2 (by simp [hM₁]))
      ((hev hL).2 (by simp [hML]))
    have h₂ := hmem v hc₁v ((mem_zeroLocus_singleton_iff hL).1 hvL)
    rw [zeroLocus_pair_sum_C_mul_X hind] at h₁ h₂
    exact h₁.trans h₂.symm
  refine ⟨N, ⟨fun Q hQ ↦ ?_, ?_, fun P hP L' hL' ↦ ?_⟩⟩
  · rw [← hML, ← Set.image_pair, zeroLocus_linearSubst _ hN] at hQ
    rw [← hML, intersectionNumber_linearSubst hF hL N Q]
    exact hI _ hQ
  · rw [Ne, ← hev hF, hτ]
    exact fun h0 ↦ hvB.1 (mem_zeroLocus_pair_iff.2 ⟨(mem_zeroLocus_singleton_iff hF).2 h0, hvL⟩)
  · -- Move the tangent `L'` back to a tangent of `F` at `τ P`.
    set L'' := linearSubst N.1⁻¹ L'
    have hL'' : linearSubst N.1 L'' = L' := linearSubst_linearSubst_nonsing_inv hdet L'
    rw [← hL'', isTangentAt_linearSubst_iff hF hN] at hL'
    rw [isMultiplePoint_linearSubst_iff hF hN] at hP
    obtain ⟨hL''1, hL''0, -, -⟩ := isTangentAt_def.1 hL'
    obtain ⟨c', hc', hc'v⟩ := exists_associated_sum_C_rep_mul_X hL''1 hL''0
    have hc'T : c' ∈ T := ⟨_, hP, isTangentAt_def.2 ⟨isHomogeneous_sum_C_mul_X _,
      sum_C_mul_X_ne_zero c'.rep_ne_zero, (hc'v _).2 (isTangentAt_def.1 hL').2.2.1,
      hc'.symm.dvd.trans (isTangentAt_def.1 hL').2.2.2⟩⟩
    rw [← hL'', Ne, ← hev hL''1, hτ, ← hc'v]
    exact fun h0 ↦ hvB.2 c' hc'T (mem_zeroLocus_pair_iff.2 ⟨hvL,
      (mem_zeroLocus_singleton_iff (isHomogeneous_sum_C_mul_X _)).2 h0⟩)

end PlaneCurves.Projective

end
