/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Singularities.Chart

/-!
# Two curves under one quadratic transformation

Let `F` and `G` be relatively prime forms of degrees `m` and `n` with `F G` in excellent position,
`r = m_P(F)` and `t = m_P(G)` their multiplicities at the centre `P = [0 : 0 : 1]`, and `F'`, `G'`
their proper transforms. The common points of `F'` and `G'` are the images of the common points of
`F` and `G` off the fundamental triangle, with the same multiplicities, the fundamental points,
where the multiplicities are `m, n` and `m - r, n - t`, and the points over the centre. Since `F'`
and `G'` have degrees `2m - r` and `2n - t`, this gives the identity

`(2m - r)(2n - t) + ∑_P m_P(F) m_P(G) + ∑_Q m_Q(F') m_Q(G') = m n + ∑_Q m_Q(F') m_Q(G')`,

the first sum on the right running over the points `Q` over the centre. Written with
`D(F, G) = m n - ∑_P m_P(F) m_P(G)`, it says that `D(F, G) = D(F', G') + ∑_Q m_Q(F') m_Q(G')`, the
sum running over the points over the centre (Fulton, §7.4, Problem 7.15).

A common tangent of `F` and `G` at the centre gives a common point of `F'` and `G'` over the
centre, so the quadratic transformation lowers `D` by at least one.

## Main results

* `PlaneCurves.Projective.IsExcellentPosition.mul_add_finsum_mult_mul_mult_properTransform`: the
  identity above.
* `PlaneCurves.Projective.mul_add_finsum_mult_mul_mult_properTransform_linearSubst`: the same
  identity after a change of coordinates that puts `F G` in excellent position.
* `PlaneCurves.Projective.IsExcellentPosition.exists_mem_pointsOverCentre_of_isTangentAt`: a common
  tangent at the centre gives a common point over the centre, and
  `PlaneCurves.Projective.IsExcellentPosition.one_le_finsum_mult_mul_mult_pointsOverCentre`, its
  consequence for the sum over the points over the centre.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.4, Problem 7.15
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F G : MvPolynomial (Fin 3) k} {m n : ℕ}

/-- The arithmetic of the one-step identity:
`(2m - r)(2n - t) + r t = m n + (m n + 2(m - r)(n - t))` for `r ≤ m` and `t ≤ n`. -/
private theorem two_mul_sub_mul_two_mul_sub_add_mul {r t : ℕ} (hrm : r ≤ m) (htn : t ≤ n) :
    (2 * m - r) * (2 * n - t) + r * t = m * n + (m * n + 2 * ((m - r) * (n - t))) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hrm
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le htn
  rw [show 2 * (r + a) - r = r + 2 * a by omega, show 2 * (t + b) - t = t + 2 * b by omega,
    Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  ring

namespace IsExcellentPosition

/-- The part of `∑_P m_P(F) m_P(G)` on the fundamental triangle, for `F G` in excellent position:
only `[0 : 0 : 1]` contributes. -/
private theorem finsum_mem_fundamentalTriangle_mult_mul_mult (h : IsExcellentPosition (F * G))
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) :
    ∑ᶠ P ∈ fundamentalTriangle, mult F P * mult G P =
      mult F (fundamentalPoint 2) * mult G (fundamentalPoint 2) := by
  rw [← finsum_mem_singleton (a := fundamentalPoint 2) (f := fun P ↦ mult F P * mult G P)]
  refine finsum_mem_inter_support_eq' _ _ _ fun P hP ↦ ?_
  rw [support_mult_mul_mult hF hG, mem_zeroLocus_pair_iff] at hP
  refine ⟨fun hPT ↦ ?_, fun hP2 ↦ ?_⟩
  · rw [fundamentalTriangle_eq_iUnion, Set.mem_iUnion] at hPT
    obtain ⟨j, hj⟩ := hPT
    refine h.eq_fundamentalPoint_two_of_mem hF hG (j := j) ?_
    rw [zeroLocus_insert, zeroLocus_insert]
    exact ⟨hP.1, hP.2, hj⟩
  · rw [Set.mem_singleton_iff.1 hP2]
    exact fundamentalPoint_mem_fundamentalTriangle 2

/-- The part of `∑_Q m_Q(F') m_Q(G')` on the fundamental triangle, for `F G` in excellent position:
the fundamental points and the points over the centre. -/
private theorem finsum_mem_fundamentalTriangle_mult_mul_mult_properTransform
    (h : IsExcellentPosition (F * G)) (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) :
    ∑ᶠ Q ∈ fundamentalTriangle, mult (properTransform F) Q * mult (properTransform G) Q =
      ((m * n + 2 * ((m - (mult F (fundamentalPoint 2)).toNat) *
        (n - (mult G (fundamentalPoint 2)).toNat)) : ℕ) : ℕ∞) +
        ∑ᶠ Q ∈ pointsOverCentre (F * G),
          mult (properTransform F) Q * mult (properTransform G) Q := by
  have hFe := h.of_mul_left hF hG
  have hGe := h.of_mul_right hF hG
  set c := fun Q ↦ mult (properTransform F) Q * mult (properTransform G) Q
  have hO := h.pointsOverCentre_finite (hF.mul hG)
  have hnO (i : Fin 3) : fundamentalPoint i ∉ pointsOverCentre (F * G) := fun hi ↦
    (pointsOverCentre_def (F * G) ▸ hi).2 i rfl
  rw [finsum_mem_inter_support_eq' c fundamentalTriangle
    (insert (fundamentalPoint 2) (insert (fundamentalPoint 0)
      (insert (fundamentalPoint 1) (pointsOverCentre (F * G))))) fun Q hQ ↦ ?_]
  · have h01 : fundamentalPoint (k := k) 0 ≠ fundamentalPoint 1 := by
      simp [fundamentalPoint_inj]
    have h02 : fundamentalPoint (k := k) 2 ≠ fundamentalPoint 0 := by
      simp [fundamentalPoint_inj]
    have h12 : fundamentalPoint (k := k) 2 ≠ fundamentalPoint 1 := by
      simp [fundamentalPoint_inj]
    rw [finsum_mem_insert _ (by simp [h02, h12, hnO]) (by simpa using hO),
      finsum_mem_insert _ (by simp [h01, hnO]) (by simpa using hO),
      finsum_mem_insert _ (hnO 1) hO]
    simp only [c, hFe.mult_properTransform_fundamentalPoint_two hF,
      hGe.mult_properTransform_fundamentalPoint_two hG,
      hFe.mult_properTransform_fundamentalPoint hF (i := 0) (by decide),
      hFe.mult_properTransform_fundamentalPoint hF (i := 1) (by decide),
      hGe.mult_properTransform_fundamentalPoint hG (i := 0) (by decide),
      hGe.mult_properTransform_fundamentalPoint hG (i := 1) (by decide)]
    push_cast
    ring
  · rw [support_mult_mul_mult hF.properTransform hG.properTransform] at hQ
    simp only [Set.mem_insert_iff]
    refine ⟨fun hQT ↦ ?_, ?_⟩
    · rcases hFe.eq_fundamentalPoint_or_mem_pointsOverCentre hF (mem_zeroLocus_pair_iff.1 hQ).1
        hQT with ⟨i, rfl⟩ | hO
      · fin_cases i <;> simp
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [pointsOverCentre_mul hF hG]
        exact Or.inl hO
    · rintro (rfl | rfl | rfl | hO)
      iterate 3 exact fundamentalPoint_mem_fundamentalTriangle _
      exact pointsOverCentre_subset_fundamentalTriangle hO

/-- **Two curves under one quadratic transformation** (Fulton, §7.4, Problem 7.15). Let `F` and
`G` be relatively prime forms of degrees `m` and `n` with `F G` in excellent position, `r` and `t`
their multiplicities at `[0 : 0 : 1]`, and `F'`, `G'` their proper transforms. Then
`(2m - r)(2n - t) + ∑_P m_P(F) m_P(G) + ∑_Q m_Q(F') m_Q(G') = m n + ∑_Q m_Q(F') m_Q(G')`, the first
sum over `Q` running over the points over the centre and the other sums over all of `ℙ²`. With
`D(F, G) = m n - ∑_P m_P(F) m_P(G)`, this says `D(F, G) = D(F', G') + ∑_Q m_Q(F') m_Q(G')`. -/
theorem mul_add_finsum_mult_mul_mult_properTransform (h : IsExcellentPosition (F * G))
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (hFG : IsRelPrime F G) :
    (((2 * m - (mult F (fundamentalPoint 2)).toNat) *
        (2 * n - (mult G (fundamentalPoint 2)).toNat) : ℕ) : ℕ∞) +
      ∑ᶠ P, mult F P * mult G P +
      ∑ᶠ Q ∈ pointsOverCentre (F * G), mult (properTransform F) Q * mult (properTransform G) Q =
    ((m * n : ℕ) : ℕ∞) + ∑ᶠ Q, mult (properTransform F) Q * mult (properTransform G) Q := by
  have hFe := h.of_mul_left hF hG
  have hGe := h.of_mul_right hF hG
  set r := (mult F (fundamentalPoint 2)).toNat with hr
  set t := (mult G (fundamentalPoint 2)).toNat with ht
  have hrm : r ≤ m := ENat.toNat_le_of_le_natCast (mult_le_degree hF hFe.ne_zero _)
  have htn : t ≤ n := ENat.toNat_le_of_le_natCast (mult_le_degree hG hGe.ne_zero _)
  have hfin : (Function.support fun P ↦ mult F P * mult G P).Finite := by
    rw [support_mult_mul_mult hF hG]
    exact finite_zeroLocus_pair_of_isRelPrime hF hG hFG
  have hfin' : (Function.support fun Q ↦
      mult (properTransform F) Q * mult (properTransform G) Q).Finite := by
    rw [support_mult_mul_mult hF.properTransform hG.properTransform]
    exact finite_zeroLocus_pair_of_isRelPrime hF.properTransform hG.properTransform
      (hFG.properTransform hF hG hFe.not_X_dvd hGe.not_X_dvd)
  have hU := finsum_mem_eq_of_bijOn quadraticMap bijOn_quadraticMap_compl_fundamentalTriangle
    (f := fun P ↦ mult F P * mult G P)
    (g := fun Q ↦ mult (properTransform F) Q * mult (properTransform G) Q)
    fun P hP ↦ by
      rw [mult_properTransform_quadraticMap hF hP, mult_properTransform_quadraticMap hG hP]
  have hrt : mult F (fundamentalPoint 2) * mult G (fundamentalPoint 2) = ((r * t : ℕ) : ℕ∞) := by
    rw [Nat.cast_mul, hr, ht, natCast_toNat_mult hFe.ne_zero, natCast_toNat_mult hGe.ne_zero]
  rw [← finsum_mem_univ fun P ↦ mult F P * mult G P,
    ← finsum_mem_univ fun Q ↦ mult (properTransform F) Q * mult (properTransform G) Q,
    ← finsum_mem_add_sdiff' (Set.subset_univ fundamentalTriangle) (by simpa using hfin),
    ← finsum_mem_add_sdiff' (Set.subset_univ fundamentalTriangle) (by simpa using hfin'),
    ← Set.compl_eq_univ_sdiff, h.finsum_mem_fundamentalTriangle_mult_mul_mult hF hG,
    h.finsum_mem_fundamentalTriangle_mult_mul_mult_properTransform hF hG, hU, hrt, ← hr, ← ht]
  have key : (((2 * m - r) * (2 * n - t) : ℕ) : ℕ∞) + ((r * t : ℕ) : ℕ∞) =
      ((m * n : ℕ) : ℕ∞) + ((m * n + 2 * ((m - r) * (n - t)) : ℕ) : ℕ∞) := by
    rw [← Nat.cast_add, ← Nat.cast_add, two_mul_sub_mul_two_mul_sub_add_mul hrm htn]
  calc _ = ((((2 * m - r) * (2 * n - t) : ℕ) : ℕ∞) + ((r * t : ℕ) : ℕ∞)) +
        ((∑ᶠ Q ∈ fundamentalTriangleᶜ,
          mult (properTransform F) Q * mult (properTransform G) Q) +
        ∑ᶠ Q ∈ pointsOverCentre (F * G),
          mult (properTransform F) Q * mult (properTransform G) Q) := by ac_rfl
    _ = _ := by rw [key]; ac_rfl

end IsExcellentPosition

/-- **Two curves under one quadratic transformation, after a change of coordinates.** Let `F` and
`G` be relatively prime forms of degrees `m` and `n`, and `T` a change of coordinates, given by an
invertible matrix `M`, that puts `(F G)^T` in excellent position. With `P = T([0 : 0 : 1])`,
`r = m_P(F)`, `t = m_P(G)` and `F'`, `G'` the proper transforms of `F^T` and `G^T`,
`(2m - r)(2n - t) + ∑_P m_P(F) m_P(G) + ∑_Q m_Q(F') m_Q(G') = m n + ∑_Q m_Q(F') m_Q(G')`, the first
sum over `Q` running over the points over the centre. -/
theorem mul_add_finsum_mult_mul_mult_properTransform_linearSubst (hF : F.IsHomogeneous m)
    (hG : G.IsHomogeneous n) (hFG : IsRelPrime F G) {M : Matrix (Fin 3) (Fin 3) k}
    (hM : Function.Injective M.mulVecLin) (h : IsExcellentPosition (linearSubst M (F * G))) :
    (((2 * m - (mult F (map M.mulVecLin hM (fundamentalPoint 2))).toNat) *
        (2 * n - (mult G (map M.mulVecLin hM (fundamentalPoint 2))).toNat) : ℕ) : ℕ∞) +
      ∑ᶠ P, mult F P * mult G P +
      ∑ᶠ Q ∈ pointsOverCentre (linearSubst M (F * G)),
        mult (properTransform (linearSubst M F)) Q * mult (properTransform (linearSubst M G)) Q =
    ((m * n : ℕ) : ℕ∞) + ∑ᶠ Q,
      mult (properTransform (linearSubst M F)) Q * mult (properTransform (linearSubst M G)) Q := by
  have hdet := Matrix.isUnit_det_of_mulVecLin_injective hM
  have hbij : Function.Bijective (map M.mulVecLin hM) :=
    bijective_map_mulVecLin ((Matrix.isUnit_iff_isUnit_det M).2 hdet).unit
  rw [map_mul] at h ⊢
  have key := h.mul_add_finsum_mult_mul_mult_properTransform (hF.linearSubst M)
    (hG.linearSubst M) ((isRelPrime_linearSubst_iff hdet).2 hFG)
  have hs : ∑ᶠ P, mult F (map M.mulVecLin hM P) * mult G (map M.mulVecLin hM P) =
      ∑ᶠ P, mult F P * mult G P :=
    finsum_comp_equiv (Equiv.ofBijective _ hbij) (f := fun P ↦ mult F P * mult G P)
  simp only [mult_linearSubst hF hM, mult_linearSubst hG hM] at key
  rwa [hs] at key

namespace IsExcellentPosition

/-- **A common tangent at the centre gives a common point over the centre.** If `F G` is in
excellent position and `F` and `G` have a common tangent at `[0 : 0 : 1]`, then `F` and `G` have a
common point over the centre: the point `[α : 1 : 0]` of the exceptional line that corresponds to
the tangent. -/
theorem exists_mem_pointsOverCentre_of_isTangentAt (h : IsExcellentPosition (F * G))
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) {L : MvPolynomial (Fin 3) k}
    (hLF : IsTangentAt F (fundamentalPoint 2) L) (hLG : IsTangentAt G (fundamentalPoint 2) L) :
    ∃ Q, Q ∈ pointsOverCentre F ∧ Q ∈ pointsOverCentre G := by
  have hFe := h.of_mul_left hF hG
  have hGe := h.of_mul_right hF hG
  have hP : fundamentalPoint (k := k) 2 ∈ affineOpen 2 := fundamentalPoint_mem_affineOpen_iff.2 rfl
  have hAF := (isTangentAt_iff_affine_of_affineChart_eq_zero hP (affineChart_fundamentalPoint 2)
    hF (isTangentAt_def.1 hLF).1 (isTangentAt_def.1 hLF).2.2.1).1 hLF
  have hAG := (isTangentAt_iff_affine_of_affineChart_eq_zero hP (affineChart_fundamentalPoint 2)
    hG (isTangentAt_def.1 hLG).1 (isTangentAt_def.1 hLG).2.2.1).1 hLG
  obtain ⟨hLh, -, hLdvd⟩ := Affine.isTangentAt_def.1 hAF
  obtain ⟨c, hc⟩ : ∃ c : Fin 2 → k, dehomogenize 2 L = ∑ r, C (c r) * X r :=
    ⟨_, hLh.eq_sum_C_mul_X⟩
  rw [Fin.sum_univ_two] at hc
  have hc0 : c 0 ≠ 0 := fun hc0 ↦ hFe.isGoodPosition.not_isTangentAt_dehomogenize_X hF 1
    (Affine.isTangentAt_def.2 ⟨isHomogeneous_X k 1, X_ne_zero 1,
      dvd_trans ⟨C (c 1), by rw [hc, hc0, C_0]; ring⟩ hLdvd⟩)
  have hc1 : c 1 ≠ 0 := fun hc1 ↦ hFe.isGoodPosition.not_isTangentAt_dehomogenize_X hF 0
    (Affine.isTangentAt_def.2 ⟨isHomogeneous_X k 0, X_ne_zero 0,
      dvd_trans ⟨C (c 0), by rw [hc, hc1, C_0]; ring⟩ hLdvd⟩)
  have hα : -c 0 / c 1 ≠ 0 := div_ne_zero (neg_ne_zero.2 hc0) hc1
  have hL : eval ![1, -c 0 / c 1] (dehomogenize 2 L) = 0 := by
    rw [hc]
    simp
    field_simp
    ring
  refine ⟨mk k ![-c 0 / c 1, 1, 0] (by simp), ?_, ?_⟩
  · rw [hFe.mem_pointsOverCentre_iff hF]
    obtain ⟨q, hq⟩ := hLdvd
    exact ⟨_, hα, rfl, by rw [hq, eval_mul, hL, zero_mul]⟩
  · rw [hGe.mem_pointsOverCentre_iff hG]
    obtain ⟨q, hq⟩ := (Affine.isTangentAt_def.1 hAG).2.2
    exact ⟨_, hα, rfl, by rw [hq, eval_mul, hL, zero_mul]⟩

/-- **A common tangent at the centre lowers `D` by at least one.** If `F G` is in excellent
position and `F` and `G` have a common tangent at `[0 : 0 : 1]`, the sum
`∑_Q m_Q(F') m_Q(G')` over the points `Q` over the centre is at least one. -/
theorem one_le_finsum_mult_mul_mult_pointsOverCentre (h : IsExcellentPosition (F * G))
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) {L : MvPolynomial (Fin 3) k}
    (hLF : IsTangentAt F (fundamentalPoint 2) L) (hLG : IsTangentAt G (fundamentalPoint 2) L) :
    1 ≤ ∑ᶠ Q ∈ pointsOverCentre (F * G),
      mult (properTransform F) Q * mult (properTransform G) Q := by
  obtain ⟨Q, hQF, hQG⟩ := h.exists_mem_pointsOverCentre_of_isTangentAt hF hG hLF hLG
  have hQ : Q ∈ pointsOverCentre (F * G) := by
    rw [pointsOverCentre_mul hF hG]
    exact Or.inl hQF
  have hF' := (mult_pos_iff hF.properTransform).2
    (zeroLocus_anti_mono (by simp) (pointsOverCentre_def F ▸ hQF).1)
  have hG' := (mult_pos_iff hG.properTransform).2
    (zeroLocus_anti_mono (by simp) (pointsOverCentre_def G ▸ hQG).1)
  rw [← finsum_mem_add_sdiff' (Set.singleton_subset_iff.2 hQ)
    ((h.pointsOverCentre_finite (hF.mul hG)).inter_of_left _), finsum_mem_singleton]
  exact (one_le_mul_of_one_le_of_one_le (Order.one_le_iff_pos.2 hF')
    (Order.one_le_iff_pos.2 hG')).trans le_self_add

end IsExcellentPosition

end PlaneCurves.Projective

end
