/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Bezout.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Sequence
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Singularities.CommonPoints
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Singularities.Genus

/-!
# Neighbouring singularities

Let `F` and `G` be relatively prime forms of degrees `m` and `n`, and apply the same sequence of
quadratic transformations to both, by applying it to `F G`: `Fᵢ₊₁` and `Gᵢ₊₁` are the proper
transforms of `Fᵢ` and `Gᵢ` in the coordinates `M i` of the `i`-th step. The *neighbouring
singularities* of the `i`-th step are the points of `Fᵢ₊₁ Gᵢ₊₁` over its centre. Each step lowers
`D(F, G) = m n - ∑_P m_P(F) m_P(G)` by the sum of `m_Q(Fᵢ₊₁) m_Q(Gᵢ₊₁)` over these points, and
`D` vanishes for a pair with no common tangent, by Bézout's theorem. This gives **Noether's
formula** (Fulton, §7.4, Problem 7.15)

`m n = ∑_P m_P(F) m_P(G) + ∑_i ∑_Q m_Q(Fᵢ₊₁) m_Q(Gᵢ₊₁)`

for every sequence whose last pair `F_s`, `G_s` has no common tangent at any point, in every
characteristic.

For one irreducible curve `F` of degree `n`, the virtual genus drops along a sequence by the
`m_Q(m_Q - 1)/2` of the points `Q` over the centres, and it stays nonnegative. This gives the
**inequality** (Fulton, §7.4, Problem 7.16 (b))

`∑_P m_P(F)(m_P(F) - 1) + ∑_i ∑_Q m_Q(Fᵢ₊₁)(m_Q(Fᵢ₊₁) - 1) ≤ (n - 1)(n - 2)`

for every sequence of quadratic transformations of `F`.

## Main results

* `PlaneCurves.Projective.IsQuadraticTransformSeq.mul_add_finsum_mult_mul_mult`: the identity
  `m n + ∑_P m_P(F_s) m_P(G_s) = m_s n_s + ∑_P m_P(F) m_P(G) + ∑_i ∑_Q m_Q(Fᵢ₊₁) m_Q(Gᵢ₊₁)` along
  any sequence, `m_s` and `n_s` being the degrees of `F_s` and `G_s`.
* `PlaneCurves.Projective.IsQuadraticTransformSeq.natCast_mul_eq_finsum_mult_mul_mult_add`:
  Noether's formula.
* `PlaneCurves.Projective.IsQuadraticTransformSeq.two_mul_virtualGenus_eq`: the virtual genus
  along a sequence of an irreducible curve.
* `PlaneCurves.Projective.IsQuadraticTransformSeq.finsum_mult_mul_mult_sub_one_add_le`: the
  inequality.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.4, Problems 7.15 and 7.16
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {M : ℕ → Matrix (Fin 3) (Fin 3) k}
  {F G : MvPolynomial (Fin 3) k} {m n s : ℕ}

/-- For relatively prime forms, the product of their degrees does not depend on the degrees chosen:
if one of them is `0`, the other is a unit, of degree `0`. -/
private theorem mul_eq_mul_of_isRelPrime {m' n' : ℕ} (hF : F.IsHomogeneous m)
    (hF' : F.IsHomogeneous m') (hG : G.IsHomogeneous n) (hG' : G.IsHomogeneous n')
    (hFG : IsRelPrime F G) : m * n = m' * n' := by
  have hdeg {H : MvPolynomial (Fin 3) k} {d d' : ℕ} (hH : H.IsHomogeneous d)
      (hH' : H.IsHomogeneous d') (hu : IsUnit H) : d = 0 ∧ d' = 0 := by
    have h0 := (isUnit_iff_totalDegree_of_isReduced.1 hu).2
    exact ⟨(hH.totalDegree hu.ne_zero).symm.trans h0, (hH'.totalDegree hu.ne_zero).symm.trans h0⟩
  by_cases hF0 : F = 0
  · subst hF0
    obtain ⟨h1, h2⟩ := hdeg hG hG' (isRelPrime_zero_left.1 hFG)
    simp [h1, h2]
  by_cases hG0 : G = 0
  · subst hG0
    obtain ⟨h1, h2⟩ := hdeg hF hF' (isRelPrime_zero_right.1 hFG)
    simp [h1, h2]
  rw [hF.inj_right hF' hF0, hG.inj_right hG' hG0]

/-- The rearrangement that telescopes the identity along a sequence by one step. -/
private theorem add_add_eq_of_add_eq {α : Type*} [AddCommSemigroup α] {a b c d e f g h : α}
    (key : a + e = c + f + g) (step : a + d + h = b + f) :
    a + (b + e) = a + (c + d + (g + h)) :=
  calc a + (b + e) = b + (a + e) := by ac_rfl
    _ = b + (c + f + g) := by rw [key]
    _ = c + g + (b + f) := by ac_rfl
    _ = c + g + (a + d + h) := by rw [step]
    _ = _ := by ac_rfl

namespace IsQuadraticTransformSeq

/-- **The identity along a sequence of quadratic transformations** (Fulton, §7.4, Problem 7.15).
Let `F` and `G` be relatively prime forms of degrees `m` and `n`, and apply a sequence of `s`
quadratic transformations of `F G` to both. If `F_s` and `G_s` have degrees `m_s` and `n_s`, then
`m n + ∑_P m_P(F_s) m_P(G_s) = m_s n_s + ∑_P m_P(F) m_P(G) + ∑_{i < s} ∑_Q m_Q(Fᵢ₊₁) m_Q(Gᵢ₊₁)`,
the inner sum running over the points `Q` over the centre of the `i`-th step. With
`D(F, G) = m n - ∑_P m_P(F) m_P(G)`, this says
`D(F, G) = D(F_s, G_s) + ∑_{i < s} ∑_Q m_Q(Fᵢ₊₁) m_Q(Gᵢ₊₁)`. -/
theorem mul_add_finsum_mult_mul_mult (h : IsQuadraticTransformSeq M (F * G) s)
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (hFG : IsRelPrime F G) {m' n' : ℕ}
    (hFs : (quadraticTransformSeq M F s).IsHomogeneous m')
    (hGs : (quadraticTransformSeq M G s).IsHomogeneous n') :
    ((m * n : ℕ) : ℕ∞) +
        ∑ᶠ P, mult (quadraticTransformSeq M F s) P * mult (quadraticTransformSeq M G s) P =
      ((m' * n' : ℕ) : ℕ∞) + ∑ᶠ P, mult F P * mult G P +
        ∑ i ∈ Finset.range s,
          ∑ᶠ Q ∈ pointsOverCentre (linearSubst (M i) (quadraticTransformSeq M (F * G) i)),
            mult (quadraticTransformSeq M F (i + 1)) Q *
              mult (quadraticTransformSeq M G (i + 1)) Q := by
  induction s generalizing M F G m n with
  | zero =>
    rw [quadraticTransformSeq_zero] at hFs hGs
    simp [mul_eq_mul_of_isRelPrime hF hFs hG hGs hFG, add_comm]
  | succ s ih =>
    obtain ⟨⟨hM, hE⟩, ht⟩ := isQuadraticTransformSeq_succ_iff.1 h
    have hE' := hE
    rw [map_mul] at hE'
    have hFe := hE'.of_mul_left (hF.linearSubst (M 0)) (hG.linearSubst (M 0))
    have hGe := hE'.of_mul_right (hF.linearSubst (M 0)) (hG.linearSubst (M 0))
    have hPT : properTransform (linearSubst (M 0) (F * G)) =
        properTransform (linearSubst (M 0) F) * properTransform (linearSubst (M 0) G) := by
      rw [map_mul, properTransform_mul (hF.linearSubst _) (hG.linearSubst _)]
    have hF1 := hFe.isHomogeneous_properTransform (hF.linearSubst (M 0))
    have hG1 := hGe.isHomogeneous_properTransform (hG.linearSubst (M 0))
    rw [mult_linearSubst hF hM] at hF1
    rw [mult_linearSubst hG hM] at hG1
    have hFG1 : IsRelPrime (properTransform (linearSubst (M 0) F))
        (properTransform (linearSubst (M 0) G)) := by
      simpa using h.isRelPrime hF hG hFG (i := 1) (by omega)
    rw [quadraticTransformSeq_succ'] at hFs hGs
    have key := ih (hPT ▸ ht) hF1 hG1 hFG1 hFs hGs
    have step := mul_add_finsum_mult_mul_mult_properTransform_linearSubst hF hG hFG hM hE
    simp only [← hPT] at key
    simp only [quadraticTransformSeq_succ' M F, quadraticTransformSeq_succ' M G,
      quadraticTransformSeq_succ' M (F * G), Finset.sum_range_succ', quadraticTransformSeq_zero]
    exact WithTop.add_left_cancel (ENat.natCast_ne_top _) (add_add_eq_of_add_eq key step)

/-- **Noether's formula** (Fulton, §7.4, Problem 7.15). Let `k` be algebraically closed, `F` and
`G` nonzero relatively prime forms of degrees `m` and `n`, and apply a sequence of `s` quadratic
transformations of `F G` to both. If `F_s` and `G_s` have no common tangent at any point, then
`m n = ∑_P m_P(F) m_P(G) + ∑_{i < s} ∑_Q m_Q(Fᵢ₊₁) m_Q(Gᵢ₊₁)`, the inner sum running over the
points `Q` over the centre of the `i`-th step, the neighbouring singularities. -/
theorem natCast_mul_eq_finsum_mult_mul_mult_add [IsAlgClosed k]
    (h : IsQuadraticTransformSeq M (F * G) s) (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) (hFG : IsRelPrime F G)
    (hT : ∀ P L, ¬(IsTangentAt (quadraticTransformSeq M F s) P L ∧
      IsTangentAt (quadraticTransformSeq M G s) P L)) :
    ((m * n : ℕ) : ℕ∞) = ∑ᶠ P, mult F P * mult G P +
      ∑ i ∈ Finset.range s,
        ∑ᶠ Q ∈ pointsOverCentre (linearSubst (M i) (quadraticTransformSeq M (F * G) i)),
          mult (quadraticTransformSeq M F (i + 1)) Q *
            mult (quadraticTransformSeq M G (i + 1)) Q := by
  obtain ⟨m', hFs⟩ := isHomogeneous_quadraticTransformSeq (M := M) hF s
  obtain ⟨n', hGs⟩ := isHomogeneous_quadraticTransformSeq (M := M) hG s
  have hFGs := h.isRelPrime hF hG hFG le_rfl
  have hB : ∑ᶠ P, mult (quadraticTransformSeq M F s) P * mult (quadraticTransformSeq M G s) P =
      ((m' * n' : ℕ) : ℕ∞) := by
    rw [← finsum_intersectionNumber_eq_mul hFs hGs hFGs]
    refine finsum_congr fun P ↦ ((intersectionNumber_eq_mul_mult_iff hFs hGs
      ((h.of_mul_left hF hG).ne_zero hF hF0 le_rfl)
      ((h.of_mul_right hF hG).ne_zero hG hG0 le_rfl)).2 ?_).symm
    rintro ⟨L, hL⟩
    exact hT P L hL
  have key := h.mul_add_finsum_mult_mul_mult hF hG hFG hFs hGs
  rw [hB, add_comm, add_assoc] at key
  exact WithTop.add_left_cancel (ENat.natCast_ne_top _) key

/-- `2 * m.choose 2 = m (m - 1)` in `ℤ`, summed over a set. -/
private theorem two_mul_finsum_mem_choose_two {α : Type*} (S : Set α) (f : α → ℕ) :
    2 * ∑ᶠ a ∈ S, ((f a).choose 2 : ℤ) = ∑ᶠ a ∈ S, ((f a : ℤ) * ((f a : ℤ) - 1)) := by
  rw [mul_finsum_mem]
  refine finsum_mem_congr rfl fun a _ ↦ ?_
  have h2 : 2 * (f a).choose 2 = f a * (f a - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd]
  rcases Nat.eq_zero_or_pos (f a) with h0 | hpos
  · simp [h0]
  · have := congrArg (Nat.cast : ℕ → ℤ) h2
    push_cast [Nat.cast_sub hpos] at this
    exact this

/-- **The virtual genus along a sequence of quadratic transformations** (Fulton, §7.4,
Problem 7.16). Let `k` be algebraically closed and `F` an irreducible form, and apply a sequence of
`s` quadratic transformations to it. Then
`2 g*(F) = 2 g*(F_s) + ∑_{i < s} ∑_Q m_Q(Fᵢ₊₁)(m_Q(Fᵢ₊₁) - 1)`, the inner sum running over the
points `Q` over the centre of the `i`-th step. -/
theorem two_mul_virtualGenus_eq [IsAlgClosed k] (h : IsQuadraticTransformSeq M F s)
    (hF : F.IsHomogeneous n) (hirr : Irreducible F) :
    2 * virtualGenus F = 2 * virtualGenus (quadraticTransformSeq M F s) +
      ∑ i ∈ Finset.range s,
        ∑ᶠ Q ∈ pointsOverCentre (linearSubst (M i) (quadraticTransformSeq M F i)),
          ((mult (quadraticTransformSeq M F (i + 1)) Q).toNat : ℤ) *
            ((mult (quadraticTransformSeq M F (i + 1)) Q).toNat - 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    obtain ⟨d, hd⟩ := isHomogeneous_quadraticTransformSeq (M := M) hF s
    have hirr' := h.irreducible hF hirr (i := s) (by omega)
    have hM := h.injective (Nat.lt_succ_self s)
    have hg := (h.isExcellentPosition (Nat.lt_succ_self s)).virtualGenus_properTransform
      (hd.linearSubst (M s))
      ((irreducible_linearSubst_iff (Matrix.isUnit_det_of_mulVecLin_injective hM)).2 hirr')
    rw [virtualGenus_linearSubst hd hM, ← quadraticTransformSeq_succ] at hg
    rw [ih (h.mono (Nat.le_succ s)), Finset.sum_range_succ, ← two_mul_finsum_mem_choose_two, hg]
    ring

/-- **The inequality for neighbouring singularities** (Fulton, §7.4, Problem 7.16 (b)). Let `k` be
algebraically closed and `F` an irreducible form of degree `n`, and apply a sequence of `s`
quadratic transformations to it. Then
`∑_P m_P(F)(m_P(F) - 1) + ∑_{i < s} ∑_Q m_Q(Fᵢ₊₁)(m_Q(Fᵢ₊₁) - 1) ≤ (n - 1)(n - 2)`, the inner sum
running over the points `Q` over the centre of the `i`-th step. -/
theorem finsum_mult_mul_mult_sub_one_add_le [IsAlgClosed k] (h : IsQuadraticTransformSeq M F s)
    (hF : F.IsHomogeneous n) (hirr : Irreducible F) :
    ∑ᶠ P, ((mult F P).toNat : ℤ) * ((mult F P).toNat - 1) +
        ∑ i ∈ Finset.range s,
          ∑ᶠ Q ∈ pointsOverCentre (linearSubst (M i) (quadraticTransformSeq M F i)),
            ((mult (quadraticTransformSeq M F (i + 1)) Q).toNat : ℤ) *
              ((mult (quadraticTransformSeq M F (i + 1)) Q).toNat - 1) ≤
      ((n : ℤ) - 1) * ((n : ℤ) - 2) := by
  obtain ⟨d, hd⟩ := isHomogeneous_quadraticTransformSeq (M := M) hF s
  have hg := h.two_mul_virtualGenus_eq hF hirr
  rw [two_mul_virtualGenus hF hirr.ne_zero (hF.degree_ne_zero_of_irreducible hirr)] at hg
  linarith [virtualGenus_nonneg hd (h.irreducible hF hirr le_rfl)]

end IsQuadraticTransformSeq

end PlaneCurves.Projective

end
