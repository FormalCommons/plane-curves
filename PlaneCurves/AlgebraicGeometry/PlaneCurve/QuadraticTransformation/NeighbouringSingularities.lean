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

In characteristic zero, for forms `F` and `G` with `F G` squarefree, there is a sequence whose
last pair has only ordinary multiple points and no common tangents (Fulton, §7.4,
Problem 7.16 (a)). The proof is induction on
`∑_k (N(q_k) + g*(q_k)) + ∑_{k ≠ l} D(q_k, q_l)` over the irreducible factors `q_k` of `F G`,
`N` counting the non-ordinary multiple points: each step, centred at a non-ordinary multiple
point of the product, lowers it.

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
* `PlaneCurves.Projective.exists_isQuadraticTransformSeq_forall_isOrdinaryMultiplePoint`: in
  characteristic zero, for forms `F` and `G` with `F G` squarefree, a sequence after which
  `F_s G_s` has only ordinary multiple points (Fulton, §7.4, Problem 7.16 (a)); also for a
  squarefree form
  (`exists_isQuadraticTransformSeq_forall_isOrdinaryMultiplePoint_of_squarefree`)
  and for a family of pairwise relatively prime irreducible forms
  (`exists_isQuadraticTransformSeq_prod_forall_isOrdinaryMultiplePoint`).
* `PlaneCurves.Projective.exists_isQuadraticTransformSeq_forall_not_isTangentAt`: its corollary,
  a sequence after which `F_s` and `G_s` have only ordinary multiple points and no common
  tangent at any point, the last pair of Noether's formula.
* `PlaneCurves.Projective.natCast_mul_eq_finsum_mult_mul_mult_add_spec`: Noether's formula, the
  inequality, and, in characteristic zero, a sequence along which the formula holds, together.

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
    exact ⟨hH.eq_zero_of_isUnit hu, hH'.eq_zero_of_isUnit hu⟩
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
    rw [ih (h.mono (Nat.le_succ s)), Finset.sum_range_succ, hg, mul_sub, mul_finsum_mem]
    simp_rw [Nat.two_mul_cast_choose_two]
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

/-! ### Existence of sequences to ordinary multiple points -/

section Existence

variable [IsAlgClosed k]

/-- One step for a pair of factors: for relatively prime forms `F` and `G` with `F G` in
excellent position after the change of coordinates `M`, centred at `P`, the defect
`D(F, G) = m n - ∑_Q m_Q(F) m_Q(G)` of the pair does not grow, and it drops when `F` and `G`
have a common tangent at `P`. -/
private theorem defect_properTransform_linearSubst_le (hF : F.IsHomogeneous m)
    (hG : G.IsHomogeneous n) (hFG : IsRelPrime F G) {M : Matrix (Fin 3) (Fin 3) k}
    (hM : Function.Injective M.mulVecLin) (h : IsExcellentPosition (linearSubst M (F * G)))
    {P : ℙ k (Fin 3 → k)} (hP : map M.mulVecLin hM (fundamentalPoint 2) = P) :
    ((((2 * m - (mult F P).toNat) * (2 * n - (mult G P).toNat) : ℕ) : ℤ) -
        ((∑ᶠ Q, mult (properTransform (linearSubst M F)) Q *
          mult (properTransform (linearSubst M G)) Q).toNat : ℤ) ≤
      ((m * n : ℕ) : ℤ) - ((∑ᶠ Q, mult F Q * mult G Q).toNat : ℤ)) ∧
    ((∃ L, IsTangentAt F P L ∧ IsTangentAt G P L) →
      ((((2 * m - (mult F P).toNat) * (2 * n - (mult G P).toNat) : ℕ) : ℤ) -
          ((∑ᶠ Q, mult (properTransform (linearSubst M F)) Q *
            mult (properTransform (linearSubst M G)) Q).toNat : ℤ) <
        ((m * n : ℕ) : ℤ) - ((∑ᶠ Q, mult F Q * mult G Q).toNat : ℤ))) := by
  subst hP
  have hE := h
  rw [map_mul] at hE
  have hFe := hE.of_mul_left (hF.linearSubst M) (hG.linearSubst M)
  have hGe := hE.of_mul_right (hF.linearSubst M) (hG.linearSubst M)
  have hF1 := hFe.isHomogeneous_properTransform (hF.linearSubst M)
  have hG1 := hGe.isHomogeneous_properTransform (hG.linearSubst M)
  rw [mult_linearSubst hF hM] at hF1
  rw [mult_linearSubst hG hM] at hG1
  have hU := Matrix.isUnit_det_of_mulVecLin_injective hM
  have hFG1 := ((isRelPrime_linearSubst_iff hU).2 hFG).properTransform (hF.linearSubst M)
    (hG.linearSubst M) hFe.not_X_dvd hGe.not_X_dvd
  have hS' := finsum_mult_mul_mult_le hF1 hG1 hFG1
  have key := mul_add_finsum_mult_mul_mult_properTransform_linearSubst hF hG hFG hM h
  generalize (2 * m - (mult F (map M.mulVecLin hM (fundamentalPoint 2))).toNat) *
    (2 * n - (mult G (map M.mulVecLin hM (fundamentalPoint 2))).toNat) = A at key hS' ⊢
  have hJ : ∀ L, IsTangentAt F (map M.mulVecLin hM (fundamentalPoint 2)) L →
      IsTangentAt G (map M.mulVecLin hM (fundamentalPoint 2)) L →
      1 ≤ ∑ᶠ Q ∈ pointsOverCentre (linearSubst M (F * G)),
        mult (properTransform (linearSubst M F)) Q * mult (properTransform (linearSubst M G)) Q :=
    fun L hLF hLG ↦ by
      rw [map_mul]
      exact hE.one_le_finsum_mult_mul_mult_pointsOverCentre (hF.linearSubst M) (hG.linearSubst M)
        ((isTangentAt_linearSubst_iff hF hM _).2 hLF) ((isTangentAt_linearSubst_iff hG hM _).2 hLG)
  revert key hJ hS'
  generalize ∑ᶠ Q, mult (properTransform (linearSubst M F)) Q *
    mult (properTransform (linearSubst M G)) Q = S'
  generalize ∑ᶠ Q, mult F Q * mult G Q = S
  generalize ∑ᶠ Q ∈ pointsOverCentre (linearSubst M (F * G)),
    mult (properTransform (linearSubst M F)) Q * mult (properTransform (linearSubst M G)) Q = J
  intro key hS' hJ
  obtain ⟨S', rfl⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top _) hS')
  have hfin : (A : ℕ∞) + S + J ≠ ⊤ := by
    rw [key, ← Nat.cast_add]; exact ENat.natCast_ne_top _
  simp only [ne_eq, ENat.add_eq_top, not_or] at hfin
  obtain ⟨⟨-, hS⟩, hJ0⟩ := hfin
  obtain ⟨S, rfl⟩ := ENat.ne_top_iff_exists.1 hS
  obtain ⟨J, rfl⟩ := ENat.ne_top_iff_exists.1 hJ0
  have key' : A + S + J = m * n + S' := by exact_mod_cast key
  simp only [ENat.toNat_natCast]
  zify at key'
  push_cast
  refine ⟨by linarith, fun ⟨L, hLF, hLG⟩ ↦ ?_⟩
  have : (1 : ℤ) ≤ J := by exact_mod_cast hJ L hLF hLG
  linarith

/-- The measure of the existence proof, for a family `q` of curves indexed by `s`:
`∑_a (N(q_a) + g*(q_a)) + ∑_{a ≠ b} D(q_a, q_b)`, with `N` the number of non-ordinary multiple
points and `D(q_a, q_b) = d_a d_b - ∑_P m_P(q_a) m_P(q_b)`. -/
private noncomputable def measure {ι : Type*} (s : Finset ι) (q : ι → MvPolynomial (Fin 3) k)
    (d : ι → ℕ) : ℤ :=
  ∑ a ∈ s, (((nonOrdinaryMultiplePoints (q a)).ncard : ℤ) + virtualGenus (q a)) +
    ∑ p ∈ s.offDiag,
      (((d p.1 * d p.2 : ℕ) : ℤ) - ((∑ᶠ P, mult (q p.1) P * mult (q p.2) P).toNat : ℤ))

/-- The measure of a family of pairwise relatively prime irreducible forms is nonnegative. -/
private theorem measure_nonneg {ι : Type*} {s : Finset ι} {q : ι → MvPolynomial (Fin 3) k}
    {d : ι → ℕ} (hq : ∀ a ∈ s, (q a).IsHomogeneous (d a)) (hirr : ∀ a ∈ s, Irreducible (q a))
    (hrel : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → IsRelPrime (q a) (q b)) : 0 ≤ measure s q d := by
  refine add_nonneg (Finset.sum_nonneg fun a ha ↦
    add_nonneg (Nat.cast_nonneg _) (virtualGenus_nonneg (hq a ha) (hirr a ha)))
    (Finset.sum_nonneg fun p hp ↦ ?_)
  obtain ⟨h1, h2, h12⟩ := Finset.mem_offDiag.1 hp
  have := ENat.toNat_le_toNat (finsum_mult_mul_mult_le (hq _ h1) (hq _ h2)
    (hrel _ h1 _ h2 h12)) (ENat.natCast_ne_top _)
  rw [ENat.toNat_natCast] at this
  omega

/-- The existence of a sequence to ordinary multiple points, by induction on a bound `N` for the
measure. -/
private theorem exists_isQuadraticTransformSeq_prod_of_measure_lt [CharZero k] {ι : Type*}
    (s : Finset ι) (N : ℕ) :
    ∀ (q : ι → MvPolynomial (Fin 3) k) (d : ι → ℕ), (∀ a ∈ s, (q a).IsHomogeneous (d a)) →
      (∀ a ∈ s, Irreducible (q a)) → (∀ a ∈ s, ∀ b ∈ s, a ≠ b → IsRelPrime (q a) (q b)) →
      measure s q d < N →
      ∃ (M : ℕ → Matrix (Fin 3) (Fin 3) k) (t : ℕ),
        IsQuadraticTransformSeq M (∏ a ∈ s, q a) t ∧
          nonOrdinaryMultiplePoints (quadraticTransformSeq M (∏ a ∈ s, q a) t) = ∅ := by
  induction N with
  | zero =>
    intro q d hq hirr hrel hμ
    exact absurd hμ (not_lt.2 (measure_nonneg hq hirr hrel))
  | succ N ih =>
    intro q d hq hirr hrel hμ
    by_cases hN : nonOrdinaryMultiplePoints (∏ a ∈ s, q a) = ∅
    · exact ⟨fun _ ↦ 1, 0, isQuadraticTransformSeq_zero _ _, by rwa [quadraticTransformSeq_zero]⟩
    obtain ⟨P, hP⟩ := Set.nonempty_iff_ne_empty.2 hN
    obtain ⟨M, hM, hTP, hE0, -⟩ := exists_isExcellentPosition_prod_avoiding hq hirr hrel
      (fun a ha ↦ not_isTerriblePoint (hq a ha) (hirr a ha) P.rep_ne_zero) Set.finite_empty
      (Set.notMem_empty P)
    have hE := hE0
    rw [map_prod, isExcellentPosition_prod_iff fun a ha ↦ (hq a ha).linearSubst M] at hE
    have hU := Matrix.isUnit_det_of_mulVecLin_injective hM
    have hq' (a : ι) (ha : a ∈ s) : (properTransform (linearSubst M (q a))).IsHomogeneous
        (2 * d a - (mult (q a) P).toNat) := by
      have := (hE.1 a ha).isHomogeneous_properTransform ((hq a ha).linearSubst M)
      rwa [mult_linearSubst (hq a ha) hM, hTP] at this
    have hirr' (a : ι) (ha : a ∈ s) : Irreducible (properTransform (linearSubst M (q a))) :=
      irreducible_properTransform ((hq a ha).linearSubst M)
        ((irreducible_linearSubst_iff hU).2 (hirr a ha)) (hE.1 a ha).not_X_dvd
    have hrel' (a : ι) (ha : a ∈ s) (b : ι) (hb : b ∈ s) (hab : a ≠ b) :
        IsRelPrime (properTransform (linearSubst M (q a)))
          (properTransform (linearSubst M (q b))) :=
      ((isRelPrime_linearSubst_iff hU).2 (hrel a ha b hb hab)).properTransform
        ((hq a ha).linearSubst M) ((hq b hb).linearSubst M) (hE.1 a ha).not_X_dvd
        (hE.1 b hb).not_X_dvd
    have hprod : properTransform (linearSubst M (∏ a ∈ s, q a)) =
        ∏ a ∈ s, properTransform (linearSubst M (q a)) := by
      rw [map_prod, properTransform_prod s fun a ha ↦ (hq a ha).linearSubst M]
    -- The terms of one factor do not grow, and drop for a factor with `P` non-ordinary.
    have hN1 (a : ι) (ha : a ∈ s) :
        ((nonOrdinaryMultiplePoints (properTransform (linearSubst M (q a)))).ncard : ℤ) +
            virtualGenus (properTransform (linearSubst M (q a))) ≤
          (nonOrdinaryMultiplePoints (q a)).ncard + virtualGenus (q a) := by
      have := (hE.1 a ha).ncard_add_virtualGenus_properTransform_le ((hq a ha).linearSubst M)
        ((irreducible_linearSubst_iff hU).2 (hirr a ha))
      rwa [ncard_nonOrdinaryMultiplePoints_linearSubst (hq a ha) hM,
        virtualGenus_linearSubst (hq a ha) hM] at this
    have hN2 (a : ι) (ha : a ∈ s) (hPa : P ∈ nonOrdinaryMultiplePoints (q a)) :
        ((nonOrdinaryMultiplePoints (properTransform (linearSubst M (q a)))).ncard : ℤ) +
            virtualGenus (properTransform (linearSubst M (q a))) <
          (nonOrdinaryMultiplePoints (q a)).ncard + virtualGenus (q a) := by
      have := (hE.1 a ha).ncard_add_virtualGenus_properTransform_lt ((hq a ha).linearSubst M)
        ((irreducible_linearSubst_iff hU).2 (hirr a ha))
        (by rwa [nonOrdinaryMultiplePoints_linearSubst (hq a ha) hM, Set.mem_preimage, hTP])
      rwa [ncard_nonOrdinaryMultiplePoints_linearSubst (hq a ha) hM,
        virtualGenus_linearSubst (hq a ha) hM] at this
    -- The defect of a pair does not grow, and drops for a pair with a common tangent at `P`.
    have hD (p : ι × ι) (hp : p ∈ s.offDiag) := by
      obtain ⟨h1, h2, h12⟩ := Finset.mem_offDiag.1 hp
      refine defect_properTransform_linearSubst_le (hq _ h1) (hq _ h2) (hrel _ h1 _ h2 h12) hM
        ?_ hTP
      rw [map_mul, isExcellentPosition_mul_iff ((hq _ h1).linearSubst M) ((hq _ h2).linearSubst M)]
      exact ⟨hE.1 _ h1, hE.1 _ h2, hE.2 _ h1 _ h2 h12⟩
    have hlt : measure s (fun a ↦ properTransform (linearSubst M (q a)))
        (fun a ↦ 2 * d a - (mult (q a) P).toNat) < measure s q d := by
      rw [measure, measure]
      rcases (mem_nonOrdinaryMultiplePoints_prod_iff hq fun a ha ↦ (hirr a ha).ne_zero).1 hP with
        ⟨a, ha, hPa⟩ | ⟨a, ha, b, hb, hab, hL⟩
      · exact add_lt_add_of_lt_of_le (Finset.sum_lt_sum hN1 ⟨a, ha, hN2 a ha hPa⟩)
          (Finset.sum_le_sum fun p hp ↦ (hD p hp).1)
      · exact add_lt_add_of_le_of_lt (Finset.sum_le_sum hN1)
          (Finset.sum_lt_sum (fun p hp ↦ (hD p hp).1)
            ⟨(a, b), Finset.mem_offDiag.2 ⟨ha, hb, hab⟩,
              (hD (a, b) (Finset.mem_offDiag.2 ⟨ha, hb, hab⟩)).2 hL⟩)
    obtain ⟨M', t, hseq, hord⟩ := ih _ _ hq' hirr' hrel' (by omega)
    refine ⟨fun | 0 => M | j + 1 => M' j, t + 1,
      isQuadraticTransformSeq_succ_iff.2 ⟨⟨hM, hE0⟩, ?_⟩, ?_⟩
    · rw [hprod]
      exact hseq
    · rw [quadraticTransformSeq_succ']
      dsimp only
      rw [hprod]
      exact hord

/-- **Sequences of quadratic transformations to ordinary multiple points, for a family**
(Fulton, §7.4, Problem 7.16 (a)). Let `k` be algebraically closed of characteristic zero and
`q_a`, for `a ∈ s`, pairwise relatively prime irreducible forms. Then there is a sequence of
quadratic transformations of `∏_a q_a` after which all multiple points are ordinary. -/
theorem exists_isQuadraticTransformSeq_prod_forall_isOrdinaryMultiplePoint [CharZero k]
    {ι : Type*} {s : Finset ι} {q : ι → MvPolynomial (Fin 3) k} {d : ι → ℕ}
    (hq : ∀ a ∈ s, (q a).IsHomogeneous (d a)) (hirr : ∀ a ∈ s, Irreducible (q a))
    (hrel : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → IsRelPrime (q a) (q b)) :
    ∃ (M : ℕ → Matrix (Fin 3) (Fin 3) k) (t : ℕ), IsQuadraticTransformSeq M (∏ a ∈ s, q a) t ∧
      ∀ P, IsMultiplePoint (quadraticTransformSeq M (∏ a ∈ s, q a) t) P →
        IsOrdinaryMultiplePoint (quadraticTransformSeq M (∏ a ∈ s, q a) t) P := by
  obtain ⟨M, t, h, hN⟩ := exists_isQuadraticTransformSeq_prod_of_measure_lt s
    ((measure s q d).toNat + 1) q d hq hirr hrel
    (by have := Int.toNat_of_nonneg (measure_nonneg hq hirr hrel); omega)
  exact ⟨M, t, h, nonOrdinaryMultiplePoints_eq_empty_iff.1 hN⟩

open UniqueFactorizationMonoid in
/-- **Sequences of quadratic transformations to ordinary multiple points, for a squarefree form**
(Fulton, §7.4, Problem 7.16 (a)). Let `k` be algebraically closed of characteristic zero and `H`
a squarefree form. Then there is a sequence of quadratic transformations of `H` after which all
multiple points are ordinary. -/
theorem exists_isQuadraticTransformSeq_forall_isOrdinaryMultiplePoint_of_squarefree [CharZero k]
    {H : MvPolynomial (Fin 3) k} (hH : H.IsHomogeneous n) (hsq : Squarefree H) :
    ∃ (M : ℕ → Matrix (Fin 3) (Fin 3) k) (t : ℕ), IsQuadraticTransformSeq M H t ∧
      ∀ P, IsMultiplePoint (quadraticTransformSeq M H t) P →
        IsOrdinaryMultiplePoint (quadraticTransformSeq M H t) P := by
  classical
  have hm (q : MvPolynomial (Fin 3) k) (hq : q ∈ (factors H).toFinset) :
      Irreducible q ∧ q ∣ H := by
    rw [Multiset.mem_toFinset] at hq
    exact ⟨irreducible_of_factor q hq, dvd_of_mem_factors hq⟩
  have hF (q : MvPolynomial (Fin 3) k) (hq : q ∈ (factors H).toFinset) :
      q.IsHomogeneous q.totalDegree :=
    hH.isHomogeneous_totalDegree_of_dvd hsq.ne_zero (hm q hq).2
  obtain ⟨M, t, h, hord⟩ := exists_isQuadraticTransformSeq_prod_forall_isOrdinaryMultiplePoint
    (s := (factors H).toFinset) (q := fun q ↦ q) hF (fun q hq ↦ (hm q hq).1)
    (fun p hp q hq hpq ↦ hsq.pairwise_isRelPrime_toFinset_factors hp hq hpq)
  obtain ⟨c, hc, hHc⟩ := exists_eq_smul_prod_toFinset_factors hsq
  have hP := IsHomogeneous.prod _ _ _ hF
  refine ⟨M, t, ?_, fun P hP' ↦ ?_⟩
  · rw [hHc, isQuadraticTransformSeq_smul_iff hP hc]
    exact h
  · rw [hHc, quadraticTransformSeq_smul hP] at hP' ⊢
    have := nonOrdinaryMultiplePoints_eq_empty_iff.2 hord
    rw [← nonOrdinaryMultiplePoints_smul hc] at this
    exact nonOrdinaryMultiplePoints_eq_empty_iff.1 this P hP'

/-- **Sequences of quadratic transformations to ordinary multiple points** (Fulton, §7.4,
Problem 7.16 (a)). Let `k` be algebraically closed of characteristic zero and `F`, `G` forms with
`F G` squarefree. Then there is a sequence of quadratic transformations of `F G` after which all
multiple points of `F_s G_s` are ordinary. -/
theorem exists_isQuadraticTransformSeq_forall_isOrdinaryMultiplePoint [CharZero k]
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (hsq : Squarefree (F * G)) :
    ∃ (M : ℕ → Matrix (Fin 3) (Fin 3) k) (s : ℕ), IsQuadraticTransformSeq M (F * G) s ∧
      ∀ P, IsMultiplePoint (quadraticTransformSeq M F s * quadraticTransformSeq M G s) P →
        IsOrdinaryMultiplePoint (quadraticTransformSeq M F s * quadraticTransformSeq M G s) P := by
  obtain ⟨M, s, h, hord⟩ :=
    exists_isQuadraticTransformSeq_forall_isOrdinaryMultiplePoint_of_squarefree (hF.mul hG) hsq
  rw [quadraticTransformSeq_mul hF hG] at hord
  exact ⟨M, s, h, hord⟩

/-- **Sequences of quadratic transformations to a pair with ordinary multiple points and no
common tangents** (Fulton, §7.4, Problem 7.16 (a)). Let `k` be algebraically closed of
characteristic zero and `F`, `G` forms with `F G` squarefree. Then there is a sequence of
quadratic transformations of `F G` after which `F_s` and `G_s` have only ordinary multiple points
and no common tangent at any point. -/
theorem exists_isQuadraticTransformSeq_forall_not_isTangentAt [CharZero k]
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n) (hsq : Squarefree (F * G)) :
    ∃ (M : ℕ → Matrix (Fin 3) (Fin 3) k) (s : ℕ), IsQuadraticTransformSeq M (F * G) s ∧
      (∀ P, IsMultiplePoint (quadraticTransformSeq M F s) P →
        IsOrdinaryMultiplePoint (quadraticTransformSeq M F s) P) ∧
      (∀ P, IsMultiplePoint (quadraticTransformSeq M G s) P →
        IsOrdinaryMultiplePoint (quadraticTransformSeq M G s) P) ∧
      ∀ P L, ¬(IsTangentAt (quadraticTransformSeq M F s) P L ∧
        IsTangentAt (quadraticTransformSeq M G s) P L) := by
  obtain ⟨M, s, h, hord⟩ := exists_isQuadraticTransformSeq_forall_isOrdinaryMultiplePoint hF hG hsq
  have hle (P : ℙ k (Fin 3 → k)) := le_self_add (a := mult (quadraticTransformSeq M F s) P)
    (b := mult (quadraticTransformSeq M G s) P)
  have hle' (P : ℙ k (Fin 3 → k)) := le_add_self (a := mult (quadraticTransformSeq M G s) P)
    (b := mult (quadraticTransformSeq M F s) P)
  refine ⟨M, s, h, fun P hP ↦ ?_, fun P hP ↦ ?_, fun P L ⟨hLF, hLG⟩ ↦ ?_⟩
  · have hO := hord P (isMultiplePoint_def.2 ((isMultiplePoint_def.1 hP).trans
      ((hle P).trans (mult_mul _ _ P).ge)))
    exact hO.mult_le_one_or_isOrdinaryMultiplePoint_left.resolve_left
      (not_le.2 (lt_of_lt_of_le (by norm_num) (isMultiplePoint_def.1 hP)))
  · have hO := hord P (isMultiplePoint_def.2 ((isMultiplePoint_def.1 hP).trans
      ((hle' P).trans (mult_mul _ _ P).ge)))
    exact hO.mult_le_one_or_isOrdinaryMultiplePoint_right.resolve_left
      (not_le.2 (lt_of_lt_of_le (by norm_num) (isMultiplePoint_def.1 hP)))
  · have h1 := Order.one_le_iff_pos.2 (mult_pos_iff_eval_rep.2 hLF.eval_rep_eq_zero)
    have h2 := Order.one_le_iff_pos.2 (mult_pos_iff_eval_rep.2 hLG.eval_rep_eq_zero)
    have hO := hord P (isMultiplePoint_def.2 (by
      rw [mult_mul]
      exact (add_le_add h1 h2).trans_eq' (by norm_num)))
    exact hO.not_isTangentAt_and ⟨L, hLF, hLG⟩

end Existence

/-! ### Noether's formula -/

/-- **Noether's formula for intersection numbers at infinitely near points** (Fulton, §7.4,
Problems 7.15 and 7.16). Let `k` be algebraically closed and `F`, `G` forms of degrees `m` and `n`
in `k[X, Y, Z]`. Along a sequence of `s` quadratic transformations, write `Fᵢ` and `Gᵢ` for the
curves after `i` steps; the *neighbouring singularities* of the `i`-th step are the points `Q`
over its centre.

1. If `F` and `G` are nonzero and relatively prime, then for every sequence of quadratic
   transformations of `F G` after which `F_s` and `G_s` have no common tangent at any point,
   `m n = ∑_P m_P(F) m_P(G) + ∑_{i < s} ∑_Q m_Q(Fᵢ₊₁) m_Q(Gᵢ₊₁)`.
2. If `F` is irreducible, then for every sequence of quadratic transformations of `F`,
   `∑_P m_P(F)(m_P(F) - 1) + ∑_{i < s} ∑_Q m_Q(Fᵢ₊₁)(m_Q(Fᵢ₊₁) - 1) ≤ (m - 1)(m - 2)`.
3. If `k` has characteristic zero and `F G` is squarefree, there is a sequence of quadratic
   transformations of `F G` after which `F_s` and `G_s` have only ordinary multiple points and no
   common tangent at any point, and the formula of 1 holds along it.

The book states 1 and 2 for sequences that end at ordinary multiple points. Here 1 needs only that
the last pair has no common tangent, and 2 holds for every sequence; both hold in every
characteristic.

Milestone: *Noether's formula for intersection numbers at infinitely near points*. -/
theorem natCast_mul_eq_finsum_mult_mul_mult_add_spec [IsAlgClosed k] (hF : F.IsHomogeneous m)
    (hG : G.IsHomogeneous n) :
    (∀ (M : ℕ → Matrix (Fin 3) (Fin 3) k) (s : ℕ), IsQuadraticTransformSeq M (F * G) s →
      F ≠ 0 → G ≠ 0 → IsRelPrime F G →
      (∀ P L, ¬(IsTangentAt (quadraticTransformSeq M F s) P L ∧
        IsTangentAt (quadraticTransformSeq M G s) P L)) →
      ((m * n : ℕ) : ℕ∞) = ∑ᶠ P, mult F P * mult G P +
        ∑ i ∈ Finset.range s,
          ∑ᶠ Q ∈ pointsOverCentre (linearSubst (M i) (quadraticTransformSeq M (F * G) i)),
            mult (quadraticTransformSeq M F (i + 1)) Q *
              mult (quadraticTransformSeq M G (i + 1)) Q) ∧
    (∀ (M : ℕ → Matrix (Fin 3) (Fin 3) k) (s : ℕ), IsQuadraticTransformSeq M F s →
      Irreducible F →
      ∑ᶠ P, ((mult F P).toNat : ℤ) * ((mult F P).toNat - 1) +
          ∑ i ∈ Finset.range s,
            ∑ᶠ Q ∈ pointsOverCentre (linearSubst (M i) (quadraticTransformSeq M F i)),
              ((mult (quadraticTransformSeq M F (i + 1)) Q).toNat : ℤ) *
                ((mult (quadraticTransformSeq M F (i + 1)) Q).toNat - 1) ≤
        ((m : ℤ) - 1) * ((m : ℤ) - 2)) ∧
    (CharZero k → Squarefree (F * G) →
      ∃ (M : ℕ → Matrix (Fin 3) (Fin 3) k) (s : ℕ), IsQuadraticTransformSeq M (F * G) s ∧
        (∀ P, IsMultiplePoint (quadraticTransformSeq M F s) P →
          IsOrdinaryMultiplePoint (quadraticTransformSeq M F s) P) ∧
        (∀ P, IsMultiplePoint (quadraticTransformSeq M G s) P →
          IsOrdinaryMultiplePoint (quadraticTransformSeq M G s) P) ∧
        (∀ P L, ¬(IsTangentAt (quadraticTransformSeq M F s) P L ∧
          IsTangentAt (quadraticTransformSeq M G s) P L)) ∧
        ((m * n : ℕ) : ℕ∞) = ∑ᶠ P, mult F P * mult G P +
          ∑ i ∈ Finset.range s,
            ∑ᶠ Q ∈ pointsOverCentre (linearSubst (M i) (quadraticTransformSeq M (F * G) i)),
              mult (quadraticTransformSeq M F (i + 1)) Q *
                mult (quadraticTransformSeq M G (i + 1)) Q) := by
  refine ⟨fun M s h hF0 hG0 hFG hT ↦ h.natCast_mul_eq_finsum_mult_mul_mult_add hF hG hF0 hG0 hFG hT,
    fun M s h hirr ↦ h.finsum_mult_mul_mult_sub_one_add_le hF hirr, fun _ hsq ↦ ?_⟩
  obtain ⟨M, s, h, hFo, hGo, hT⟩ := exists_isQuadraticTransformSeq_forall_not_isTangentAt hF hG hsq
  have hFG0 : F * G ≠ 0 := fun h0 ↦ not_squarefree_zero (h0 ▸ hsq)
  exact ⟨M, s, h, hFo, hGo, hT, h.natCast_mul_eq_finsum_mult_mul_mult_add hF hG
    (left_ne_zero_of_mul hFG0) (right_ne_zero_of_mul hFG0) (squarefree_mul_iff.1 hsq).1 hT⟩

end PlaneCurves.Projective

end
