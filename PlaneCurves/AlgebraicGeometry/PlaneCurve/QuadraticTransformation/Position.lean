/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.GenericLine
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.TerriblePoint
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.LinearSubvariety
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.GoodPosition

/-!
# Excellent position for the standard quadratic transformation

A plane curve `F` of degree `n` is in *excellent position* (Fulton, §7.4) if it is in good
position, the exceptional line `L = V(Z)` meets it transversally in points that are not
fundamental, and the exceptional lines `L' = V(Y)` and `L'' = V(X)` through `P = [0 : 0 : 1]`
meet it transversally, away from the fundamental points, in their points other than `P`. We
state this pointwise: every point `Q ≠ P` of `F` on an exceptional line `V(Xⱼ)` is not
fundamental and has `I(Q, F ∩ Xⱼ) = 1`. The counts `n` and `n - r` of Fulton's definition,
`r = m_P(F)`, are then consequences of Bézout's theorem.

A curve in excellent position does not pass through `P' = [0 : 1 : 0]` or `P'' = [1 : 0 : 0]`,
its points on the fundamental triangle other than `P` are simple, and its restrictions to the
exceptional lines are squarefree once the factor coming from `P` is removed: `F(X, Y, 0)` is
squarefree, and `F(X, 0, Z) = X^r H` with `H` squarefree. The last statements follow from a
squarefree criterion by intersection numbers,
`PlaneCurves.Projective.squarefree_of_forall_intersectionNumber_le_one`.

## Main definitions

* `PlaneCurves.Projective.IsExcellentPosition F`: `F` is in excellent position.
* `PlaneCurves.Projective.IsQuadraticTransformAt F P G`: `G` is a quadratic transformation of `F`
  centred at `P`, the proper transform of `F` after a change of coordinates moving `[0 : 0 : 1]`
  to `P` and putting `F` in excellent position.

## Main results

* `PlaneCurves.Projective.isExcellentPosition_smul_iff`: invariance under nonzero scalars.
* `PlaneCurves.Projective.IsExcellentPosition.fundamentalPoint_notMem`: `P'`, `P''` are not on
  `F`, so `PlaneCurves.Projective.IsExcellentPosition.mult_fundamentalPoint_eq_zero`.
* `PlaneCurves.Projective.IsExcellentPosition.not_X_dvd`: no exceptional line is a component.
* `PlaneCurves.Projective.IsExcellentPosition.isSimplePoint_of_mem_fundamentalTriangle`,
  `PlaneCurves.Projective.IsExcellentPosition.notMem_fundamentalTriangle_of_isMultiplePoint`:
  the points of `F` on the fundamental triangle other than `P` are simple.
* `PlaneCurves.Projective.IsExcellentPosition.squarefree_restrict_X_two`,
  `PlaneCurves.Projective.IsExcellentPosition.restrict_X_one_eq`,
  `PlaneCurves.Projective.IsExcellentPosition.restrict_X_zero_eq`: the squarefree restrictions
  to the exceptional lines.
* `PlaneCurves.Projective.IsExcellentPosition.ncard_zeroLocus_X_two`,
  `PlaneCurves.Projective.IsExcellentPosition.ncard_zeroLocus_X_diff`: `L` meets `F` in `n`
  points, `L'` and `L''` in `n - r` points other than `P`.
* `PlaneCurves.Projective.exists_isExcellentPosition`: Fulton's Lemma 1, for every point that is
  not terrible, in any characteristic;
  `PlaneCurves.Projective.exists_isExcellentPosition_of_charZero` is the book's
  form, for every point in characteristic zero.
* `PlaneCurves.Projective.exists_isQuadraticTransformAt`: quadratic transformations centred at a
  point that is not terrible exist; `PlaneCurves.Projective.IsQuadraticTransformAt.isHomogeneous`
  and `PlaneCurves.Projective.IsQuadraticTransformAt.irreducible` give their degree `2n - m_P(F)`
  and irreducibility.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.4
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {Q : ℙ k (Fin 3 → k)} {n : ℕ}

private theorem eval_rep_eq_zero_iff_mem (hF : F.IsHomogeneous n) :
    eval Q.rep F = 0 ↔ Q ∈ zeroLocus {F} := by
  rw [mem_zeroLocus_iff_eval_rep (by simpa using ⟨n, hF⟩)]
  simp

/-! ### Excellent position -/

/-- A plane curve `F` is in *excellent position* (Fulton, §7.4) if it is in good position and
every point `Q ≠ [0 : 0 : 1]` of `F` on an exceptional line `V(Xⱼ)` is not a fundamental point and
meets that line transversally, `I(Q, F ∩ Xⱼ) = 1`. For `j = 2` the condition `Q ≠ [0 : 0 : 1]`
is empty, since `[0 : 0 : 1]` is not on `V(Z)`. -/
def IsExcellentPosition (F : MvPolynomial (Fin 3) k) : Prop :=
  IsGoodPosition F ∧ ∀ j, ∀ Q ∈ zeroLocus {F, X j}, Q ≠ fundamentalPoint 2 →
    (∀ i, Q ≠ fundamentalPoint i) ∧ intersectionNumber Q F (X j) = 1

theorem isExcellentPosition_def :
    IsExcellentPosition F ↔ IsGoodPosition F ∧ ∀ j, ∀ Q ∈ zeroLocus {F, X j},
      Q ≠ fundamentalPoint 2 → (∀ i, Q ≠ fundamentalPoint i) ∧ intersectionNumber Q F (X j) = 1 :=
  Iff.rfl

theorem isExcellentPosition_smul_iff {c : k} (hc : c ≠ 0) :
    IsExcellentPosition (c • F) ↔ IsExcellentPosition F := by
  simp only [isExcellentPosition_def, isGoodPosition_smul_iff hc, Set.insert_eq, zeroLocus_union,
    zeroLocus_singleton_smul hc, intersectionNumber_smul_left hc]

theorem IsExcellentPosition.smul (h : IsExcellentPosition F) {c : k} (hc : c ≠ 0) :
    IsExcellentPosition (c • F) :=
  (isExcellentPosition_smul_iff hc).2 h

namespace IsExcellentPosition

theorem isGoodPosition (h : IsExcellentPosition F) : IsGoodPosition F :=
  h.1

/-- A curve in excellent position has no exceptional line as a component. -/
theorem not_X_dvd (h : IsExcellentPosition F) (j : Fin 3) : ¬ X j ∣ F :=
  h.1.not_X_dvd j

theorem ne_zero (h : IsExcellentPosition F) : F ≠ 0 :=
  h.1.ne_zero

/-- A point `Q ≠ [0 : 0 : 1]` of `F` on an exceptional line is not a fundamental point. -/
theorem ne_fundamentalPoint (h : IsExcellentPosition F) {j : Fin 3}
    (hQ : Q ∈ zeroLocus {F, X j}) (hQP : Q ≠ fundamentalPoint 2) (i : Fin 3) :
    Q ≠ fundamentalPoint i :=
  (h.2 j Q hQ hQP).1 i

/-- A point `Q ≠ [0 : 0 : 1]` of `F` on an exceptional line `V(Xⱼ)` has `I(Q, F ∩ Xⱼ) = 1`. -/
theorem intersectionNumber_eq_one (h : IsExcellentPosition F) {j : Fin 3}
    (hQ : Q ∈ zeroLocus {F, X j}) (hQP : Q ≠ fundamentalPoint 2) :
    intersectionNumber Q F (X j) = 1 :=
  (h.2 j Q hQ hQP).2

/-- The points of `F` on `V(Z)` meet it transversally. -/
theorem intersectionNumber_X_two_eq_one (h : IsExcellentPosition F)
    (hQ : Q ∈ zeroLocus {F, X 2}) : intersectionNumber Q F (X 2) = 1 :=
  h.intersectionNumber_eq_one hQ fun hQP ↦ by
    rw [hQP, mem_zeroLocus_pair_iff, fundamentalPoint_mem_zeroLocus_X_iff] at hQ
    exact hQ.2 rfl

/-- **`P'` and `P''` are not on a curve in excellent position.** -/
theorem fundamentalPoint_notMem (h : IsExcellentPosition F) {i : Fin 3} (hi : i ≠ 2) :
    fundamentalPoint i ∉ zeroLocus {F} := fun hF ↦ by
  have hQ : fundamentalPoint i ∈ zeroLocus {F, X 2} :=
    mem_zeroLocus_pair_iff.2 ⟨hF, fundamentalPoint_mem_zeroLocus_X_iff.2 hi⟩
  exact h.ne_fundamentalPoint hQ (by simpa using hi) i rfl

/-- A curve in excellent position does not vanish at `eᵢ` for `i ≠ 2`: `F(1, 0, 0) ≠ 0` and
`F(0, 1, 0) ≠ 0`. -/
theorem eval_single_ne_zero (h : IsExcellentPosition F) (hF : F.IsHomogeneous n) {i : Fin 3}
    (hi : i ≠ 2) : eval (Pi.single i 1) F ≠ 0 := fun h0 ↦ by
  refine h.fundamentalPoint_notMem hi ?_
  rw [fundamentalPoint_def, mk_mem_zeroLocus_iff (by simpa using ⟨n, hF⟩)]
  simpa using h0

/-- The multiplicity of a curve in excellent position at `P'` and `P''` is zero. -/
theorem mult_fundamentalPoint_eq_zero (h : IsExcellentPosition F) (hF : F.IsHomogeneous n)
    {i : Fin 3} (hi : i ≠ 2) : mult F (fundamentalPoint i) = 0 :=
  (mult_eq_zero_iff hF).2 (h.fundamentalPoint_notMem hi)

/-- The lines `V(X)` and `V(Y)` are not tangent to `F` at `P = [0 : 0 : 1]`, so they meet `F`
there with intersection number `m_P(F)`. -/
theorem intersectionNumber_fundamentalPoint_two (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) {j : Fin 3} (hj : j ≠ 2) :
    intersectionNumber (fundamentalPoint 2) F (X j) = mult F (fundamentalPoint 2) := by
  refine (intersectionNumber_eq_mult_iff_not_isTangentAt hF h.ne_zero (isHomogeneous_X k j)
    (X_ne_zero j) ?_).2 (isGoodPosition_def.1 h.1 2 j hj.symm)
  rw [eval_X, ← mem_zeroLocus_X_iff]
  exact fundamentalPoint_mem_zeroLocus_X_iff.2 hj.symm

/-- An intersection number of `F` with `V(Xⱼ)` that is one at the common points is at most one
everywhere. -/
private theorem intersectionNumber_le_one_of (hF : F.IsHomogeneous n) {j : Fin 3}
    (H : Q ∈ zeroLocus {F, X j} → intersectionNumber Q F (X j) = 1) :
    intersectionNumber Q F (X j) ≤ 1 := by
  by_cases hQ : Q ∈ zeroLocus {F, X j}
  · exact (H hQ).le
  · rw [(intersectionNumber_eq_zero_iff hF (isHomogeneous_X k j)).2]
    · exact zero_le_one
    · rw [mem_zeroLocus_pair_iff, ← eval_rep_eq_zero_iff_mem hF, mem_zeroLocus_X_iff] at hQ
      by_contra! h'
      exact hQ ⟨h'.1, by simpa using h'.2⟩

/-- Every intersection number of `F` with an exceptional line `V(Xⱼ)` away from `[0 : 0 : 1]` is
at most one. -/
theorem intersectionNumber_le_one (h : IsExcellentPosition F) (hF : F.IsHomogeneous n)
    (j : Fin 3) (hQP : Q ≠ fundamentalPoint 2) : intersectionNumber Q F (X j) ≤ 1 :=
  intersectionNumber_le_one_of hF fun hQ ↦ h.intersectionNumber_eq_one hQ hQP

/-- Every intersection number of `F` with `V(Z)` is at most one. -/
theorem intersectionNumber_X_two_le_one (h : IsExcellentPosition F) (hF : F.IsHomogeneous n)
    (Q : ℙ k (Fin 3 → k)) : intersectionNumber Q F (X 2) ≤ 1 :=
  intersectionNumber_le_one_of hF h.intersectionNumber_X_two_eq_one

/-- **The points of `F` on the fundamental triangle other than `P` are simple**: such a point
meets an exceptional line transversally. -/
theorem isSimplePoint_of_mem_fundamentalTriangle (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) (hQ : Q ∈ zeroLocus {F}) (hQT : Q ∈ fundamentalTriangle)
    (hQP : Q ≠ fundamentalPoint 2) : IsSimplePoint F Q := by
  rw [fundamentalTriangle_eq_iUnion, Set.mem_iUnion] at hQT
  obtain ⟨j, hj⟩ := hQT
  have hI := h.intersectionNumber_eq_one (mem_zeroLocus_pair_iff.2 ⟨hQ, hj⟩) hQP
  rw [mem_zeroLocus_X_iff] at hj
  exact ((intersectionNumber_eq_one_iff hF (isHomogeneous_X k j) (X_ne_zero j)
    (by simpa using hj)).1 hI).1

/-- The multiple points of a curve in excellent position other than `P` are off the fundamental
triangle. -/
theorem notMem_fundamentalTriangle_of_isMultiplePoint (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) (hQ : IsMultiplePoint F Q) (hQP : Q ≠ fundamentalPoint 2) :
    Q ∉ fundamentalTriangle := fun hQT ↦ by
  have hQF : Q ∈ zeroLocus {F} :=
    (mult_pos_iff hF).1 (lt_of_lt_of_le (by norm_num) (isMultiplePoint_def.1 hQ))
  have hs := isSimplePoint_def.1 (h.isSimplePoint_of_mem_fundamentalTriangle hF hQF hQT hQP)
  have := isMultiplePoint_def.1 hQ
  rw [hs] at this
  exact absurd this (by decide)

/-! ### The restrictions to the exceptional lines -/

/-- The restriction of a curve in excellent position to an exceptional line `V(Xⱼ)` does not
vanish at the fundamental point `[eₗ]` on that line, for `l ≠ 2`. -/
private theorem eval_single_bind₁_ne_zero (h : IsExcellentPosition F) (hF : F.IsHomogeneous n)
    {j l : Fin 3} (hl : l ≠ 2) (hjl : j ≠ l) :
    eval (Pi.single l 1) (bind₁ (Function.update X j 0) F) ≠ 0 := by
  rw [eval_bind₁_update_X_zero, Function.update_eq_self_iff.2 (by simp [hjl])]
  exact h.eval_single_ne_zero hF hl

private theorem eval_single_X {i l : Fin 3} (hil : i ≠ l) :
    eval (Pi.single l (1 : k)) (X i : MvPolynomial (Fin 3) k) = 0 := by
  simp [hil]

/-- **The restriction to `V(Z)`.** For a curve in excellent position over an algebraically
closed field, the binary form `F(X, Y, 0)` is squarefree and divisible by neither `X` nor `Y`. -/
theorem squarefree_restrict_X_two [IsAlgClosed k] (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) :
    Squarefree (aeval (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) F) ∧
      ¬ X 0 ∣ aeval (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) F ∧
      ¬ X 1 ∣ aeval (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) F := by
  have hv : (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) = Function.update X 2 0 := by
    funext i
    fin_cases i <;> rfl
  rw [hv, aeval_eq_bind₁]
  have hG := hF.bind₁_update_X_zero 2
  have hG0 : bind₁ (Function.update X 2 0) F ≠ 0 :=
    fun h0 ↦ h.not_X_dvd 2 (X_dvd_of_bind₁_update_X_zero_eq_zero h0)
  refine ⟨squarefree_of_forall_intersectionNumber_le_one hG hG0 (isHomogeneous_X k 2)
    one_ne_zero fun Q ↦ ?_, fun hd ↦ ?_, fun hd ↦ ?_⟩
  · rw [intersectionNumber_bind₁_update_X_zero]
    exact h.intersectionNumber_X_two_le_one hF Q
  · obtain ⟨A, hA⟩ := hd
    refine eval_single_bind₁_ne_zero h hF (j := 2) (l := 1) (by decide) (by decide) ?_
    rw [hA, eval_mul, eval_single_X (by decide), zero_mul]
  · obtain ⟨A, hA⟩ := hd
    refine eval_single_bind₁_ne_zero h hF (j := 2) (l := 0) (by decide) (by decide) ?_
    rw [hA, eval_mul, eval_single_X (by decide), zero_mul]

/-- **The restriction to `V(Xⱼ)`, `j ≠ 2`.** Let `l` be the third index, so that `[0 : 0 : 1]` and
`[eₗ]` are the fundamental points on `V(Xⱼ)`. For a curve in excellent position over an
algebraically closed field, with `r = m_{[0:0:1]}(F)`, the restriction of `F` to `Xⱼ = 0` is
`X_l^r H` with `H` squarefree and divisible by neither `X_l` nor `Z`. -/
theorem exists_restrict_X_eq [IsAlgClosed k] (h : IsExcellentPosition F) (hF : F.IsHomogeneous n)
    {j l : Fin 3} (hj : j ≠ 2) (hl : l ≠ 2) (hjl : j ≠ l) :
    ∃ H, bind₁ (Function.update X j 0) F = X l ^ (mult F (fundamentalPoint 2)).toNat * H ∧
      Squarefree H ∧ ¬ X l ∣ H ∧ ¬ X 2 ∣ H := by
  set r := (mult F (fundamentalPoint 2)).toNat with hr
  set P : ℙ k (Fin 3 → k) := fundamentalPoint 2
  have hG0 : bind₁ (Function.update X j 0) F ≠ 0 :=
    fun h0 ↦ h.not_X_dvd j (X_dvd_of_bind₁_update_X_zero_eq_zero h0)
  obtain ⟨H, hGH⟩ := pow_dvd_of_le_multiplicity (mult_fundamentalPoint_le_multiplicity_bind₁ hF
    (Ne.symm hj) (Ne.symm hl) hjl (h.not_X_dvd j))
  have hH0 : H ≠ 0 := right_ne_zero_of_mul (hGH ▸ hG0)
  have hHh : H.IsHomogeneous H.totalDegree := by
    have hG := hF.bind₁_update_X_zero j
    rw [hGH, mul_comm] at hG
    exact hG.of_mul_left (pow_ne_zero _ (X_ne_zero _))
  have hXr : (X l ^ r : MvPolynomial (Fin 3) k).IsHomogeneous r := by
    simpa using (isHomogeneous_X k l).pow r
  have hXj := isHomogeneous_X k j
  have hsplit (Q : ℙ k (Fin 3 → k)) : intersectionNumber Q F (X j) =
      intersectionNumber Q (X l ^ r) (X j) + intersectionNumber Q H (X j) := by
    rw [← intersectionNumber_bind₁_update_X_zero, hGH, intersectionNumber_mul_left hXr hHh hXj]
  have hPl : eval P.rep (X l) = 0 := by
    rw [eval_X, ← mem_zeroLocus_X_iff]
    exact fundamentalPoint_mem_zeroLocus_X_iff.2 (Ne.symm hl)
  have hPj : eval P.rep (X j) = 0 := by
    rw [eval_X, ← mem_zeroLocus_X_iff]
    exact fundamentalPoint_mem_zeroLocus_X_iff.2 (Ne.symm hj)
  -- At `P`, `X_l^r` already accounts for all of `I(P, F ∩ Xⱼ) = r`, so `H(P) ≠ 0`.
  have hHP : intersectionNumber P H (X j) = 0 := by
    have h1 : (r : ℕ∞) ≤ intersectionNumber P (X l ^ r) (X j) := by
      have := mul_mult_le_intersectionNumber (P := P) hXr hXj
      rwa [mult_pow, mult_eq_one_of_isHomogeneous_one (isHomogeneous_X k l) (X_ne_zero l) hPl,
        mult_eq_one_of_isHomogeneous_one hXj (X_ne_zero j) hPj, nsmul_eq_mul, mul_one,
        mul_one] at this
    have h2 := hsplit P
    rw [h.intersectionNumber_fundamentalPoint_two hF hj,
      ← ENat.natCast_toNat (mult_eq_top_iff.not.2 h.ne_zero), ← hr] at h2
    have h3 : (r : ℕ∞) + intersectionNumber P H (X j) ≤ r + 0 := by
      calc (r : ℕ∞) + intersectionNumber P H (X j)
          ≤ intersectionNumber P (X l ^ r) (X j) + intersectionNumber P H (X j) := by gcongr
        _ = r + 0 := by rw [← h2, add_zero]
    exact nonpos_iff_eq_zero.1 ((WithTop.add_le_add_iff_left (ENat.natCast_ne_top r)).1 h3)
  have hHPne : eval P.rep H ≠ 0 :=
    ((intersectionNumber_eq_zero_iff hHh hXj).1 hHP).resolve_right (not_not.2 hPj)
  refine ⟨H, hGH, squarefree_of_forall_intersectionNumber_le_one hHh hH0 hXj one_ne_zero
    fun Q ↦ ?_, fun ⟨A, hA⟩ ↦ hHPne (by rw [hA, eval_mul, hPl, zero_mul]), fun ⟨A, hA⟩ ↦ ?_⟩
  · by_cases hQP : Q = P
    · rw [hQP, hHP]
      exact zero_le_one
    · exact le_add_self.trans ((hsplit Q).symm.le.trans (h.intersectionNumber_le_one hF j hQP))
  · refine eval_single_bind₁_ne_zero h hF hl hjl ?_
    rw [hGH, eval_mul, hA, eval_mul, eval_single_X (Ne.symm hl), zero_mul, mul_zero]

/-- **The restriction to `V(Y)`.** For a curve in excellent position over an algebraically closed
field, `F(X, 0, Z) = X^r H` with `r = m_{[0:0:1]}(F)` and `H` squarefree and divisible by neither
`X` nor `Z`. -/
theorem restrict_X_one_eq [IsAlgClosed k] (h : IsExcellentPosition F) (hF : F.IsHomogeneous n) :
    ∃ H, aeval (![X 0, 0, X 2] : Fin 3 → MvPolynomial (Fin 3) k) F =
        X 0 ^ (mult F (fundamentalPoint 2)).toNat * H ∧ Squarefree H ∧ ¬ X 0 ∣ H ∧ ¬ X 2 ∣ H := by
  rw [show (![X 0, 0, X 2] : Fin 3 → MvPolynomial (Fin 3) k) = Function.update X 1 0 by
    funext i; fin_cases i <;> rfl, aeval_eq_bind₁]
  exact h.exists_restrict_X_eq hF (by decide) (by decide) (by decide)

/-- **The restriction to `V(X)`.** For a curve in excellent position over an algebraically closed
field, `F(0, Y, Z) = Y^r H` with `r = m_{[0:0:1]}(F)` and `H` squarefree and divisible by neither
`Y` nor `Z`. -/
theorem restrict_X_zero_eq [IsAlgClosed k] (h : IsExcellentPosition F) (hF : F.IsHomogeneous n) :
    ∃ H, aeval (![0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) k) F =
        X 1 ^ (mult F (fundamentalPoint 2)).toNat * H ∧ Squarefree H ∧ ¬ X 1 ∣ H ∧ ¬ X 2 ∣ H := by
  rw [show (![0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) k) = Function.update X 0 0 by
    funext i; fin_cases i <;> rfl, aeval_eq_bind₁]
  exact h.exists_restrict_X_eq hF (by decide) (by decide) (by decide)

/-! ### The counts -/

/-- **`L` meets `F` in `n` points.** Over an algebraically closed field, a curve of degree `n` in
excellent position meets `V(Z)` in exactly `n` points. -/
theorem ncard_zeroLocus_X_two [IsAlgClosed k] (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) : (zeroLocus {F, X 2}).ncard = n := by
  have hP' : fundamentalPoint (k := k) 1 ∉ zeroLocus {F} := h.fundamentalPoint_notMem (by decide)
  have h0 : intersectionNumber (fundamentalPoint 1) F (X 2) = ((0 : ℕ) : ℕ∞) := by
    rw [Nat.cast_zero, intersectionNumber_eq_zero_iff hF (isHomogeneous_X k 2)]
    exact Or.inl (by rwa [Ne, eval_rep_eq_zero_iff_mem hF])
  have := ncard_zeroLocus_pair_diff hF (isHomogeneous_X k 2) (X_ne_zero 2) (h.not_X_dvd 2) h0
    fun Q hQ _ ↦ h.intersectionNumber_X_two_eq_one hQ
  rwa [Set.sdiff_singleton_eq_self fun hQ ↦ hP' (mem_zeroLocus_pair_iff.1 hQ).1,
    Nat.sub_zero] at this

/-- **`L'` and `L''` meet `F` in `n - r` further points.** Over an algebraically closed field, a
curve of degree `n` in excellent position meets `V(Xⱼ)`, `j ≠ 2`, in exactly `n - r` points other
than `[0 : 0 : 1]`, with `r = m_{[0:0:1]}(F)`. -/
theorem ncard_zeroLocus_X_diff [IsAlgClosed k] (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) {j : Fin 3} (hj : j ≠ 2) :
    (zeroLocus {F, X j} \ {fundamentalPoint 2}).ncard =
      n - (mult F (fundamentalPoint 2)).toNat :=
  ncard_zeroLocus_pair_diff hF (isHomogeneous_X k j) (X_ne_zero j) (h.not_X_dvd j)
    (by rw [h.intersectionNumber_fundamentalPoint_two hF hj,
      ENat.natCast_toNat (mult_eq_top_iff.not.2 h.ne_zero)])
    fun Q hQ hQP ↦ h.intersectionNumber_eq_one hQ hQP

end IsExcellentPosition

/-! ### Existence of excellent position -/

section Existence

/-- A line `L` that meets an irreducible curve `F` with intersection number one at each common
point other than `P` is not a component of `F`: otherwise every point of `F` would have an
infinite intersection number. -/
private theorem isRelPrime_of_intersectionNumber_eq_one [IsAlgClosed k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) {L : MvPolynomial (Fin 3) k} {d : ℕ} (hL : L.IsHomogeneous d)
    {P : ℙ k (Fin 3 → k)} (h : ∀ Q ∈ zeroLocus {F, L}, Q ≠ P → intersectionNumber Q F L = 1) :
    IsRelPrime F L := by
  rw [hirr.isRelPrime_iff_not_dvd]
  intro hFL
  have hn : n ≠ 0 := hF.degree_ne_zero_of_irreducible hirr
  obtain ⟨Q, hQF, hQP⟩ :=
    ((zeroLocus_singleton_infinite (n := 2) le_rfl hF hn).sdiff (Set.finite_singleton P)).nonempty
  have hQF' := (eval_rep_eq_zero_iff_mem hF).2 hQF
  have hQL : Q ∈ zeroLocus {L} := by
    obtain ⟨g, rfl⟩ := hFL
    exact (eval_rep_eq_zero_iff_mem hL).1 (by rw [map_mul, hQF', zero_mul])
  have htop : intersectionNumber Q F L = ⊤ := by
    by_contra hne
    exact (intersectionNumber_ne_top_iff hF hL).1 hne F hirr dvd_rfl hFL hQF'
  rw [h Q (mem_zeroLocus_pair_iff.2 ⟨hQF, hQL⟩) hQP] at htop
  exact ENat.one_ne_top htop

/-- **The excellent-position conditions in new coordinates.** Let `M` carry the linear forms
`ℓⱼ = ∑ i, a j i * X i` to the coordinates `X j` and send `[0 : 0 : 1]` to `P`. Suppose that every
point `Q ≠ P` of `F` on `ℓⱼ` has `I(Q, F ∩ ℓⱼ) = 1`, that `I(P, F ∩ ℓⱼ) = m_P(F)` for `j ≠ 2`,
and that no point of `F` on `ℓ₀` or `ℓ₁` is on `ℓ₂`. Then `F(M X)` is in excellent position. -/
private theorem isExcellentPosition_linearSubst_of_lines [IsAlgClosed k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) {M : Matrix (Fin 3) (Fin 3) k} (hM : Function.Injective M.mulVecLin)
    {a : Fin 3 → Fin 3 → k} (hMa : ∀ j, linearSubst M (∑ i, C (a j i) * X i) = X j)
    {P : ℙ k (Fin 3 → k)} (hTP : map M.mulVecLin hM (fundamentalPoint 2) = P)
    (hI : ∀ j, ∀ Q ∈ zeroLocus {F, ∑ i, C (a j i) * X i}, Q ≠ P →
      intersectionNumber Q F (∑ i, C (a j i) * X i) = 1)
    (hIP : ∀ j ≠ 2, intersectionNumber P F (∑ i, C (a j i) * X i) = mult F P)
    (h2 : ∀ j ≠ 2, ∀ Q ∈ zeroLocus {F, ∑ i, C (a j i) * X i},
      Q ∉ zeroLocus {∑ i, C (a 2 i) * X i}) :
    IsExcellentPosition (linearSubst M F) := by
  have hdet : IsUnit M.det := Matrix.isUnit_det_of_mulVecLin_injective hM
  set T := map M.mulVecLin hM
  set G := linearSubst M F
  have hG : G.IsHomogeneous n := hF.linearSubst M
  have hG0 : G ≠ 0 := ((irreducible_linearSubst_iff hdet).2 hirr).ne_zero
  have hzero (H : MvPolynomial (Fin 3) k) (Q : ℙ k (Fin 3 → k)) :
      Q ∈ zeroLocus {linearSubst M H} ↔ T Q ∈ zeroLocus {H} := by
    rw [← Set.image_singleton, zeroLocus_linearSubst]
    rfl
  have hmemX {Q : ℙ k (Fin 3 → k)} {j : Fin 3} :
      Q ∈ zeroLocus {X j} ↔ T Q ∈ zeroLocus {∑ i, C (a j i) * X i} := by
    rw [← hMa j, hzero]
  have hIX (Q : ℙ k (Fin 3 → k)) (j : Fin 3) :
      intersectionNumber Q G (X j) = intersectionNumber (T Q) F (∑ i, C (a j i) * X i) := by
    rw [← hMa j]
    exact intersectionNumber_linearSubst hF (isHomogeneous_sum_C_mul_X _)
      (Matrix.nonsingInvUnit M hdet) Q
  -- `T` sends `[1 : 0 : 0]` and `[0 : 1 : 0]` off `F`.
  have hfund {i : Fin 3} (hi : i ≠ 2) : T (fundamentalPoint i) ∉ zeroLocus {F} := by
    intro hiF
    have hℓ {j : Fin 3} (hj : j ≠ i) : T (fundamentalPoint i) ∈ zeroLocus {∑ l, C (a j l) * X l} :=
      hmemX.1 (fundamentalPoint_mem_zeroLocus_X_iff.2 hj.symm)
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp at hi ⊢
    · exact h2 1 (by decide) _ (mem_zeroLocus_pair_iff.2 ⟨hiF, hℓ (by decide)⟩) (hℓ hi.symm)
    · exact h2 0 (by decide) _ (mem_zeroLocus_pair_iff.2 ⟨hiF, hℓ (by decide)⟩) (hℓ hi.symm)
  refine ⟨?_, fun j Q hQ hQP ↦ ?_⟩
  · -- Good position: at `[0 : 0 : 1]` the first two lines are not tangent.
    rw [isGoodPosition_def]
    intro i j hij ht
    by_cases hi : i = 2
    · subst hi
      rw [isTangentAt_iff_mult_lt_intersectionNumber hG hG0 (isHomogeneous_X k j) (X_ne_zero j)
        (isTangentAt_def.1 ht).2.2.1, mult_linearSubst hF hM, hIX] at ht
      change mult F (T _) < _ at ht
      rw [hTP, hIP j hij.symm] at ht
      exact lt_irrefl _ ht
    · exact hfund hi ((hzero F _).1 ((eval_rep_eq_zero_iff_mem hG).1 ht.eval_rep_eq_zero))
  · rw [mem_zeroLocus_pair_iff, hzero, hmemX] at hQ
    have hTQP : T Q ≠ P := fun h ↦ hQP (map_injective _ hM (h.trans hTP.symm))
    refine ⟨fun i hi ↦ ?_, ?_⟩
    · subst hi
      by_cases hi2 : i = 2
      · exact hQP (hi2 ▸ rfl)
      · exact hfund hi2 hQ.1
    · rw [hIX]
      exact hI j _ (mem_zeroLocus_pair_iff.2 hQ) hTQP

/-- **Existence of excellent position, avoiding a finite set** (Fulton, §7.4, Lemma 1, and
Problem 7.13 (a)). Let `k` be algebraically closed, `F` an irreducible form of degree `n`, `P` a
point of `ℙ²`, on `F` or not, that is not terrible for `F`, and `S` a finite set of points not
containing `P`. Then there is a projective change of coordinates `T`, given by an invertible
matrix `M`, with `T([0 : 0 : 1]) = P`, `F^T = F(M X)` in excellent position, and `T⁻¹(S)` off
the fundamental triangle `V(XYZ)`.

The lines `T(V(X))` and `T(V(Y))` are two lines through `P` that meet `F` transversally in
`n - m_P(F)` further points, are not tangent at `P`, and miss `S`; `T(V(Z))` is a line through
no point of `F` on them, and through neither `P` nor a point of `S`, that meets `F`
transversally in `n` points. -/
theorem exists_isExcellentPosition_avoiding [IsAlgClosed k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) {P : ℙ k (Fin 3 → k)} (hP : ¬ IsTerriblePoint F P.rep)
    {S : Set (ℙ k (Fin 3 → k))} (hS : S.Finite) (hPS : P ∉ S) :
    ∃ (M : Matrix (Fin 3) (Fin 3) k) (hM : Function.Injective M.mulVecLin),
      map M.mulVecLin hM (fundamentalPoint 2) = P ∧ IsExcellentPosition (linearSubst M F) ∧
        ∀ R, map M.mulVecLin hM R ∈ S → R ∉ fundamentalTriangle := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : ℕ, mult F P = r :=
    (ENat.ne_top_iff_exists.1 (mult_eq_top_iff.not.2 hirr.ne_zero)).imp fun _ h ↦ h.symm
  have hℓ (a : Fin 3 → k) := isHomogeneous_sum_C_mul_X (σ := Fin 3) (R := k) a
  -- Two distinct lines through `P` meeting `F` as part (d) of the terrible-point theorem says,
  -- and through no point of `S`.
  have hgood := Filter.eventually_cofinite.1
    (eventually_cofinite_ncard_zeroLocus_pair_diff_eq_of_not_isTerriblePoint hF hirr hP hr)
  obtain ⟨c₀, hc₀, c₁, hc₁, h01⟩ := ((infinite_setOf_eval_sum_C_mul_X_eq_zero P).sdiff
    (hgood.union (finite_setOf_eval_sum_C_mul_X_eq_zero_of_finite hS P))).nontrivial
  simp only [Set.mem_sdiff, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_and,
    not_exists] at hc₀ hc₁
  obtain ⟨-, hI₀, hIP₀⟩ := hc₀.2.1 hc₀.1
  obtain ⟨-, hI₁, hIP₁⟩ := hc₁.2.1 hc₁.1
  have hS₀ (Q) (hQ : Q ∈ S) := hc₀.2.2 hc₀.1 Q hQ (ne_of_mem_of_not_mem hQ hPS)
  have hS₁ (Q) (hQ : Q ∈ S) := hc₁.2.2 hc₁.1 Q hQ (ne_of_mem_of_not_mem hQ hPS)
  have h0 : c₀.rep ⬝ᵥ P.rep = 0 := by rw [← eval_sum_C_mul_X]; exact hc₀.1
  have h1 : c₁.rep ⬝ᵥ P.rep = 0 := by rw [← eval_sum_C_mul_X]; exact hc₁.1
  -- A third line, through no point of `F` on the first two, and not through `P` or `S`.
  set S' := zeroLocus {F, ∑ i, C (c₀.rep i) * X i} ∪ zeroLocus {F, ∑ i, C (c₁.rep i) * X i} ∪
    {P} ∪ S
  have hS' : S'.Finite :=
    (((finite_zeroLocus_pair_of_isRelPrime hF (hℓ _)
      (isRelPrime_of_intersectionNumber_eq_one hF hirr (hℓ _) hI₀)).union
     (finite_zeroLocus_pair_of_isRelPrime hF (hℓ _)
      (isRelPrime_of_intersectionNumber_eq_one hF hirr (hℓ _) hI₁))).union
     (Set.finite_singleton P)).union hS
  obtain ⟨c₂, hc₂, -, hI₂⟩ := exists_ncard_zeroLocus_pair_sum_C_mul_X_eq hF hirr hS'
  have h2 : c₂.rep ⬝ᵥ P.rep ≠ 0 := by
    rw [← eval_sum_C_mul_X]
    exact hc₂ P (by simp [S'])
  -- The three lines are independent, so a change of coordinates moves them to `V(Xⱼ)`.
  obtain ⟨M, hM, hMa⟩ := exists_linearSubst_sum_C_mul_X_eq_X
    (linearIndependent_rep_of_dotProduct h01 h0 h1 h2) Function.injective_id
  have hTP : map M.mulVecLin hM (fundamentalPoint 2) = P := by
    rw [fundamentalPoint_def]
    refine map_mk_single_eq_of_linearSubst_sum_C_mul_X_eq_X hM hMa fun j hj ↦ ?_
    fin_cases j
    exacts [h0, h1, absurd rfl hj]
  refine ⟨M, hM, hTP, isExcellentPosition_linearSubst_of_lines hF hirr hM hMa hTP
    (fun j ↦ ?_) (fun j hj ↦ ?_) (fun j hj Q hQ hQ2 ↦ hc₂ Q ?_ ?_), fun R hR hRT ↦ ?_⟩
  · fin_cases j
    exacts [hI₀, hI₁, fun Q hQ _ ↦ hI₂ Q hQ]
  · fin_cases j
    exacts [hIP₀.trans hr.symm, hIP₁.trans hr.symm, absurd rfl hj]
  · fin_cases j
    exacts [Or.inl (Or.inl (Or.inl hQ)), Or.inl (Or.inl (Or.inr hQ)), absurd rfl hj]
  · rw [eval_sum_C_mul_X]
    exact (mem_zeroLocus_singleton_sum_C_mul_X_iff _ _).1 hQ2
  · -- A point of `T⁻¹(S)` on `V(Xⱼ)` would put a point of `S` on the `j`-th line.
    have hoff (j : Fin 3) (a : Fin 3 → k) (ha : linearSubst M (∑ i, C (a i) * X i) = X j)
        (hRa : eval (map M.mulVecLin hM R).rep (∑ i, C (a i) * X i) ≠ 0) : R.rep j ≠ 0 := by
      intro hj
      rw [← mem_zeroLocus_X_iff, ← ha, ← Set.image_singleton, zeroLocus_linearSubst M hM,
        Set.mem_preimage, mem_zeroLocus_singleton_sum_C_mul_X_iff, ← eval_sum_C_mul_X] at hj
      exact hRa hj
    obtain ⟨j, hj⟩ := mem_fundamentalTriangle_iff.1 hRT
    refine hoff j _ (hMa j) ?_ hj
    fin_cases j
    exacts [hS₀ _ hR, hS₁ _ hR, hc₂ _ (Or.inr hR)]

/-- **Existence of excellent position** (Fulton, §7.4, Lemma 1). Let `k` be algebraically closed,
`F` an irreducible form of degree `n`, and `P` a point of `ℙ²`, on `F` or not, that is not
terrible for `F`. Then there is a projective change of coordinates `T`, given by an invertible
matrix `M`, with `T([0 : 0 : 1]) = P` and `F^T = F(M X)` in excellent position. -/
theorem exists_isExcellentPosition [IsAlgClosed k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) {P : ℙ k (Fin 3 → k)} (hP : ¬ IsTerriblePoint F P.rep) :
    ∃ (M : Matrix (Fin 3) (Fin 3) k) (hM : Function.Injective M.mulVecLin),
      map M.mulVecLin hM (fundamentalPoint 2) = P ∧ IsExcellentPosition (linearSubst M F) :=
  let ⟨M, hM, hTP, hE, _⟩ :=
    exists_isExcellentPosition_avoiding hF hirr hP Set.finite_empty (Set.notMem_empty P)
  ⟨M, hM, hTP, hE⟩

/-- **Existence of excellent position in characteristic zero** (Fulton, §7.4, Lemma 1). Over an
algebraically closed field of characteristic zero, every point `P` of `ℙ²` can be moved to
`[0 : 0 : 1]` by a projective change of coordinates that puts an irreducible curve in excellent
position, since no point is terrible. -/
theorem exists_isExcellentPosition_of_charZero [IsAlgClosed k] [CharZero k]
    (hF : F.IsHomogeneous n) (hirr : Irreducible F) (P : ℙ k (Fin 3 → k)) :
    ∃ (M : Matrix (Fin 3) (Fin 3) k) (hM : Function.Injective M.mulVecLin),
      map M.mulVecLin hM (fundamentalPoint 2) = P ∧ IsExcellentPosition (linearSubst M F) :=
  exists_isExcellentPosition hF hirr (not_isTerriblePoint hF hirr P.rep_ne_zero)

end Existence

/-! ### Quadratic transformations centred at a point -/

/-- `G` is *a quadratic transformation of `F` centred at `P`* (Fulton, §7.4): there is a
projective change of coordinates `T`, given by an invertible matrix `M`, with
`T([0 : 0 : 1]) = P`, `F^T = F(M X)` in excellent position, and `G` the proper transform of
`F^T`. -/
def IsQuadraticTransformAt (F : MvPolynomial (Fin 3) k) (P : ℙ k (Fin 3 → k))
    (G : MvPolynomial (Fin 3) k) : Prop :=
  ∃ (M : Matrix (Fin 3) (Fin 3) k) (hM : Function.Injective M.mulVecLin),
    map M.mulVecLin hM (fundamentalPoint 2) = P ∧ IsExcellentPosition (linearSubst M F) ∧
      G = properTransform (linearSubst M F)

theorem isQuadraticTransformAt_def {P : ℙ k (Fin 3 → k)} {G : MvPolynomial (Fin 3) k} :
    IsQuadraticTransformAt F P G ↔
      ∃ (M : Matrix (Fin 3) (Fin 3) k) (hM : Function.Injective M.mulVecLin),
        map M.mulVecLin hM (fundamentalPoint 2) = P ∧ IsExcellentPosition (linearSubst M F) ∧
          G = properTransform (linearSubst M F) :=
  Iff.rfl

/-- The proper transform of a curve in excellent position is a quadratic transformation of it
centred at `[0 : 0 : 1]`. -/
theorem IsExcellentPosition.isQuadraticTransformAt (h : IsExcellentPosition F) :
    IsQuadraticTransformAt F (fundamentalPoint 2) (properTransform F) := by
  refine ⟨1, fun x y hxy ↦ by simpa using hxy, ?_, by rwa [linearSubst_one], by
    rw [linearSubst_one]; rfl⟩
  simp [fundamentalPoint_def, map_mk]

namespace IsQuadraticTransformAt

variable {P : ℙ k (Fin 3 → k)} {G : MvPolynomial (Fin 3) k}

/-- A quadratic transformation of a form `F` of degree `n` centred at `P` is a form of degree
`2n - r`, where `r = m_P(F)`. -/
theorem isHomogeneous (h : IsQuadraticTransformAt F P G) (hF : F.IsHomogeneous n) :
    G.IsHomogeneous (2 * n - (mult F P).toNat) := by
  obtain ⟨M, hM, hP, hE, rfl⟩ := h
  have hG := hF.linearSubst M
  convert hG.properTransform using 1
  rw [Fin.sum_univ_three, hE.mult_fundamentalPoint_eq_zero hG (by decide),
    hE.mult_fundamentalPoint_eq_zero hG (by decide), mult_linearSubst hF hM, hP]
  simp

/-- A quadratic transformation of an irreducible form is irreducible. -/
theorem irreducible (h : IsQuadraticTransformAt F P G) (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) : Irreducible G := by
  obtain ⟨M, hM, -, hE, rfl⟩ := h
  exact irreducible_properTransform (hF.linearSubst M)
    ((irreducible_linearSubst_iff (Matrix.isUnit_det_of_mulVecLin_injective hM)).2 hirr)
    hE.not_X_dvd

end IsQuadraticTransformAt

/-- **Existence of quadratic transformations.** Over an algebraically closed field, an
irreducible curve `F` has a quadratic transformation centred at every point `P` that is not
terrible for `F`. -/
theorem exists_isQuadraticTransformAt [IsAlgClosed k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) {P : ℙ k (Fin 3 → k)} (hP : ¬ IsTerriblePoint F P.rep) :
    ∃ G, IsQuadraticTransformAt F P G :=
  let ⟨M, hM, hTP, hE⟩ := exists_isExcellentPosition hF hirr hP
  ⟨_, M, hM, hTP, hE, rfl⟩

/-- **Existence of quadratic transformations, avoiding a finite set** (Fulton, Problem 7.13 (a)).
Over an algebraically closed field, an irreducible curve `F` has a quadratic transformation
centred at every point `P` that is not terrible for `F`, by a change of coordinates `T` that keeps
a given finite set `S ∌ P` off the fundamental triangle: `T⁻¹(S) ∩ V(XYZ) = ∅`. -/
theorem exists_isQuadraticTransformAt_avoiding [IsAlgClosed k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) {P : ℙ k (Fin 3 → k)} (hP : ¬ IsTerriblePoint F P.rep)
    {S : Set (ℙ k (Fin 3 → k))} (hS : S.Finite) (hPS : P ∉ S) :
    ∃ (M : Matrix (Fin 3) (Fin 3) k) (hM : Function.Injective M.mulVecLin),
      map M.mulVecLin hM (fundamentalPoint 2) = P ∧
        IsQuadraticTransformAt F P (properTransform (linearSubst M F)) ∧
        ∀ R, map M.mulVecLin hM R ∈ S → R ∉ fundamentalTriangle :=
  let ⟨M, hM, hTP, hE, hRS⟩ := exists_isExcellentPosition_avoiding hF hirr hP hS hPS
  ⟨M, hM, hTP, ⟨M, hM, hTP, hE, rfl⟩, hRS⟩

/-! ### Examples -/

section Examples

/-- A change of coordinates putting an irreducible curve in excellent position with respect to a
non-terrible point `P` can keep any other point `Q` off the fundamental triangle. -/
example [IsAlgClosed k] (hF : F.IsHomogeneous n) (hirr : Irreducible F) {P Q : ℙ k (Fin 3 → k)}
    (hP : ¬ IsTerriblePoint F P.rep) (hQP : Q ≠ P) :
    ∃ (M : Matrix (Fin 3) (Fin 3) k) (hM : Function.Injective M.mulVecLin),
      map M.mulVecLin hM (fundamentalPoint 2) = P ∧ IsExcellentPosition (linearSubst M F) ∧
        ∀ R, map M.mulVecLin hM R = Q → R ∉ fundamentalTriangle :=
  exists_isExcellentPosition_avoiding hF hirr hP (Set.finite_singleton Q) (Ne.symm hQP)

/-- A conic that meets a line `V(Xⱼ)`, not one of its components, in two distinct points `Q₁` and
`Q₂` meets it in no other point, and transversally at both: the intersection numbers add up to
two, by Bézout's theorem. -/
private theorem eq_or_eq_and_intersectionNumber_eq_one [IsAlgClosed k] (hF : F.IsHomogeneous 2)
    {j : Fin 3} (hXj : ¬ X j ∣ F) {Q₁ Q₂ : ℙ k (Fin 3 → k)} (h12 : Q₁ ≠ Q₂)
    (h₁ : Q₁ ∈ zeroLocus {F, X j}) (h₂ : Q₂ ∈ zeroLocus {F, X j}) (hQ : Q ∈ zeroLocus {F, X j}) :
    (Q = Q₁ ∨ Q = Q₂) ∧ intersectionNumber Q F (X j) = 1 := by
  classical
  have hXh := isHomogeneous_X k j
  have hrel : IsRelPrime F (X j) :=
    ((irreducible_of_isHomogeneous_one hXh (X_ne_zero j)).isRelPrime_iff_not_dvd.2 hXj).symm
  have hle (t : Finset (ℙ k (Fin 3 → k))) : ∑ P ∈ t, intersectionNumber P F (X j) ≤ 2 := by
    have hfin := finite_support_intersectionNumber hF hXh hrel
    have hsum := finsum_intersectionNumber_eq_of_isHomogeneous_one hF hXh (X_ne_zero j) hXj
    rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset ∪ t) (by simp)] at hsum
    exact (Finset.sum_le_sum_of_subset Finset.subset_union_right).trans hsum.le
  have hone {P : ℙ k (Fin 3 → k)} (hP : P ∈ zeroLocus {F, X j}) :
      1 ≤ intersectionNumber P F (X j) := by
    rw [mem_zeroLocus_pair_iff, ← eval_rep_eq_zero_iff_mem hF,
      ← eval_rep_eq_zero_iff_mem hXh] at hP
    exact one_le_intersectionNumber hF hXh hP.1 hP.2
  have htop (P : ℙ k (Fin 3 → k)) : intersectionNumber P F (X j) ≠ ⊤ :=
    intersectionNumber_ne_top_of_isRelPrime hF hXh hrel
  have hI₁ := hone h₁
  have hI₂ := hone h₂
  have hI := hone hQ
  by_cases hQ₁ : Q = Q₁
  · subst hQ₁
    refine ⟨Or.inl rfl, ?_⟩
    have h := hle {Q, Q₂}
    rw [Finset.sum_pair h12] at h
    lift intersectionNumber Q F (X j) to ℕ using htop Q with a
    lift intersectionNumber Q₂ F (X j) to ℕ using htop Q₂ with b
    norm_cast at *
    omega
  by_cases hQ₂ : Q = Q₂
  · subst hQ₂
    refine ⟨Or.inr rfl, ?_⟩
    have h := hle {Q, Q₁}
    rw [Finset.sum_pair hQ₁] at h
    lift intersectionNumber Q F (X j) to ℕ using htop Q with a
    lift intersectionNumber Q₁ F (X j) to ℕ using htop Q₁ with b
    norm_cast at *
    omega
  · exfalso
    have h := hle {Q, Q₁, Q₂}
    rw [Finset.sum_insert (by simp [hQ₁, hQ₂]), Finset.sum_pair h12] at h
    lift intersectionNumber Q F (X j) to ℕ using htop Q with a
    lift intersectionNumber Q₁ F (X j) to ℕ using htop Q₁ with b
    lift intersectionNumber Q₂ F (X j) to ℕ using htop Q₂ with c
    norm_cast at *
    omega

private theorem mk_ne_fundamentalPoint {v : Fin 3 → k} (hv : v ≠ 0) {a b : Fin 3} (hab : a ≠ b)
    (ha : v a ≠ 0) (hb : v b ≠ 0) (i : Fin 3) : mk k v hv ≠ fundamentalPoint i := by
  rw [Ne, mk_eq_fundamentalPoint_iff]
  intro h
  by_cases hai : a = i
  · subst hai
    exact hb (h b (Ne.symm hab))
  · exact ha (h a hai)

/-- The conic `X² + 2Y² + 3Z² + 3XY + 4XZ - 5YZ` is in excellent position in characteristic zero.
It passes through no fundamental point, and it meets `Z = 0` in `[1 : -1 : 0]` and `[2 : -1 : 0]`,
`Y = 0` in `[1 : 0 : -1]` and `[3 : 0 : -1]`, and `X = 0` in `[0 : 1 : 1]` and `[0 : 3 : 2]`. -/
example [IsAlgClosed k] [CharZero k] :
    IsExcellentPosition (X 0 ^ 2 + C 2 * X 1 ^ 2 + C 3 * X 2 ^ 2 + C 3 * (X 0 * X 1) +
      C 4 * (X 0 * X 2) - C 5 * (X 1 * X 2) : MvPolynomial (Fin 3) k) := by
  set F : MvPolynomial (Fin 3) k := X 0 ^ 2 + C 2 * X 1 ^ 2 + C 3 * X 2 ^ 2 + C 3 * (X 0 * X 1) +
      C 4 * (X 0 * X 2) - C 5 * (X 1 * X 2)
  have hXX (a b : Fin 3) : (X a * X b : MvPolynomial (Fin 3) k).IsHomogeneous 2 :=
    (isHomogeneous_X k a).mul (isHomogeneous_X k b)
  have hF : F.IsHomogeneous 2 :=
    (((((isHomogeneous_X_pow 0 2).add ((isHomogeneous_X_pow 1 2).C_mul 2)).add
      ((isHomogeneous_X_pow 2 2).C_mul 3)).add ((hXX 0 1).C_mul 3)).add ((hXX 0 2).C_mul 4)).sub
      ((hXX 1 2).C_mul 5)
  have hgood : IsGoodPosition F := by
    rw [isGoodPosition_def]
    intro i j _ ht
    have h := ht.eval_rep_eq_zero
    rw [fundamentalPoint_def, hF.eval_rep_mk_eq_zero_iff] at h
    fin_cases i <;> norm_num [F] at h
  have hmem {j : Fin 3} {v : Fin 3 → k} (hv : v ≠ 0) (hFv : eval v F = 0) (hj : v j = 0) :
      mk k v hv ∈ zeroLocus {F, X j} := by
    rw [mk_mem_zeroLocus_iff (by rintro f (rfl | rfl); exacts [⟨2, hF⟩, ⟨1, isHomogeneous_X k j⟩])]
    rintro f (rfl | rfl)
    exacts [hFv, by simpa using hj]
  have hne {v : Fin 3 → k} {a : Fin 3} (ha : v a ≠ 0) : v ≠ 0 := fun h ↦ ha (by simp [h])
  refine ⟨hgood, fun j Q hQ _ ↦ ?_⟩
  fin_cases j
  · obtain ⟨hQ12, hI⟩ := eq_or_eq_and_intersectionNumber_eq_one hF (hgood.not_X_dvd 0)
      (Q₁ := mk k ![0, 1, 1] (hne (a := 1) (by simp)))
      (Q₂ := mk k ![0, 3, 2] (hne (a := 1) (by simp)))
      (by
        rw [Ne, mk_eq_mk_iff']
        rintro ⟨a, ha⟩
        have h1 : a * 3 = 1 := by simpa using congrFun ha 1
        have h2 : a * 2 = 1 := by simpa using congrFun ha 2
        have : a = 0 := by linear_combination h1 - h2
        norm_num [this] at h1)
      (hmem _ (by norm_num [F]) (by simp)) (hmem _ (by norm_num [F]) (by simp)) hQ
    refine ⟨fun i ↦ ?_, hI⟩
    rcases hQ12 with rfl | rfl
    exacts [mk_ne_fundamentalPoint _ (a := 1) (b := 2) (by decide) (by simp) (by simp) i,
      mk_ne_fundamentalPoint _ (a := 1) (b := 2) (by decide) (by simp) (by simp) i]
  · obtain ⟨hQ12, hI⟩ := eq_or_eq_and_intersectionNumber_eq_one hF (hgood.not_X_dvd 1)
      (Q₁ := mk k ![1, 0, -1] (hne (a := 0) (by simp)))
      (Q₂ := mk k ![3, 0, -1] (hne (a := 0) (by simp)))
      (by
        rw [Ne, mk_eq_mk_iff']
        rintro ⟨a, ha⟩
        have h0 : a * 3 = 1 := by simpa using congrFun ha 0
        have h2 : -a = -1 := by simpa using congrFun ha 2
        have : a = 1 := by linear_combination -h2
        norm_num [this] at h0)
      (hmem _ (by norm_num [F]) (by simp)) (hmem _ (by norm_num [F]) (by simp)) hQ
    refine ⟨fun i ↦ ?_, hI⟩
    rcases hQ12 with rfl | rfl
    exacts [mk_ne_fundamentalPoint _ (a := 0) (b := 2) (by decide) (by simp) (by simp) i,
      mk_ne_fundamentalPoint _ (a := 0) (b := 2) (by decide) (by simp) (by simp) i]
  · obtain ⟨hQ12, hI⟩ := eq_or_eq_and_intersectionNumber_eq_one hF (hgood.not_X_dvd 2)
      (Q₁ := mk k ![1, -1, 0] (hne (a := 0) (by simp)))
      (Q₂ := mk k ![2, -1, 0] (hne (a := 0) (by simp)))
      (by
        rw [Ne, mk_eq_mk_iff']
        rintro ⟨a, ha⟩
        have h0 : a * 2 = 1 := by simpa using congrFun ha 0
        have h1 : -a = -1 := by simpa using congrFun ha 1
        have : a = 1 := by linear_combination -h1
        norm_num [this] at h0)
      (hmem _ (by norm_num [F]) (by simp)) (hmem _ (by norm_num [F]) (by simp)) hQ
    refine ⟨fun i ↦ ?_, hI⟩
    rcases hQ12 with rfl | rfl
    exacts [mk_ne_fundamentalPoint _ (a := 0) (b := 1) (by decide) (by simp) (by simp) i,
      mk_ne_fundamentalPoint _ (a := 0) (b := 1) (by decide) (by simp) (by simp) i]

/-- The line `X + Z` is in good position, but not in excellent position: it passes through
`P' = [0 : 1 : 0]`. -/
example : IsGoodPosition (X 0 + X 2 : MvPolynomial (Fin 3) ℚ) ∧
    ¬ IsExcellentPosition (X 0 + X 2 : MvPolynomial (Fin 3) ℚ) := by
  have hL : (X 0 + X 2 : MvPolynomial (Fin 3) ℚ).IsHomogeneous 1 :=
    (isHomogeneous_X ℚ 0).add (isHomogeneous_X ℚ 2)
  have hP' : fundamentalPoint (k := ℚ) 1 ∈ zeroLocus {X 0 + X 2} := by
    rw [fundamentalPoint_def, mk_mem_zeroLocus_iff (by simpa using ⟨1, hL⟩)]
    simp
  refine ⟨isGoodPosition_def.2 fun i j hij ht ↦ ?_,
    fun h ↦ h.fundamentalPoint_notMem (i := 1) (by decide) hP'⟩
  have h := ht.eval_rep_eq_zero
  rw [fundamentalPoint_def, hL.eval_rep_mk_eq_zero_iff] at h
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp
  · simp at h
  · -- At `P'`, the leading form of the line is the line itself, which no `Xⱼ` divides.
    have hv0 : (fundamentalPoint (k := ℚ) 1).rep 0 = 0 := by
      rw [← mem_zeroLocus_X_iff]
      exact fundamentalPoint_mem_zeroLocus_X_iff.2 (by decide)
    have hv2 : (fundamentalPoint (k := ℚ) 1).rep 2 = 0 := by
      rw [← mem_zeroLocus_X_iff]
      exact fundamentalPoint_mem_zeroLocus_X_iff.2 (by decide)
    have hlead : leadingForm (X 0 + X 2 : MvPolynomial (Fin 3) ℚ) (fundamentalPoint 1) =
        X 0 + X 2 := by
      have e := leadingFormAt_taylor (fundamentalPoint (k := ℚ) 1).rep 0
        (X 0 + X 2 : MvPolynomial (Fin 3) ℚ)
      rw [zero_add, map_add, taylor_X, taylor_X, hv0, hv2, C_0, add_zero, add_zero,
        hL.leadingFormAt_zero] at e
      rw [leadingForm_def, ← e]
    have hdvd := (isTangentAt_def.1 ht).2.2.2
    rw [hlead, X_dvd_iff_bind₁_update_X_zero_eq_zero] at hdvd
    fin_cases j
    · simp [X_ne_zero] at hdvd
    · exact hij rfl
    · simp [X_ne_zero] at hdvd
  · simp at h

end Examples

end PlaneCurves.Projective

end
