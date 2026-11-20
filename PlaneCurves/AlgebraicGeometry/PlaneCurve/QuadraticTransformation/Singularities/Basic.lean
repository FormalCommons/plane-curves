/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Finiteness
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Position
import TauCeti.Algebra.Squarefree

/-!
# The proper transform of a curve in excellent position

Let `F` be a form of degree `n` in excellent position (Fulton, §7.4), with `r = m_P(F)` at
`P = [0 : 0 : 1]`, and let `F'` be its proper transform under the standard quadratic
transformation. Then `F` does not pass through `P' = [0 : 1 : 0]` or `P'' = [1 : 0 : 0]`, so
`F^Q = Z^r F'` and `F'` is a form of degree `2n - r`. This file describes `C' = V(F')` on the
fundamental triangle: Fulton's step (7) (b), and the setting of (7) (c).

* The restrictions of `F'` to the exceptional lines are `F'(X, Y, 0) = (XY)^(n - r) F_r(Y, X)`,
  with `F_r` the tangent cone of `F` at `P`, `F'(X, 0, Z) = F(0, 1, 0) X^n Z^(n - r)` and
  `F'(0, Y, Z) = F(1, 0, 0) Y^n Z^(n - r)`. So `C'` meets `L' = V(Y)` and `L'' = V(X)` only in
  fundamental points, and its other points on `L = V(Z)` are the *points over the centre*, the
  `[α : 1 : 0]` with `α ≠ 0` and `F_r(1, α) = 0`.
* `C'` has multiplicity `n` at `P` and `n - r` at `P'` and `P''`. Its leading form at `P` is
  `F(Y, X, 0)`, at `P'` it is `H(Z, X)` where `F(X, 0, Z) = X^r H(X, Z)`, and symmetrically at
  `P''`. These are squarefree by excellent position, so the fundamental points of `C'` are
  ordinary whenever they are multiple points.

The leading form of `F'` at `P` comes from that of `F^Q`, which is `F(Y, X, 0)` for every form
`F` without the component `V(Z)`. At `P'` and `P''` it follows by swapping variables.

All declarations are in the namespace `PlaneCurves.Projective`.

## Main definitions

* `pointsOverCentre F`: the points of `C'` on `V(Z)` that are not fundamental points.

## Main results

* `leadingFormAt_quadraticTransform_single_two`,
  `X_pow_mul_leadingFormAt_properTransform_single_two`: the leading forms of `F^Q` and of `F'`
  at `[0 : 0 : 1]`, for every form without the component `V(Z)`.
* `IsExcellentPosition.quadraticTransform_eq`: `F^Q = Z^r F'`;
  `IsExcellentPosition.isHomogeneous_properTransform`: `F'` has degree `2n - r`.
* `IsExcellentPosition.aeval_X_two_eq_zero_properTransform`,
  `IsExcellentPosition.aeval_X_one_eq_zero_properTransform`,
  `IsExcellentPosition.aeval_X_zero_eq_zero_properTransform`: the restrictions of `F'` to the
  exceptional lines.
* `IsExcellentPosition.zeroLocus_properTransform_X_one_subset`,
  `IsExcellentPosition.zeroLocus_properTransform_X_zero_subset`: `C'` meets `L'` and `L''` only
  in fundamental points; `IsExcellentPosition.eq_fundamentalPoint_or_mem_pointsOverCentre`: its
  points on the triangle are fundamental or over the centre.
* `IsExcellentPosition.mem_pointsOverCentre_iff`, `IsExcellentPosition.pointsOverCentre_finite`:
  the points over the centre, in terms of the tangent cone of `F` at `P`;
  `pointsOverCentre_mul`: those of a product are those of the factors.
* `IsExcellentPosition.mult_properTransform_fundamentalPoint_two`,
  `IsExcellentPosition.mult_properTransform_fundamentalPoint`: the multiplicities `n`, `n - r`,
  `n - r` of `C'` at `P`, `P'`, `P''`.
* `IsExcellentPosition.leadingFormAt_properTransform_single_two`,
  `IsExcellentPosition.X_two_pow_mul_leadingFormAt_properTransform_single_one`,
  `IsExcellentPosition.X_two_pow_mul_leadingFormAt_properTransform_single_zero`: the leading
  forms of `F'` at the fundamental points;
  `IsExcellentPosition.squarefree_leadingForm_properTransform`: they are squarefree;
  `IsExcellentPosition.isOrdinaryMultiplePoint_properTransform_fundamentalPoint`: the
  fundamental points of `C'` that are multiple points are ordinary.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.4
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

/-! ### The leading form of `F'` at `[0 : 0 : 1]` -/

section LeadingForm

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {n : ℕ}

/-- `F(Y, X, 0)` is a form of degree `n`. -/
private theorem isHomogeneous_aeval_X_one_X_zero (hF : F.IsHomogeneous n) :
    (aeval (![X 1, X 0, 0] : Fin 3 → MvPolynomial (Fin 3) k) F).IsHomogeneous n := by
  simpa only [one_mul] using hF.aeval (n := 1) _ fun i ↦ by
    fin_cases i
    · simpa using isHomogeneous_X k 1
    · simpa using isHomogeneous_X k 0
    · simpa using isHomogeneous_zero (Fin 3) k 1

private theorem aeval_X_one_X_zero_ne_zero (hX : ¬ X 2 ∣ F) :
    aeval (![X 1, X 0, 0] : Fin 3 → MvPolynomial (Fin 3) k) F ≠ 0 := by
  intro h0
  refine hX (X_dvd_of_bind₁_update_X_zero_eq_zero ?_)
  have : aeval (![X 1, X 0, X 2] : Fin 3 → MvPolynomial (Fin 3) k)
      (aeval (![X 1, X 0, 0] : Fin 3 → MvPolynomial (Fin 3) k) F) =
      bind₁ (Function.update X 2 0) F := by
    rw [← AlgHom.comp_apply, comp_aeval, aeval_eq_bind₁]
    congr 2
    funext i
    fin_cases i <;> simp
  rw [← this, h0, map_zero]

/-- `F(Y, X, 0)` does not involve `Z`, so at `[0 : 0 : 1]` it has order `n` and is its own leading
form. -/
private theorem orderAt_leadingFormAt_aeval_X_one_X_zero (hF : F.IsHomogeneous n)
    (hX : ¬ X 2 ∣ F) :
    (aeval (![X 1, X 0, 0] : Fin 3 → MvPolynomial (Fin 3) k) F).orderAt (Pi.single 2 1) = n ∧
      (aeval (![X 1, X 0, 0] : Fin 3 → MvPolynomial (Fin 3) k) F).leadingFormAt
        (Pi.single 2 1) = aeval (![X 1, X 0, 0] : Fin 3 → MvPolynomial (Fin 3) k) F := by
  set R := aeval (![X 1, X 0, 0] : Fin 3 → MvPolynomial (Fin 3) k) F with hR
  have htay : taylor (Pi.single 2 1) R = R := by
    rw [hR, ← AlgHom.comp_apply, comp_aeval]
    congr 2
    funext i
    fin_cases i <;> simp [taylor_X]
  have h1 := orderAt_taylor (Pi.single 2 1) 0 R
  have h2 := leadingFormAt_taylor (Pi.single 2 1) 0 R
  rw [htay, zero_add, (isHomogeneous_aeval_X_one_X_zero hF).orderAt_zero
    (aeval_X_one_X_zero_ne_zero hX)] at h1
  rw [htay, zero_add, (isHomogeneous_aeval_X_one_X_zero hF).leadingFormAt_zero] at h2
  exact ⟨h1.symm, h2.symm⟩

/-- If `ZK` is a form of degree `n`, then `XY K^Q` has order at least `n + 1` at `[0 : 0 : 1]`. -/
private theorem add_one_le_orderAt_X_mul_X_mul_quadraticTransform {K : MvPolynomial (Fin 3) k}
    (hXK : (X 2 * K).IsHomogeneous n) :
    ((n : ℕ∞) + 1) ≤ (X 0 * X 1 * quadraticTransform K).orderAt (Pi.single 2 1) := by
  obtain rfl | hK0 := eq_or_ne K 0
  · simp
  have hdeg : K.totalDegree + 1 = n := by
    have := hXK.totalDegree (mul_ne_zero (X_ne_zero 2) hK0)
    rwa [totalDegree_mul_of_isDomain (X_ne_zero 2) hK0, totalDegree_X, add_comm] at this
  have hKQ : (K.totalDegree : ℕ∞) ≤ (quadraticTransform K).orderAt (Pi.single 2 1) := by
    rw [quadraticTransform_def, ← aeval_eq_bind₁]
    refine le_trans ?_ (orderAt_le_orderAt_aeval _ _ K)
    have h0 : (fun i ↦ eval (Pi.single 2 1) (![X 1 * X 2, X 0 * X 2, X 0 * X 1] i :
        MvPolynomial (Fin 3) k)) = 0 := by
      funext i
      fin_cases i <;> simp
    rw [h0]
    exact (hXK.of_mul_right (X_ne_zero 2)).natCast_le_orderAt_zero
  rw [orderAt_mul, orderAt_mul, orderAt_X_of_eq_zero (by simp),
    orderAt_X_of_eq_zero (by simp), ← hdeg]
  calc ((K.totalDegree + 1 : ℕ) : ℕ∞) + 1 = 1 + 1 + K.totalDegree := by push_cast; ring
    _ ≤ 1 + 1 + (quadraticTransform K).orderAt (Pi.single 2 1) := by gcongr

/-- **The leading form of `F^Q` at `[0 : 0 : 1]`.** For a form `F` of degree `n` without the
component `V(Z)`, the leading form of its quadratic transform at `[0 : 0 : 1]` is `F(Y, X, 0)`:
writing `F = F(X, Y, 0) + Z K`, `F^Q = Z^n F(Y, X, 0) + XY K^Q`, and the second summand has
larger order there. -/
theorem leadingFormAt_quadraticTransform_single_two (hF : F.IsHomogeneous n) (hX : ¬ X 2 ∣ F) :
    (quadraticTransform F).leadingFormAt (Pi.single 2 1) =
      aeval (![X 1, X 0, 0] : Fin 3 → MvPolynomial (Fin 3) k) F := by
  set R := aeval (![X 1, X 0, 0] : Fin 3 → MvPolynomial (Fin 3) k) F with hR
  obtain ⟨hRord, hRlf⟩ := orderAt_leadingFormAt_aeval_X_one_X_zero hF hX
  obtain ⟨K, hK⟩ := X_dvd_sub_bind₁_update_X_zero 2 F
  have hRQ : quadraticTransform (bind₁ (Function.update X 2 0) F) = X 2 ^ n * R := by
    rw [← aeval_eq_bind₁, ← AlgHom.comp_apply, comp_aeval, hR, ← hF.aeval_mul_left]
    congr 2
    funext i
    fin_cases i <;> simp [mul_comm]
  have hQ : quadraticTransform F = X 2 ^ n * R + X 0 * X 1 * quadraticTransform K := by
    rw [← hRQ, ← quadraticTransform_X_two, ← map_mul, ← map_add, ← hK, add_sub_cancel]
  have hX2 : eval (Pi.single 2 1) (X 2 ^ n : MvPolynomial (Fin 3) k) ≠ 0 := by simp
  have hlt : (X 2 ^ n * R).orderAt (Pi.single 2 1) <
      (X 0 * X 1 * quadraticTransform K).orderAt (Pi.single 2 1) := by
    rw [orderAt_mul, orderAt_eq_zero_iff.2 hX2, zero_add, hRord]
    refine lt_of_lt_of_le (ENat.lt_add_one_iff (ENat.natCast_ne_top n) |>.2 le_rfl)
      (add_one_le_orderAt_X_mul_X_mul_quadraticTransform ?_)
    rw [← hK]
    exact hF.sub (hF.bind₁_update_X_zero 2)
  rw [hQ, leadingFormAt_add_of_lt hlt, leadingFormAt_mul, leadingFormAt_of_eval_ne_zero hX2, hRlf]
  simp [hR]

/-- **The leading form of `F'` at `[0 : 0 : 1]`.** For a form `F` of degree `n` without the
component `V(Z)`, with `rᵢ` its multiplicity at `[eᵢ]`, the leading form of the proper
transform at `[0 : 0 : 1]` times `X^r₀ Y^r₁` is `F(Y, X, 0)`. -/
theorem X_pow_mul_leadingFormAt_properTransform_single_two (hF : F.IsHomogeneous n)
    (hX : ¬ X 2 ∣ F) :
    X 0 ^ (mult F (fundamentalPoint 0)).toNat * X 1 ^ (mult F (fundamentalPoint 1)).toNat *
        (properTransform F).leadingFormAt (Pi.single 2 1) =
      aeval (![X 1, X 0, 0] : Fin 3 → MvPolynomial (Fin 3) k) F := by
  rw [← leadingFormAt_quadraticTransform_single_two hF hX, quadraticTransform_eq hF,
    leadingFormAt_mul, leadingFormAt_mul, leadingFormAt_mul, leadingFormAt_pow, leadingFormAt_pow,
    leadingFormAt_pow, leadingFormAt_X_of_eq_zero (by simp),
    leadingFormAt_X_of_eq_zero (by simp),
    leadingFormAt_of_eval_ne_zero (by simp : eval (Pi.single 2 1 : Fin 3 → k) (X 2) ≠ 0)]
  simp

end LeadingForm

/-! ### The proper transform of a curve in excellent position -/

section Excellent

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {Q : ℙ k (Fin 3 → k)} {n : ℕ}

namespace IsExcellentPosition

private theorem toNat_mult_eq_zero (h : IsExcellentPosition F) (hF : F.IsHomogeneous n)
    {i : Fin 3} (hi : i ≠ 2) : (mult F (fundamentalPoint i)).toNat = 0 := by
  rw [h.mult_fundamentalPoint_eq_zero hF hi, ENat.toNat_zero]

private theorem toNat_mult_le (h : IsExcellentPosition F) (hF : F.IsHomogeneous n) :
    (mult F (fundamentalPoint 2)).toNat ≤ n :=
  ENat.toNat_le_of_le_natCast (mult_le_degree hF h.ne_zero _)

/-- **`F^Q = Z^r F'`** for a curve in excellent position, `r = m_{[0:0:1]}(F)`: it does not pass
through the other two fundamental points. -/
theorem quadraticTransform_eq (h : IsExcellentPosition F) (hF : F.IsHomogeneous n) :
    quadraticTransform F = X 2 ^ (mult F (fundamentalPoint 2)).toNat * properTransform F := by
  rw [Projective.quadraticTransform_eq hF, h.toNat_mult_eq_zero hF (i := 0) (by decide),
    h.toNat_mult_eq_zero hF (i := 1) (by decide), pow_zero, pow_zero, one_mul, one_mul]

/-- The proper transform of a curve of degree `n` in excellent position is a form of degree
`2n - r`, `r = m_{[0:0:1]}(F)`. -/
theorem isHomogeneous_properTransform (h : IsExcellentPosition F) (hF : F.IsHomogeneous n) :
    (properTransform F).IsHomogeneous (2 * n - (mult F (fundamentalPoint 2)).toNat) := by
  have := hF.properTransform
  rwa [Fin.sum_univ_three, h.toNat_mult_eq_zero hF (i := 0) (by decide),
    h.toNat_mult_eq_zero hF (i := 1) (by decide), zero_add, zero_add] at this

/-- **The restriction of `F'` to `L = V(Z)`.** For a curve of degree `n` in excellent position,
`F'(X, Y, 0) = (XY)^(n - r) F_r(Y, X)`, where `F_r` is the leading form of `F(X, Y, 1)` at the
origin, the tangent cone of `F` at `[0 : 0 : 1]`, and `r = m_{[0:0:1]}(F)`. -/
theorem aeval_X_two_eq_zero_properTransform (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) :
    aeval (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) (properTransform F) =
      (X 0 * X 1) ^ (n - (mult F (fundamentalPoint 2)).toNat) *
        rename ![1, 0] (leadingFormAt (dehomogenize 2 F) 0) := by
  have := Projective.aeval_X_two_eq_zero_properTransform hF h.ne_zero
  rwa [h.toNat_mult_eq_zero hF (i := 0) (by decide),
    h.toNat_mult_eq_zero hF (i := 1) (by decide), pow_zero, pow_zero, one_mul, one_mul] at this

/-- **The restriction of `F'` to `V(Xⱼ)`, `j ≠ 2`.** Let `l` be the third index. For a curve
of degree `n` in excellent position, setting `Xⱼ = 0` in `F'` gives `F(eⱼ) X_l^n Z^(n - r)`, with
`r = m_{[0:0:1]}(F)` and `F(eⱼ) ≠ 0`. -/
theorem bind₁_update_X_zero_properTransform (h : IsExcellentPosition F) (hF : F.IsHomogeneous n)
    {j l : Fin 3} (hj : j ≠ 2) (hl : l ≠ 2) (hjl : j ≠ l) :
    bind₁ (Function.update X j 0) (properTransform F) =
      C (eval (Pi.single j 1) F) * X l ^ n *
        X 2 ^ (n - (mult F (fundamentalPoint 2)).toNat) := by
  set r := (mult F (fundamentalPoint 2)).toNat
  have hrn : r ≤ n := h.toNat_mult_le hF
  have hq : (fun i ↦ bind₁ (Function.update X j 0)
      (![X 1 * X 2, X 0 * X 2, X 0 * X 1] i : MvPolynomial (Fin 3) k)) =
      fun i ↦ (X l * X 2) * C (Pi.single j 1 i) := by
    funext i
    fin_cases j <;> fin_cases l <;> fin_cases i <;>
      simp_all [Function.update, mul_comm]
  have hQ := congrArg (bind₁ (Function.update X j 0)) (h.quadraticTransform_eq hF)
  rw [quadraticTransform_def, bind₁_bind₁, hq, ← aeval_eq_bind₁, hF.aeval_mul_left, map_mul,
    map_pow, bind₁_X_right, Function.update_of_ne (by simpa using hj.symm)] at hQ
  have hC : aeval (fun i ↦ C (Pi.single j (1 : k) i)) F =
      (C (eval (Pi.single j 1) F) : MvPolynomial (Fin 3) k) := by
    rw [aeval_def, eval, coe_eval₂Hom, eval₂_comp_left]
    rfl
  rw [hC] at hQ
  refine mul_left_cancel₀ (pow_ne_zero r (X_ne_zero 2))
    ?_
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hrn
  rw [← hQ, Nat.add_sub_cancel_left]
  ring

/-- **The restriction of `F'` to `L' = V(Y)`**: `F'(X, 0, Z) = F(0, 1, 0) X^n Z^(n - r)`. -/
theorem aeval_X_one_eq_zero_properTransform (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) :
    aeval (![X 0, 0, X 2] : Fin 3 → MvPolynomial (Fin 3) k) (properTransform F) =
      C (eval (Pi.single 1 1) F) * X 0 ^ n * X 2 ^ (n - (mult F (fundamentalPoint 2)).toNat) := by
  rw [show (![X 0, 0, X 2] : Fin 3 → MvPolynomial (Fin 3) k) = Function.update X 1 0 by
    funext i; fin_cases i <;> rfl, aeval_eq_bind₁]
  exact h.bind₁_update_X_zero_properTransform hF (by decide) (by decide) (by decide)

/-- **The restriction of `F'` to `L'' = V(X)`**: `F'(0, Y, Z) = F(1, 0, 0) Y^n Z^(n - r)`. -/
theorem aeval_X_zero_eq_zero_properTransform (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) :
    aeval (![0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) k) (properTransform F) =
      C (eval (Pi.single 0 1) F) * X 1 ^ n * X 2 ^ (n - (mult F (fundamentalPoint 2)).toNat) := by
  rw [show (![0, X 1, X 2] : Fin 3 → MvPolynomial (Fin 3) k) = Function.update X 0 0 by
    funext i; fin_cases i <;> rfl, aeval_eq_bind₁]
  exact h.bind₁_update_X_zero_properTransform hF (by decide) (by decide) (by decide)

/-- **`C'` meets `V(Xⱼ)`, `j ≠ 2`, only in fundamental points**: in `[0 : 0 : 1]` and the
fundamental point `[e_l]` for the third index `l`. -/
theorem zeroLocus_properTransform_X_subset (h : IsExcellentPosition F) (hF : F.IsHomogeneous n)
    {j l : Fin 3} (hj : j ≠ 2) (hl : l ≠ 2) (hjl : j ≠ l) :
    zeroLocus {properTransform F, X j} ⊆ {fundamentalPoint l, fundamentalPoint 2} := by
  intro Q hQ
  have hF' := h.isHomogeneous_properTransform hF
  rw [mem_zeroLocus_iff_eval_rep (by simpa using ⟨⟨_, hF'⟩, ⟨1, isHomogeneous_X k j⟩⟩)] at hQ
  have h0 : eval Q.rep (properTransform F) = 0 := hQ _ (by simp)
  have hj0 : Q.rep j = 0 := by simpa using hQ (X j) (by simp)
  rw [← Function.update_eq_self j Q.rep, hj0, ← eval_bind₁_update_X_zero,
    h.bind₁_update_X_zero_properTransform hF hj hl hjl] at h0
  simp only [eval_mul, eval_C, eval_pow, eval_X, mul_eq_zero,
    h.eval_single_ne_zero hF hj, false_or] at h0
  have hcases : ∀ m : Fin 3, m = j ∨ m = l ∨ m = 2 := by
    intro m
    omega
  rw [← Q.mk_rep]
  rcases h0 with h0 | h0
  · refine Or.inr ((mk_eq_fundamentalPoint_iff _ _ _).2 fun m hm ↦ ?_)
    rcases hcases m with rfl | rfl | rfl
    exacts [hj0, eq_zero_of_pow_eq_zero h0, absurd rfl hm]
  · refine Or.inl ((mk_eq_fundamentalPoint_iff _ _ _).2 fun m hm ↦ ?_)
    rcases hcases m with rfl | rfl | rfl
    exacts [hj0, absurd rfl hm, eq_zero_of_pow_eq_zero h0]

/-- `C'` meets `L' = V(Y)` only in `[1 : 0 : 0]` and `[0 : 0 : 1]`. -/
theorem zeroLocus_properTransform_X_one_subset (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) :
    zeroLocus {properTransform F, X 1} ⊆ {fundamentalPoint 0, fundamentalPoint 2} :=
  h.zeroLocus_properTransform_X_subset hF (by decide) (by decide) (by decide)

/-- `C'` meets `L'' = V(X)` only in `[0 : 1 : 0]` and `[0 : 0 : 1]`. -/
theorem zeroLocus_properTransform_X_zero_subset (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) :
    zeroLocus {properTransform F, X 0} ⊆ {fundamentalPoint 1, fundamentalPoint 2} :=
  h.zeroLocus_properTransform_X_subset hF (by decide) (by decide) (by decide)

private theorem eval_aeval (w : Fin 3 → k) (g : Fin 3 → MvPolynomial (Fin 3) k)
    (p : MvPolynomial (Fin 3) k) : eval w (aeval g p) = eval (fun i ↦ eval w (g i)) p := by
  rw [aeval_eq_bind₁]
  exact eval₂Hom_bind₁ _ _ _ _

/-- The points of `L = V(Z)` other than the fundamental points are the `[α : 1 : 0]`, `α ≠ 0`. -/
private theorem mem_zeroLocus_X_two_and_ne_iff :
    (Q ∈ zeroLocus {X 2} ∧ ∀ i, Q ≠ fundamentalPoint i) ↔
      ∃ α : k, α ≠ 0 ∧ Q = mk k ![α, 1, 0] (by simp) := by
  constructor
  · rintro ⟨hQ, hne⟩
    rw [mem_zeroLocus_X_iff] at hQ
    have h0 : Q.rep 0 ≠ 0 := fun h0 ↦ hne 1 (by
      rw [← Q.mk_rep, mk_eq_fundamentalPoint_iff]
      intro m hm
      fin_cases m <;> simp_all)
    have h1 : Q.rep 1 ≠ 0 := fun h1 ↦ hne 0 (by
      rw [← Q.mk_rep, mk_eq_fundamentalPoint_iff]
      intro m hm
      fin_cases m <;> simp_all)
    refine ⟨Q.rep 0 / Q.rep 1, div_ne_zero h0 h1, ?_⟩
    rw [← Q.mk_rep, mk_eq_mk_iff']
    refine ⟨Q.rep 1, ?_⟩
    funext m
    fin_cases m <;> simp [hQ, mul_div_cancel₀ _ h1]
  · rintro ⟨α, hα, rfl⟩
    refine ⟨(mk_mem_zeroLocus_singleton_iff (isHomogeneous_X k 2) _ _).2
      (by simp), fun i hi ↦ ?_⟩
    rw [mk_eq_fundamentalPoint_iff] at hi
    fin_cases i
    · simpa using hi 1 (by decide)
    · exact hα (by simpa using hi 0 (by decide))
    · simpa using hi 1 (by decide)

end IsExcellentPosition

/-- The *points over the centre* of a curve `F`: the points `P₁, …, Pₛ` of its proper transform
`C' = V(F')` on the exceptional line `L = V(Z)` that are not fundamental points. For a curve in
excellent position they are the points `[α : 1 : 0]`, `α ≠ 0`, with `F_r(1, α) = 0`, for `F_r`
the tangent cone of `F` at `[0 : 0 : 1]` (`IsExcellentPosition.mem_pointsOverCentre_iff`). -/
def pointsOverCentre (F : MvPolynomial (Fin 3) k) : Set (ℙ k (Fin 3 → k)) :=
  {Q | Q ∈ zeroLocus {properTransform F, X 2} ∧ ∀ i, Q ≠ fundamentalPoint i}

theorem pointsOverCentre_def (F : MvPolynomial (Fin 3) k) :
    pointsOverCentre F =
      {Q | Q ∈ zeroLocus {properTransform F, X 2} ∧ ∀ i, Q ≠ fundamentalPoint i} :=
  (rfl)

/-- The points over the centre lie on the fundamental triangle. -/
theorem pointsOverCentre_subset_fundamentalTriangle :
    pointsOverCentre F ⊆ fundamentalTriangle := fun Q hQ ↦ by
  rw [fundamentalTriangle_eq_iUnion, Set.mem_iUnion]
  exact ⟨2, zeroLocus_anti_mono (by simp) hQ.1⟩

/-- The points over the centre of a product of forms are those of the factors: `(F G)' = F' G'`.
-/
theorem pointsOverCentre_mul {G : MvPolynomial (Fin 3) k} {m : ℕ} (hF : F.IsHomogeneous n)
    (hG : G.IsHomogeneous m) :
    pointsOverCentre (F * G) = pointsOverCentre F ∪ pointsOverCentre G := by
  ext Q
  simp only [pointsOverCentre_def, Set.mem_ofPred_eq, Set.mem_union, properTransform_mul hF hG,
    mem_zeroLocus_pair_iff, mem_zeroLocus_singleton_iff (hF.properTransform.mul hG.properTransform),
    mem_zeroLocus_singleton_iff hF.properTransform, mem_zeroLocus_singleton_iff hG.properTransform,
    eval_mul, mul_eq_zero]
  tauto

namespace IsExcellentPosition

/-- At `[α : 1 : 0]`, `F' = α^(n - r) F_r(1, α)`, for `F_r` the tangent cone of `F` at
`[0 : 0 : 1]` and `r = m_{[0:0:1]}(F)`. -/
theorem eval_properTransform_vec_one_zero (h : IsExcellentPosition F) (hF : F.IsHomogeneous n)
    (α : k) :
    eval ![α, 1, 0] (properTransform F) = α ^ (n - (mult F (fundamentalPoint 2)).toNat) *
      eval ![1, α] (leadingFormAt (dehomogenize 2 F) 0) := by
  have h' := congrArg (eval ![α, 1, 0]) (h.aeval_X_two_eq_zero_properTransform hF)
  have e1 : (fun i ↦ eval ![α, 1, 0] (![X 0, X 1, 0] i : MvPolynomial (Fin 3) k)) =
      ![α, 1, 0] := by
    funext i
    fin_cases i <;> simp
  have e2 : (![α, 1, 0] ∘ ![1, 0] : Fin 2 → k) = ![1, α] := by
    funext i
    fin_cases i <;> rfl
  rw [eval_aeval, e1, eval_mul, eval_pow, eval_mul, eval_X, eval_X, eval_rename, e2] at h'
  simpa using h'

/-- **The points over the centre.** For a curve in excellent position, a point of `ℙ²` is over
the centre exactly when it is `[α : 1 : 0]` with `α ≠ 0` and `F_r(1, α) = 0`, for `F_r` the
tangent cone of `F` at `[0 : 0 : 1]`. -/
theorem mem_pointsOverCentre_iff (h : IsExcellentPosition F) (hF : F.IsHomogeneous n) :
    Q ∈ pointsOverCentre F ↔ ∃ α : k, α ≠ 0 ∧ Q = mk k ![α, 1, 0] (by simp) ∧
      eval ![1, α] (leadingFormAt (dehomogenize 2 F) 0) = 0 := by
  have hF' := h.isHomogeneous_properTransform hF
  change (Q ∈ zeroLocus {properTransform F, X 2} ∧ ∀ i, Q ≠ fundamentalPoint i) ↔ _
  rw [zeroLocus_insert]
  constructor
  · rintro ⟨⟨hQF, hQ2⟩, hne⟩
    obtain ⟨α, hα, rfl⟩ := mem_zeroLocus_X_two_and_ne_iff.1 ⟨hQ2, hne⟩
    refine ⟨α, hα, rfl, ?_⟩
    have := (mk_mem_zeroLocus_singleton_iff hF' _ _).1 hQF
    rw [h.eval_properTransform_vec_one_zero hF] at this
    exact (mul_eq_zero.1 this).resolve_left (pow_ne_zero _ hα)
  · rintro ⟨α, hα, rfl, h0⟩
    obtain ⟨h2, hne⟩ := mem_zeroLocus_X_two_and_ne_iff.2 ⟨α, hα, rfl⟩
    exact ⟨⟨(mk_mem_zeroLocus_singleton_iff hF' _ _).2
      (by rw [h.eval_properTransform_vec_one_zero hF, h0, mul_zero]), h2⟩, hne⟩

/-- A curve in excellent position has only finitely many points over the centre. -/
theorem pointsOverCentre_finite (h : IsExcellentPosition F) (hF : F.IsHomogeneous n) :
    (pointsOverCentre F).Finite :=
  (finite_zeroLocus_pair_of_isRelPrime (h.isHomogeneous_properTransform hF)
    (isHomogeneous_X k 2) (prime_X.irreducible.isRelPrime_iff_not_dvd.2
      (not_X_dvd_properTransform hF h.ne_zero 2)).symm).subset fun _ hQ ↦ hQ.1

/-- **The points of `C'` on the fundamental triangle** are fundamental points or over the
centre. -/
theorem eq_fundamentalPoint_or_mem_pointsOverCentre (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) (hQ : Q ∈ zeroLocus {properTransform F})
    (hQT : Q ∈ fundamentalTriangle) : (∃ i, Q = fundamentalPoint i) ∨ Q ∈ pointsOverCentre F := by
  by_cases hne : ∀ i, Q ≠ fundamentalPoint i
  · rw [fundamentalTriangle_eq_iUnion, Set.mem_iUnion] at hQT
    obtain ⟨j, hj⟩ := hQT
    have hQj : Q ∈ zeroLocus {properTransform F, X j} := by
      rw [zeroLocus_insert]
      exact ⟨hQ, hj⟩
    fin_cases j
    · rcases h.zeroLocus_properTransform_X_zero_subset hF hQj with h1 | h1
      exacts [absurd h1 (hne 1), absurd h1 (hne 2)]
    · rcases h.zeroLocus_properTransform_X_one_subset hF hQj with h1 | h1
      exacts [absurd h1 (hne 0), absurd h1 (hne 2)]
    · exact Or.inr ⟨hQj, hne⟩
  · push Not at hne
    exact Or.inl hne

/-! ### The fundamental points of `C'` -/

/-- **`C'` has multiplicity `n` at `P = [0 : 0 : 1]`.** -/
theorem mult_properTransform_fundamentalPoint_two (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) : mult (properTransform F) (fundamentalPoint 2) = n := by
  rw [Projective.mult_properTransform_fundamentalPoint_two hF (h.not_X_dvd 2),
    h.toNat_mult_eq_zero hF (i := 0) (by decide), h.toNat_mult_eq_zero hF (i := 1) (by decide)]
  rfl

/-- **`C'` has multiplicity `n - r` at `P' = [0 : 1 : 0]` and `P'' = [1 : 0 : 0]`**, with
`r = m_{[0:0:1]}(F)`. -/
theorem mult_properTransform_fundamentalPoint (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) {i : Fin 3} (hi : i ≠ 2) :
    mult (properTransform F) (fundamentalPoint i) =
      (n - (mult F (fundamentalPoint 2)).toNat : ℕ) := by
  fin_cases i
  · change mult _ (fundamentalPoint 0) = _
    rw [Projective.mult_properTransform_fundamentalPoint_zero hF (h.not_X_dvd 0),
      h.toNat_mult_eq_zero hF (i := 1) (by decide), Nat.sub_zero]
  · change mult _ (fundamentalPoint 1) = _
    rw [Projective.mult_properTransform_fundamentalPoint_one hF (h.not_X_dvd 1),
      h.toNat_mult_eq_zero hF (i := 0) (by decide), Nat.sub_zero]
  · exact absurd rfl hi

/-- **The leading form of `F'` at `P = [0 : 0 : 1]`** is `F(Y, X, 0)`. -/
theorem leadingFormAt_properTransform_single_two (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) :
    (properTransform F).leadingFormAt (Pi.single 2 1) =
      aeval (![X 1, X 0, 0] : Fin 3 → MvPolynomial (Fin 3) k) F := by
  have := X_pow_mul_leadingFormAt_properTransform_single_two hF (h.not_X_dvd 2)
  rwa [h.toNat_mult_eq_zero hF (i := 0) (by decide), h.toNat_mult_eq_zero hF (i := 1) (by decide),
    pow_zero, pow_zero, one_mul, one_mul] at this

/-- The leading form of `F'` at `[eᵢ]`, `i ≠ 2`, from the one at `[0 : 0 : 1]` by swapping the
variables `Xᵢ` and `Z`. -/
private theorem X_two_pow_mul_leadingFormAt_properTransform_single (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) {i : Fin 3} (hi : i ≠ 2) :
    X 2 ^ (mult F (fundamentalPoint 2)).toNat *
        (properTransform F).leadingFormAt (Pi.single i 1) =
      aeval (fun m ↦ rename (Equiv.swap i 2)
        ((![X 1, X 0, 0] : Fin 3 → MvPolynomial (Fin 3) k) (Equiv.swap i 2 m))) F := by
  set σ := Equiv.swap i 2
  have hσσ (p : MvPolynomial (Fin 3) k) : rename σ (rename σ p) = p := by
    rw [rename_rename]
    convert rename_id_apply p
    funext m
    exact Equiv.swap_apply_self _ _ _
  have hX : ¬ X 2 ∣ rename σ F := fun hd ↦ h.not_X_dvd i (by
    simpa [hσσ, σ] using map_dvd (rename σ) hd)
  have key := X_pow_mul_leadingFormAt_properTransform_single_two
    (hF.rename_isHomogeneous (f := σ)) hX
  have hm (m : Fin 3) :
      mult (rename σ F) (fundamentalPoint m) = mult F (fundamentalPoint (σ m)) := by
    have := mult_rename_fundamentalPoint hF σ (σ m)
    rwa [Equiv.swap_apply_self] at this
  have he : (Pi.single 2 1 : Fin 3 → k) ∘ σ = Pi.single i 1 := by
    funext m
    simp only [Function.comp_apply, Pi.single_apply, σ, Equiv.swap_apply_eq_iff,
      Equiv.swap_apply_right]
  have hXX : (X 0 ^ (mult F (fundamentalPoint (σ 0))).toNat *
      X 1 ^ (mult F (fundamentalPoint (σ 1))).toNat : MvPolynomial (Fin 3) k) =
      X i ^ (mult F (fundamentalPoint 2)).toNat := by
    fin_cases i
    · simp [σ, Equiv.swap_apply_of_ne_of_ne, h.toNat_mult_eq_zero hF (i := 1) (by decide)]
    · simp [σ, Equiv.swap_apply_of_ne_of_ne, h.toNat_mult_eq_zero hF (i := 0) (by decide)]
    · exact absurd rfl hi
  rw [hm, hm, hXX, properTransform_rename hF, leadingFormAt_rename σ.injective, he,
    aeval_rename] at key
  have := congrArg (rename σ) key
  rwa [map_mul, map_pow, rename_X, hσσ, ← AlgHom.comp_apply, comp_aeval, Equiv.swap_apply_left]
    at this

/-- **The leading form of `F'` at `P' = [0 : 1 : 0]`**, times `Z^r`, is `F(Z, 0, X)`. Writing
`F(X, 0, Z) = X^r H(X, Z)`, it is `H(Z, X)`. -/
theorem X_two_pow_mul_leadingFormAt_properTransform_single_one (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) :
    X 2 ^ (mult F (fundamentalPoint 2)).toNat *
        (properTransform F).leadingFormAt (Pi.single 1 1) =
      aeval (![X 2, 0, X 0] : Fin 3 → MvPolynomial (Fin 3) k) F := by
  rw [h.X_two_pow_mul_leadingFormAt_properTransform_single hF (by decide)]
  congr 2
  funext m
  fin_cases m <;> simp [Equiv.swap_apply_of_ne_of_ne]

/-- **The leading form of `F'` at `P'' = [1 : 0 : 0]`**, times `Z^r`, is `F(0, Z, Y)`. Writing
`F(0, Y, Z) = Y^r H(Y, Z)`, it is `H(Z, Y)`. -/
theorem X_two_pow_mul_leadingFormAt_properTransform_single_zero (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) :
    X 2 ^ (mult F (fundamentalPoint 2)).toNat *
        (properTransform F).leadingFormAt (Pi.single 0 1) =
      aeval (![0, X 2, X 1] : Fin 3 → MvPolynomial (Fin 3) k) F := by
  rw [h.X_two_pow_mul_leadingFormAt_properTransform_single hF (by decide)]
  congr 2
  funext m
  fin_cases m <;> simp [Equiv.swap_apply_of_ne_of_ne]

private theorem rename_swap_aeval (σ : Equiv.Perm (Fin 3)) (v w : Fin 3 → MvPolynomial (Fin 3) k)
    (hvw : ∀ m, w m = rename σ (v m)) :
    aeval w F = rename σ (aeval v F) := by
  rw [← AlgHom.comp_apply, comp_aeval]
  exact congrArg (aeval · F) (funext hvw)

/-- **The leading forms of `F'` at the fundamental points are squarefree**, for a curve in
excellent position over an algebraically closed field. -/
theorem squarefree_leadingFormAt_properTransform [IsAlgClosed k] (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) (i : Fin 3) :
    Squarefree ((properTransform F).leadingFormAt (Pi.single i 1)) := by
  have hX2 : (X 2 : MvPolynomial (Fin 3) k) ^ (mult F (fundamentalPoint 2)).toNat ≠ 0 :=
    pow_ne_zero _ (X_ne_zero 2)
  fin_cases i
  · obtain ⟨H, hH, hsq, -, -⟩ := h.restrict_X_zero_eq hF
    have key := h.X_two_pow_mul_leadingFormAt_properTransform_single_zero hF
    rw [rename_swap_aeval (Equiv.swap 1 2) ![0, X 1, X 2] _ (fun m ↦ by
      fin_cases m <;> simp), hH, map_mul, map_pow, rename_X,
      Equiv.swap_apply_left] at key
    exact (mul_left_cancel₀ hX2 key) ▸ (TauCeti.squarefree_map_iff (renameEquiv k _)).2 hsq
  · obtain ⟨H, hH, hsq, -, -⟩ := h.restrict_X_one_eq hF
    have key := h.X_two_pow_mul_leadingFormAt_properTransform_single_one hF
    rw [rename_swap_aeval (Equiv.swap 0 2) ![X 0, 0, X 2] _ (fun m ↦ by
      fin_cases m <;> simp), hH, map_mul, map_pow, rename_X,
      Equiv.swap_apply_left] at key
    exact (mul_left_cancel₀ hX2 key) ▸ (TauCeti.squarefree_map_iff (renameEquiv k _)).2 hsq
  · change Squarefree ((properTransform F).leadingFormAt (Pi.single 2 1))
    rw [h.leadingFormAt_properTransform_single_two hF, rename_swap_aeval (Equiv.swap 0 1)
      ![X 0, X 1, 0] _ (fun m ↦ by fin_cases m <;> simp)]
    exact (TauCeti.squarefree_map_iff (renameEquiv k _)).2 (h.squarefree_restrict_X_two hF).1

/-- The leading form of `C'` at each fundamental point is squarefree. -/
theorem squarefree_leadingForm_properTransform [IsAlgClosed k] (h : IsExcellentPosition F)
    (hF : F.IsHomogeneous n) (i : Fin 3) :
    Squarefree (leadingForm (properTransform F) (fundamentalPoint i)) := by
  rw [fundamentalPoint_def, (associated_leadingForm_mk (h.isHomogeneous_properTransform hF) _
    _).squarefree_iff]
  exact h.squarefree_leadingFormAt_properTransform hF i

/-- **The fundamental points of `C'` are ordinary** when they are multiple points, for a curve
in excellent position over an algebraically closed field. -/
theorem isOrdinaryMultiplePoint_properTransform_fundamentalPoint [IsAlgClosed k]
    (h : IsExcellentPosition F) (hF : F.IsHomogeneous n) {i : Fin 3}
    (hm : IsMultiplePoint (properTransform F) (fundamentalPoint i)) :
    IsOrdinaryMultiplePoint (properTransform F) (fundamentalPoint i) :=
  isOrdinaryMultiplePoint_def.2 ⟨hm, h.squarefree_leadingForm_properTransform hF i⟩

end IsExcellentPosition

end Excellent

end PlaneCurves.Projective

end
