/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.Algebra.MvPolynomial.Derivation
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Adjoint.RiemannRochSpace
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.CanonicalDivisor.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.CanonicalDivisor.Position
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.OrdinaryMultiplePoint
public import PlaneCurves.FieldTheory.FunctionField.KaehlerDifferential

/-!
# The differential `dx / f_y` of a plane curve

Let `C : F = 0` be an irreducible projective plane curve of degree `n`, with function field
`K = k(C)`, and let `Z = 0` not be a component of `C`. The affine coordinates
`x = X / Z`, `y = Y / Z` and the functions `f_x = F_X / Z^{n-1}`, `f_y = F_Y / Z^{n-1}` of `K`
are the values of `X`, `Y`, `F_X`, `F_Y` at the point `(X / Z, Y / Z, 1)` of `K³`
(`PlaneCurves.Projective.chartCoord`). Differentiating `F(x, y, 1) = 0` gives
`f_x dx + f_y dy = 0` in `Ω[K⁄k]`, and Fulton's differential `ω₀ = dx / f_y`
(`PlaneCurves.Projective.chartDifferential`) is also `-dy / f_x`.

In transverse position (`PlaneCurves.Projective.IsTransversePosition`) and for `n ≥ 2`, the order
of `ω₀` at every place `P` is at most the coefficient at `P` of `(n - 3) div Z - E`, `E` the
adjoint divisor:

* over an affine ordinary multiple point `Q = [a : b : 1]` of multiplicity `r`, the line
  `Y - b Z` is not tangent, so `y - b` is a uniformizer, and `ord_P(f_x) ≥ r - 1`; so
  `ord_P(ω₀) = -ord_P(f_x) ≤ -(r - 1)`;
* over an affine simple point, one of `x - a` and `y - b` is a uniformizer, and `f_x`, `f_y` have
  no pole; so `ord_P(ω₀) ≤ 0`;
* over a point of `Z = 0`, `1 / y` is a uniformizer and `ord_P(f_x) ≥ -(n - 1)`; so
  `ord_P(ω₀) ≤ n - 3`.

## Main definitions

* `PlaneCurves.Projective.chartCoord hF hi`: the point `(X₀ / Xᵢ, X₁ / Xᵢ, X₂ / Xᵢ)` of `k(C)³`.
* `PlaneCurves.Projective.chartDifferential hF h2`: the differential `dx / f_y`.

## Main results

* `PlaneCurves.Projective.aeval_chartCoord_eq_formQuotient`: a form `G` of degree `m` evaluated
  at `chartCoord` is the quotient `G / Xᵢᵐ`.
* `PlaneCurves.Projective.ord_aeval_chartCoord`: its order at a place `P` is
  `ord_P(G) - m ord_P(Xᵢ)`.
* `PlaneCurves.Projective.fx_smul_D_add_fy_smul_D`: `f_x dx + f_y dy = 0`.
* `PlaneCurves.Projective.chartDifferential_eq`: `dx / f_y = -dy / f_x`.
* `PlaneCurves.Projective.chartDifferential_ne_zero`: `dx / f_y ≠ 0`.
* `coeff_kaehlerDifferentialDivisor_chartDifferential_le_of_isOrdinaryMultiplePoint`,
  `coeff_kaehlerDifferentialDivisor_chartDifferential_le_of_isSimplePoint`,
  `coeff_kaehlerDifferentialDivisor_chartDifferential_le_of_eval_X_two_eq_zero`:
  the bounds on the orders of `dx / f_y`.
* `PlaneCurves.Projective.kaehlerDifferentialDivisor_chartDifferential`: when the multiple points
  of `C` are ordinary, `div (dx / f_y) = (n - 3) div Z - E`, since both sides have degree `2g - 2`.
* `PlaneCurves.Projective.nonneg_kaehlerDifferentialDivisor_iff`: the differentials without poles
  are the `H(x, y, 1) dx / f_y` for the adjoints `H` of degree `n - 3`.
* `PlaneCurves.Projective.canonical_eq_formDivisor_sub_adjointDivisor`: canonical divisors of a
  plane curve are cut out by adjoints of degree `n - 3`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §8.5
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti KaehlerDifferential
open TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {n m : ℕ}
  {hF : F.IsHomogeneous n} [Fact (Irreducible F)] {i : Fin 3} {G : MvPolynomial (Fin 3) k}

/-! ### The affine coordinates of a chart -/

variable (hF) in
/-- The point `(X₀ / Xᵢ, X₁ / Xᵢ, X₂ / Xᵢ)` of `k(C)³`, for a coordinate `Xᵢ` with `F ∤ Xᵢ`: its
entries other than the `i`-th are the affine coordinates of the chart `Xᵢ ≠ 0`. -/
noncomputable def chartCoord (hi : ¬ F ∣ X i) (j : Fin 3) : functionField hF :=
  functionField.mk (isHomogeneous_X k j) (isHomogeneous_X k i)
    (projectivePlaneCurve.notMem_ideal_of_not_dvd hF hi)

theorem chartCoord_def (hi : ¬ F ∣ X i) (j : Fin 3) :
    chartCoord hF hi j = functionField.mk (isHomogeneous_X k j) (isHomogeneous_X k i)
      (projectivePlaneCurve.notMem_ideal_of_not_dvd hF hi) :=
  (rfl)

/-- The `i`-th entry of `chartCoord` in the chart `Xᵢ ≠ 0` is `1`. -/
@[simp]
theorem chartCoord_self (hi : ¬ F ∣ X i) : chartCoord hF hi i = 1 :=
  functionField.mk_self _ _

/-- A form `G` of degree `m` evaluated at `chartCoord` is the fraction `G / Xᵢᵐ`. -/
theorem aeval_chartCoord (hi : ¬ F ∣ X i) (hG : G.IsHomogeneous m) :
    aeval (chartCoord hF hi) G = functionField.mk hG (isHomogeneous_X_pow i m)
      (projectivePlaneCurve.pow_notMem_ideal hF hi m) :=
  functionField.aeval_mk_X _ hG

/-- A form `G` of degree `m` with `F ∤ G` evaluated at `chartCoord` is the quotient `G / Xᵢᵐ`. -/
theorem aeval_chartCoord_eq_formQuotient (hi : ¬ F ∣ X i) (hG : G.IsHomogeneous m)
    (hFG : ¬ F ∣ G) :
    aeval (chartCoord hF hi) G =
      formQuotient hF hG (isHomogeneous_X_pow i m) hFG (not_dvd_pow_of_not_dvd hi m) := by
  rw [aeval_chartCoord hi hG, coe_formQuotient]

/-- `F` vanishes at `chartCoord`. -/
@[simp]
theorem aeval_chartCoord_self (hi : ¬ F ∣ X i) : aeval (chartCoord hF hi) F = 0 := by
  rw [aeval_chartCoord hi hF, functionField.mk_eq_zero_iff, projectivePlaneCurve.mem_ideal_iff]

/-- A form `G` vanishes at `chartCoord` iff `F ∣ G`. -/
theorem aeval_chartCoord_eq_zero_iff (hi : ¬ F ∣ X i) (hG : G.IsHomogeneous m) :
    aeval (chartCoord hF hi) G = 0 ↔ F ∣ G := by
  rw [aeval_chartCoord hi hG, functionField.mk_eq_zero_iff, projectivePlaneCurve.mem_ideal_iff]

/-- **The order of `G / Xᵢᵐ`.** At a place `P`, a form `G` of degree `m` with `F ∤ G`, evaluated
at `chartCoord`, has order `ord_P(G) - m ord_P(Xᵢ)`. -/
theorem ord_aeval_chartCoord [IsAlgClosed k] (hi : ¬ F ∣ X i) (hG : G.IsHomogeneous m)
    (hFG : ¬ F ∣ G) (P : Place k (functionField hF)) :
    P.ord (aeval (chartCoord hF hi) G) =
      (formDivisor hF hG).coeff P - m * (formDivisor hF (isHomogeneous_X k i)).coeff P := by
  rw [aeval_chartCoord_eq_formQuotient hi hG hFG,
    ← Divisor.coeff_principal (functionField.isFunctionField hF), principal_formQuotient,
    WeilDivisor.coeff_sub,
    formDivisor_congr _ ((isHomogeneous_X k i).pow m) rfl, formDivisor_pow _ hi,
    WeilDivisor.coeff_nsmul]

/-! ### The relation `f_x dx + f_y dy = 0` and the differential `dx / f_y` -/

/-- **`f_x dx + f_y dy = 0`.** Differentiating `F(x, y, 1) = 0`, for the affine coordinates
`x = X / Z`, `y = Y / Z` and `f_x = F_X / Z^{n-1}`, `f_y = F_Y / Z^{n-1}`, gives
`f_x dx + f_y dy = 0` in `Ω[k(C)⁄k]`. -/
theorem fx_smul_D_add_fy_smul_D (h2 : ¬ F ∣ X 2) :
    aeval (chartCoord hF h2) (pderiv 0 F) • D k (functionField hF) (chartCoord hF h2 0) +
      aeval (chartCoord hF h2) (pderiv 1 F) • D k (functionField hF) (chartCoord hF h2 1) =
        0 := by
  have h : D k (functionField hF) (aeval (chartCoord hF h2) F) = 0 := by
    rw [aeval_chartCoord_self, Derivation.map_zero]
  rwa [Derivation.map_aeval_mvPolynomial, Fin.sum_univ_three, chartCoord_self,
    Derivation.map_one_eq_zero, smul_zero, add_zero] at h

variable (hF) in
/-- **The differential `dx / f_y`** of `k(C)`, for `x = X / Z` and `f_y = F_Y / Z^{n-1}`
(Fulton, §8.5). It is `0` when `F_Y` vanishes on `C`. -/
noncomputable def chartDifferential (h2 : ¬ F ∣ X 2) : Ω[functionField hF⁄k] :=
  (aeval (chartCoord hF h2) (pderiv 1 F))⁻¹ • D k (functionField hF) (chartCoord hF h2 0)

theorem chartDifferential_def (h2 : ¬ F ∣ X 2) :
    chartDifferential hF h2 =
      (aeval (chartCoord hF h2) (pderiv 1 F))⁻¹ • D k (functionField hF) (chartCoord hF h2 0) :=
  (rfl)

/-- **`dx / f_y = -dy / f_x`**, when `F` divides neither `F_X` nor `F_Y`. -/
theorem chartDifferential_eq (h2 : ¬ F ∣ X 2) (h0 : ¬ F ∣ pderiv 0 F) (h1 : ¬ F ∣ pderiv 1 F) :
    chartDifferential hF h2 =
      -((aeval (chartCoord hF h2) (pderiv 0 F))⁻¹ •
        D k (functionField hF) (chartCoord hF h2 1)) := by
  have ha := (aeval_chartCoord_eq_zero_iff (hF := hF) h2 hF.pderiv).not.2 h0
  have hb := (aeval_chartCoord_eq_zero_iff (hF := hF) h2 hF.pderiv).not.2 h1
  have h := fx_smul_D_add_fy_smul_D (hF := hF) h2
  rw [add_eq_zero_iff_eq_neg] at h
  rw [chartDifferential_def, ← inv_smul_smul₀ ha (D k _ (chartCoord hF h2 0)), h, smul_neg,
    smul_neg, smul_smul]
  congr 1
  refine (mul_smul (_ : functionField hF) _ (_ : Ω[functionField hF⁄k])).symm.trans ?_
  congr 1
  field_simp

/-- The derivation `d` of `k(C)` vanishes if it vanishes at `x = X / Z` and `y = Y / Z`:
`k(C)` is generated by `x` and `y`. -/
private theorem D_eq_zero_of_D_chartCoord_eq_zero (h2 : ¬ F ∣ X 2)
    (h0 : D k (functionField hF) (chartCoord hF h2 0) = 0)
    (h1 : D k (functionField hF) (chartCoord hF h2 1) = 0) (z : functionField hF) :
    D k (functionField hF) z = 0 := by
  have hp (p : MvPolynomial (Fin 3) k) :
      D k (functionField hF) (aeval (chartCoord hF h2) p) = 0 := by
    simp [Derivation.map_aeval_mvPolynomial, Fin.sum_univ_three, h0, h1]
  obtain ⟨m, f, g, hf, hg, hgI, rfl⟩ := functionField.exists_eq_mk z
  have hz : functionField.mk hf hg hgI =
      aeval (chartCoord hF h2) f / aeval (chartCoord hF h2) g :=
    functionField.mk_eq_aeval_div_aeval (projectivePlaneCurve.notMem_ideal_of_not_dvd hF h2) hf hg
      hgI
  rw [hz, Derivation.leibniz_div, hp, hp, smul_zero, smul_zero, sub_zero, smul_zero]

/-- **`dx / f_y ≠ 0`**, when `F ∤ F_Y`: otherwise `dx = 0`, so `dy = 0` by
`f_x dx + f_y dy = 0`, and then every differential vanishes, since `x` and `y` generate `k(C)`;
but the differential of a separating element is nonzero. -/
theorem chartDifferential_ne_zero [PerfectField k] (h2 : ¬ F ∣ X 2) (h1 : ¬ F ∣ pderiv 1 F) :
    chartDifferential hF h2 ≠ 0 := by
  have hb := (aeval_chartCoord_eq_zero_iff (hF := hF) h2 hF.pderiv).not.2 h1
  intro h
  replace h := (smul_eq_zero.1 h).resolve_left (inv_ne_zero hb)
  have h' := fx_smul_D_add_fy_smul_D (hF := hF) h2
  rw [h, smul_zero, zero_add] at h'
  replace h' := (smul_eq_zero.1 h').resolve_left hb
  obtain ⟨t, ht, hsep⟩ :=
    (functionField.isFunctionField hF).exists_transcendental_and_isSeparable_adjoin_of_perfectField
  exact D_ne_zero_of_separating ht (D_eq_zero_of_D_chartCoord_eq_zero h2 h h' t)

/-- The differential of `X_j / Z - a`, the line `X_j - a Z` evaluated at `chartCoord`. -/
private theorem D_aeval_chartCoord_sub (h2 : ¬ F ∣ X 2) (j : Fin 3) (a : k) :
    D k (functionField hF) (aeval (chartCoord hF h2) (X j - C a * X 2)) =
      D k (functionField hF) (chartCoord hF h2 j) := by
  simp [chartCoord_self]

/-! ### The orders of `dx / f_y` -/

section Orders

variable [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- A line is not divisible by a form of degree at least `2`. -/
private theorem not_dvd_of_isHomogeneous_one (hF : F.IsHomogeneous n) (hn : 2 ≤ n)
    {L : MvPolynomial (Fin 3) k}
    (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) : ¬ F ∣ L := fun hd ↦ by
  have hle := totalDegree_le_of_dvd_of_isDomain hd hL0
  rw [hF.totalDegree (Fact.out : Irreducible F).ne_zero, hL.totalDegree hL0] at hle
  omega

/-- At a place over an affine point, `Z` has order `0`. -/
private theorem coeff_formDivisor_X_two_eq_zero (h2 : ¬ F ∣ X 2) {P : Place k (functionField hF)}
    (hP : eval (center hF P).1.rep (X 2) ≠ 0) :
    (formDivisor hF (isHomogeneous_X k 2)).coeff P = 0 :=
  (coeff_formDivisor_eq_zero_iff _ h2).2 hP

/-- **The order of `dx / f_y` through a uniformizer `t` with `dt = dy`**: it is `-ord_P(f_x)`. -/
private theorem coeff_kaehlerDifferentialDivisor_chartDifferential_of_D_eq_D_one
    (h2 : ¬ F ∣ X 2) (h0 : ¬ F ∣ pderiv 0 F) (h1 : ¬ F ∣ pderiv 1 F)
    {P : Place k (functionField hF)} {t : functionField hF} (ht : P.ord t = 1)
    (hDt : D k (functionField hF) t = D k (functionField hF) (chartCoord hF h2 1)) :
    (kaehlerDifferentialDivisor (functionField.isFunctionField hF)
      isIntegrallyClosedIn_of_isAlgClosed
      (chartDifferential hF h2) (chartDifferential_ne_zero h2 h1)).coeff P =
      -P.ord (aeval (chartCoord hF h2) (pderiv 0 F)) := by
  rw [coeff_kaehlerDifferentialDivisor_of_eq_smul_D _ _ ht _
    (by rw [chartDifferential_eq h2 h0 h1, hDt]
        exact (neg_smul (_ : functionField hF) (_ : Ω[functionField hF⁄k])).symm),
    Place.ord_neg, Place.ord_inv]

/-- **The order of `dx / f_y` through a uniformizer `t` with `dt = dx`**: it is `-ord_P(f_y)`. -/
private theorem coeff_kaehlerDifferentialDivisor_chartDifferential_of_D_eq_D_zero
    (h2 : ¬ F ∣ X 2) (h1 : ¬ F ∣ pderiv 1 F)
    {P : Place k (functionField hF)} {t : functionField hF} (ht : P.ord t = 1)
    (hDt : D k (functionField hF) t = D k (functionField hF) (chartCoord hF h2 0)) :
    (kaehlerDifferentialDivisor (functionField.isFunctionField hF)
      isIntegrallyClosedIn_of_isAlgClosed
      (chartDifferential hF h2) (chartDifferential_ne_zero h2 h1)).coeff P =
      -P.ord (aeval (chartCoord hF h2) (pderiv 1 F)) := by
  rw [coeff_kaehlerDifferentialDivisor_of_eq_smul_D _ _ ht _
    (by rw [chartDifferential_def, hDt]), Place.ord_inv]

variable (hpos : IsTransversePosition F) (hn : 2 ≤ n)
include hpos hn

/-- **The order of `dx / f_y` over an affine ordinary multiple point.** In transverse position,
at a place `P` over an ordinary multiple point `Q = [a : b : 1]` of multiplicity `r`,
`ord_P(dx / f_y) ≤ -(r - 1)`, the coefficient of `(n - 3) div Z - E` at `P`. The line `Y - b Z`
is not tangent at `Q`, since it passes through `[1 : 0 : 0]`, so `y - b` is a uniformizer at `P`,
while `ord_P(f_x) ≥ m_Q(F_X) ≥ r - 1`. -/
theorem coeff_kaehlerDifferentialDivisor_chartDifferential_le_of_isOrdinaryMultiplePoint
    {P : Place k (functionField hF)} (hP2 : eval (center hF P).1.rep (X 2) ≠ 0)
    (hP : IsOrdinaryMultiplePoint F (center hF P).1) :
    (kaehlerDifferentialDivisor (functionField.isFunctionField hF)
      isIntegrallyClosedIn_of_isAlgClosed
      (chartDifferential hF (hpos.not_dvd_X hF hn 2))
      (chartDifferential_ne_zero _ (hpos.not_dvd_pderiv_one hF hn))).coeff P ≤
      (((n : ℤ) - 3) • formDivisor hF (isHomogeneous_X k 2) - adjointDivisor hF).coeff P := by
  have h2 := hpos.not_dvd_X hF hn 2
  have h0 := hpos.not_dvd_pderiv_zero hF (by omega)
  set Q := (center hF P).1 with hQ
  have hQ2 : Q.rep 2 ≠ 0 := by simpa using hP2
  -- The line `Y - b Z` through `Q` is not tangent there, so `y - b` is a uniformizer.
  set L : MvPolynomial (Fin 3) k := X 1 - C (Q.rep 1 / Q.rep 2) * X 2
  have hL : L.IsHomogeneous 1 :=
    (isHomogeneous_X k 1).sub ((isHomogeneous_C _ _).mul (isHomogeneous_X k 2))
  have hL0 : L ≠ 0 := fun h ↦ by simpa [L] using congrArg (eval ![0, 1, 0]) h
  have hLQ : eval Q.rep L = 0 := by simp [L, hQ2]
  have hLT : ¬IsTangentAt F Q L := fun hT ↦
    hpos.not_isTangentAt Q (isOrdinaryMultiplePoint_def.1 hP).1 L hT (by simp [L])
  have hLP : (formDivisor hF hL).coeff P = 1 := by
    rw [coeff_formDivisor_eq_untopD,
      ordForm_eq_one_of_not_isTangentAt hP hL hL0 hLQ hLT (mem_placesOver_center P)]
    rfl
  have ht : P.ord (aeval (chartCoord hF h2) L) = 1 := by
    rw [ord_aeval_chartCoord h2 hL (not_dvd_of_isHomogeneous_one hF hn hL hL0), hLP,
      coeff_formDivisor_X_two_eq_zero h2 hP2]
    simp
  rw [coeff_kaehlerDifferentialDivisor_chartDifferential_of_D_eq_D_one h2 h0
    (hpos.not_dvd_pderiv_one hF hn) ht
    (D_aeval_chartCoord_sub h2 1 _), ord_aeval_chartCoord h2 hF.pderiv h0,
    coeff_formDivisor_X_two_eq_zero h2 hP2, WeilDivisor.coeff_sub, WeilDivisor.coeff_zsmul,
    coeff_formDivisor_X_two_eq_zero h2 hP2, coeff_adjointDivisor]
  -- `ord_P(F_X) ≥ m_Q(F_X) ≥ m_Q(F) - 1`.
  have hF0 : F ≠ 0 := (Fact.out : Irreducible F).ne_zero
  have hX0 := hpos.pderiv_zero_ne_zero hF (by omega)
  have hle := natCast_toNat_mult_le_ordForm hP hF.pderiv hX0 (mem_placesOver_center P)
  rw [← coeff_formDivisor hF.pderiv h0] at hle
  have hm := mult_sub_one_le_mult_pderiv F Q 0
  rw [← natCast_toNat_mult hF0, ← natCast_toNat_mult hX0] at hm
  have hm' : (mult F Q).toNat - 1 ≤ (mult (pderiv 0 F) Q).toNat := by exact_mod_cast hm
  have hle' : ((mult (pderiv 0 F) Q).toNat : ℤ) ≤
      (formDivisor hF (hF.pderiv (i := 0))).coeff P := by
    exact_mod_cast hle
  rw [← hQ]
  simp only [mul_zero, sub_zero]
  omega

/-- **The order of `dx / f_y` over an affine simple point.** In transverse position, at a place
`P` over a simple point `Q = [a : b : 1]`, `ord_P(dx / f_y) ≤ 0`, the coefficient of
`(n - 3) div Z - E` at `P`. One of the lines `X - a Z` and `Y - b Z` is not the tangent at `Q`, so
`x - a` or `y - b` is a uniformizer at `P`, and `f_x`, `f_y` have no pole at `P`. -/
theorem coeff_kaehlerDifferentialDivisor_chartDifferential_le_of_isSimplePoint
    {P : Place k (functionField hF)} (hP2 : eval (center hF P).1.rep (X 2) ≠ 0)
    (hP : IsSimplePoint F (center hF P).1) :
    (kaehlerDifferentialDivisor (functionField.isFunctionField hF)
      isIntegrallyClosedIn_of_isAlgClosed
      (chartDifferential hF (hpos.not_dvd_X hF hn 2))
      (chartDifferential_ne_zero _ (hpos.not_dvd_pderiv_one hF hn))).coeff P ≤
      (((n : ℤ) - 3) • formDivisor hF (isHomogeneous_X k 2) - adjointDivisor hF).coeff P := by
  have h2 := hpos.not_dvd_X hF hn 2
  have h0 := hpos.not_dvd_pderiv_zero hF (by omega)
  have h1 := hpos.not_dvd_pderiv_one hF hn
  set Q := (center hF P).1 with hQ
  have hQ2 : Q.rep 2 ≠ 0 := by simpa using hP2
  -- A line `X_j - c Z` through `Q` that is not tangent there gives a uniformizer.
  have hline (j : Fin 3) (hj : j ≠ 2)
      (hT : ¬IsTangentAt F Q (X j - C (Q.rep j / Q.rep 2) * X 2)) :
      P.ord (aeval (chartCoord hF h2) (X j - C (Q.rep j / Q.rep 2) * X 2)) = 1 := by
    have hL : (X j - C (Q.rep j / Q.rep 2) * X 2 : MvPolynomial (Fin 3) k).IsHomogeneous 1 :=
      (isHomogeneous_X k j).sub ((isHomogeneous_C _ _).mul (isHomogeneous_X k 2))
    have hL0 : (X j - C (Q.rep j / Q.rep 2) * X 2 : MvPolynomial (Fin 3) k) ≠ 0 := fun h ↦ by
      simpa [Pi.single_apply, hj.symm] using congrArg (eval (Pi.single j 1)) h
    have hLQ : eval Q.rep (X j - C (Q.rep j / Q.rep 2) * X 2) = 0 := by
      simp [div_mul_cancel₀ _ hQ2]
    have hFL := not_dvd_of_isHomogeneous_one hF hn hL hL0
    rw [ord_aeval_chartCoord h2 hL hFL, coeff_formDivisor_of_isSimplePoint hL hFL hP, ← hQ,
      (intersectionNumber_eq_one_iff hF hL hL0 hLQ).2 ⟨hP, hT⟩,
      coeff_formDivisor_X_two_eq_zero h2 hP2]
    simp
  have hR : (((n : ℤ) - 3) • formDivisor hF (isHomogeneous_X k 2) -
      adjointDivisor hF).coeff P = 0 := by
    rw [WeilDivisor.coeff_sub, WeilDivisor.coeff_zsmul, coeff_formDivisor_X_two_eq_zero h2 hP2,
      coeff_adjointDivisor, ← hQ, isSimplePoint_def.1 hP]
    simp
  rw [hR]
  by_cases hT : IsTangentAt F Q (X 1 - C (Q.rep 1 / Q.rep 2) * X 2)
  · -- Then `X - a Z` is not tangent: `Q` has only one tangent.
    have hT0 : ¬IsTangentAt F Q (X 0 - C (Q.rep 0 / Q.rep 2) * X 2) := fun hT0 ↦ by
      obtain ⟨u, hu⟩ := (hP.associated_tangentLine_of_isTangentAt hF hT0).trans
        (hP.associated_tangentLine_of_isTangentAt hF hT).symm
      simpa using congrArg (eval ![0, 1, 0]) hu
    rw [coeff_kaehlerDifferentialDivisor_chartDifferential_of_D_eq_D_zero h2 h1
      (hline 0 (by decide) hT0) (D_aeval_chartCoord_sub h2 0 _),
      ord_aeval_chartCoord h2 hF.pderiv h1, coeff_formDivisor_X_two_eq_zero h2 hP2]
    have := (WeilDivisor.nonneg_iff _).1 (formDivisor_nonneg (hF := hF) (hF.pderiv (i := 1))) P
    simp only [mul_zero, sub_zero]
    omega
  · rw [coeff_kaehlerDifferentialDivisor_chartDifferential_of_D_eq_D_one h2 h0 h1
      (hline 1 (by decide) hT) (D_aeval_chartCoord_sub h2 1 _),
      ord_aeval_chartCoord h2 hF.pderiv h0, coeff_formDivisor_X_two_eq_zero h2 hP2]
    have := (WeilDivisor.nonneg_iff _).1 (formDivisor_nonneg (hF := hF) (hF.pderiv (i := 0))) P
    simp only [mul_zero, sub_zero]
    omega

/-- **The order of `dx / f_y` over a point of `Z = 0`.** In transverse position, at a place `P`
over a point `Q` of `C` on `Z = 0`, `ord_P(dx / f_y) ≤ n - 3`, the coefficient of
`(n - 3) div Z - E` at `P`. The point `Q = [a : 1 : 0]` is simple and `ord_P(Z) = 1`, so
`1 / y` is a uniformizer at `P`, `dy` has order `-2`, and `ord_P(f_x) ≥ -(n - 1)`. -/
theorem coeff_kaehlerDifferentialDivisor_chartDifferential_le_of_eval_X_two_eq_zero
    {P : Place k (functionField hF)} (hP2 : eval (center hF P).1.rep (X 2) = 0) :
    (kaehlerDifferentialDivisor (functionField.isFunctionField hF)
      isIntegrallyClosedIn_of_isAlgClosed
      (chartDifferential hF (hpos.not_dvd_X hF hn 2))
      (chartDifferential_ne_zero _ (hpos.not_dvd_pderiv_one hF hn))).coeff P ≤
      (((n : ℤ) - 3) • formDivisor hF (isHomogeneous_X k 2) - adjointDivisor hF).coeff P := by
  have h2 := hpos.not_dvd_X hF hn 2
  have h0 := hpos.not_dvd_pderiv_zero hF (by omega)
  have h1 := hpos.not_dvd_pderiv_one hF hn
  set Q := (center hF P).1 with hQ
  have hQZ : Q ∈ zeroLocus {F, X 2} := by
    refine mem_zeroLocus_pair_iff.2 ⟨?_, mem_zeroLocus_X_iff.2 (by simpa using hP2)⟩
    rw [mem_zeroLocus_iff_eval_rep (by simpa using ⟨n, hF⟩)]
    simpa using (mem_zeroLocus_ideal_iff hF).1 (center hF P).2
  have hs := hpos.isSimplePoint hF hQZ
  -- `ord_P(Z) = 1` and `ord_P(Y) = 0`, so `ord_P(y) = -1`.
  have hZ1 : (formDivisor hF (isHomogeneous_X k 2)).coeff P = 1 := by
    rw [coeff_formDivisor_of_isSimplePoint _ h2 hs, ← hQ, hpos.intersectionNumber_X_two Q hQZ]
    rfl
  have hY0 : (formDivisor hF (isHomogeneous_X k 1)).coeff P = 0 :=
    (coeff_formDivisor_eq_zero_iff _ (hpos.not_dvd_X hF hn 1)).2
      (by simpa using hpos.eval_one_ne_zero hF hQZ)
  have hy : P.ord (chartCoord hF h2 1) = -1 := by
    have := ord_aeval_chartCoord h2 (isHomogeneous_X k 1) (hpos.not_dvd_X hF hn 1) P
    rw [aeval_X, hY0, hZ1] at this
    simpa using this
  have hy0 : chartCoord hF h2 1 ≠ 0 := fun h ↦ by
    rw [h, Place.ord_zero] at hy
    omega
  have ht : P.ord (chartCoord hF h2 1)⁻¹ = 1 := by
    rw [Place.ord_inv, hy, neg_neg]
  -- `dx / f_y = -dy / f_x = (y² / f_x) d(1 / y)`.
  have hc : ((aeval (chartCoord hF h2) (pderiv 0 F))⁻¹ * chartCoord hF h2 1 ^ 2) *
      -((chartCoord hF h2 1)⁻¹ ^ 2) = -(aeval (chartCoord hF h2) (pderiv 0 F))⁻¹ := by
    field_simp
  have hω : chartDifferential hF h2 =
      ((aeval (chartCoord hF h2) (pderiv 0 F))⁻¹ * chartCoord hF h2 1 ^ 2) •
        D k (functionField hF) (chartCoord hF h2 1)⁻¹ := by
    rw [chartDifferential_eq h2 h0 h1, Derivation.leibniz_inv,
      ← mul_smul (_ : functionField hF) _ (_ : Ω[functionField hF⁄k]), hc]
    exact (neg_smul (_ : functionField hF) (_ : Ω[functionField hF⁄k])).symm
  have ha := (aeval_chartCoord_eq_zero_iff (hF := hF) h2 hF.pderiv).not.2 h0
  rw [coeff_kaehlerDifferentialDivisor_of_eq_smul_D _ _ ht _ hω,
    P.ord_mul (inv_ne_zero ha) (pow_ne_zero 2 hy0), Place.ord_inv, Place.ord_pow, hy,
    ord_aeval_chartCoord h2 hF.pderiv h0, hZ1, WeilDivisor.coeff_sub, WeilDivisor.coeff_zsmul,
    hZ1, coeff_adjointDivisor, ← hQ, isSimplePoint_def.1 hs]
  have := (WeilDivisor.nonneg_iff _).1 (formDivisor_nonneg (hF := hF) (hF.pderiv (i := 0))) P
  simp only [ENat.toNat_one, Nat.sub_self, Nat.cast_zero, sub_zero, mul_one]
  push_cast [Nat.cast_sub (show 1 ≤ n by omega)]
  omega

end Orders

/-! ### The divisor of `dx / f_y` and the holomorphic differentials -/

section Divisor

variable [IsAlgClosed k] (hord : ∀ P, IsMultiplePoint F P → IsOrdinaryMultiplePoint F P)
include hord

section Transverse

variable (hpos : IsTransversePosition F) (hn : 2 ≤ n)
include hpos hn

/-- **`div (dx / f_y) ≤ (n - 3) div Z - E`.** In transverse position, for `n ≥ 2` and a curve
whose multiple points are ordinary, the divisor of `dx / f_y` is at most `(n - 3) div Z - E`,
`E` the adjoint divisor. -/
theorem kaehlerDifferentialDivisor_chartDifferential_le :
    kaehlerDifferentialDivisor (functionField.isFunctionField hF)
        isIntegrallyClosedIn_of_isAlgClosed
        (chartDifferential hF (hpos.not_dvd_X hF hn 2))
        (chartDifferential_ne_zero _ (hpos.not_dvd_pderiv_one hF hn)) ≤
      ((n : ℤ) - 3) • formDivisor hF (isHomogeneous_X k 2) - adjointDivisor hF := by
  refine WeilDivisor.le_iff.2 fun P ↦ ?_
  by_cases hP2 : eval (center hF P).1.rep (X 2) = 0
  · exact coeff_kaehlerDifferentialDivisor_chartDifferential_le_of_eval_X_two_eq_zero hpos hn hP2
  have hC : (center hF P).1 ∈ zeroLocus {F} := by
    rw [mem_zeroLocus_iff_eval_rep (by simpa using ⟨n, hF⟩)]
    simpa using (mem_zeroLocus_ideal_iff hF).1 (center hF P).2
  rcases isSimplePoint_or_isMultiplePoint hF hC with hs | hm
  · exact coeff_kaehlerDifferentialDivisor_chartDifferential_le_of_isSimplePoint hpos hn hP2 hs
  · exact coeff_kaehlerDifferentialDivisor_chartDifferential_le_of_isOrdinaryMultiplePoint hpos hn
      hP2 (hord _ hm)

/-- **The divisor of `dx / f_y`** (Fulton, §8.5): in transverse position, for `n ≥ 2` and a curve
whose multiple points are ordinary, `div (dx / f_y) = (n - 3) div Z - E`, `E` the adjoint
divisor. Both sides have degree `2g - 2`, and the left one is at most the right one. -/
theorem kaehlerDifferentialDivisor_chartDifferential :
    kaehlerDifferentialDivisor (functionField.isFunctionField hF)
        isIntegrallyClosedIn_of_isAlgClosed
        (chartDifferential hF (hpos.not_dvd_X hF hn 2))
        (chartDifferential_ne_zero _ (hpos.not_dvd_pderiv_one hF hn)) =
      ((n : ℤ) - 3) • formDivisor hF (isHomogeneous_X k 2) - adjointDivisor hF := by
  have hK := functionField.isFunctionField hF
  have hle := kaehlerDifferentialDivisor_chartDifferential_le (hF := hF) hord hpos hn
  have h0 := (Divisor.degree_eq_zero_iff hK (sub_nonneg.2 hle)).1 (by
    rw [map_sub, degree_zsmul_formDivisor_sub_adjointDivisor hord _ (hpos.not_dvd_X hF hn 2),
      (isRiemannRochDivisor_kaehlerDifferentialDivisor hK _ _ _).degree_eq hK
        isIntegrallyClosedIn_of_isAlgClosed, sub_self])
  exact (sub_eq_zero.1 h0).symm

end Transverse

/-- **The holomorphic differentials of a plane curve** (Fulton, §8.5): in transverse position,
for `n ≥ 3` and a curve whose multiple points are ordinary, a Kähler differential `ω` has no pole
exactly when `ω = H(x, y, 1) dx / f_y` for an adjoint `H` of degree `n - 3`. -/
theorem nonneg_kaehlerDifferentialDivisor_iff (hpos : IsTransversePosition F) (hn : 3 ≤ n)
    (ω : Ω[functionField hF⁄k]) :
    (∀ hω : ω ≠ 0, 0 ≤ kaehlerDifferentialDivisor (functionField.isFunctionField hF)
        isIntegrallyClosedIn_of_isAlgClosed ω hω) ↔
      ∃ H ∈ adjointSubmodule F (n - 3),
        ω = aeval (chartCoord hF (hpos.not_dvd_X hF (Nat.le_of_succ_le hn) 2)) H •
          chartDifferential hF (hpos.not_dvd_X hF (Nat.le_of_succ_le hn) 2) := by
  have h2n : 2 ≤ n := Nat.le_of_succ_le hn
  have hK := functionField.isFunctionField hF
  have h2 := hpos.not_dvd_X hF h2n 2
  have hω₀ := chartDifferential_ne_zero (hF := hF) h2 (hpos.not_dvd_pderiv_one hF h2n)
  have hZ : (X 2 : MvPolynomial (Fin 3) k).IsHomogeneous 1 := isHomogeneous_X k 2
  -- `G ↦ G / Z^{n-3}` is `G ↦ G(x, y, 1)`.
  have hcoe (G : adjointSubmodule F (n - 3)) :
      (adjointToRiemannRochSpace hF hord hZ h2 G : functionField hF) =
        aeval (chartCoord hF h2) (G : MvPolynomial (Fin 3) k) := by
    rw [coe_adjointToRiemannRochSpace_apply hord hZ h2 (isHomogeneous_X_pow 2 (n - 3)) G
      (projectivePlaneCurve.pow_notMem_ideal hF h2 _),
      aeval_chartCoord h2 (mem_adjointSubmodule_iff.1 G.2).1]
  -- `h dx / f_y` has no pole iff `h ∈ L((n - 3) div Z - E)`.
  have key (h : functionField hF) (hh : h ≠ 0) :
      0 ≤ kaehlerDifferentialDivisor hK isIntegrallyClosedIn_of_isAlgClosed
          (h • chartDifferential hF h2) (smul_ne_zero hh hω₀) ↔
        h ∈ riemannRochSpace ((n - 3) • formDivisor hF hZ - adjointDivisor hF) := by
    have hE : (n - 3) • formDivisor hF hZ = ((n : ℤ) - 3) • formDivisor hF hZ := by
      rw [← natCast_zsmul, Nat.cast_sub hn, Nat.cast_ofNat]
    rw [kaehlerDifferentialDivisor_smul hK _ hh hω₀,
      kaehlerDifferentialDivisor_chartDifferential hord hpos h2n, hE,
      ← mem_riemannRochSpace_units_iff hK, Units.val_mk0]
  constructor
  · intro hω
    obtain ⟨t, ht, hsep⟩ := hK.exists_transcendental_and_isSeparable_adjoin_of_perfectField
    obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' _ hω₀).1
      (finrank_kaehlerDifferential_eq_one_of_separating ht) ω
    rcases eq_or_ne c 0 with rfl | hc0
    · exact ⟨0, zero_mem _, by rw [map_zero]⟩
    obtain ⟨G, hG⟩ := adjointToRiemannRochSpace_surjective hord hZ h2
      ⟨c, (key c hc0).1 (hω (smul_ne_zero hc0 hω₀))⟩
    exact ⟨G, G.2, by rw [← hcoe, hG]⟩
  · rintro ⟨H, hH, rfl⟩ hω
    have hh : aeval (chartCoord hF h2) H ≠ 0 := fun h0 ↦ hω (by
      rw [h0]; exact zero_smul (functionField hF) (_ : Ω[functionField hF⁄k]))
    refine (key _ hh).2 ?_
    rw [← hcoe ⟨H, hH⟩]
    exact (adjointToRiemannRochSpace hF hord hZ h2 ⟨H, hH⟩).2

/-- **Canonical divisors of a plane curve are cut out by adjoints** (Fulton, §8.5, Proposition 8
and its Corollary). Let `C : F = 0` be an irreducible projective plane curve of degree `n` over an
algebraically closed field, all of whose multiple points are ordinary, with function field `K`
of genus `g` and adjoint divisor `E`. Then:

1. for every line `L` with `F ∤ L`, `(n - 3) div L - E` is canonical; for `n ≥ 3`, so is
   `div G - E` for every form `G` of degree `n - 3` with `F ∤ G`; for `n = 3`, `-E` is canonical;
2. in transverse position and for `n ≥ 2`, `div (dx / f_y) = (n - 3) div Z - E`;
3. every canonical divisor `W` has `deg W = 2g - 2` and `ℓ(W) = g`;
4. for `n ≥ 3`, the effective canonical divisors are the `div G - E` for the nonzero adjoints `G`
   of degree `n - 3`, these adjoints form a space of dimension `g`, and in transverse position
   the differentials without poles are the `H(x, y, 1) dx / f_y` for the adjoints `H` of degree
   `n - 3`.

Milestone: *Canonical divisors of a plane curve are cut out by adjoints of degree n − 3*. -/
theorem canonical_eq_formDivisor_sub_adjointDivisor :
    ((∀ {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1), ¬ F ∣ L →
        (Place.orderSystem (functionField.isFunctionField hF)).divisorClass
            (((n : ℤ) - 3) • formDivisor hF hL - adjointDivisor hF) =
          canonicalClass (functionField.isFunctionField hF) isIntegrallyClosedIn_of_isAlgClosed) ∧
      (3 ≤ n → ∀ {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous (n - 3)), ¬ F ∣ G →
        (Place.orderSystem (functionField.isFunctionField hF)).divisorClass
            (formDivisor hF hG - adjointDivisor hF) =
          canonicalClass (functionField.isFunctionField hF) isIntegrallyClosedIn_of_isAlgClosed) ∧
      (n = 3 → (Place.orderSystem (functionField.isFunctionField hF)).divisorClass
            (-adjointDivisor hF) =
          canonicalClass (functionField.isFunctionField hF) isIntegrallyClosedIn_of_isAlgClosed)) ∧
    (∀ (hpos : IsTransversePosition F) (hn : 2 ≤ n),
      kaehlerDifferentialDivisor (functionField.isFunctionField hF)
          isIntegrallyClosedIn_of_isAlgClosed
          (chartDifferential hF (hpos.not_dvd_X hF hn 2))
          (chartDifferential_ne_zero _ (hpos.not_dvd_pderiv_one hF hn)) =
        ((n : ℤ) - 3) • formDivisor hF (isHomogeneous_X k 2) - adjointDivisor hF) ∧
    (∀ W : Divisor k (functionField hF),
      (Place.orderSystem (functionField.isFunctionField hF)).divisorClass W =
          canonicalClass (functionField.isFunctionField hF) isIntegrallyClosedIn_of_isAlgClosed →
        Divisor.degree W = 2 * (genus k (functionField hF) : ℤ) - 2 ∧
          Divisor.dim W = genus k (functionField hF)) ∧
    (∀ hn : 3 ≤ n,
      (∀ W : Divisor k (functionField hF),
        0 ≤ W ∧ (Place.orderSystem (functionField.isFunctionField hF)).divisorClass W =
            canonicalClass (functionField.isFunctionField hF)
              isIntegrallyClosedIn_of_isAlgClosed ↔
          ∃ (G : MvPolynomial (Fin 3) k) (hG : G ∈ adjointSubmodule F (n - 3)), G ≠ 0 ∧
            W = formDivisor hF (mem_adjointSubmodule_iff.1 hG).1 - adjointDivisor hF) ∧
      Module.finrank k (adjointSubmodule F (n - 3)) = genus k (functionField hF) ∧
      ∀ (hpos : IsTransversePosition F) (ω : Ω[functionField hF⁄k]),
        (∀ hω : ω ≠ 0, 0 ≤ kaehlerDifferentialDivisor (functionField.isFunctionField hF)
            isIntegrallyClosedIn_of_isAlgClosed ω hω) ↔
          ∃ H ∈ adjointSubmodule F (n - 3),
            ω = aeval (chartCoord hF (hpos.not_dvd_X hF (Nat.le_of_succ_le hn) 2)) H •
              chartDifferential hF (hpos.not_dvd_X hF (Nat.le_of_succ_le hn) 2)) := by
  have hK := functionField.isFunctionField hF
  refine ⟨⟨fun hL hFL ↦
      divisorClass_sub_three_zsmul_formDivisor_sub_adjointDivisor_eq_canonicalClass hord hL hFL,
    fun hn _ hG hFG ↦ divisorClass_formDivisor_sub_adjointDivisor_eq_canonicalClass hord hn hG hFG,
    divisorClass_neg_adjointDivisor_eq_canonicalClass hord⟩,
    fun hpos hn ↦ kaehlerDifferentialDivisor_chartDifferential hord hpos hn,
    fun W hW ↦ ⟨(isRiemannRochDivisor_of_divisorClass_eq_canonicalClass hK _ hW).degree_eq hK
        isIntegrallyClosedIn_of_isAlgClosed,
      (isRiemannRochDivisor_of_divisorClass_eq_canonicalClass hK _ hW).dim_eq hK
        isIntegrallyClosedIn_of_isAlgClosed⟩,
    fun hn ↦ ⟨fun _ ↦ nonneg_and_divisorClass_eq_canonicalClass_iff hord hn,
      finrank_adjointSubmodule_sub_three hord hn,
      fun hpos ω ↦ nonneg_kaehlerDifferentialDivisor_iff hord hpos hn ω⟩⟩

end Divisor

end PlaneCurves.Projective

end
