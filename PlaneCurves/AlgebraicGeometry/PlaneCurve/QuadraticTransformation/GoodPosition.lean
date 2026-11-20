/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.Algebra.MvPolynomial.SetVarZero
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Tangent
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Basic

/-!
# Good position for the standard quadratic transformation

A plane curve `F` is in *good position* if no exceptional line `V(Xⱼ)` is tangent to `F` at a
fundamental point `[eᵢ]` lying on it. Such an `F` has no exceptional component, and Fulton's step
(4) says that its proper transform `F'` is in good position too.

The proof needs no intersection numbers. For a form `F` with `Z ∤ F`, the restriction
`F(X, Y, 0)` has `X`-adic order at least `m_{[0:1:0]}(F)`, with equality exactly when `Z` is not
tangent to `F` at `[0 : 1 : 0]` (Problem 5.5 of Fulton). The restriction of `F'` to `Z = 0` is
`(XY)^(n - r₂) G(Y, X) / (X^r₀ Y^r₁)`, with `G` the tangent cone of `F` at `[0 : 0 : 1]`; so `Z` is
tangent to `F'` at `[0 : 1 : 0]` exactly when `Y` is tangent to `F` at `[0 : 0 : 1]`. The other
five pairs of a fundamental point and an exceptional line through it follow by permuting the
variables.

## Main definitions

* `PlaneCurves.Projective.IsGoodPosition F`: no exceptional line is tangent to `F` at a
  fundamental point.

## Main results

* `PlaneCurves.Projective.isTangentAt_rename_fundamentalPoint_iff`: permuting the variables moves
  the tangents at the fundamental points along.
* `PlaneCurves.Projective.isTangentAt_fundamentalPoint_two_iff_dvd_leadingFormAt`: the
  coordinate tangents at `[0 : 0 : 1]` in the chart `Z = 1`.
* `PlaneCurves.Projective.mult_fundamentalPoint_one_le_multiplicity`,
  `PlaneCurves.Projective.isTangentAt_fundamentalPoint_one_X_two_iff`,
  `PlaneCurves.Projective.isTangentAt_fundamentalPoint_X_iff`: an exceptional line `V(Xⱼ)` is
  tangent to `F` at `[eᵢ]` exactly when the restriction of `F` to it vanishes to order more than
  `m_{[eᵢ]}(F)` at `[eᵢ]`.
* `PlaneCurves.Projective.mult_fundamentalPoint_le_multiplicity_bind₁`: the restriction of `F`
  to `V(Xⱼ)` vanishes to order at least `m_{[eᵢ]}(F)` at `[eᵢ]`.
* `PlaneCurves.Projective.isGoodPosition_rename_iff`: good position is invariant under
  permutations of the variables.
* `PlaneCurves.Projective.IsGoodPosition.not_X_dvd`: a curve in good position has no exceptional
  component.
* `PlaneCurves.Projective.IsGoodPosition.not_isTangentAt_dehomogenize_X`: in good position,
  neither coordinate axis is tangent to `F(x, y, 1)` at the origin.
* `PlaneCurves.Projective.IsGoodPosition.properTransform`: Fulton's (4), the proper transform of
  a curve in good position is in good position.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.4, Problem 5.5
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F L : MvPolynomial (Fin 3) k} {n : ℕ}

/-! ### Tangents at the fundamental points -/

private theorem injective_mulVecLin_toPEquiv_toMatrix (σ : Equiv.Perm (Fin 3)) :
    Function.Injective (σ.toPEquiv.toMatrix : Matrix (Fin 3) (Fin 3) k).mulVecLin := by
  intro v w h
  simp only [Matrix.mulVecLin_apply, PEquiv.toMatrix_toPEquiv_mulVec] at h
  exact σ.surjective.injective_comp_right h

private theorem map_toPEquiv_toMatrix_fundamentalPoint (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    Projectivization.map (σ.toPEquiv.toMatrix : Matrix (Fin 3) (Fin 3) k).mulVecLin
      (injective_mulVecLin_toPEquiv_toMatrix σ) (fundamentalPoint (σ i)) = fundamentalPoint i := by
  rw [fundamentalPoint_def, fundamentalPoint_def, map_mk]
  congr 1
  rw [Matrix.mulVecLin_apply, PEquiv.toMatrix_toPEquiv_mulVec]
  funext j
  simp [Pi.single_apply, σ.injective.eq_iff]

/-- Renaming the variables by a permutation `σ` moves a tangent `L` of a form `F` at the
fundamental point `[eᵢ]` to the tangent `L^σ` of `F^σ` at `[e_{σ i}]`. -/
theorem isTangentAt_rename_fundamentalPoint_iff (hF : F.IsHomogeneous n)
    (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    IsTangentAt (rename σ F) (fundamentalPoint (σ i)) (rename σ L) ↔
      IsTangentAt F (fundamentalPoint i) L := by
  rw [← linearSubst_toPEquiv_toMatrix, ← linearSubst_toPEquiv_toMatrix,
    isTangentAt_linearSubst_iff hF (injective_mulVecLin_toPEquiv_toMatrix σ),
    map_toPEquiv_toMatrix_fundamentalPoint]

private theorem eval_rep_fundamentalPoint_X {i j : Fin 3} (hij : i ≠ j) :
    eval (fundamentalPoint (k := k) i).rep (X j) = 0 := by
  have h := (fundamentalPoint_mem_zeroLocus_X_iff (k := k)).2 hij
  rw [mem_zeroLocus_singleton_iff (isHomogeneous_X k j)] at h
  simpa using h

/-- **The coordinate tangents at `[0 : 0 : 1]`.** For `i = 0, 1`, the line `Xᵢ = 0` is tangent to
a form `F` at `[0 : 0 : 1]` exactly when `Xᵢ` divides the tangent cone of `F(X, Y, 1)` at the
origin. -/
theorem isTangentAt_fundamentalPoint_two_iff_dvd_leadingFormAt (hF : F.IsHomogeneous n)
    (i : Fin 2) :
    IsTangentAt F (fundamentalPoint 2) (X (Fin.succAbove 2 i)) ↔
      X i ∣ (dehomogenize 2 F).leadingFormAt 0 := by
  rw [isTangentAt_iff_affine hF (fundamentalPoint_mem_affineOpen_iff.2 rfl) (isHomogeneous_X k _)
    (eval_rep_fundamentalPoint_X (Fin.succAbove_ne 2 i).symm), affineChart_fundamentalPoint,
    dehomogenize_X, Fin.insertNth_apply_succAbove, taylor_zero, Affine.isTangentAt_def]
  simp [isHomogeneous_X, X_ne_zero]

/-! ### The criterion for an exceptional line -/

/-- A binary form `G` of degree `i`, evaluated at `(a, 0)`, is `G(1, 0) aⁱ`. -/
private theorem aeval_vecCons_zero {S : Type*} [CommSemiring S] [Algebra k S] (a : S)
    {G : MvPolynomial (Fin 2) k} {i : ℕ} (hG : G.IsHomogeneous i) :
    aeval ![a, 0] G = algebraMap k S (G.coeff (Finsupp.single 0 i)) * a ^ i := by
  conv_lhs => rw [G.as_sum, map_sum]
  rw [Finset.sum_eq_single (Finsupp.single 0 i)]
  · simp [aeval_monomial]
  · intro d hd hne
    have hdeg := hG (mem_support_iff.1 hd)
    have h1 : d 1 ≠ 0 := by
      intro h1
      apply hne
      ext j
      fin_cases j <;> simp_all [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two]
    simp [aeval_monomial, Finsupp.prod_fintype, Fin.prod_univ_two, zero_pow h1]
  · intro h
    simp [notMem_support_iff.1 h]

/-- `F = ∑ᵢ Gᵢ(X, Z) Y^(n - i)`, with `Gᵢ` the degree `i` part of `F(X, 1, Z)`. -/
private theorem eq_sum_rename_succAbove_one (hF : F.IsHomogeneous n) :
    F = ∑ i ∈ Finset.range (n + 1),
      rename (Fin.succAbove 1) (homogeneousComponent i (dehomogenize 1 F)) * X 1 ^ (n - i) := by
  conv_lhs => rw [← homogenize_dehomogenize (i := 1) hF, homogenize_def]
  simp only [← rename_homogeneousComponent]

private theorem aeval_X_two_zero_eq_bind₁ (p : MvPolynomial (Fin 3) k) :
    aeval (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) p =
      bind₁ (Function.update X 2 0) p := by
  have h : (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) = Function.update X 2 0 := by
    funext j
    fin_cases j <;> simp
  rw [h, aeval_eq_bind₁]

private theorem multiplicity_X_mul {i : Fin 3} {a b : MvPolynomial (Fin 3) k} (ha : a ≠ 0)
    (hb : b ≠ 0) :
    multiplicity (X i) (a * b) = multiplicity (X i) a + multiplicity (X i) b :=
  multiplicity_mul prime_X (FiniteMultiplicity.of_prime_left prime_X (mul_ne_zero ha hb))

/-- For a form `F` with `Z ∤ F`, and `m` its multiplicity at `[0 : 1 : 0]`: `F(X, Y, 0) = X^m H`
with `H ≠ 0`, and `X ∣ H` exactly when `Z` is tangent to `F` at `[0 : 1 : 0]`. -/
private theorem exists_aeval_X_two_zero_eq (hF : F.IsHomogeneous n) (hZ : ¬ X 2 ∣ F) :
    ∃ H, aeval (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) F =
        X 0 ^ (mult F (fundamentalPoint 1)).toNat * H ∧ H ≠ 0 ∧
      (X 0 ∣ H ↔ IsTangentAt F (fundamentalPoint 1) (X 2)) := by
  have hF0 : F ≠ 0 := by rintro rfl; exact hZ (dvd_zero _)
  set G := fun i ↦ homogeneousComponent i (dehomogenize 1 F)
  set m := (mult F (fundamentalPoint 1)).toNat with hm
  set c := fun i ↦ (G i).coeff (Finsupp.single 0 i) with hc
  have hmn : m ≤ n := ENat.toNat_le_of_le_natCast (mult_le_degree hF hF0 _)
  have hm' : (m : ℕ∞) = (dehomogenize 1 F).orderAt 0 := by
    rw [hm, natCast_toNat_mult hF0, mult_fundamentalPoint_eq_orderAt hF]
  have hlt : ∀ i < m, G i = 0 := fun i hi ↦ by
    simpa [taylor_zero] using le_orderAt_iff_homogeneousComponent.1 hm'.le i hi
  have hGm0 : G m ≠ 0 := by
    have h : G m = (dehomogenize 1 F).leadingFormAt 0 := by
      rw [leadingFormAt_def, ← hm', ENat.toNat_natCast, taylor_zero]
    rw [h]
    exact leadingFormAt_ne_zero (dehomogenize_ne_zero_of_isHomogeneous 1 hF hF0)
  -- The tangency of `Z` is `Z ∣ G m`, that is, `c m = 0`.
  have htan : IsTangentAt F (fundamentalPoint 1) (X 2) ↔ c m = 0 := by
    have hfp : fundamentalPoint (k := k) 1 = mk k ![0, 1, 0] (by simp) := by
      rw [fundamentalPoint_def]
      congr 1
      funext j
      fin_cases j <;> rfl
    obtain ⟨-, -, h, -⟩ := mult_eq_and_isTangentAt_iff_of_eq_sum
      (fun i ↦ homogeneousComponent_isHomogeneous i _) (eq_sum_rename_succAbove_one hF) hmn hlt
      hGm0
    have h1 := h (X 1)
    rw [rename_X, ← hfp] at h1
    rw [show X 2 = (X (Fin.succAbove 1 1) : MvPolynomial (Fin 3) k) from rfl, h1]
    have hψ : bind₁ (Function.update (X : Fin 2 → MvPolynomial (Fin 2) k) 1 0) =
        aeval ![X 0, 0] := by
      have h : (![X 0, 0] : Fin 2 → MvPolynomial (Fin 2) k) = Function.update X 1 0 := by
        funext j
        fin_cases j <;> simp
      rw [h, aeval_eq_bind₁]
    simp only [isHomogeneous_X, ne_eq, X_ne_zero, not_false_eq_true, true_and,
      X_dvd_iff_bind₁_update_X_zero_eq_zero, hψ,
      aeval_vecCons_zero _ (homogeneousComponent_isHomogeneous m _), algebraMap_eq, mul_eq_zero,
      C_eq_zero, pow_eq_zero_iff', X_ne_zero, false_and, or_false, hc]
    exact Iff.rfl
  -- The restriction `F(X, Y, 0) = ∑ᵢ c i Xⁱ Y^(n - i)`.
  have hR : aeval (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) F =
      ∑ i ∈ Finset.range (n + 1), C (c i) * X 0 ^ i * X 1 ^ (n - i) := by
    have hv : (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) ∘ Fin.succAbove 1 = ![X 0, 0] := by
      funext j
      fin_cases j <;> rfl
    conv_lhs => rw [eq_sum_rename_succAbove_one hF]
    simp only [map_sum, map_mul, map_pow, aeval_rename, hv, aeval_X]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [aeval_vecCons_zero _ (homogeneousComponent_isHomogeneous i _), algebraMap_eq]
    rfl
  set H : MvPolynomial (Fin 3) k :=
    ∑ i ∈ Finset.Ico m (n + 1), C (c i) * X 0 ^ (i - m) * X 1 ^ (n - i) with hH
  have hRH : aeval (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) F = X 0 ^ m * H := by
    rw [hR, ← Finset.sum_range_add_sum_Ico _ (by omega : m ≤ n + 1),
      Finset.sum_eq_zero fun i hi ↦ by simp [hc, hlt i (Finset.mem_range.1 hi)], zero_add,
      hH, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [← Nat.add_sub_cancel' (Finset.mem_Ico.1 hi).1]
    simp only [Nat.add_sub_cancel_left, pow_add]
    ring
  have hH0 : bind₁ (Function.update X 0 0) H = C (c m) * X 1 ^ (n - m) := by
    rw [hH, map_sum, Finset.sum_eq_single_of_mem m (by simp; omega)]
    · simp
    · intro i hi him
      have : i - m ≠ 0 := by simp at hi; omega
      simp [zero_pow this]
  refine ⟨H, hRH, fun h0 ↦ hZ (X_dvd_of_bind₁_update_X_zero_eq_zero ?_), ?_⟩
  · rw [← aeval_X_two_zero_eq_bind₁, hRH, h0, mul_zero]
  · rw [htan, X_dvd_iff_bind₁_update_X_zero_eq_zero, hH0]
    simp [X_ne_zero]

/-- For a form `F` of degree `n` not divisible by `Z`, the restriction `F(X, Y, 0)` vanishes to
order at least `m_{[0:1:0]}(F)` at `[0 : 1 : 0]`: `X^m` divides it. -/
theorem mult_fundamentalPoint_one_le_multiplicity (hF : F.IsHomogeneous n) (hZ : ¬ X 2 ∣ F) :
    (mult F (fundamentalPoint 1)).toNat ≤
      multiplicity (X 0) (aeval (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) F) := by
  obtain ⟨H, hR, hH, -⟩ := exists_aeval_X_two_zero_eq hF hZ
  rw [hR, multiplicity_X_mul (pow_ne_zero _ (X_ne_zero _)) hH,
    multiplicity_pow_self_of_prime prime_X]
  exact Nat.le_add_right _ _

/-- **Tangency of `Z` at `[0 : 1 : 0]`.** For a form `F` of degree `n` not divisible by `Z`, the
line `Z = 0` is tangent to `F` at `[0 : 1 : 0]` exactly when the restriction `F(X, Y, 0)` vanishes
there to order more than `m_{[0:1:0]}(F)`. -/
theorem isTangentAt_fundamentalPoint_one_X_two_iff (hF : F.IsHomogeneous n) (hZ : ¬ X 2 ∣ F) :
    IsTangentAt F (fundamentalPoint 1) (X 2) ↔ (mult F (fundamentalPoint 1)).toNat <
      multiplicity (X 0) (aeval (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) F) := by
  obtain ⟨H, hR, hH, htan⟩ := exists_aeval_X_two_zero_eq hF hZ
  rw [hR, multiplicity_X_mul (pow_ne_zero _ (X_ne_zero _)) hH,
    multiplicity_pow_self_of_prime prime_X, ← htan, lt_add_iff_pos_right, Nat.pos_iff_ne_zero, Ne,
    multiplicity_eq_zero (FiniteMultiplicity.of_prime_left prime_X hH), not_not]

private theorem exists_perm_eq_one_two {i j : Fin 3} (hij : i ≠ j) :
    ∃ τ : Equiv.Perm (Fin 3), τ i = 1 ∧ τ j = 2 := by
  refine ⟨Equiv.swap (Equiv.swap j 2 i) 1 * Equiv.swap j 2, ?_⟩
  revert i j
  decide

private theorem perm_eq_zero {τ : Equiv.Perm (Fin 3)} {i j l : Fin 3} (hi : τ i = 1)
    (hj : τ j = 2) (hil : i ≠ l) (hjl : j ≠ l) : τ l = 0 := by
  have h1 : τ l ≠ 1 := hi ▸ τ.injective.ne hil.symm
  have h2 : τ l ≠ 2 := hj ▸ τ.injective.ne hjl.symm
  revert h1 h2
  generalize τ l = a
  revert a
  decide

private theorem bind₁_update_X_zero_rename (τ : Equiv.Perm (Fin 3)) (j : Fin 3)
    (p : MvPolynomial (Fin 3) k) :
    bind₁ (Function.update X (τ j) 0) (rename τ p) =
      rename τ (bind₁ (Function.update X j 0) p) := by
  have h : (bind₁ (Function.update X (τ j) 0)).comp (rename τ) =
      (rename τ).comp (bind₁ (Function.update (X : Fin 3 → MvPolynomial (Fin 3) k) j 0)) :=
    algHom_ext fun a ↦ by
      rcases eq_or_ne a j with rfl | ha
      · simp
      · simp [Function.update_of_ne ha, Function.update_of_ne (τ.injective.ne ha)]
  exact DFunLike.congr_fun h p

/-- **Tangency of an exceptional line.** Let `i, j, l` be the three indices, and `F` a form not
divisible by `Xⱼ`. The line `Xⱼ = 0` is tangent to `F` at `[eᵢ]` exactly when the restriction of
`F` to `Xⱼ = 0` vanishes at `[eᵢ]` to order more than `m_{[eᵢ]}(F)`, that is, when `X_l` divides
it more than `m_{[eᵢ]}(F)` times. -/
theorem isTangentAt_fundamentalPoint_X_iff (hF : F.IsHomogeneous n) {i j l : Fin 3}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (hXj : ¬ X j ∣ F) :
    IsTangentAt F (fundamentalPoint i) (X j) ↔
      (mult F (fundamentalPoint i)).toNat <
        multiplicity (X l) (bind₁ (Function.update X j 0) F) := by
  obtain ⟨τ, hi, hj⟩ := exists_perm_eq_one_two hij
  have hl := perm_eq_zero hi hj hil hjl
  have hZ : ¬ X 2 ∣ rename τ F := by
    rw [← hj, ← rename_X]
    exact fun hd ↦ hXj ((map_dvd_iff (renameEquiv k τ)).1 hd)
  have e1 := isTangentAt_rename_fundamentalPoint_iff hF τ i (L := X j)
  rw [hi, rename_X, hj] at e1
  have e2 := mult_rename_fundamentalPoint hF τ i
  rw [hi] at e2
  have e3 : multiplicity (X 0) (aeval (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k)
      (rename τ F)) = multiplicity (X l) (bind₁ (Function.update X j 0) F) := by
    have h := multiplicity_map_eq (renameEquiv k τ) (a := X l)
      (b := bind₁ (Function.update X j 0) F)
    rw [renameEquiv_apply, renameEquiv_apply, rename_X, hl, ← bind₁_update_X_zero_rename, hj]
      at h
    rw [aeval_X_two_zero_eq_bind₁, h]
  rw [← e1, isTangentAt_fundamentalPoint_one_X_two_iff hF.rename_isHomogeneous hZ, e2, e3]

/-- Let `i, j, l` be the three indices, and `F` a form not divisible by `Xⱼ`. The restriction of
`F` to `Xⱼ = 0` vanishes at `[eᵢ]` to order at least `m_{[eᵢ]}(F)`: `X_l ^ m_{[eᵢ]}(F)` divides
it. -/
theorem mult_fundamentalPoint_le_multiplicity_bind₁ (hF : F.IsHomogeneous n) {i j l : Fin 3}
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) (hXj : ¬ X j ∣ F) :
    (mult F (fundamentalPoint i)).toNat ≤
      multiplicity (X l) (bind₁ (Function.update X j 0) F) := by
  obtain ⟨τ, hi, hj⟩ := exists_perm_eq_one_two hij
  have hl := perm_eq_zero hi hj hil hjl
  have hZ : ¬ X 2 ∣ rename τ F := by
    rw [← hj, ← rename_X]
    exact fun hd ↦ hXj ((map_dvd_iff (renameEquiv k τ)).1 hd)
  have e2 := mult_rename_fundamentalPoint hF τ i
  rw [hi] at e2
  have h := multiplicity_map_eq (renameEquiv k τ) (a := X l)
    (b := bind₁ (Function.update X j 0) F)
  rw [renameEquiv_apply, renameEquiv_apply, rename_X, hl, ← bind₁_update_X_zero_rename, hj] at h
  rw [← e2, ← h, ← aeval_X_two_zero_eq_bind₁]
  exact mult_fundamentalPoint_one_le_multiplicity hF.rename_isHomogeneous hZ

/-! ### Good position -/

/-- A plane curve `F` is in *good position* if no exceptional line `V(Xⱼ)` is tangent to `F` at a
fundamental point `[eᵢ]` on it, `i ≠ j` (Fulton, §7.4). A fundamental point not on `F` has no
tangent at all. -/
def IsGoodPosition (F : MvPolynomial (Fin 3) k) : Prop :=
  ∀ i j, i ≠ j → ¬ IsTangentAt F (fundamentalPoint i) (X j)

theorem isGoodPosition_def :
    IsGoodPosition F ↔ ∀ i j, i ≠ j → ¬ IsTangentAt F (fundamentalPoint i) (X j) :=
  Iff.rfl

theorem isGoodPosition_smul_iff {c : k} (hc : c ≠ 0) :
    IsGoodPosition (c • F) ↔ IsGoodPosition F := by
  simp only [isGoodPosition_def, isTangentAt_smul_iff hc]

theorem IsGoodPosition.smul (h : IsGoodPosition F) {c : k} (hc : c ≠ 0) :
    IsGoodPosition (c • F) :=
  (isGoodPosition_smul_iff hc).2 h

/-- Good position is invariant under permutations of the variables. -/
theorem isGoodPosition_rename_iff (hF : F.IsHomogeneous n) (σ : Equiv.Perm (Fin 3)) :
    IsGoodPosition (rename σ F) ↔ IsGoodPosition F := by
  simp only [isGoodPosition_def]
  refine ⟨fun h i j hij ↦ ?_, fun h i j hij ↦ ?_⟩
  · rw [← isTangentAt_rename_fundamentalPoint_iff hF σ, rename_X]
    exact h _ _ (σ.injective.ne hij)
  · obtain ⟨i, rfl⟩ := σ.surjective i
    obtain ⟨j, rfl⟩ := σ.surjective j
    rw [← rename_X, isTangentAt_rename_fundamentalPoint_iff hF σ]
    exact h _ _ fun e ↦ hij (congrArg σ e)

private theorem leadingFormAt_X_of_eq_zero {j : Fin 3} {v : Fin 3 → k} (hv : v j = 0) :
    (X j : MvPolynomial (Fin 3) k).leadingFormAt v = X j := by
  have h := leadingFormAt_taylor v 0 (X j : MvPolynomial (Fin 3) k)
  rwa [zero_add, taylor_X, hv, C_0, add_zero, (isHomogeneous_X k j).leadingFormAt_zero,
    eq_comm] at h

/-- A curve in good position has no exceptional component: an exceptional line `V(Xⱼ)` in it
would be tangent to it at the fundamental points on `V(Xⱼ)`. -/
theorem IsGoodPosition.not_X_dvd (h : IsGoodPosition F) (j : Fin 3) : ¬ X j ∣ F := by
  rintro ⟨G, rfl⟩
  have hij : j + 1 ≠ j := by fin_cases j <;> decide
  have hv := eval_rep_fundamentalPoint_X (k := k) hij
  refine h (j + 1) j hij (isTangentAt_def.2 ⟨isHomogeneous_X k j, X_ne_zero j, hv, ?_⟩)
  rw [leadingForm_def, leadingFormAt_mul, leadingFormAt_X_of_eq_zero (by simpa using hv)]
  exact dvd_mul_right _ _

theorem IsGoodPosition.ne_zero (h : IsGoodPosition F) : F ≠ 0 := by
  rintro rfl
  exact h.not_X_dvd 0 (dvd_zero _)

/-- In good position, neither `x` nor `y` is tangent at the origin to `F(x, y, 1)`: this is good
position at `[0 : 0 : 1]`. -/
theorem IsGoodPosition.not_isTangentAt_dehomogenize_X (h : IsGoodPosition F)
    (hF : F.IsHomogeneous n) (i : Fin 2) : ¬ Affine.IsTangentAt (dehomogenize 2 F) 0 (X i) :=
  fun hT ↦ isGoodPosition_def.1 h 2 (Fin.succAbove 2 i) (Fin.succAbove_ne 2 i).symm
    ((isTangentAt_fundamentalPoint_two_iff_dvd_leadingFormAt hF i).2
      (Affine.isTangentAt_def.1 hT).2.2)

/-- `X ∣ G(Y, X)` exactly when `Y ∣ G(X, Y)`. -/
private theorem X_zero_dvd_rename_iff {G : MvPolynomial (Fin 2) k} :
    X 0 ∣ rename (![1, 0] : Fin 2 → Fin 3) G ↔ X 1 ∣ G := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simpa using map_dvd (rename (![1, 0] : Fin 2 → Fin 3)) h⟩
  have hg : (aeval (![X 1, X 0, 0] : Fin 3 → MvPolynomial (Fin 2) k)).comp
      (rename (![1, 0] : Fin 2 → Fin 3)) = AlgHom.id k _ :=
    algHom_ext fun i ↦ by fin_cases i <;> simp
  have h' := map_dvd (aeval (![X 1, X 0, 0] : Fin 3 → MvPolynomial (Fin 2) k)) h
  rwa [← AlgHom.comp_apply, hg, AlgHom.id_apply, aeval_X, Matrix.cons_val_zero] at h'

private theorem multiplicity_X_zero_X_pow_mul_X_pow (a b : ℕ) :
    multiplicity (X 0) (X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 3) k) = a := by
  have hb : ¬ (X 0 : MvPolynomial (Fin 3) k) ∣ X 1 ^ b := fun h ↦ by
    simpa [X_dvd_X] using prime_X.dvd_of_dvd_pow h
  rw [multiplicity_X_mul (pow_ne_zero _ (X_ne_zero _)) (pow_ne_zero _ (X_ne_zero _)),
    multiplicity_pow_self_of_prime prime_X,
    (multiplicity_eq_zero (FiniteMultiplicity.of_prime_left prime_X
      (pow_ne_zero _ (X_ne_zero _)))).2 hb, add_zero]

/-- Fulton's (4) at the pair `[0 : 1 : 0]`, `Z = 0`. -/
private theorem IsGoodPosition.not_isTangentAt_properTransform (h : IsGoodPosition F)
    (hF : F.IsHomogeneous n) :
    ¬ IsTangentAt (properTransform F) (fundamentalPoint 1) (X 2) := by
  have hF0 := h.ne_zero
  have hZ' := not_X_dvd_properTransform hF hF0 2
  set R := aeval (![X 0, X 1, 0] : Fin 3 → MvPolynomial (Fin 3) k) (properTransform F) with hR
  have hR0 : R ≠ 0 := fun h0 ↦
    hZ' (X_dvd_of_bind₁_update_X_zero_eq_zero (by rw [← aeval_X_two_zero_eq_bind₁, ← hR, h0]))
  set G := rename (![1, 0] : Fin 2 → Fin 3) ((dehomogenize 2 F).leadingFormAt 0) with hG
  have hG0 : G ≠ 0 := (map_ne_zero_iff _ (rename_injective _ (by decide))).2
    (leadingFormAt_ne_zero (dehomogenize_ne_zero_of_isHomogeneous 2 hF hF0))
  have hres := aeval_X_two_eq_zero_properTransform hF hF0
  rw [← hR, ← hG, mul_pow] at hres
  have hm := congrArg (multiplicity (X 0)) hres
  rw [multiplicity_X_mul (mul_ne_zero (pow_ne_zero _ (X_ne_zero _)) (pow_ne_zero _ (X_ne_zero _)))
      hR0, multiplicity_X_zero_X_pow_mul_X_pow,
    multiplicity_X_mul (mul_ne_zero (pow_ne_zero _ (X_ne_zero _)) (pow_ne_zero _ (X_ne_zero _)))
      hG0, multiplicity_X_zero_X_pow_mul_X_pow] at hm
  have hle := mult_fundamentalPoint_add_le hF (h.not_X_dvd 1) (i := 1) (j := 0) (l := 2)
    (by decide) (by decide) (by decide)
  rw [← natCast_toNat_mult (P := fundamentalPoint 0) hF0,
    ← natCast_toNat_mult (P := fundamentalPoint 2) hF0] at hle
  norm_cast at hle
  intro ht
  rw [isTangentAt_fundamentalPoint_one_X_two_iff hF.properTransform hZ',
    mult_properTransform_fundamentalPoint_one hF (h.not_X_dvd 1), ENat.toNat_natCast, ← hR] at ht
  have hpos : 0 < multiplicity (X 0) G := by omega
  rw [Nat.pos_iff_ne_zero, Ne, multiplicity_eq_zero (FiniteMultiplicity.of_prime_left prime_X hG0),
    not_not, hG, X_zero_dvd_rename_iff,
    ← isTangentAt_fundamentalPoint_two_iff_dvd_leadingFormAt hF] at hpos
  exact h 2 _ (by decide) hpos

/-- **Fulton's (4).** The proper transform of a curve in good position is in good position. -/
theorem IsGoodPosition.properTransform (h : IsGoodPosition F) (hF : F.IsHomogeneous n) :
    IsGoodPosition (properTransform F) := by
  intro i j hij ht
  obtain ⟨τ, hi, hj⟩ := exists_perm_eq_one_two hij
  have hG := ((isGoodPosition_rename_iff hF τ).2 h).not_isTangentAt_properTransform
    hF.rename_isHomogeneous
  have e := isTangentAt_rename_fundamentalPoint_iff hF.properTransform τ i (L := X j)
  rw [hi, rename_X, hj] at e
  rw [properTransform_rename hF] at hG
  exact hG (e.2 ht)

/-- The line `X + Y + Z` passes through no fundamental point, so it is in good position. -/
example : IsGoodPosition (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) ℚ) := by
  have hL : (X 0 + X 1 + X 2 : MvPolynomial (Fin 3) ℚ).IsHomogeneous 1 :=
    ((isHomogeneous_X ℚ 0).add (isHomogeneous_X ℚ 1)).add (isHomogeneous_X ℚ 2)
  intro i j _ ht
  have h := ht.eval_rep_eq_zero
  rw [fundamentalPoint_def, hL.eval_rep_mk_eq_zero_iff] at h
  fin_cases i <;> simp at h

/-- A curve with an exceptional component, such as the line `X = 0`, is not in good position. -/
example : ¬ IsGoodPosition (X 0 : MvPolynomial (Fin 3) ℚ) :=
  fun h ↦ h.not_X_dvd 0 dvd_rfl

end PlaneCurves.Projective

end
