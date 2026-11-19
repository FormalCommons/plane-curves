/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Monad
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.Line
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.Multiplicity
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.SimplePoint
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.Tangent
public import PlaneCurves.RingTheory.MvPolynomial.Homogeneous
public import PlaneCurves.RingTheory.MvPolynomial.LeadingForm

/-!
# The strict transform of a plane curve under the blow-up of the origin

Let `F : MvPolynomial (Fin 2) R` be an affine plane curve of multiplicity `r = m_0(F)` at the
origin, and write `F = F_r + F_{r+1} + ⋯ + F_n` with `F_i` a form of degree `i`. In the chart
`X = X, Y = XZ` of the blow-up of the origin, the variables of the blown-up chart being
`X = X 0` and `Z = X 1`, the total transform `F(X, XZ)` is `X ^ r F'(X, Z)` with

  `F' = F_r(1, Z) + X F_{r+1}(1, Z) + ⋯ + X ^ (n - r) F_n(1, Z)`,

the *strict transform* of `F`. It is not divisible by `X`, and on the exceptional line `X = 0` it
is `F_r(1, Z)`, the leading form of `F` at the origin restricted to the chart.

Over a field, the points of the strict transform on the exceptional line, the fibre of the
blow-up over the origin, are the points `(0, α)` for the tangents `Y - α X` of `F` at the
origin, and the strict transform meets the exceptional line at `(0, α)` with intersection number
the multiplicity of that tangent (Step (2) of §7.2 of Fulton). In particular, over an ordinary
multiple point every point of the fibre is a simple point of the strict transform.

## Main definitions

* `PlaneCurves.Affine.blowupStrictTransform F`: the strict transform `F'`, the polynomial
  `F(X, XZ)` divided by `X ^ r`.

## Main results

* `PlaneCurves.Affine.X_pow_mul_blowupStrictTransform`: `F(X, XZ) = X ^ r F'(X, Z)`, and
  `PlaneCurves.Affine.eval_blowupStrictTransform` its evaluated form.
* `PlaneCurves.Affine.blowupStrictTransform_eq_sum`: `F' = ∑ᵢ X ^ (i - r) F_i(1, Z)`.
* `PlaneCurves.Affine.aeval_zero_X_blowupStrictTransform`: `F'(0, Z) = F_r(1, Z)`.
* `PlaneCurves.Affine.not_X_dvd_blowupStrictTransform`: `X ∤ F'` for `F ≠ 0`.
* `PlaneCurves.Affine.blowupStrictTransform_eq_of_aeval_eq_of_not_dvd`: over a domain, a
  factorization `F(X, XZ) = X ^ n G` with `X ∤ G` is the one by the strict transform.
* `PlaneCurves.Affine.blowupStrictTransform_mul`: over a domain, `(FG)' = F'G'`.
* `PlaneCurves.Affine.eval_zero_blowupStrictTransform_eq_zero_iff`: `F'(0, α) = 0` iff `Y - α X`
  is tangent to `F` at the origin.
* `PlaneCurves.Affine.exists_finset_eval_zero_blowupStrictTransform`: over an algebraically
  closed field, if `X` is not tangent, the leading form is `ε ∏ (Y - α X) ^ rₐ` over the finitely
  many points `(0, α)` of the fibre.
* `PlaneCurves.Affine.intersectionNumber_blowupStrictTransform_X_zero`:
  `I((0, α), F' ∩ X) = rₐ`, the multiplicity of the tangent `Y - α X`, and
  `PlaneCurves.Affine.orderAt_blowupStrictTransform_le_intersectionNumber`:
  `m_{(0, α)}(F') ≤ I((0, α), F' ∩ X)`.
* `PlaneCurves.Affine.IsOrdinaryMultiplePoint.isSimplePoint_blowupStrictTransform`: over an
  ordinary multiple point, the points of the fibre are simple points of `F'`, where it meets the
  exceptional line with intersection number one.
* `PlaneCurves.Affine.blowupStrictTransform_cusp`: the cusp `Y² - X³` has strict transform
  `Z² - X`, with one point over the origin, a simple one.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.2
-/

public section

namespace PlaneCurves.Affine

open MvPolynomial

variable {R : Type*}

section CommSemiring

variable [CommSemiring R] {F G : MvPolynomial (Fin 2) R}

/-- The *strict transform* of the plane curve `F` under the blow-up of the origin, in the chart
`X = X, Y = XZ` (with `X = X 0`, `Z = X 1`): the polynomial `F(X, XZ)` divided by `X ^ r`, where
`r = m_0(F)` is the multiplicity of `F` at the origin. -/
noncomputable def blowupStrictTransform (F : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R :=
  (aeval ![X 0, X 0 * X 1] F).divMonomial (Finsupp.single 0 (F.orderAt 0).toNat)

theorem blowupStrictTransform_def (F : MvPolynomial (Fin 2) R) :
    blowupStrictTransform F =
      (aeval ![X 0, X 0 * X 1] F).divMonomial (Finsupp.single 0 (F.orderAt 0).toNat) :=
  (rfl)

/-- If `F(X, XZ) = X ^ r G` for the multiplicity `r` of `F` at the origin, then `G` is the strict
transform of `F`. -/
theorem blowupStrictTransform_eq_of_aeval_eq
    (h : aeval ![X 0, X 0 * X 1] F = X 0 ^ (F.orderAt 0).toNat * G) :
    blowupStrictTransform F = G := by
  rw [blowupStrictTransform_def, h, X_pow_eq_monomial, divMonomial_monomial_mul]

/-- Substituting `X, XZ` into a form `F_i` of degree `i` gives `X ^ i F_i(1, Z)`. -/
theorem _root_.MvPolynomial.IsHomogeneous.aeval_X_X_mul_X {p : MvPolynomial (Fin 2) R} {i : ℕ}
    (hp : p.IsHomogeneous i) :
    aeval ![X 0, X 0 * X 1] p = X 0 ^ i * aeval ![1, (X 1 : MvPolynomial (Fin 2) R)] p := by
  rw [← hp.aeval_mul_left]
  congr 1
  ext j : 1
  fin_cases j <;> simp

/-- The homogeneous components of `F` of degree less than its multiplicity at the origin
vanish. -/
private theorem homogeneousComponent_eq_zero_of_lt_toNat {i : ℕ}
    (hi : i < (F.orderAt 0).toNat) : homogeneousComponent i F = 0 := by
  have := homogeneousComponent_taylor_eq_zero_of_lt (p := F) (a := 0) (i := i)
    ((Nat.cast_lt.2 hi).trans_le (ENat.natCast_toNat_le_self _))
  rwa [taylor_zero] at this

/-- `F(X, XZ) = X ^ r ∑ᵢ X ^ (i - r) F_i(1, Z)`, along the homogeneous components `F_i`. -/
private theorem aeval_X_X_mul_X_eq_sum (F : MvPolynomial (Fin 2) R) :
    aeval ![X 0, X 0 * X 1] F = X 0 ^ (F.orderAt 0).toNat *
      ∑ i ∈ Finset.range (F.totalDegree + 1), X 0 ^ (i - (F.orderAt 0).toNat) *
        aeval ![1, (X 1 : MvPolynomial (Fin 2) R)] (homogeneousComponent i F) := by
  conv_lhs => rw [← sum_homogeneousComponent F]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [(homogeneousComponent_isHomogeneous i F).aeval_X_X_mul_X]
  rcases lt_or_ge i (F.orderAt 0).toNat with hi | hi
  · simp [homogeneousComponent_eq_zero_of_lt_toNat hi]
  · rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hi]

/-- The strict transform expanded along the homogeneous components `F_i` of `F`:
`F' = F_r(1, Z) + X F_{r+1}(1, Z) + ⋯`. The terms with `i < r` vanish, as `F_i = 0` there. -/
theorem blowupStrictTransform_eq_sum (F : MvPolynomial (Fin 2) R) :
    blowupStrictTransform F = ∑ i ∈ Finset.range (F.totalDegree + 1),
      X 0 ^ (i - (F.orderAt 0).toNat) *
        aeval ![1, (X 1 : MvPolynomial (Fin 2) R)] (homogeneousComponent i F) :=
  blowupStrictTransform_eq_of_aeval_eq (aeval_X_X_mul_X_eq_sum F)

/-- The total transform factors through the strict transform: `F(X, XZ) = X ^ r F'(X, Z)`. -/
theorem X_pow_mul_blowupStrictTransform (F : MvPolynomial (Fin 2) R) :
    X 0 ^ (F.orderAt 0).toNat * blowupStrictTransform F = aeval ![X 0, X 0 * X 1] F := by
  rw [blowupStrictTransform_eq_sum, aeval_X_X_mul_X_eq_sum]

/-- The evaluated form of the factorization: `F(x, xz) = x ^ r F'(x, z)`. -/
theorem eval_blowupStrictTransform (F : MvPolynomial (Fin 2) R) (x z : R) :
    eval ![x, x * z] F = x ^ (F.orderAt 0).toNat * eval ![x, z] (blowupStrictTransform F) := by
  have h := congr(eval ![x, z] $(X_pow_mul_blowupStrictTransform F))
  have he : eval ![x, z] (aeval ![X 0, X 0 * X 1] F) = eval ![x, x * z] F := by
    have h := aeval_bind₁ ![x, z] ![X 0, X 0 * X 1] F
    refine (h.trans ?_ :)
    change _ = aeval ![x, x * z] F
    congr 1
    ext j : 1
    fin_cases j <;> simp
  rw [map_mul, map_pow, eval_X, he] at h
  simpa using h.symm

@[simp]
theorem blowupStrictTransform_zero : blowupStrictTransform (0 : MvPolynomial (Fin 2) R) = 0 :=
  blowupStrictTransform_eq_of_aeval_eq (by simp)

/-- A constant curve is its own strict transform. -/
@[simp]
theorem blowupStrictTransform_C (c : R) : blowupStrictTransform (C c : MvPolynomial (Fin 2) R) =
    C c := by
  refine blowupStrictTransform_eq_of_aeval_eq ?_
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · simp [orderAt_C_of_ne_zero hc]

@[simp]
theorem blowupStrictTransform_one : blowupStrictTransform (1 : MvPolynomial (Fin 2) R) = 1 := by
  simpa using blowupStrictTransform_C (1 : R)

/-- The total transform of the line `X = 0` is the exceptional line, so its strict transform
is `1`. -/
@[simp]
theorem blowupStrictTransform_X_zero [Nontrivial R] :
    blowupStrictTransform (X 0 : MvPolynomial (Fin 2) R) = 1 := by
  refine blowupStrictTransform_eq_of_aeval_eq ?_
  rw [(isHomogeneous_X R 0).orderAt_zero (X_ne_zero _)]
  simp

/-- The strict transform of the line `Y = 0` is the line `Z = 0`. -/
@[simp]
theorem blowupStrictTransform_X_one [Nontrivial R] :
    blowupStrictTransform (X 1 : MvPolynomial (Fin 2) R) = X 1 := by
  refine blowupStrictTransform_eq_of_aeval_eq ?_
  rw [(isHomogeneous_X R 1).orderAt_zero (X_ne_zero _)]
  simp

/-- `G(0, Z) = G(1, Z)` for a polynomial `G` in `Z` alone. -/
private theorem aeval_zero_X_aeval_one_X (p : MvPolynomial (Fin 2) R) :
    aeval ![0, (X 1 : MvPolynomial (Fin 2) R)] (aeval ![1, (X 1 : MvPolynomial (Fin 2) R)] p) =
      aeval ![1, (X 1 : MvPolynomial (Fin 2) R)] p := by
  have h := aeval_bind₁ ![0, (X 1 : MvPolynomial (Fin 2) R)] ![1, X 1] p
  rw [← aeval_eq_bind₁] at h
  rw [h]
  congr 1
  ext j : 1
  fin_cases j <;> simp

/-- The value of the strict transform on the exceptional line `X = 0`: `F'(0, Z) = F_r(1, Z)`,
where `F_r` is the leading form of `F` at the origin. -/
theorem aeval_zero_X_blowupStrictTransform (F : MvPolynomial (Fin 2) R) :
    aeval ![0, (X 1 : MvPolynomial (Fin 2) R)] (blowupStrictTransform F) =
      aeval ![1, (X 1 : MvPolynomial (Fin 2) R)] (F.leadingFormAt 0) := by
  rw [blowupStrictTransform_eq_sum, map_sum, leadingFormAt_def, taylor_zero]
  simp_rw [map_mul, map_pow, aeval_zero_X_aeval_one_X]
  rw [Finset.sum_eq_single (F.orderAt 0).toNat]
  · simp
  · intro i _ hi
    rcases lt_or_gt_of_ne hi with hi | hi
    · simp [homogeneousComponent_eq_zero_of_lt_toNat hi]
    · simp [Nat.sub_ne_zero_of_lt hi]
  · intro h
    rw [homogeneousComponent_eq_zero _ _
      (by simpa [Nat.lt_succ_iff] using h), map_zero, mul_zero]

/-- The value of the strict transform on the exceptional line, as a polynomial in one variable:
`F'(0, T) = F_r(1, T)`. -/
theorem aeval_zero_polynomial_X_blowupStrictTransform (F : MvPolynomial (Fin 2) R) :
    (MvPolynomial.aeval ![0, Polynomial.X] (blowupStrictTransform F) : Polynomial R) =
      MvPolynomial.aeval ![1, Polynomial.X] (F.leadingFormAt 0) := by
  have h := congr(MvPolynomial.aeval ![(0 : Polynomial R), Polynomial.X]
    $(aeval_zero_X_blowupStrictTransform F))
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, comp_aeval, comp_aeval] at h
  convert h using 2 <;> (ext i : 1; fin_cases i <;> simp)

/-- The value of the strict transform at a point `(0, z)` of the exceptional line:
`F'(0, z) = F_r(1, z)`. -/
theorem eval_zero_blowupStrictTransform (F : MvPolynomial (Fin 2) R) (z : R) :
    eval ![0, z] (blowupStrictTransform F) = eval ![1, z] (F.leadingFormAt 0) := by
  have h := congr(MvPolynomial.aeval ![(0 : R), z] $(aeval_zero_X_blowupStrictTransform F))
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, comp_aeval, comp_aeval] at h
  change MvPolynomial.aeval ![0, z] _ = MvPolynomial.aeval ![1, z] _
  convert h using 2 <;> (ext i : 1; fin_cases i <;> simp)

/-- The strict transform of a nonzero curve is not divisible by `X`: it does not contain the
exceptional line. -/
theorem not_X_dvd_blowupStrictTransform (hF : F ≠ 0) : ¬ X 0 ∣ blowupStrictTransform F := by
  rintro ⟨q, hq⟩
  have h := aeval_zero_X_blowupStrictTransform F
  rw [hq, map_mul, aeval_X] at h
  simp only [Matrix.cons_val_zero, zero_mul] at h
  exact leadingFormAt_ne_zero hF
    (((isHomogeneous_leadingFormAt F 0).aeval_one_X_eq_zero_iff).1 h.symm)

end CommSemiring

section Domain

variable [CommRing R] [IsDomain R] {F G : MvPolynomial (Fin 2) R}

/-- Over a domain, a factorization `F(X, XZ) = X ^ n G` of a nonzero `F` with `X ∤ G` is the one
by the strict transform: `n` is the multiplicity of `F` at the origin and `G = F'`. -/
theorem blowupStrictTransform_eq_of_aeval_eq_of_not_dvd (hF : F ≠ 0) {n : ℕ}
    (h : aeval ![X 0, X 0 * X 1] F = X 0 ^ n * G) (hG : ¬ X 0 ∣ G) :
    (F.orderAt 0).toNat = n ∧ blowupStrictTransform F = G := by
  set r := (F.orderAt 0).toNat
  have hX : ∀ m : ℕ, (X 0 : MvPolynomial (Fin 2) R) ^ m ≠ 0 := fun m ↦ pow_ne_zero _ (X_ne_zero _)
  have h' : X 0 ^ r * blowupStrictTransform F = X 0 ^ n * G :=
    (X_pow_mul_blowupStrictTransform F).trans h
  have hrn : r = n := by
    rcases lt_trichotomy r n with hrn | hrn | hrn
    · rw [← Nat.add_sub_cancel' hrn.le, pow_add, mul_assoc] at h'
      exact absurd ⟨_, (mul_left_cancel₀ (hX r) h').trans
        (by rw [← Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt hrn), pow_succ', mul_assoc])⟩
        (not_X_dvd_blowupStrictTransform hF)
    · exact hrn
    · rw [← Nat.add_sub_cancel' hrn.le, pow_add, mul_assoc] at h'
      exact absurd ⟨_, (mul_left_cancel₀ (hX n) h').symm.trans
        (by rw [← Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt hrn), pow_succ', mul_assoc])⟩ hG
  exact ⟨hrn, mul_left_cancel₀ (hX r) (hrn ▸ h')⟩

/-- Over a domain, the strict transform is multiplicative: `(FG)' = F'G'`. -/
theorem blowupStrictTransform_mul (F G : MvPolynomial (Fin 2) R) :
    blowupStrictTransform (F * G) = blowupStrictTransform F * blowupStrictTransform G := by
  rcases eq_or_ne F 0 with rfl | hF
  · simp
  rcases eq_or_ne G 0 with rfl | hG
  · simp
  refine blowupStrictTransform_eq_of_aeval_eq ?_
  rw [orderAt_mul, ENat.toNat_add (orderAt_eq_top_iff.not.2 hF) (orderAt_eq_top_iff.not.2 hG),
    map_mul, ← X_pow_mul_blowupStrictTransform F, ← X_pow_mul_blowupStrictTransform G]
  ring

/-- Over a domain, the strict transform of `F ^ n` is the `n`-th power of that of `F`. -/
theorem blowupStrictTransform_pow (F : MvPolynomial (Fin 2) R) (n : ℕ) :
    blowupStrictTransform (F ^ n) = blowupStrictTransform F ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, blowupStrictTransform_mul, ih, pow_succ]

/-- Multiplying a curve by a constant multiplies its strict transform by the same constant. -/
@[simp]
theorem blowupStrictTransform_C_mul (c : R) (F : MvPolynomial (Fin 2) R) :
    blowupStrictTransform (C c * F) = C c * blowupStrictTransform F := by
  rw [blowupStrictTransform_mul, blowupStrictTransform_C]

/-- Multiplying a curve by a scalar multiplies its strict transform by the same scalar. -/
@[simp]
theorem blowupStrictTransform_smul (c : R) (F : MvPolynomial (Fin 2) R) :
    blowupStrictTransform (c • F) = c • blowupStrictTransform F := by
  rw [smul_eq_C_mul, smul_eq_C_mul, blowupStrictTransform_C_mul]

/-- The strict transform of the node `Y² - X² - X³` is `Z² - 1 - X`: the node has multiplicity
two at the origin, and its strict transform meets the exceptional line `X = 0` in the two points
`Z = ±1`, one for each tangent line `Y = ±X`. -/
theorem blowupStrictTransform_node :
    (((X 1 ^ 2 - X 0 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) R)).orderAt 0).toNat = 2 ∧
      blowupStrictTransform (X 1 ^ 2 - X 0 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) R) =
        X 1 ^ 2 - 1 - X 0 := by
  refine blowupStrictTransform_eq_of_aeval_eq_of_not_dvd ?_ ?_ ?_
  · intro h
    simpa using congr(eval ![0, 1] $h)
  · simp
    ring
  · rintro ⟨q, hq⟩
    simpa using congr(eval 0 $hq)

end Domain

section Fibre

/-! ### The fibre over the origin

The points of the strict transform on the exceptional line `X = 0` are the points `(0, α)` for
the tangents `Y - α X` of `F` at the origin, and the intersection number there with the
exceptional line is the multiplicity of the tangent. -/

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 2) k}

/-- **The fibre of the blow-up over the origin.** The strict transform of a nonzero curve `F`
passes through the point `(0, α)` of the exceptional line exactly when `Y - α X` is tangent to
`F` at the origin. -/
theorem eval_zero_blowupStrictTransform_eq_zero_iff (hF : F ≠ 0) (α : k) :
    eval ![0, α] (blowupStrictTransform F) = 0 ↔ IsTangentAt F 0 (X 1 - C α * X 0) := by
  have hG := (isHomogeneous_leadingFormAt F 0)
  rw [← tangentMultiplicity_pos_iff hF (isHomogeneous_X_one_sub_C_mul_X_zero α)
    (X_one_sub_C_mul_X_zero_ne_zero α), tangentMultiplicity_def,
    hG.multiplicity_X_one_sub_C_mul_X_zero (leadingFormAt_ne_zero hF),
    Polynomial.rootMultiplicity_pos
      ((hG.aeval_one_polynomial_X_eq_zero_iff).not.2 (leadingFormAt_ne_zero hF)),
    Polynomial.IsRoot.def, eval_zero_blowupStrictTransform, ← Polynomial.coe_aeval_eq_eval,
    ← AlgHom.comp_apply, comp_aeval]
  change MvPolynomial.aeval ![1, α] _ = 0 ↔ _
  congr! 2
  ext i : 1
  fin_cases i <;> simp

/-- **Intersection with the exceptional line.** For a nonzero curve `F`, the intersection number
at `(0, α)` of the strict transform with the exceptional line `X = 0` is the multiplicity of
`Y - α X` as a tangent of `F` at the origin. -/
theorem intersectionNumber_blowupStrictTransform_X_zero (hF : F ≠ 0) (α : k) :
    intersectionNumber ![0, α] (blowupStrictTransform F) (X 0) =
      tangentMultiplicity F 0 (X 1 - C α * X 0) := by
  have hG := isHomogeneous_leadingFormAt F 0
  have hv : (![0, 1] : Fin 2 → k) ≠ 0 := fun h ↦ by simpa using congrFun h 1
  have hr : (fun i ↦ Polynomial.C ((0 : Fin 2 → k) i) + Polynomial.C (![0, 1] i) * Polynomial.X) =
      ![0, Polynomial.X] := by
    ext i : 1
    fin_cases i <;> simp
  have h := intersectionNumber_line_eq_rootMultiplicity (a := 0) (F := blowupStrictTransform F) hv
    (by
      rw [hr, aeval_zero_polynomial_X_blowupStrictTransform]
      exact hG.aeval_one_polynomial_X_eq_zero_iff.not.2 (leadingFormAt_ne_zero hF)) α
  rw [hr, aeval_zero_polynomial_X_blowupStrictTransform] at h
  have hP : (0 : Fin 2 → k) + α • ![0, 1] = ![0, α] := by
    ext i : 1
    fin_cases i <;> simp
  rw [hP] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Pi.zero_apply,
    map_one, map_zero, sub_zero, one_mul, zero_mul] at h
  rw [intersectionNumber_comm, h, tangentMultiplicity_def,
    hG.multiplicity_X_one_sub_C_mul_X_zero (leadingFormAt_ne_zero hF)]

/-- The multiplicity of the strict transform at a point `(0, α)` of the exceptional line is at
most its intersection number there with the exceptional line. -/
theorem orderAt_blowupStrictTransform_le_intersectionNumber (F : MvPolynomial (Fin 2) k) (α : k) :
    (blowupStrictTransform F).orderAt ![0, α] ≤
      intersectionNumber ![0, α] (blowupStrictTransform F) (X 0) := by
  have h1 : (X 0 : MvPolynomial (Fin 2) k).orderAt ![0, α] = 1 :=
    isSimplePoint_iff_orderAt_eq_one.1 (isSimplePoint_def.2 ⟨by simp, 0, by simp⟩)
  simpa [h1] using
    mul_orderAt_le_intersectionNumber ![0, α] (blowupStrictTransform F) (X 0)

/-- The multiplicity of the strict transform of a nonzero curve `F` at `(0, α)` is at most the
multiplicity of `Y - α X` as a tangent of `F` at the origin. -/
theorem orderAt_blowupStrictTransform_le_tangentMultiplicity (hF : F ≠ 0) (α : k) :
    (blowupStrictTransform F).orderAt ![0, α] ≤ tangentMultiplicity F 0 (X 1 - C α * X 0) :=
  intersectionNumber_blowupStrictTransform_X_zero hF α ▸
    orderAt_blowupStrictTransform_le_intersectionNumber F α

/-- **Blowing up an ordinary multiple point.** If the origin is an ordinary multiple point of `F`
and `Y - α X` is a tangent there, then `(0, α)` is a simple point of the strict transform, where
it meets the exceptional line with intersection number one. -/
theorem IsOrdinaryMultiplePoint.isSimplePoint_blowupStrictTransform
    (h : IsOrdinaryMultiplePoint F 0) {α : k} (hα : IsTangentAt F 0 (X 1 - C α * X 0)) :
    IsSimplePoint (blowupStrictTransform F) ![0, α] ∧
      intersectionNumber ![0, α] (blowupStrictTransform F) (X 0) = 1 := by
  have hI : intersectionNumber ![0, α] (blowupStrictTransform F) (X 0) = 1 := by
    rw [intersectionNumber_blowupStrictTransform_X_zero h.ne_zero, h.tangentMultiplicity_eq_one hα,
      Nat.cast_one]
  refine ⟨isSimplePoint_iff_orderAt_eq_one.2 (le_antisymm ?_ ?_), hI⟩
  · exact hI ▸ orderAt_blowupStrictTransform_le_intersectionNumber F α
  · exact Order.one_le_iff_pos.2 (orderAt_pos_iff.2
      ((eval_zero_blowupStrictTransform_eq_zero_iff h.ne_zero α).2 hα))

/-- If the origin is an ordinary multiple point of `F` and `Y - α X` is a tangent there, then the
exceptional line `X = 0` has order one at the simple point `(0, α)` of the strict transform: the
order `ord_{(0, α)}(x)` in the local ring of the strict transform is one. -/
theorem IsOrdinaryMultiplePoint.ord_X_zero_blowupStrictTransform
    (h : IsOrdinaryMultiplePoint F 0) {α : k} (hα : IsTangentAt F 0 (X 1 - C α * X 0)) :
    Ring.ord (AffineSpace.localRing k ![0, α] ⧸
        Ideal.span {algebraMap _ (AffineSpace.localRing k ![0, α]) (blowupStrictTransform F)})
      (Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin 2) k) (AffineSpace.localRing k ![0, α])
        (X 0))) = 1 :=
  (intersectionNumber_eq_ord _ _ _).symm.trans (h.isSimplePoint_blowupStrictTransform hα).2

/-- Over an algebraically closed field, if `X` is not tangent to the nonzero curve `F` at the
origin, the points of the strict transform on the exceptional line are the points `(0, α)` for
`α` in a finite set `A`, and the leading form of `F` at the origin is
`ε ∏_{α ∈ A} (Y - α X) ^ rₐ` with `ε ≠ 0` and `rₐ` the multiplicity of the tangent `Y - α X`. -/
theorem exists_finset_eval_zero_blowupStrictTransform [IsAlgClosed k] (hF : F ≠ 0)
    (hX : ¬IsTangentAt F 0 (X 0)) :
    ∃ A : Finset k, (∀ α, α ∈ A ↔ eval ![0, α] (blowupStrictTransform F) = 0) ∧
      ∃ ε : k, ε ≠ 0 ∧ F.leadingFormAt 0 =
        C ε * ∏ α ∈ A, (X 1 - C α * X 0) ^ tangentMultiplicity F 0 (X 1 - C α * X 0) := by
  classical
  set g : Polynomial k := MvPolynomial.aeval ![0, Polynomial.X] (blowupStrictTransform F)
  have hg : g ≠ 0 := by
    rw [show g = _ from aeval_zero_polynomial_X_blowupStrictTransform F]
    exact (isHomogeneous_leadingFormAt F 0).aeval_one_polynomial_X_eq_zero_iff.not.2
      (leadingFormAt_ne_zero hF)
  have hA : ∀ α, α ∈ g.roots.toFinset ↔ eval ![0, α] (blowupStrictTransform F) = 0 := by
    intro α
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hg, Polynomial.IsRoot.def,
      ← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, comp_aeval]
    change _ ↔ MvPolynomial.aeval ![0, α] _ = 0
    congr! 2
    ext i : 1
    fin_cases i <;> simp
  have hfib := eval_zero_blowupStrictTransform_eq_zero_iff hF
  refine ⟨g.roots.toFinset, hA, ?_⟩
  have hs : ∀ L ∈ g.roots.toFinset.image (fun α ↦ (X 1 - C α * X 0 : MvPolynomial (Fin 2) k)),
      IsTangentAt F 0 L := by
    simp only [Finset.mem_image]
    rintro _ ⟨α, hα, rfl⟩
    exact (hfib α).1 ((hA α).1 hα)
  have hpair : (↑(g.roots.toFinset.image (fun α ↦ (X 1 - C α * X 0 : MvPolynomial (Fin 2) k))) :
      Set (MvPolynomial (Fin 2) k)).Pairwise (fun L L' ↦ ¬Associated L L') := by
    simp only [Finset.coe_image, Set.Pairwise, Set.mem_image, Finset.mem_coe]
    rintro _ ⟨α, -, rfl⟩ _ ⟨β, -, rfl⟩ hne h
    exact hne (by rw [associated_X_one_sub_C_mul_X_zero_iff.1 h])
  have hcov : ∀ L, IsTangentAt F 0 L → ∃ L' ∈ g.roots.toFinset.image
      (fun α ↦ (X 1 - C α * X 0 : MvPolynomial (Fin 2) k)), Associated L L' := by
    intro L hL
    obtain ⟨α, hα⟩ := hL.exists_associated_X_one_sub_C_mul_X_zero hX
    refine ⟨_, Finset.mem_image_of_mem _ ((hA α).2 ((hfib α).2 ?_)), hα⟩
    exact isTangentAt_def.2 ⟨isHomogeneous_X_one_sub_C_mul_X_zero α,
      X_one_sub_C_mul_X_zero_ne_zero α, hα.symm.dvd.trans hL.dvd⟩
  obtain ⟨ε, hε, heq⟩ := leadingFormAt_eq_C_mul_prod_pow hs hpair hcov hF
  exact ⟨ε, hε, by rwa [Finset.prod_image fun α _ β _ h ↦
    X_one_sub_C_mul_X_zero_injective h] at heq⟩

/-- The strict transform of the cusp `Y² - X³` is `Z² - X`: the cusp has multiplicity two at the
origin, and its only tangent is `Y`. -/
theorem blowupStrictTransform_cusp :
    (((X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k)).orderAt 0).toNat = 2 ∧
      blowupStrictTransform (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k) = X 1 ^ 2 - X 0 := by
  refine blowupStrictTransform_eq_of_aeval_eq_of_not_dvd ?_ ?_ ?_
  · intro h
    simpa using congr(eval ![0, 1] $h)
  · simp
    ring
  · rintro ⟨q, hq⟩
    simpa using congr(eval ![0, 1] $hq)

/-- The strict transform `Z² - X` of the cusp `Y² - X³` meets the exceptional line `X = 0` only
at the origin, the point corresponding to its tangent `Y` (Problem 7.6 of Fulton). -/
theorem eval_zero_blowupStrictTransform_cusp_eq_zero_iff (α : k) :
    eval ![0, α] (blowupStrictTransform (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k)) = 0 ↔
      α = 0 := by
  simp [(blowupStrictTransform_cusp (k := k)).2]

/-- The only point `(0, 0)` of the strict transform of the cusp `Y² - X³` over the origin is a
simple point of it. -/
theorem isSimplePoint_blowupStrictTransform_cusp :
    IsSimplePoint (blowupStrictTransform (X 1 ^ 2 - X 0 ^ 3 : MvPolynomial (Fin 2) k)) 0 := by
  rw [(blowupStrictTransform_cusp (k := k)).2]
  exact isSimplePoint_def.2 ⟨by simp, 0, by simp⟩

end Fibre

end PlaneCurves.Affine

end
