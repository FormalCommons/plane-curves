/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import TauCeti.RingTheory.Conductor
public import TauCeti.RingTheory.Ideal.AffineBlowup
public import PlaneCurves.AlgebraicGeometry.AffineSpace.PlaneZeroLocus
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.Blowup.Basic

/-!
# The chart of the blow-up of a plane curve over the origin

Let `F = ∑ a_{ij} X ^ i Y ^ j` be a plane curve of multiplicity `r` at the origin, and let `x, y`
satisfy `F(x, y) = 0` in a ring `A`. In an `A`-algebra in which `x` is a nonzerodivisor, an
element `z` with `xz = y` (such as `y/x` in the affine blow-up algebra `A[(x, y)/x]`) satisfies
Fulton's equation

  `∑ a_{ij} x ^ (i - r) y ^ (j - (r - i)) z ^ (r - i) = 0`,

the equation `F'(x, z) = 0` of the strict transform with its high powers of `z` rewritten through
`xz = y`. It has degree at most `r` in `z`, and its coefficient of `z ^ r` is `H(x, y)` for the
polynomial `H = ∑_j a_{0j} Y ^ (j - r)`, whose value `H(0, 0) = a_{0r}` is nonzero exactly when
`X` is not tangent to `F` at the origin. So, once `H(x, y)` is inverted, as on the open set
`W = C_{gH}` of the curve `C = V(F)` for any `g`, the element `z = y/x` is integral of degree `r`,
the affine blow-up algebra `Γ(W') = Γ(W)[y/x]` is module-finite over `Γ(W)`, and `x ^ (r - 1)`
lies in its conductor (Step (3) of §7.2 of Fulton). When `F` is prime and does not divide `X`,
`Γ(W)` embeds in `Γ(W')`, so every point of `W` lies under a point of `W'`, and the map
`Spec Γ(W') → Spec Γ(W)` is closed. A shear `X ↦ X + dY` makes `W` contain any given finite set of
points (Fulton's Remarks).

## Main definitions

* `PlaneCurves.Affine.blowupChartPolynomial F x y`: the polynomial
  `∑ a_{ij} x ^ (i - r) y ^ (j - (r - i)) T ^ (r - i)` over `A`.
* `PlaneCurves.Affine.blowupChartLeadingCoeff F`: the polynomial `H`, its coefficient of
  `T ^ r` over `k[X, Y]`.

## Main results

* `PlaneCurves.Affine.algebraMap_pow_mul_aeval_blowupChartPolynomial`: for `xz = y`,
  `x ^ r P(z) = F(x, y)`.
* `PlaneCurves.Affine.coeff_blowupChartPolynomial`: the coefficient of `T ^ r` is `H(x, y)`;
  `PlaneCurves.Affine.eval_zero_blowupChartLeadingCoeff`: `H(0, 0) = a_{0r}`; and, for `r ≥ 1`,
  `PlaneCurves.Affine.pow_mul_aeval_blowupChartLeadingCoeff`: `y ^ r H(x, y) = F(0, y)`.
* `PlaneCurves.Affine.exists_monic_aeval_eq_zero_of_isUnit_aeval_blowupChartLeadingCoeff`,
  `PlaneCurves.Affine.isIntegral_of_isUnit_aeval_blowupChartLeadingCoeff`,
  `PlaneCurves.Affine.finite_adjoin_of_isUnit_aeval_blowupChartLeadingCoeff`,
  `PlaneCurves.Affine.pow_mem_conductor_adjoin_of_isUnit_aeval_blowupChartLeadingCoeff`: if
  `H(x, y)` is a unit, `z` is a root of a monic polynomial of degree `r`, `A[z]` is module-finite
  over `A` and `x ^ (r - 1)` lies in the conductor of `A[z]`.
* `PlaneCurves.Affine.affineBlowup_span_pair_eq_adjoin`,
  `PlaneCurves.Affine.finite_affineBlowup_of_isUnit_aeval_blowupChartLeadingCoeff`,
  `PlaneCurves.Affine.pow_mem_conductor_affineBlowup_of_isUnit_aeval_blowupChartLeadingCoeff`,
  `PlaneCurves.Affine.exists_monic_aeval_divBy_eq_zero_of_isUnit_aeval_blowupChartLeadingCoeff`:
  the same for the affine blow-up algebra `A[(x, y)/x] = A[y/x]`.
* `PlaneCurves.Affine.finite_affineBlowup_blowupChart`,
  `PlaneCurves.Affine.exists_monic_aeval_divBy_blowupChart`,
  `PlaneCurves.Affine.pow_mem_conductor_affineBlowup_blowupChart`: Step (3) for a plane curve:
  on `W = C_{gH}`, a neighbourhood of the origin when `g(0) ≠ 0` and `X` is not tangent
  (`PlaneCurves.Affine.isTangentAt_zero_X_zero_iff`), `Γ(W') = Γ(W)[y/x]` is module-finite over
  `Γ(W)`, `y/x` is integral of degree `r` and `x ^ (r - 1)` lies in the conductor.
* `PlaneCurves.Affine.injective_algebraMap_affineBlowup_blowupChart`,
  `PlaneCurves.Affine.exists_isPrime_comap_affineBlowup_blowupChart`,
  `PlaneCurves.Affine.isClosedMap_comap_affineBlowup_blowupChart`: `Γ(W) → Γ(W')` is injective,
  so `f(W') = W`, and `Spec Γ(W') → Spec Γ(W)` is closed.
* `PlaneCurves.Affine.exists_linearSubst_eval_blowupChartLeadingCoeff_ne_zero`: after a shear
  `X ↦ X + dY`, `H` does not vanish at any given finite set of points.
* `PlaneCurves.Affine.blowupStrictTransform_fibre_finite`: the milestone, Steps (1)–(3) of §7.2
  together, with the Remarks.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.2
-/


public section

namespace PlaneCurves.Affine

open MvPolynomial TauCeti.Localization

section Polynomial

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- **Fulton's equation of `y/x`.** For the plane curve `F = ∑ a_{ij} X ^ i Y ^ j` of
multiplicity `r` at the origin and `x, y` in an `R`-algebra `A`, the polynomial
`∑ a_{ij} x ^ (i - r) y ^ (j - (r - i)) T ^ (r - i)` over `A`, with truncated subtraction. When
`xz = y` it is `F'(x, z)`, the strict transform evaluated at `(x, z)`. -/
noncomputable def blowupChartPolynomial (F : MvPolynomial (Fin 2) R) (x y : A) : Polynomial A :=
  ∑ m ∈ F.support, Polynomial.monomial ((F.orderAt 0).toNat - m 0)
    (algebraMap R A (F.coeff m) * x ^ (m 0 - (F.orderAt 0).toNat) *
      y ^ (m 1 - ((F.orderAt 0).toNat - m 0)))

theorem blowupChartPolynomial_def (F : MvPolynomial (Fin 2) R) (x y : A) :
    blowupChartPolynomial F x y = ∑ m ∈ F.support, Polynomial.monomial ((F.orderAt 0).toNat - m 0)
      (algebraMap R A (F.coeff m) * x ^ (m 0 - (F.orderAt 0).toNat) *
        y ^ (m 1 - ((F.orderAt 0).toNat - m 0))) :=
  (rfl)

/-- The polynomial `H = ∑_j a_{0j} Y ^ (j - r)` of Fulton's Step (3): the coefficient of `T ^ r`
in `blowupChartPolynomial F (X 0) (X 1)`. -/
noncomputable def blowupChartLeadingCoeff (F : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R :=
  (blowupChartPolynomial F (X 0 : MvPolynomial (Fin 2) R) (X 1)).coeff (F.orderAt 0).toNat

theorem blowupChartLeadingCoeff_def (F : MvPolynomial (Fin 2) R) :
    blowupChartLeadingCoeff F =
      (blowupChartPolynomial F (X 0 : MvPolynomial (Fin 2) R) (X 1)).coeff (F.orderAt 0).toNat :=
  (rfl)

/-- The chart polynomial commutes with `R`-algebra maps. -/
theorem map_blowupChartPolynomial {A' : Type*} [CommSemiring A'] [Algebra R A'] (f : A →ₐ[R] A')
    (F : MvPolynomial (Fin 2) R) (x y : A) :
    (blowupChartPolynomial F x y).map (f : A →+* A') = blowupChartPolynomial F (f x) (f y) := by
  simp [blowupChartPolynomial_def, Polynomial.map_sum]

/-- The coefficient of `T ^ r` in the chart polynomial at `(x, y)` is `H(x, y)`. -/
theorem coeff_blowupChartPolynomial (F : MvPolynomial (Fin 2) R) (x y : A) :
    (blowupChartPolynomial F x y).coeff (F.orderAt 0).toNat =
      aeval ![x, y] (blowupChartLeadingCoeff F) := by
  have h := congrArg (fun p : Polynomial A ↦ p.coeff (F.orderAt 0).toNat)
    (map_blowupChartPolynomial (aeval ![x, y]) F (X 0 : MvPolynomial (Fin 2) R) (X 1))
  rw [Polynomial.coeff_map] at h
  simpa [blowupChartLeadingCoeff_def] using h.symm

/-- The chart polynomial has degree at most the multiplicity `r`. -/
theorem natDegree_blowupChartPolynomial_le (F : MvPolynomial (Fin 2) R) (x y : A) :
    (blowupChartPolynomial F x y).natDegree ≤ (F.orderAt 0).toNat :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun _ _ ↦
    (Polynomial.natDegree_monomial_le _).trans (Nat.sub_le _ _)

/-- Every monomial `X ^ i Y ^ j` of `F` has `r ≤ i + j`. -/
private theorem toNat_orderAt_zero_le {F : MvPolynomial (Fin 2) R} {m : Fin 2 →₀ ℕ}
    (hm : m ∈ F.support) : (F.orderAt 0).toNat ≤ m 0 + m 1 := by
  simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using toNat_orderAt_zero_le_degree hm

/-- **The chart equation.** If `xz = y` in an `A`-algebra `B`, then `x ^ r P(z) = F(x, y)` for
the chart polynomial `P` of `F` at `(x, y)`. -/
theorem algebraMap_pow_mul_aeval_blowupChartPolynomial {B : Type*} [CommSemiring B] [Algebra A B]
    (F : MvPolynomial (Fin 2) R) {x y : A} {z : B}
    (hz : algebraMap A B x * z = algebraMap A B y) :
    algebraMap A B x ^ (F.orderAt 0).toNat * Polynomial.aeval z (blowupChartPolynomial F x y) =
      algebraMap A B (aeval ![x, y] F) := by
  rw [blowupChartPolynomial_def, map_sum, Finset.mul_sum, aeval_def, eval₂_eq', map_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hr := toNat_orderAt_zero_le hm
  set r := (F.orderAt 0).toNat
  set X' := algebraMap A B x
  set c := algebraMap A B (algebraMap R A (F.coeff m))
  have h1 : X' ^ r * X' ^ (m 0 - r) = X' ^ m 0 * X' ^ (r - m 0) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have h2 : m 1 = m 1 - (r - m 0) + (r - m 0) := by omega
  simp only [Polynomial.aeval_monomial, Fin.prod_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, map_mul, map_pow, ← hz]
  conv_rhs => rw [h2, pow_add (X' * z), mul_pow X' z (r - m 0)]
  calc X' ^ r * (c * X' ^ (m 0 - r) * (X' * z) ^ (m 1 - (r - m 0)) * z ^ (r - m 0))
      = c * (X' * z) ^ (m 1 - (r - m 0)) * z ^ (r - m 0) * (X' ^ r * X' ^ (m 0 - r)) := by ring
    _ = c * (X' ^ m 0 * ((X' * z) ^ (m 1 - (r - m 0)) * (X' ^ (r - m 0) * z ^ (r - m 0)))) := by
      rw [h1]; ring

/-- At `x = y = 0` the coefficient of `T ^ r` is `a_{0r}`, the coefficient of `Y ^ r` in `F`. -/
theorem coeff_blowupChartPolynomial_zero_zero (F : MvPolynomial (Fin 2) R) :
    (blowupChartPolynomial F (0 : A) 0).coeff (F.orderAt 0).toNat =
      algebraMap R A (F.coeff (Finsupp.single 1 (F.orderAt 0).toNat)) := by
  classical
  rw [blowupChartPolynomial_def, Polynomial.finsetSum_coeff]
  set r := (F.orderAt 0).toNat
  refine (Finset.sum_eq_single (Finsupp.single 1 r) (fun m hm hne ↦ ?_) fun h ↦ ?_).trans ?_
  · have hr := toNat_orderAt_zero_le hm
    rw [Polynomial.coeff_monomial, Finsupp.single_apply]
    split_ifs with h
    · rcases Nat.eq_zero_or_pos (m 0 - r) with h0 | h0
      · have h1 : m 1 - (r - m 0) ≠ 0 := by
          intro h1
          apply hne
          ext i
          fin_cases i <;> simp <;> omega
        simp [zero_pow h1]
      · simp [zero_pow h0.ne']
    · rfl
  · simp [notMem_support_iff.1 h]
  · simp [Polynomial.coeff_monomial]

/-- `H(0, 0) = a_{0r}`, the coefficient of `Y ^ r` in `F`. -/
theorem eval_zero_blowupChartLeadingCoeff (F : MvPolynomial (Fin 2) R) :
    eval 0 (blowupChartLeadingCoeff F) = F.coeff (Finsupp.single 1 (F.orderAt 0).toNat) := by
  have h := coeff_blowupChartPolynomial (A := R) F 0 0
  rw [coeff_blowupChartPolynomial_zero_zero] at h
  have h0 : (![0, 0] : Fin 2 → R) = 0 := by
    ext i : 1
    fin_cases i <;> rfl
  rw [h0] at h
  simpa [MvPolynomial.coe_aeval_eq_eval] using h.symm


/-- For `r ≥ 1`, `H(x, y) = ∑_j a_{0j} y ^ (j - r)`. -/
theorem aeval_blowupChartLeadingCoeff (F : MvPolynomial (Fin 2) R)
    (hr : 0 < (F.orderAt 0).toNat) (x y : A) :
    aeval ![x, y] (blowupChartLeadingCoeff F) = ∑ m ∈ F.support,
      if m 0 = 0 then algebraMap R A (F.coeff m) * y ^ (m 1 - (F.orderAt 0).toNat) else 0 := by
  classical
  rw [← coeff_blowupChartPolynomial, blowupChartPolynomial_def, Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  by_cases h : m 0 = 0
  · simp [h, Polynomial.coeff_monomial]
  · rw [Polynomial.coeff_monomial_of_ne _ (by omega)]
    simp [h]

/-- For `r ≥ 1`, `H` does not involve `X`: `H(x, y) = H(0, y)`. -/
theorem aeval_blowupChartLeadingCoeff_eq_aeval_zero (F : MvPolynomial (Fin 2) R)
    (hr : 0 < (F.orderAt 0).toNat) (x y : A) :
    aeval ![x, y] (blowupChartLeadingCoeff F) = aeval ![0, y] (blowupChartLeadingCoeff F) := by
  rw [aeval_blowupChartLeadingCoeff F hr, aeval_blowupChartLeadingCoeff F hr]

/-- For `r ≥ 1`, `y ^ r H(x, y) = F(0, y)`: `H` is `F(0, Y) / Y ^ r`. -/
theorem pow_mul_aeval_blowupChartLeadingCoeff (F : MvPolynomial (Fin 2) R)
    (hr : 0 < (F.orderAt 0).toNat) (x y : A) :
    y ^ (F.orderAt 0).toNat * aeval ![x, y] (blowupChartLeadingCoeff F) = aeval ![0, y] F := by
  rw [aeval_blowupChartLeadingCoeff F hr, Finset.mul_sum, aeval_def, eval₂_eq']
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have := toNat_orderAt_zero_le hm
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  by_cases h : m 0 = 0
  · simp only [h, ↓reduceIte, pow_zero, one_mul]
    rw [mul_left_comm, ← pow_add, Nat.add_sub_cancel' (by omega)]
  · simp only [h, ↓reduceIte, zero_pow h, zero_mul, mul_zero]

end Polynomial

section Integral

variable {R A B : Type*} [CommSemiring R] [CommRing A] [Algebra R A] [CommRing B] [Algebra A B]
  {F : MvPolynomial (Fin 2) R} {x y : A} {z : B}

/-- If `F(x, y) = 0` and `xz = y` with `x` a nonzerodivisor, then `z` is a root of the chart
polynomial. -/
theorem aeval_blowupChartPolynomial_eq_zero (hF : aeval ![x, y] F = 0)
    (hz : algebraMap A B x * z = algebraMap A B y) (hx : IsLeftRegular (algebraMap A B x)) :
    Polynomial.aeval z (blowupChartPolynomial F x y) = 0 := by
  have h : algebraMap A B x ^ (F.orderAt 0).toNat * Polynomial.aeval z
      (blowupChartPolynomial F x y) = algebraMap A B x ^ (F.orderAt 0).toNat * 0 := by
    rw [algebraMap_pow_mul_aeval_blowupChartPolynomial F hz, hF, map_zero, mul_zero]
  exact hx.pow _ h

/-- The chart polynomial divided by its unit coefficient `H(x, y)`: monic, of degree at most
`r`, with root `z`. -/
private theorem exists_monic_natDegree_le (hF : aeval ![x, y] F = 0)
    (hz : algebraMap A B x * z = algebraMap A B y) (hx : IsLeftRegular (algebraMap A B x))
    (hH : IsUnit (aeval ![x, y] (blowupChartLeadingCoeff F))) :
    ∃ p : Polynomial A, p.Monic ∧ p.natDegree ≤ (F.orderAt 0).toNat ∧
      p.coeff (F.orderAt 0).toNat = 1 ∧ Polynomial.aeval z p = 0 := by
  have hd : (Polynomial.C ((hH.unit⁻¹ : Aˣ) : A) * blowupChartPolynomial F x y).natDegree ≤
      (F.orderAt 0).toNat :=
    (Polynomial.natDegree_C_mul_le _ _).trans (natDegree_blowupChartPolynomial_le F x y)
  have h1 : (Polynomial.C ((hH.unit⁻¹ : Aˣ) : A) * blowupChartPolynomial F x y).coeff
      (F.orderAt 0).toNat = 1 := by
    rw [Polynomial.coeff_C_mul, coeff_blowupChartPolynomial]
    exact hH.val_inv_mul
  refine ⟨_, Polynomial.monic_of_natDegree_le_of_coeff_eq_one _ hd h1, hd, h1, ?_⟩
  rw [map_mul, aeval_blowupChartPolynomial_eq_zero hF hz hx, mul_zero]

/-- **`y/x` is integral of degree `r`.** If `F(x, y) = 0`, `H(x, y)` is a unit and `xz = y`
with `x` a nonzerodivisor, then `z` is a root of a monic polynomial over `A` of degree the
multiplicity `r` of `F` at the origin. -/
theorem exists_monic_aeval_eq_zero_of_isUnit_aeval_blowupChartLeadingCoeff [Nontrivial A]
    (hF : aeval ![x, y] F = 0) (hz : algebraMap A B x * z = algebraMap A B y)
    (hx : IsLeftRegular (algebraMap A B x))
    (hH : IsUnit (aeval ![x, y] (blowupChartLeadingCoeff F))) :
    ∃ p : Polynomial A, p.Monic ∧ p.natDegree = (F.orderAt 0).toNat ∧
      Polynomial.aeval z p = 0 := by
  obtain ⟨p, hp, hd, h1, h0⟩ := exists_monic_natDegree_le hF hz hx hH
  exact ⟨p, hp, le_antisymm hd (Polynomial.le_natDegree_of_ne_zero (by simp [h1])), h0⟩

/-- If `F(x, y) = 0`, `H(x, y)` is a unit and `xz = y` with `x` a nonzerodivisor, then `z` is
integral over `A`. -/
theorem isIntegral_of_isUnit_aeval_blowupChartLeadingCoeff (hF : aeval ![x, y] F = 0)
    (hz : algebraMap A B x * z = algebraMap A B y) (hx : IsLeftRegular (algebraMap A B x))
    (hH : IsUnit (aeval ![x, y] (blowupChartLeadingCoeff F))) : IsIntegral A z := by
  obtain ⟨p, hp, -, -, h0⟩ := exists_monic_natDegree_le hF hz hx hH
  exact ⟨p, hp, by rwa [← Polynomial.aeval_def]⟩

/-- If `F(x, y) = 0`, `H(x, y)` is a unit and `xz = y` with `x` a nonzerodivisor, then `A[z]`
is module-finite over `A`. -/
theorem finite_adjoin_of_isUnit_aeval_blowupChartLeadingCoeff (hF : aeval ![x, y] F = 0)
    (hz : algebraMap A B x * z = algebraMap A B y) (hx : IsLeftRegular (algebraMap A B x))
    (hH : IsUnit (aeval ![x, y] (blowupChartLeadingCoeff F))) :
    Module.Finite A (Algebra.adjoin A {z}) :=
  Algebra.finite_adjoin_simple_of_isIntegral
    (isIntegral_of_isUnit_aeval_blowupChartLeadingCoeff hF hz hx hH)

/-- If `xz = y`, then `x ^ (r - 1) s(z)` lies in the image of `A` for every polynomial `s` of
degree less than `r`. -/
private theorem exists_algebraMap_eq_pow_mul_aeval {r : ℕ}
    (hz : algebraMap A B x * z = algebraMap A B y) {s : Polynomial A} (hs : s.degree < r) :
    ∃ c : A, algebraMap A B c = algebraMap A B x ^ (r - 1) * Polynomial.aeval z s := by
  rcases eq_or_ne s 0 with rfl | hs0
  · exact ⟨0, by simp⟩
  have hn : s.natDegree < r := (Polynomial.natDegree_lt_iff_degree_lt hs0).2 hs
  refine ⟨∑ i ∈ Finset.range r, s.coeff i * x ^ (r - 1 - i) * y ^ i, ?_⟩
  rw [Polynomial.aeval_eq_sum_range' hn, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi : i ≤ r - 1 := by
    have := Finset.mem_range.1 hi
    omega
  rw [Algebra.smul_def, map_mul, map_mul, map_pow, map_pow, ← hz, mul_pow]
  conv_rhs => rw [← Nat.sub_add_cancel hi, pow_add]
  ring

/-- **The conductor.** If `F(x, y) = 0`, `H(x, y)` is a unit and `xz = y` with `x` a
nonzerodivisor, then `x ^ (r - 1)` lies in the conductor of `A[z]` over `A`: it carries `A[z]`
into `A`. -/
theorem pow_mem_conductor_adjoin_of_isUnit_aeval_blowupChartLeadingCoeff
    (hF : aeval ![x, y] F = 0) (hz : algebraMap A B x * z = algebraMap A B y)
    (hx : IsLeftRegular (algebraMap A B x))
    (hH : IsUnit (aeval ![x, y] (blowupChartLeadingCoeff F))) :
    x ^ ((F.orderAt 0).toNat - 1) ∈ TauCeti.Algebra.conductor A (Algebra.adjoin A {z}) := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim (x ^ ((F.orderAt 0).toNat - 1)) 0]
    exact zero_mem _
  obtain ⟨p, hp, hd, -, h0⟩ := exists_monic_natDegree_le hF hz hx hH
  rw [TauCeti.Algebra.mem_conductor_iff]
  rintro ⟨b, hb⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
  obtain ⟨q, rfl⟩ := hb
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_pow_mul_aeval (r := (F.orderAt 0).toNat) hz
    (s := q %ₘ p) ((Polynomial.degree_modByMonic_lt q hp).trans_le
      (Polynomial.degree_le_of_natDegree_le hd))
  refine ⟨c, Subtype.ext ?_⟩
  rw [Polynomial.aeval_modByMonic_eq_self_of_root h0] at hc
  simpa [map_pow] using hc

end Integral

section AffineBlowup

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
  {F : MvPolynomial (Fin 2) R} {x y : A} {S : Type*} [CommRing S] [Algebra A S]
  [IsLocalization.Away x S]

/-- The affine blow-up algebra `A[(x, y)/x]` is `A[y/x]`. -/
theorem affineBlowup_span_pair_eq_adjoin (x y : A) [IsLocalization.Away x S] :
    (Ideal.span {x, y}).affineBlowup x S = Algebra.adjoin A {(divBy y x : S)} := by
  rw [Ideal.affineBlowup_eq_adjoin_of_span_eq rfl, Set.image_pair, divBy_self]
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_mono (by simp))
  rintro _ (rfl | rfl)
  · exact one_mem _
  · exact Algebra.subset_adjoin rfl

private theorem isLeftRegular_algebraMap (x : A) [IsLocalization.Away x S] :
    IsLeftRegular (algebraMap A S x) :=
  (IsLocalization.Away.algebraMap_isUnit (S := S) x).isRegular.left

/-- **Local finiteness of the blow-up.** If `F(x, y) = 0` and `H(x, y)` is a unit, the affine
blow-up algebra `A[(x, y)/x]` is module-finite over `A`. -/
theorem finite_affineBlowup_of_isUnit_aeval_blowupChartLeadingCoeff (hF : aeval ![x, y] F = 0)
    (hH : IsUnit (aeval ![x, y] (blowupChartLeadingCoeff F))) :
    Module.Finite A ((Ideal.span {x, y}).affineBlowup x S) := by
  rw [affineBlowup_span_pair_eq_adjoin]
  exact finite_adjoin_of_isUnit_aeval_blowupChartLeadingCoeff hF (algebraMap_mul_divBy y x)
    (isLeftRegular_algebraMap x) hH

/-- If `F(x, y) = 0` and `H(x, y)` is a unit, `x ^ (r - 1)` lies in the conductor of the affine
blow-up algebra `A[(x, y)/x]` over `A`. -/
theorem pow_mem_conductor_affineBlowup_of_isUnit_aeval_blowupChartLeadingCoeff
    (hF : aeval ![x, y] F = 0) (hH : IsUnit (aeval ![x, y] (blowupChartLeadingCoeff F))) :
    x ^ ((F.orderAt 0).toNat - 1) ∈
      TauCeti.Algebra.conductor A ((Ideal.span {x, y}).affineBlowup x S) := by
  rw [affineBlowup_span_pair_eq_adjoin]
  exact pow_mem_conductor_adjoin_of_isUnit_aeval_blowupChartLeadingCoeff hF
    (algebraMap_mul_divBy y x) (isLeftRegular_algebraMap x) hH

/-- If `F(x, y) = 0` and `H(x, y)` is a unit, `y/x` is a root of a monic polynomial over `A` of
degree `r`. -/
theorem exists_monic_aeval_divBy_eq_zero_of_isUnit_aeval_blowupChartLeadingCoeff [Nontrivial A]
    (hF : aeval ![x, y] F = 0) (hH : IsUnit (aeval ![x, y] (blowupChartLeadingCoeff F))) :
    ∃ p : Polynomial A, p.Monic ∧ p.natDegree = (F.orderAt 0).toNat ∧
      Polynomial.aeval (divBy y x : S) p = 0 :=
  exists_monic_aeval_eq_zero_of_isUnit_aeval_blowupChartLeadingCoeff hF
    (algebraMap_mul_divBy y x) (isLeftRegular_algebraMap x) hH

end AffineBlowup

section Curve

/-! ### The chart over a neighbourhood of the origin of a plane curve

For the curve `C = V(F)` with coordinate ring `Γ = R[X, Y] ⧸ (F)`, a polynomial `g` and
`H = blowupChartLeadingCoeff F`, let `W = C_{gH}` be the open subset of `C` where `gH` does not
vanish, with coordinate ring `Γ(W) = Γ_{gH}`, and `x, y` the coordinates in it. The ring of the
chart `W'` of the strict transform over `W` is `Γ(W') = Γ(W)[y/x]`, the affine blow-up algebra
`Γ(W)[(x, y)/x]`. As `g` varies over the polynomials with `g(P) ≠ 0`, the open sets `C_g` form a
base of neighbourhoods of `P`, so `W` can be taken inside any given neighbourhood of `P`. -/

variable {R : Type*} [CommRing R]

/-- The ring `Γ(W) = Γ_{gH}` of the open subset `W = C_{gH}` of the curve `C = V(F)`. -/
local notation "ΓW[" F ", " g "]" =>
  Localization.Away (Ideal.Quotient.mk (Ideal.span {F}) (g * blowupChartLeadingCoeff F))

/-- The coordinate `x` in `Γ(W)`. -/
local notation "xW[" F ", " g "]" => algebraMap (MvPolynomial (Fin 2) _ ⧸ Ideal.span {F})
  ΓW[F, g] (Ideal.Quotient.mk (Ideal.span {F}) (X 0))

/-- The coordinate `y` in `Γ(W)`. -/
local notation "yW[" F ", " g "]" => algebraMap (MvPolynomial (Fin 2) _ ⧸ Ideal.span {F})
  ΓW[F, g] (Ideal.Quotient.mk (Ideal.span {F}) (X 1))

/-- The ring `Γ(W') = Γ(W)[(x, y)/x]` of the chart of the strict transform over `W`. -/
local notation "ΓW'[" F ", " g "]" =>
  Ideal.affineBlowup (Ideal.span {xW[F, g], yW[F, g]}) xW[F, g] (Localization.Away xW[F, g])

/-- Evaluating at the images of `X` and `Y` under an `R`-algebra map is applying the map. -/
private theorem aeval_algHom_X {A : Type*} [CommSemiring A] [Algebra R A]
    (f : MvPolynomial (Fin 2) R →ₐ[R] A) (G : MvPolynomial (Fin 2) R) :
    aeval ![f (X 0), f (X 1)] G = f G := by
  have h : (![f (X 0), f (X 1)] : Fin 2 → A) = f ∘ X := by
    ext i : 1
    fin_cases i <;> rfl
  rw [h, ← aeval_unique f]

/-- In `Γ(W)`, `F(x, y) = 0` and `H(x, y)` is a unit. -/
private theorem aeval_xW_yW (F g : MvPolynomial (Fin 2) R) :
    aeval ![xW[F, g], yW[F, g]] F = 0 ∧
      IsUnit (aeval ![xW[F, g], yW[F, g]] (blowupChartLeadingCoeff F)) := by
  set f := (IsScalarTower.toAlgHom R (MvPolynomial (Fin 2) R ⧸ Ideal.span {F}) ΓW[F, g]).comp
    (Ideal.Quotient.mkₐ R (Ideal.span {F}))
  have h (G : MvPolynomial (Fin 2) R) : aeval ![xW[F, g], yW[F, g]] G =
      algebraMap _ ΓW[F, g] (Ideal.Quotient.mk (Ideal.span {F}) G) :=
    aeval_algHom_X f G
  rw [h, h, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton F)), map_zero]
  refine ⟨rfl, isUnit_of_mul_isUnit_right
    (x := algebraMap _ ΓW[F, g] (Ideal.Quotient.mk (Ideal.span {F}) g)) ?_⟩
  rw [← map_mul, ← map_mul]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- **Local finiteness of the blow-up.** The ring `Γ(W') = Γ(W)[(x, y)/x]` of the chart of the
strict transform over `W = C_{gH}` is module-finite over `Γ(W)`. -/
theorem finite_affineBlowup_blowupChart (F g : MvPolynomial (Fin 2) R) :
    Module.Finite ΓW[F, g] ΓW'[F, g] :=
  finite_affineBlowup_of_isUnit_aeval_blowupChartLeadingCoeff (aeval_xW_yW F g).1
    (aeval_xW_yW F g).2

/-- **The conductor of the blow-up.** `x ^ (r - 1)` carries `Γ(W') = Γ(W)[(x, y)/x]` into
`Γ(W)`, for `W = C_{gH}`. -/
theorem pow_mem_conductor_affineBlowup_blowupChart (F g : MvPolynomial (Fin 2) R) :
    xW[F, g] ^ ((F.orderAt 0).toNat - 1) ∈ TauCeti.Algebra.conductor ΓW[F, g] ΓW'[F, g] :=
  pow_mem_conductor_affineBlowup_of_isUnit_aeval_blowupChartLeadingCoeff (aeval_xW_yW F g).1
    (aeval_xW_yW F g).2

/-- If the origin lies on `F`, `g(0)` is a unit and `a_{0r}` is a unit, then `W = C_{gH}`
contains the origin, so `Γ(W)` is not the zero ring. -/
theorem nontrivial_blowupChart [Nontrivial R] {F g : MvPolynomial (Fin 2) R} (h0 : eval 0 F = 0)
    (hg : IsUnit (eval 0 g)) (hX : IsUnit (F.coeff (Finsupp.single 1 (F.orderAt 0).toNat))) :
    Nontrivial ΓW[F, g] := by
  let φ : MvPolynomial (Fin 2) R ⧸ Ideal.span {F} →+* R :=
    Ideal.Quotient.lift _ (eval 0) fun G hG ↦ by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hG
      rw [map_mul, h0, mul_zero]
  have hφ : IsUnit (φ (Ideal.Quotient.mk _ (g * blowupChartLeadingCoeff F))) := by
    rw [Ideal.Quotient.lift_mk, map_mul, eval_zero_blowupChartLeadingCoeff]
    exact hg.mul hX
  exact (IsLocalization.Away.lift _ hφ : ΓW[F, g] →+* R).domain_nontrivial

/-- **`y/x` is integral of degree `r`.** If the origin lies on `F`, `g(0)` is a unit and
`a_{0r}` is a unit, then `y/x` is a root of a monic polynomial of degree `r` over `Γ(W)`, for
`W = C_{gH}`. -/
theorem exists_monic_aeval_divBy_blowupChart [Nontrivial R] {F g : MvPolynomial (Fin 2) R}
    (h0 : eval 0 F = 0) (hg : IsUnit (eval 0 g))
    (hX : IsUnit (F.coeff (Finsupp.single 1 (F.orderAt 0).toNat))) :
    ∃ p : Polynomial ΓW[F, g], p.Monic ∧ p.natDegree = (F.orderAt 0).toNat ∧
      Polynomial.aeval (divBy yW[F, g] xW[F, g] : Localization.Away xW[F, g]) p = 0 :=
  have := nontrivial_blowupChart h0 hg hX
  exists_monic_aeval_divBy_eq_zero_of_isUnit_aeval_blowupChartLeadingCoeff (aeval_xW_yW F g).1
    (aeval_xW_yW F g).2

/-- If `F` is prime and does not divide `X`, then `x` is a nonzerodivisor of `Γ(W)`, so `Γ(W)`
embeds in `Γ(W') ⊆ Γ(W)_x`: `Γ(W')` is the ring of the open set `f⁻¹(W)` of the strict
transform. -/
theorem injective_algebraMap_affineBlowup_blowupChart [IsDomain R] {F : MvPolynomial (Fin 2) R}
    (hF : Prime F) (hX : ¬F ∣ X 0) (g : MvPolynomial (Fin 2) R) :
    Function.Injective (algebraMap ΓW[F, g] ΓW'[F, g]) := by
  have : (Ideal.span {F}).IsPrime := (Ideal.span_singleton_prime hF.ne_zero).2 hF
  have hx0 : Ideal.Quotient.mk (Ideal.span {F}) (X 0) ∈
      nonZeroDivisors (MvPolynomial (Fin 2) R ⧸ Ideal.span {F}) :=
    mem_nonZeroDivisors_of_ne_zero fun h ↦
      hX (Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 h))
  have hx : xW[F, g] ∈ nonZeroDivisors ΓW[F, g] :=
    IsLocalization.map_nonZeroDivisors_le
      (Submonoid.powers (Ideal.Quotient.mk (Ideal.span {F}) (g * blowupChartLeadingCoeff F)))
      ΓW[F, g] ⟨_, hx0, rfl⟩
  have hinj : Function.Injective (algebraMap ΓW[F, g] (Localization.Away xW[F, g])) :=
    IsLocalization.injective _ (Submonoid.powers_le.2 hx)
  exact fun a b h ↦ hinj (congrArg Subtype.val h)

/-- **`f(W') = W`.** If `F` is prime and does not divide `X`, every prime of `Γ(W)` lies under a
prime of `Γ(W')`: every point of `W` is the image of a point of `W'`. -/
theorem exists_isPrime_comap_affineBlowup_blowupChart [IsDomain R] {F : MvPolynomial (Fin 2) R}
    (hF : Prime F) (hX : ¬F ∣ X 0) (g : MvPolynomial (Fin 2) R) (p : Ideal ΓW[F, g])
    [p.IsPrime] :
    ∃ Q : Ideal ΓW'[F, g], Q.IsPrime ∧ Q.comap (algebraMap ΓW[F, g] ΓW'[F, g]) = p := by
  have := finite_affineBlowup_blowupChart F g
  have : Algebra.IsIntegral ΓW[F, g] ΓW'[F, g] := Algebra.IsIntegral.of_finite _ _
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := ΓW'[F, g]) p
    (⊥ : Ideal ΓW'[F, g]) (by
      rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1
        (injective_algebraMap_affineBlowup_blowupChart hF hX g)]
      exact bot_le)
  exact ⟨Q, hQ, hQp⟩

/-- The map `Spec Γ(W') → Spec Γ(W)` is closed, `Γ(W')` being integral over `Γ(W)`. So, for every
open set `U'` containing the points over a point `P` of `W`, some basic open neighbourhood
`D(h)` of `P` has its preimage in `U'`: `W'` can be taken inside any given neighbourhood of the
fibre over `P`. -/
theorem isClosedMap_comap_affineBlowup_blowupChart (F g : MvPolynomial (Fin 2) R) :
    IsClosedMap (PrimeSpectrum.comap (algebraMap ΓW[F, g] ΓW'[F, g])) :=
  have := finite_affineBlowup_blowupChart F g
  PrimeSpectrum.isClosedMap_comap_of_isIntegral (R := ΓW[F, g]) (S := ΓW'[F, g]) _
    (algebraMap_isIntegral_iff.2 (Algebra.IsIntegral.of_finite _ _))

section Shear

/-! ### Fulton's Remarks: `W` containing a given finite set of points

`H(x, y) = F(0, y) / y ^ r` vanishes at a point `(a, b)` with `b ≠ 0` exactly when `(0, b)` lies
on `C`, and at a point `(a, 0)` exactly when `X` is tangent to `F` at the origin. After the shear
`(x, y) ↦ (x - d y, y)`, that is `F ↦ F(X + dY, Y)`, the first condition becomes `F(db, b) = 0`,
and the second that `X - dY` is tangent to `F`; each fails for all but finitely many `d`. -/

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 2) k}

private theorem linearSubst_shear_X_zero (d : k) :
    linearSubst !![1, d; 0, 1] (X 0 - C d * X 1 : MvPolynomial (Fin 2) k) = X 0 := by
  simp [linearSubst_X, Fin.sum_univ_two]

private theorem shear_mulVec (d : k) (p : Fin 2 → k) :
    Matrix.mulVec !![1, d; 0, 1] p = ![p 0 + d * p 1, p 1] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Only finitely many lines `X - dY` are tangent to `F ≠ 0` at the origin. -/
private theorem finite_setOf_isTangentAt_shear [IsAlgClosed k] (hF : F ≠ 0) :
    {d : k | IsTangentAt F 0 (X 0 - C d * X 1)}.Finite := by
  obtain ⟨s, -, -, hs⟩ := exists_finset_isTangentAt (P := 0) hF
  refine (s.finite_toSet.biUnion fun L _ ↦
    (?_ : {d : k | Associated (X 0 - C d * X 1) L}.Subsingleton).finite).subset fun d hd ↦ ?_
  · intro d hd d' hd'
    have hd : Associated (X 0 - C d * X 1) L := hd
    have hd' : Associated (X 0 - C d' * X 1) L := hd'
    obtain ⟨c, hc⟩ := (hd.trans hd'.symm).dvd
    have h := congrArg (eval ![d, 1]) hc
    simp only [map_sub, map_mul, eval_X, eval_C, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_one, sub_self, zero_mul] at h
    exact sub_eq_zero.1 h
  · obtain ⟨L, hL, hdL⟩ := hs _ hd
    exact Set.mem_biUnion hL hdL

/-- If `F` is irreducible and passes through the origin, then for `b ≠ 0` there are only
finitely many `d` with `F(db, b) = 0`. -/
private theorem finite_setOf_eval_mul_eq_zero (hF : Irreducible F) (h0 : eval 0 F = 0) {b : k}
    (hb : b ≠ 0) : {d : k | eval ![d * b, b] F = 0}.Finite := by
  have hrel : IsRelPrime F (X 1 - C b) := by
    refine hF.isRelPrime_iff_not_dvd.2 fun ⟨c, hc⟩ ↦ hb ?_
    have h := congrArg (eval 0) hc
    rw [map_mul, h0, zero_mul] at h
    simpa using h
  refine ((finite_zeroLocus_span_pair_of_isRelPrime hrel k).preimage
    (f := fun d : k ↦ ![d * b, b]) fun d _ d' _ h ↦ ?_).subset fun d hd ↦ ?_
  · exact mul_right_cancel₀ hb (by simpa using congrFun h 0)
  · intro p hp
    obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.1 hp
    simp [show eval ![d * b, b] F = 0 from hd]

/-- **Fulton's Remarks.** Let `F` be irreducible through the origin and `S` a finite set of
points. After a shear `F ↦ F(X + dY, Y)`, which carries a point `Q` of `F` to the point
`(Q₀ - d Q₁, Q₁)` of the new curve, the curve is still irreducible, through the origin and not
associated to `X`, the line `X` is not tangent to it at the origin, and `H` does not vanish at the
images of the points of `S`: the open set `W = C_H` of Step (3) contains them. -/
theorem exists_linearSubst_eval_blowupChartLeadingCoeff_ne_zero [IsAlgClosed k]
    (hF : Irreducible F)
    (h0 : eval 0 F = 0) (S : Finset (Fin 2 → k)) :
    ∃ d : k, Irreducible (linearSubst !![1, d; 0, 1] F) ∧
      ¬Associated (linearSubst !![1, d; 0, 1] F) (X 0) ∧
      eval 0 (linearSubst !![1, d; 0, 1] F) = 0 ∧
      ¬IsTangentAt (linearSubst !![1, d; 0, 1] F) 0 (X 0) ∧
      ∀ Q ∈ S, eval ![Q 0 - d * Q 1, Q 1]
        (blowupChartLeadingCoeff (linearSubst !![1, d; 0, 1] F)) ≠ 0 := by
  classical
  set B := (S.image (· 1)).filter (· ≠ 0)
  have hB : (⋃ b ∈ (B : Set k), {d : k | eval ![d * b, b] F = 0}).Finite :=
    B.finite_toSet.biUnion fun b hb ↦
      finite_setOf_eval_mul_eq_zero hF h0 (Finset.mem_filter.1 hb).2
  obtain ⟨d, hd⟩ := ((finite_setOf_isTangentAt_shear hF.ne_zero).union hB).exists_notMem
  simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, not_or, not_exists] at hd
  obtain ⟨hdT, hdS⟩ := hd
  have hdet : IsUnit (!![1, d; 0, 1] : Matrix (Fin 2) (Fin 2) k).det := by
    simp [Matrix.det_fin_two_of]
  set G := linearSubst !![1, d; 0, 1] F with hGdef
  have hG : Irreducible G := by
    have : G = linearSubstAlgEquiv (Matrix.nonsingInvUnit _ hdet) F := by
      rw [linearSubstAlgEquiv_apply]
      rfl
    rw [this, MulEquiv.irreducible_iff]
    exact hF
  have hG0 : eval 0 G = 0 := by rw [hGdef, eval_linearSubst, Matrix.mulVec_zero, h0]
  have hT : ¬IsTangentAt G 0 (X 0) := by
    rw [hGdef, ← linearSubst_shear_X_zero d, isTangentAt_linearSubst_iff hdet,
      Matrix.mulVec_zero]
    exact hdT
  have ha : G.coeff (Finsupp.single 1 (G.orderAt 0).toNat) ≠ 0 :=
    fun h ↦ hT (isTangentAt_zero_X_zero_iff.2 h)
  have hr : 0 < (G.orderAt 0).toNat :=
    ENat.toNat_pos (orderAt_eq_zero_iff.not.2 (not_not.2 hG0))
      (orderAt_ne_top hG.ne_zero)
  refine ⟨d, hG, fun hA ↦ ha ?_, hG0, hT, fun Q hQ ↦ ?_⟩
  · rw [← hGdef] at hA
    obtain ⟨c, hc⟩ := hA.symm.dvd
    rw [hc, coeff_X_mul']
    simp
  · rw [← hGdef]
    have hx : eval ![Q 0 - d * Q 1, Q 1] (blowupChartLeadingCoeff G) =
        eval ![0, Q 1] (blowupChartLeadingCoeff G) :=
      aeval_blowupChartLeadingCoeff_eq_aeval_zero G hr _ _
    rw [hx]
    by_cases hb : Q 1 = 0
    · have h00 : (![0, Q 1] : Fin 2 → k) = 0 := by
        ext i : 1
        fin_cases i <;> simp [hb]
      rwa [h00, eval_zero_blowupChartLeadingCoeff]
    · intro h
      have : Q 1 ^ (G.orderAt 0).toNat * eval ![0, Q 1] (blowupChartLeadingCoeff G) =
          eval ![0, Q 1] G :=
        pow_mul_aeval_blowupChartLeadingCoeff G hr 0 (Q 1)
      rw [h, mul_zero, hGdef, eval_linearSubst, shear_mulVec] at this
      refine hdS (Q 1) (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hQ, hb⟩) ?_
      simpa using this.symm

end Shear

section Milestone

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 2) k}

/-- **Blowing up a plane curve at a point.** Let `k` be algebraically closed and
`F ∈ k[X, Y]` irreducible, not associated to `X`, through the origin `P`, with multiplicity
`r = m_P(F)`, and `F = F_r + F_{r+1} + ⋯` its homogeneous components; let `F'` be its strict
transform in the chart `(x, z) ↦ (x, xz)`, with exceptional line `E = V(X)`.

1. `F(X, XZ) = X ^ r F'` with `F' = ∑ᵢ X ^ (i - r) F_i(1, Z)`; `F'` is irreducible and not
   divisible by `X`; the blow-up map is a bijection from `{F' = 0, x ≠ 0}` onto
   `{F = 0, x ≠ 0}`, and `k(C) ≅ k(C')` by `x ↦ x`, `y ↦ xz`.

Suppose that `X` is not tangent to `F` at `P`.

2. The fibre over `P` is the finite set of points `(0, α)` for the tangents `Y - α X` of `F`
   at `P`, the leading form being `F_r = ε ∏ (Y - α X) ^ rₐ`; at `(0, α)`,
   `m(F') ≤ I((0, α), F' ∩ E) = rₐ`. If `P` is an ordinary multiple point, every point of the
   fibre is a simple point of `F'`, where `F'` meets `E` with intersection number one.
3. `H(P) = a_{0r} ≠ 0`. For every `g` with `g(P) ≠ 0`, the affine open set `W = C_{gH}`
   contains `P`, and the ring `Γ(W') = Γ(W)[(x, y)/x] = Γ(W)[y/x]` of the chart over it is
   module-finite over `Γ(W)`, `y/x` is a root of a monic polynomial of degree `r` over `Γ(W)`,
   and `x ^ (r - 1)` lies in the conductor of `Γ(W')` over `Γ(W)`. Moreover `Γ(W)` embeds in
   `Γ(W')`, so that `Γ(W')` is the ring of `W' = f⁻¹(W)`; every prime of `Γ(W)` lies under a
   prime of `Γ(W')`, that is `f(W') = W`; and `Spec Γ(W') → Spec Γ(W)` is a closed map.

   The sets `C_g` with `g(P) ≠ 0` form a base of neighbourhoods of `P`, so `W` can be taken
   inside any neighbourhood of `P`. As the map is closed, for every open `U'` containing the
   fibre over `P`, the image of its complement is closed and misses `P`, so some `C_g` has its
   preimage in `U'`: `W'` can be taken inside any neighbourhood of the fibre. Finally, for
   every finite set `S` of points, after a shear `F ↦ F(X + dY, Y)` the curve still satisfies
   all the hypotheses, and `H` does not vanish at the images of the points of `S`, so that
   `W = C_H` contains them.

Milestone: *Blowing up a plane curve at a point: strict transform, fibre and local
finiteness*. -/
theorem blowupStrictTransform_fibre_finite (hF : Irreducible F) (hX : ¬Associated F (X 0))
    (h0 : eval 0 F = 0) (hT : ¬IsTangentAt F 0 (X 0)) :
    X 0 ^ (F.orderAt 0).toNat * blowupStrictTransform F = aeval ![X 0, X 0 * X 1] F ∧
    blowupStrictTransform F = ∑ i ∈ Finset.range (F.totalDegree + 1),
      X 0 ^ (i - (F.orderAt 0).toNat) *
        aeval ![1, (X 1 : MvPolynomial (Fin 2) k)] (homogeneousComponent i F) ∧
    ¬X 0 ∣ blowupStrictTransform F ∧ Irreducible (blowupStrictTransform F) ∧
    Set.BijOn (fun p : Fin 2 → k ↦ ![p 0, p 0 * p 1])
      {p | eval p (blowupStrictTransform F) = 0 ∧ p 0 ≠ 0} {p | eval p F = 0 ∧ p 0 ≠ 0} ∧
    (∃ e : FractionRing (MvPolynomial (Fin 2) k ⧸ Ideal.span {F}) ≃ₐ[k]
        FractionRing (MvPolynomial (Fin 2) k ⧸ Ideal.span {blowupStrictTransform F}),
      e (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 0))) =
        algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {blowupStrictTransform F}) (X 0)) ∧
      e (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {F}) (X 1))) =
        algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {blowupStrictTransform F}) (X 0)) *
          algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {blowupStrictTransform F}) (X 1))) ∧
    (∃ A : Finset k, (∀ α, α ∈ A ↔ eval ![0, α] (blowupStrictTransform F) = 0) ∧
      ∃ ε : k, ε ≠ 0 ∧ F.leadingFormAt 0 =
        C ε * ∏ α ∈ A, (X 1 - C α * X 0) ^ tangentMultiplicity F 0 (X 1 - C α * X 0)) ∧
    (∀ α : k, (blowupStrictTransform F).orderAt ![0, α] ≤
        intersectionNumber ![0, α] (blowupStrictTransform F) (X 0) ∧
      intersectionNumber ![0, α] (blowupStrictTransform F) (X 0) =
        tangentMultiplicity F 0 (X 1 - C α * X 0)) ∧
    (IsOrdinaryMultiplePoint F 0 → ∀ α : k, eval ![0, α] (blowupStrictTransform F) = 0 →
      IsSimplePoint (blowupStrictTransform F) ![0, α] ∧
        intersectionNumber ![0, α] (blowupStrictTransform F) (X 0) = 1) ∧
    eval 0 (blowupChartLeadingCoeff F) ≠ 0 ∧
    (∀ g : MvPolynomial (Fin 2) k, eval 0 g ≠ 0 →
      Nontrivial ΓW[F, g] ∧ Module.Finite ΓW[F, g] ΓW'[F, g] ∧
      (∃ p : Polynomial ΓW[F, g], p.Monic ∧ p.natDegree = (F.orderAt 0).toNat ∧
        Polynomial.aeval (divBy yW[F, g] xW[F, g] : Localization.Away xW[F, g]) p = 0) ∧
      xW[F, g] ^ ((F.orderAt 0).toNat - 1) ∈ TauCeti.Algebra.conductor ΓW[F, g] ΓW'[F, g] ∧
      Function.Injective (algebraMap ΓW[F, g] ΓW'[F, g]) ∧
      (∀ p : Ideal ΓW[F, g], p.IsPrime →
        ∃ Q : Ideal ΓW'[F, g], Q.IsPrime ∧ Q.comap (algebraMap ΓW[F, g] ΓW'[F, g]) = p) ∧
      IsClosedMap (PrimeSpectrum.comap (algebraMap ΓW[F, g] ΓW'[F, g]))) ∧
    ∀ S : Finset (Fin 2 → k), ∃ d : k, Irreducible (linearSubst !![1, d; 0, 1] F) ∧
      ¬Associated (linearSubst !![1, d; 0, 1] F) (X 0) ∧
      eval 0 (linearSubst !![1, d; 0, 1] F) = 0 ∧
      ¬IsTangentAt (linearSubst !![1, d; 0, 1] F) 0 (X 0) ∧
      ∀ Q ∈ S, eval ![Q 0 - d * Q 1, Q 1]
        (blowupChartLeadingCoeff (linearSubst !![1, d; 0, 1] F)) ≠ 0 := by
  have ha : F.coeff (Finsupp.single 1 (F.orderAt 0).toNat) ≠ 0 :=
    fun h ↦ hT (isTangentAt_zero_X_zero_iff.2 h)
  have hP : Prime F := UniqueFactorizationMonoid.irreducible_iff_prime.1 hF
  have hXd : ¬F ∣ X 0 := fun h ↦ hX (hF.associated_of_dvd prime_X.irreducible h)
  refine ⟨X_pow_mul_blowupStrictTransform F, blowupStrictTransform_eq_sum F,
    not_X_dvd_blowupStrictTransform hF.ne_zero, irreducible_blowupStrictTransform hF hX,
    bijOn_blowupStrictTransform F, ⟨blowupFunctionFieldEquiv hF hX,
      blowupFunctionFieldEquiv_x hF hX, blowupFunctionFieldEquiv_y hF hX⟩,
    exists_finset_eval_zero_blowupStrictTransform hF.ne_zero hT,
    fun α ↦ ⟨orderAt_blowupStrictTransform_le_intersectionNumber F α,
      intersectionNumber_blowupStrictTransform_X_zero hF.ne_zero α⟩,
    fun h α hα ↦ h.isSimplePoint_blowupStrictTransform
      ((eval_zero_blowupStrictTransform_eq_zero_iff hF.ne_zero α).1 hα),
    by rwa [eval_zero_blowupChartLeadingCoeff], fun g hg ↦ ⟨?_, finite_affineBlowup_blowupChart F g,
      exists_monic_aeval_divBy_blowupChart h0 (isUnit_iff_ne_zero.2 hg) (isUnit_iff_ne_zero.2 ha),
      pow_mem_conductor_affineBlowup_blowupChart F g,
      injective_algebraMap_affineBlowup_blowupChart hP hXd g,
      fun p _ ↦ exists_isPrime_comap_affineBlowup_blowupChart hP hXd g p,
      isClosedMap_comap_affineBlowup_blowupChart F g⟩,
    exists_linearSubst_eval_blowupChartLeadingCoeff_ne_zero hF h0⟩
  exact nontrivial_blowupChart h0 (isUnit_iff_ne_zero.2 hg) (isUnit_iff_ne_zero.2 ha)

end Milestone

end Curve

end PlaneCurves.Affine

end
