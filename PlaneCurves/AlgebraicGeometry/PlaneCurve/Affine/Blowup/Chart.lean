/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.Adjoin.Polynomial.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import TauCeti.RingTheory.Conductor
public import TauCeti.RingTheory.Ideal.AffineBlowup
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
`W = C_H` of the curve `C = V(F)`, the element `z = y/x` is integral of degree `r`, the affine
blow-up algebra `Γ(W') = Γ(W)[y/x]` is module-finite over `Γ(W)`, and `x ^ (r - 1)` lies in its
conductor (Step (3) of §7.2 of Fulton).

## Main definitions

* `PlaneCurves.Affine.blowupChartPolynomial F x y`: the polynomial
  `∑ a_{ij} x ^ (i - r) y ^ (j - (r - i)) T ^ (r - i)` over `A`.
* `PlaneCurves.Affine.blowupChartLeadingCoeff F`: the polynomial `H`, its coefficient of
  `T ^ r` over `k[X, Y]`.

## Main results

* `PlaneCurves.Affine.algebraMap_pow_mul_aeval_blowupChartPolynomial`: for `xz = y`,
  `x ^ r P(z) = F(x, y)`.
* `PlaneCurves.Affine.coeff_blowupChartPolynomial`: the coefficient of `T ^ r` is `H(x, y)`, and
  `PlaneCurves.Affine.eval_zero_blowupChartLeadingCoeff`: `H(0, 0) = a_{0r}`.
* `PlaneCurves.Affine.exists_monic_aeval_eq_zero`, `PlaneCurves.Affine.isIntegral_of_isUnit`,
  `PlaneCurves.Affine.finite_adjoin_of_isUnit`,
  `PlaneCurves.Affine.pow_mem_conductor_adjoin_of_isUnit`: if `H(x, y)` is a unit, `z` is a root
  of a monic polynomial of degree `r`, `A[z]` is module-finite over `A` and `x ^ (r - 1)` lies in
  the conductor of `A[z]`.
* `PlaneCurves.Affine.affineBlowup_span_pair_eq_adjoin`,
  `PlaneCurves.Affine.finite_affineBlowup_of_isUnit`,
  `PlaneCurves.Affine.pow_mem_conductor_affineBlowup_of_isUnit`: the same for the affine blow-up
  algebra `A[(x, y)/x] = A[y/x]`.
* `PlaneCurves.Affine.finite_affineBlowup_blowupChart`,
  `PlaneCurves.Affine.exists_monic_aeval_divBy_blowupChart`,
  `PlaneCurves.Affine.pow_mem_conductor_affineBlowup_blowupChart`: Step (3) for a plane curve:
  on `W = C_H`, a neighbourhood of the origin when `X` is not tangent
  (`PlaneCurves.Affine.isTangentAt_zero_X_zero_iff`), `Γ(W') = Γ(W)[y/x]` is module-finite over
  `Γ(W)`, `y/x` is integral of degree `r` and `x ^ (r - 1)` lies in the conductor.
* `PlaneCurves.Affine.blowupStrictTransform_fibre_finite`: the milestone, Steps (1)–(3) of §7.2
  together.

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
theorem exists_monic_aeval_eq_zero [Nontrivial A] (hF : aeval ![x, y] F = 0)
    (hz : algebraMap A B x * z = algebraMap A B y) (hx : IsLeftRegular (algebraMap A B x))
    (hH : IsUnit (aeval ![x, y] (blowupChartLeadingCoeff F))) :
    ∃ p : Polynomial A, p.Monic ∧ p.natDegree = (F.orderAt 0).toNat ∧
      Polynomial.aeval z p = 0 := by
  obtain ⟨p, hp, hd, h1, h0⟩ := exists_monic_natDegree_le hF hz hx hH
  exact ⟨p, hp, le_antisymm hd (Polynomial.le_natDegree_of_ne_zero (by simp [h1])), h0⟩

/-- Under the hypotheses of `exists_monic_aeval_eq_zero`, `z` is integral over `A`. -/
theorem isIntegral_of_isUnit (hF : aeval ![x, y] F = 0)
    (hz : algebraMap A B x * z = algebraMap A B y) (hx : IsLeftRegular (algebraMap A B x))
    (hH : IsUnit (aeval ![x, y] (blowupChartLeadingCoeff F))) : IsIntegral A z := by
  obtain ⟨p, hp, -, -, h0⟩ := exists_monic_natDegree_le hF hz hx hH
  exact ⟨p, hp, by rwa [← Polynomial.aeval_def]⟩

/-- Under the hypotheses of `exists_monic_aeval_eq_zero`, `A[z]` is module-finite over `A`. -/
theorem finite_adjoin_of_isUnit (hF : aeval ![x, y] F = 0)
    (hz : algebraMap A B x * z = algebraMap A B y) (hx : IsLeftRegular (algebraMap A B x))
    (hH : IsUnit (aeval ![x, y] (blowupChartLeadingCoeff F))) :
    Module.Finite A (Algebra.adjoin A {z}) :=
  Algebra.finite_adjoin_simple_of_isIntegral (isIntegral_of_isUnit hF hz hx hH)

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

/-- **The conductor.** Under the hypotheses of `exists_monic_aeval_eq_zero`, `x ^ (r - 1)`
lies in the conductor of `A[z]` over `A`: it carries `A[z]` into `A`. -/
theorem pow_mem_conductor_adjoin_of_isUnit (hF : aeval ![x, y] F = 0)
    (hz : algebraMap A B x * z = algebraMap A B y) (hx : IsLeftRegular (algebraMap A B x))
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

private theorem algebraMap_mul_divBy_eq (x y : A) [IsLocalization.Away x S] :
    algebraMap A S x * divBy y x = algebraMap A S y :=
  algebraMap_mul_divBy y x

private theorem isLeftRegular_algebraMap (x : A) [IsLocalization.Away x S] :
    IsLeftRegular (algebraMap A S x) :=
  (IsLocalization.Away.algebraMap_isUnit (S := S) x).isRegular.left

/-- **Local finiteness of the blow-up.** If `F(x, y) = 0` and `H(x, y)` is a unit, the affine
blow-up algebra `A[(x, y)/x]` is module-finite over `A`. -/
theorem finite_affineBlowup_of_isUnit (hF : aeval ![x, y] F = 0)
    (hH : IsUnit (aeval ![x, y] (blowupChartLeadingCoeff F))) :
    Module.Finite A ((Ideal.span {x, y}).affineBlowup x S) := by
  rw [affineBlowup_span_pair_eq_adjoin]
  exact finite_adjoin_of_isUnit hF (algebraMap_mul_divBy_eq x y) (isLeftRegular_algebraMap x) hH

/-- If `F(x, y) = 0` and `H(x, y)` is a unit, `x ^ (r - 1)` lies in the conductor of the affine
blow-up algebra `A[(x, y)/x]` over `A`. -/
theorem pow_mem_conductor_affineBlowup_of_isUnit (hF : aeval ![x, y] F = 0)
    (hH : IsUnit (aeval ![x, y] (blowupChartLeadingCoeff F))) :
    x ^ ((F.orderAt 0).toNat - 1) ∈
      TauCeti.Algebra.conductor A ((Ideal.span {x, y}).affineBlowup x S) := by
  rw [affineBlowup_span_pair_eq_adjoin]
  exact pow_mem_conductor_adjoin_of_isUnit hF (algebraMap_mul_divBy_eq x y)
    (isLeftRegular_algebraMap x) hH

/-- If `F(x, y) = 0` and `H(x, y)` is a unit, `y/x` is a root of a monic polynomial over `A` of
degree `r`. -/
theorem exists_monic_aeval_divBy_eq_zero [Nontrivial A] (hF : aeval ![x, y] F = 0)
    (hH : IsUnit (aeval ![x, y] (blowupChartLeadingCoeff F))) :
    ∃ p : Polynomial A, p.Monic ∧ p.natDegree = (F.orderAt 0).toNat ∧
      Polynomial.aeval (divBy y x : S) p = 0 :=
  exists_monic_aeval_eq_zero hF (algebraMap_mul_divBy_eq x y) (isLeftRegular_algebraMap x) hH

end AffineBlowup
section Curve

/-! ### The chart over a neighbourhood of the origin of a plane curve

For the curve `C = V(F)` with coordinate ring `Γ = R[X, Y] ⧸ (F)`, let `W = C_H` be the open
subset where `H = blowupChartLeadingCoeff F` does not vanish, with coordinate ring
`Γ(W) = Γ_H`, and `x, y` the coordinates in it. The ring of the chart `W'` of the strict
transform over `W` is `Γ(W') = Γ(W)[y/x]`, the affine blow-up algebra `Γ(W)[(x, y)/x]`. -/

variable {R : Type*} [CommRing R]

/-- The ring `Γ(W) = Γ_H` of the open subset `W = C_H` of the curve `C = V(F)`. -/
local notation "ΓW[" F "]" =>
  Localization.Away (Ideal.Quotient.mk (Ideal.span {F}) (blowupChartLeadingCoeff F))

/-- The coordinate `x` in `Γ(W)`. -/
local notation "xW[" F "]" => algebraMap (MvPolynomial (Fin 2) _ ⧸ Ideal.span {F}) ΓW[F]
  (Ideal.Quotient.mk (Ideal.span {F}) (X 0))

/-- The coordinate `y` in `Γ(W)`. -/
local notation "yW[" F "]" => algebraMap (MvPolynomial (Fin 2) _ ⧸ Ideal.span {F}) ΓW[F]
  (Ideal.Quotient.mk (Ideal.span {F}) (X 1))

/-- Evaluating at the images of `X` and `Y` under an `R`-algebra map is applying the map. -/
private theorem aeval_algHom_X {A : Type*} [CommSemiring A] [Algebra R A]
    (f : MvPolynomial (Fin 2) R →ₐ[R] A) (G : MvPolynomial (Fin 2) R) :
    aeval ![f (X 0), f (X 1)] G = f G := by
  have h : (![f (X 0), f (X 1)] : Fin 2 → A) = f ∘ X := by
    ext i : 1
    fin_cases i <;> rfl
  rw [h, ← aeval_unique f]

/-- In `Γ(W)`, `F(x, y) = 0` and `H(x, y)` is a unit. -/
private theorem aeval_xW_yW (F : MvPolynomial (Fin 2) R) :
    aeval ![xW[F], yW[F]] F = 0 ∧ IsUnit (aeval ![xW[F], yW[F]] (blowupChartLeadingCoeff F)) := by
  set f := (IsScalarTower.toAlgHom R (MvPolynomial (Fin 2) R ⧸ Ideal.span {F}) ΓW[F]).comp
    (Ideal.Quotient.mkₐ R (Ideal.span {F}))
  have h (G : MvPolynomial (Fin 2) R) : aeval ![xW[F], yW[F]] G =
      algebraMap _ ΓW[F] (Ideal.Quotient.mk (Ideal.span {F}) G) :=
    aeval_algHom_X f G
  rw [h, h, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton F)), map_zero]
  exact ⟨rfl, IsLocalization.Away.algebraMap_isUnit _⟩

/-- **Local finiteness of the blow-up.** The ring `Γ(W') = Γ(W)[(x, y)/x]` of the chart of the
strict transform over `W = C_H` is module-finite over `Γ(W)`. -/
theorem finite_affineBlowup_blowupChart (F : MvPolynomial (Fin 2) R) :
    Module.Finite ΓW[F]
      ((Ideal.span {xW[F], yW[F]}).affineBlowup xW[F] (Localization.Away xW[F])) :=
  finite_affineBlowup_of_isUnit (aeval_xW_yW F).1 (aeval_xW_yW F).2

/-- **The conductor of the blow-up.** `x ^ (r - 1)` carries `Γ(W') = Γ(W)[(x, y)/x]` into
`Γ(W)`, for `W = C_H`. -/
theorem pow_mem_conductor_affineBlowup_blowupChart (F : MvPolynomial (Fin 2) R) :
    xW[F] ^ ((F.orderAt 0).toNat - 1) ∈ TauCeti.Algebra.conductor ΓW[F]
      ((Ideal.span {xW[F], yW[F]}).affineBlowup xW[F] (Localization.Away xW[F])) :=
  pow_mem_conductor_affineBlowup_of_isUnit (aeval_xW_yW F).1 (aeval_xW_yW F).2

/-- If the origin lies on `F` and `a_{0r}` is a unit, then `W = C_H` contains the origin, so
`Γ(W)` is not the zero ring. -/
theorem nontrivial_blowupChart [Nontrivial R] {F : MvPolynomial (Fin 2) R} (h0 : eval 0 F = 0)
    (hX : IsUnit (F.coeff (Finsupp.single 1 (F.orderAt 0).toNat))) : Nontrivial ΓW[F] := by
  let φ : MvPolynomial (Fin 2) R ⧸ Ideal.span {F} →+* R :=
    Ideal.Quotient.lift _ (eval 0) fun G hG ↦ by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hG
      rw [map_mul, h0, mul_zero]
  have hφ : IsUnit (φ (Ideal.Quotient.mk _ (blowupChartLeadingCoeff F))) := by
    rw [Ideal.Quotient.lift_mk, eval_zero_blowupChartLeadingCoeff]
    exact hX
  exact (IsLocalization.Away.lift _ hφ : ΓW[F] →+* R).domain_nontrivial

/-- **`y/x` is integral of degree `r`.** If the origin lies on `F` and `a_{0r}` is a unit, then
`y/x` is a root of a monic polynomial of degree `r` over `Γ(W)`, for `W = C_H`. -/
theorem exists_monic_aeval_divBy_blowupChart [Nontrivial R] {F : MvPolynomial (Fin 2) R}
    (h0 : eval 0 F = 0) (hX : IsUnit (F.coeff (Finsupp.single 1 (F.orderAt 0).toNat))) :
    ∃ p : Polynomial ΓW[F], p.Monic ∧ p.natDegree = (F.orderAt 0).toNat ∧
      Polynomial.aeval (divBy yW[F] xW[F] : Localization.Away xW[F]) p = 0 :=
  haveI := nontrivial_blowupChart h0 hX
  exists_monic_aeval_divBy_eq_zero (aeval_xW_yW F).1 (aeval_xW_yW F).2
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
3. The open set `W = C_H` contains `P` (`H(P) = a_{0r} ≠ 0`); the ring
   `Γ(W') = Γ(W)[(x, y)/x] = Γ(W)[y/x]` of the chart over it is module-finite over `Γ(W)`,
   `y/x` is a root of a monic polynomial of degree `r` over `Γ(W)`, and `x ^ (r - 1)` lies in
   the conductor of `Γ(W')` over `Γ(W)`.

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
    Module.Finite ΓW[F]
      ((Ideal.span {xW[F], yW[F]}).affineBlowup xW[F] (Localization.Away xW[F])) ∧
    (∃ p : Polynomial ΓW[F], p.Monic ∧ p.natDegree = (F.orderAt 0).toNat ∧
      Polynomial.aeval (divBy yW[F] xW[F] : Localization.Away xW[F]) p = 0) ∧
    xW[F] ^ ((F.orderAt 0).toNat - 1) ∈ TauCeti.Algebra.conductor ΓW[F]
      ((Ideal.span {xW[F], yW[F]}).affineBlowup xW[F] (Localization.Away xW[F])) := by
  have ha : F.coeff (Finsupp.single 1 (F.orderAt 0).toNat) ≠ 0 :=
    fun h ↦ hT (isTangentAt_zero_X_zero_iff.2 h)
  refine ⟨X_pow_mul_blowupStrictTransform F, blowupStrictTransform_eq_sum F,
    not_X_dvd_blowupStrictTransform hF.ne_zero, irreducible_blowupStrictTransform hF hX,
    bijOn_blowupStrictTransform F, ⟨blowupFunctionFieldEquiv hF hX,
      blowupFunctionFieldEquiv_x hF hX, blowupFunctionFieldEquiv_y hF hX⟩,
    exists_finset_eval_zero_blowupStrictTransform hF.ne_zero hT,
    fun α ↦ ⟨orderAt_blowupStrictTransform_le_intersectionNumber F α,
      intersectionNumber_blowupStrictTransform_X_zero hF.ne_zero α⟩,
    fun h α hα ↦ h.isSimplePoint_blowupStrictTransform
      ((eval_zero_blowupStrictTransform_eq_zero_iff hF.ne_zero α).1 hα),
    by rwa [eval_zero_blowupChartLeadingCoeff], finite_affineBlowup_blowupChart F,
    exists_monic_aeval_divBy_blowupChart h0 (isUnit_iff_ne_zero.2 ha),
    pow_mem_conductor_affineBlowup_blowupChart F⟩

end Milestone

end Curve

end PlaneCurves.Affine

end
