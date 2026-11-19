/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.Additivity
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.Multiplicity
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.SimplePoint
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.CurveLocalRing
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.IntersectionNumber.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Tangent

/-!
# Properties of intersection numbers of projective plane curves

The intersection number `I(P, F ∩ G)` of two forms `F`, `G ∈ k[X, Y, Z]` at a point `P ∈ ℙ²` is
the length of `𝒪_P(ℙ²) ⧸ (F_*, G_*)` (`PlaneCurves.Projective.intersectionNumber`). This file
proves the remaining properties of §5.1 of Fulton by transport from an affine chart containing
`P`: property (5) on multiplicities and tangents, the additivity (6), and (8), the intersection
number with a curve at a simple point as an order of vanishing. It also proves that a line is
tangent to a curve exactly when it meets it more often than the multiplicity, the book's
definition of tangent lines in §5.1, and that the intersection number does not depend on the
choice of the local equations `F_*`, `G_*` nor on scaling `F` and `G`.

## Main results

* `intersectionNumber_eq_length_mk`: `I(P, F ∩ G)` is the length of `𝒪_P(ℙ²) ⧸ (F / s, G / t)`
  for any forms `s`, `t` of the degrees of `F`, `G` with `s(P) ≠ 0`, `t(P) ≠ 0`.
* `intersectionNumber_smul_left`, `intersectionNumber_smul_right`: invariance under scaling.
* `mul_mult_le_intersectionNumber`, `intersectionNumber_eq_mul_mult_iff`, property (5):
  `I(P, F ∩ G) ≥ m_P(F) m_P(G)`, with equality iff `F` and `G` have no common tangent at `P`.
* `intersectionNumber_mul_right`, `intersectionNumber_mul_left`,
  `intersectionNumber_prod_pow_prod_pow`, property (6): additivity.
* `intersectionNumber_eq_ord`, `exists_isDiscreteValuationRing_quotient_iff`,
  `intersectionNumber_eq_ord_localSubring`, property (8): `I(P, F ∩ G)` is the order of `G_*` in
  `𝒪_P(ℙ²) ⧸ (F_*)`, which is a discrete valuation ring iff `P` is a simple point of `F`; for an
  irreducible `F` this is the order of `G / H` in the local ring `𝒪_P(C)` of the curve.
* `isTangentAt_iff_mult_lt_intersectionNumber`: a line `L` through `P` is tangent to `F` at `P`
  iff `I(P, F ∩ L) > m_P(F)`.
* `intersectionNumber_spec`: the intersection number of projective plane curves at a point, with
  its properties (1)–(8).
* `isMultiplePoint_and_isTangentAt_spec`: singular points and tangent lines of a projective
  plane curve via partial derivatives.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.1, Problems 5.1, 5.4, 5.5
-/

public section

universe u v

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti TauCeti.AlgebraicGeometry PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {P : ℙ k (Fin 3 → k)} {F G H L : MvPolynomial (Fin 3) k}
  {d e m : ℕ}

/-! ### The choice of local equations, and scaling -/

/-- **The intersection number does not depend on the local equations.** For fractions `F / s`
and `G / t` of forms of the same degrees with `s(P) ≠ 0` and `t(P) ≠ 0`, for instance
`s = L^{deg F}` and `t = L^{deg G}` for a linear form `L` with `L(P) ≠ 0`,
`I(P, F ∩ G)` is the length of `𝒪_P(ℙ²) ⧸ (F / s, G / t)`. -/
theorem intersectionNumber_eq_length_mk
    (c c' : HomogeneousLocalization.NumDenSameDeg (homogeneousSubmodule (Fin 3) k)
      (pointIdeal P).toIdeal.primeCompl) :
    intersectionNumber P c.num c'.num = Module.length (localRing P)
      (localRing P ⧸ Ideal.span {HomogeneousLocalization.mk c, HomogeneousLocalization.mk c'}) := by
  rw [intersectionNumber_eq_length_localEquation ((mem_homogeneousSubmodule _ _).1 c.num.2)
    ((mem_homogeneousSubmodule _ _).1 c'.num.2)]
  exact Ideal.length_quotient_span_pair_eq_of_ringEquiv (RingEquiv.refl _)
    (associated_localEquation_mk c).symm (associated_localEquation_mk c').symm

/-- Scaling the first curve does not change the intersection number. -/
@[simp]
theorem intersectionNumber_smul_left {c : k} (hc : c ≠ 0) (P : ℙ k (Fin 3 → k))
    (F G : MvPolynomial (Fin 3) k) :
    intersectionNumber P (c • F) G = intersectionNumber P F G :=
  intersectionNumber_congr (by
    rw [smul_eq_C_mul, Ideal.span_insert, Ideal.span_insert,
      Ideal.span_singleton_mul_left_unit ((isUnit_iff_ne_zero.2 hc).map C)])

/-- Scaling the second curve does not change the intersection number. -/
@[simp]
theorem intersectionNumber_smul_right {c : k} (hc : c ≠ 0) (P : ℙ k (Fin 3 → k))
    (F G : MvPolynomial (Fin 3) k) :
    intersectionNumber P F (c • G) = intersectionNumber P F G := by
  rw [intersectionNumber_comm, intersectionNumber_smul_left hc, intersectionNumber_comm]

/-! ### Property (5): multiplicities and tangents -/

/-- **Property (5)**, the inequality: for forms `F` and `G`,
`I(P, F ∩ G) ≥ m_P(F) m_P(G)`, over any field. -/
theorem mul_mult_le_intersectionNumber (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e) :
    mult F P * mult G P ≤ intersectionNumber P F G := by
  obtain ⟨i, hP⟩ := exists_mem_affineOpen P
  rw [intersectionNumber_eq_affine hF hG hP, mult_eq_orderAt_dehomogenize hF hP,
    mult_eq_orderAt_dehomogenize hG hP]
  exact Affine.mul_orderAt_le_intersectionNumber _ _ _

/-- **Property (5)**, the equality case: over an algebraically closed field, for nonzero forms
`F` and `G`, `I(P, F ∩ G) = m_P(F) m_P(G)` iff `F` and `G` have no tangent line in common
at `P`. -/
theorem intersectionNumber_eq_mul_mult_iff [IsAlgClosed k] (hF : F.IsHomogeneous d)
    (hG : G.IsHomogeneous e) (hF0 : F ≠ 0) (hG0 : G ≠ 0) :
    intersectionNumber P F G = mult F P * mult G P ↔
      ¬∃ L, IsTangentAt F P L ∧ IsTangentAt G P L := by
  obtain ⟨i, hP⟩ := exists_mem_affineOpen P
  rw [intersectionNumber_eq_affine hF hG hP, mult_eq_orderAt_dehomogenize hF hP,
    mult_eq_orderAt_dehomogenize hG hP, exists_isTangentAt_iff_affine hF hG hP]
  exact (Affine.mul_orderAt_le_intersectionNumber_and_eq_iff
    (dehomogenize_ne_zero_of_isHomogeneous i hF hF0)
    (dehomogenize_ne_zero_of_isHomogeneous i hG hG0)).2

/-! ### Tangent lines and intersection numbers -/

/-- **Tangency of a line detected by the intersection number.** For a nonzero form `F` and a
line `L = 0` through `P` (`L` a nonzero linear form with `L(P) = 0`), `L` is tangent to `F` at
`P` iff `I(P, F ∩ L) > m_P(F)`. This is Fulton's definition of the tangent lines at `P` in
§5.1. -/
theorem isTangentAt_iff_mult_lt_intersectionNumber (hF : F.IsHomogeneous d) (hF0 : F ≠ 0)
    (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) (hLP : eval P.rep L = 0) :
    IsTangentAt F P L ↔ mult F P < intersectionNumber P F L := by
  obtain ⟨i, hP⟩ := exists_mem_affineOpen P
  have hLa : eval (Fin.insertNth (α := fun _ ↦ k) i 1 (affineChart i P)) L = 0 := by
    rw [← eval_dehomogenize]
    exact (eval_affineChart_dehomogenize_eq_zero_iff hP hL).2 hLP
  rw [isTangentAt_iff_affine hF hP hL hLP,
    Affine.isTangentAt_iff_orderAt_lt_intersectionNumber
      (dehomogenize_ne_zero_of_isHomogeneous i hF hF0)
      (isHomogeneous_taylor_dehomogenize i _ hL hLa)
      (taylor_eq_zero.not.2 (dehomogenize_ne_zero_of_isHomogeneous i hL hL0)),
    taylor_neg_taylor, intersectionNumber_eq_affine hF hL hP, mult_eq_orderAt_dehomogenize hF hP]

/-! ### Property (6): additivity -/

/-- **Property (6)**: for forms `F`, `G` and `H`, `I(P, F ∩ G H) = I(P, F ∩ G) + I(P, F ∩ H)`. -/
theorem intersectionNumber_mul_right (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e)
    (hH : H.IsHomogeneous m) :
    intersectionNumber P F (G * H) = intersectionNumber P F G + intersectionNumber P F H := by
  obtain ⟨i, hP⟩ := exists_mem_affineOpen P
  rw [intersectionNumber_eq_affine hF (hG.mul hH) hP, intersectionNumber_eq_affine hF hG hP,
    intersectionNumber_eq_affine hF hH hP, map_mul, Affine.intersectionNumber_mul_right]

/-- **Property (6)**: for forms `F`, `G` and `H`, `I(P, F G ∩ H) = I(P, F ∩ H) + I(P, G ∩ H)`. -/
theorem intersectionNumber_mul_left (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e)
    (hH : H.IsHomogeneous m) :
    intersectionNumber P (F * G) H = intersectionNumber P F H + intersectionNumber P G H := by
  rw [intersectionNumber_comm, intersectionNumber_mul_right hH hF hG, intersectionNumber_comm,
    intersectionNumber_comm P H G]

/-- **Property (6)**, factorized form: if `F = ∏ Fᵢ ^ rᵢ` and `G = ∏ Gⱼ ^ sⱼ` are products of
forms, then `I(P, F ∩ G) = ∑ᵢ ∑ⱼ rᵢ sⱼ I(P, Fᵢ ∩ Gⱼ)`. -/
theorem intersectionNumber_prod_pow_prod_pow {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    {F : ι → MvPolynomial (Fin 3) k} {G : κ → MvPolynomial (Fin 3) k} {dF : ι → ℕ}
    {dG : κ → ℕ} (hF : ∀ i ∈ s, (F i).IsHomogeneous (dF i))
    (hG : ∀ j ∈ t, (G j).IsHomogeneous (dG j)) (r : ι → ℕ) (r' : κ → ℕ) :
    intersectionNumber P (∏ i ∈ s, F i ^ r i) (∏ j ∈ t, G j ^ r' j) =
      ∑ i ∈ s, ∑ j ∈ t, (r i * r' j : ℕ∞) * intersectionNumber P (F i) (G j) := by
  obtain ⟨c, hP⟩ := exists_mem_affineOpen P
  rw [intersectionNumber_eq_affine (IsHomogeneous.prod _ _ _ fun i hi ↦ (hF i hi).pow (r i))
    (IsHomogeneous.prod _ _ _ fun j hj ↦ (hG j hj).pow (r' j)) hP, map_prod, map_prod]
  simp only [map_pow]
  rw [Affine.intersectionNumber_prod_pow_prod_pow]
  refine Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ ?_
  rw [intersectionNumber_eq_affine (hF i hi) (hG j hj) hP]

/-! ### Property (8): simple points -/

/-- `I(P, F ∩ G)` is the order of the image of `G_*` in `𝒪_P(ℙ²) ⧸ (F_*)`, for forms `F`
and `G`. -/
theorem intersectionNumber_eq_ord (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e) :
    intersectionNumber P F G = Ring.ord (localRing P ⧸ Ideal.span {localEquation P F})
      (Ideal.Quotient.mk _ (localEquation P G)) := by
  rw [intersectionNumber_eq_length_localEquation hF hG, ord_eq_length_quotient_span_pair]

/-- For a form `F` vanishing at `P`, the ring `𝒪_P(ℙ²) ⧸ (F_*)` is a discrete valuation ring iff
`P` is a simple point of `F`. -/
theorem exists_isDiscreteValuationRing_quotient_iff (hF : F.IsHomogeneous d)
    (hP : eval P.rep F = 0) :
    (∃ _ : IsDomain (localRing P ⧸ Ideal.span {localEquation P F}),
      IsDiscreteValuationRing (localRing P ⧸ Ideal.span {localEquation P F})) ↔
      IsSimplePoint F P := by
  obtain ⟨i, hPi⟩ := exists_mem_affineOpen P
  rw [isSimplePoint_iff_affine hF hPi, ← Affine.exists_isDiscreteValuationRing_quotient_iff
    ((eval_affineChart_dehomogenize_eq_zero_iff hPi hF).2 hP)]
  set φ := (quotientLocalEquationChartEquiv hF hPi).toRingEquiv
  refine ⟨fun ⟨_, _⟩ ↦ ?_, fun ⟨_, _⟩ ↦ ?_⟩
  · have := MulEquiv.isDomain _ φ.symm.toMulEquiv
    exact ⟨this, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing φ⟩
  · have := MulEquiv.isDomain _ φ.toMulEquiv
    exact ⟨this, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing φ.symm⟩

/-- **Property (8)** for an irreducible curve. Let `F` be an irreducible form, `C : F = 0` and
`P ∈ C`. For forms `G` and `H` of the same degree with `H(P) ≠ 0`, `I(P, F ∩ G)` is the order
`ord_P^F(G)` of the rational function `G / H` in the local ring `𝒪_P(C)`. -/
theorem intersectionNumber_eq_ord_localSubring (hF : F.IsHomogeneous d) [Fact (Irreducible F)]
    (P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)))
    (c : HomogeneousLocalization.NumDenSameDeg (homogeneousSubmodule (Fin 3) k)
      (pointIdeal P.1).toIdeal.primeCompl) :
    intersectionNumber P.1 F c.num = Ring.ord (localSubring hF P).toSubring
      (toLocalSubring hF P (HomogeneousLocalization.mk c)) := by
  rw [intersectionNumber_eq_ord hF ((mem_homogeneousSubmodule _ _).1 c.num.2),
    ← Ring.ord_ringEquiv (quotientLocalEquationEquiv hF P).toRingEquiv]
  change Ring.ord _ (quotientLocalEquationEquiv hF P (Ideal.Quotient.mk _ _)) = _
  rw [quotientLocalEquationEquiv_mk]
  exact Ring.ord_eq_of_associated ((associated_localEquation_mk c).map (toLocalSubring hF P))

/-! ### The milestones -/

/-- **The intersection number of projective plane curves at a point.** Let `k` be algebraically
closed, `F`, `G` nonzero forms of degrees `d`, `e` and `P ∈ ℙ²`. The intersection number
`I(P, F ∩ G) = ℓ(𝒪_P(ℙ²) ⧸ (F_*, G_*))` does not depend on the local equations (any fractions
`F / s`, `G / t` of forms of the same degrees with `s(P), t(P) ≠ 0`, for instance
`s = L^d`, `t = L^e`), nor on scaling `F` and `G`, and it is the affine intersection number of
the dehomogenizations in every standard chart containing `P`. Moreover:

1. `I(P, F ∩ G) < ∞` iff `F` and `G` have no common component through `P`;
2. `I(P, F ∩ G) = 0` iff `P ∉ V(F) ∩ V(G)`, and components of `F` not through `P` do not count;
3. `I(Q, F^T ∩ G^T) = I(T(Q), F ∩ G)` for a projective change of coordinates `T`;
4. `I(P, F ∩ G) = I(P, G ∩ F)`;
5. `I(P, F ∩ G) ≥ m_P(F) m_P(G)`, with equality iff `F` and `G` have no common tangent at `P`;
6. `I(P, F ∩ G) = ∑ᵢ ∑ⱼ rᵢ sⱼ I(P, Fᵢ ∩ Gⱼ)` if `F = ∏ Fᵢ ^ rᵢ` and `G = ∏ Gⱼ ^ sⱼ`;
7. `I(P, F ∩ (G + A F)) = I(P, F ∩ G)` for every `A` (a form of degree `e - d` for `G + A F` to
   be a form);
8. if `P` is a simple point of `F`, then `𝒪_P(ℙ²) ⧸ (F_*)` is a discrete valuation ring and
   `I(P, F ∩ G') = ord_P^F(G')` is the order of `G'_*` there, for every form `G'`; for an
   irreducible `F` this is the order of `G' / H` in `𝒪_P(C)`, for every form `H` of the degree of
   `G'` with `H(P) ≠ 0`.

Milestone: *Intersection number of projective plane curves at a point*. -/
theorem intersectionNumber_spec [IsAlgClosed k] (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e)
    (hF0 : F ≠ 0) (hG0 : G ≠ 0) :
    -- independence of the local equations, scaling, and charts
    (∀ c c' : HomogeneousLocalization.NumDenSameDeg (homogeneousSubmodule (Fin 3) k)
        (pointIdeal P).toIdeal.primeCompl,
      (c.num : MvPolynomial (Fin 3) k) = F → (c'.num : MvPolynomial (Fin 3) k) = G →
        intersectionNumber P F G = Module.length (localRing P) (localRing P ⧸
          Ideal.span {HomogeneousLocalization.mk c, HomogeneousLocalization.mk c'})) ∧
    (∀ a b : k, a ≠ 0 → b ≠ 0 → intersectionNumber P (a • F) (b • G) = intersectionNumber P F G) ∧
    (∀ i : Fin 3, P ∈ affineOpen i → intersectionNumber P F G =
      Affine.intersectionNumber (affineChart i P) (dehomogenize i F) (dehomogenize i G)) ∧
    -- (1)
    (intersectionNumber P F G ≠ ⊤ ↔
      ∀ H : MvPolynomial (Fin 3) k, Irreducible H → H ∣ F → H ∣ G → eval P.rep H ≠ 0) ∧
    -- (2)
    (intersectionNumber P F G = 0 ↔ eval P.rep F ≠ 0 ∨ eval P.rep G ≠ 0) ∧
    (∀ (U : MvPolynomial (Fin 3) k) (n : ℕ), U.IsHomogeneous n → eval P.rep U ≠ 0 →
      intersectionNumber P (F * U) G = intersectionNumber P F G) ∧
    -- (3)
    (∀ (M : GL (Fin 3) k) (Q : ℙ k (Fin 3 → k)),
      intersectionNumber Q (linearSubst M.1 F) (linearSubst M.1 G) =
        intersectionNumber (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) Q)
          F G) ∧
    -- (4)
    intersectionNumber P F G = intersectionNumber P G F ∧
    -- (5)
    (mult F P * mult G P ≤ intersectionNumber P F G ∧
      (intersectionNumber P F G = mult F P * mult G P ↔
        ¬∃ L, IsTangentAt F P L ∧ IsTangentAt G P L)) ∧
    -- (6)
    (∀ {ι : Type u} {κ : Type v} (s : Finset ι) (t : Finset κ) (Fᵢ : ι → MvPolynomial (Fin 3) k)
      (Gⱼ : κ → MvPolynomial (Fin 3) k) (dF : ι → ℕ) (dG : κ → ℕ) (r : ι → ℕ) (r' : κ → ℕ),
      (∀ i ∈ s, (Fᵢ i).IsHomogeneous (dF i)) → (∀ j ∈ t, (Gⱼ j).IsHomogeneous (dG j)) →
        F = ∏ i ∈ s, Fᵢ i ^ r i → G = ∏ j ∈ t, Gⱼ j ^ r' j →
          intersectionNumber P F G =
            ∑ i ∈ s, ∑ j ∈ t, (r i * r' j : ℕ∞) * intersectionNumber P (Fᵢ i) (Gⱼ j)) ∧
    -- (7)
    (∀ A : MvPolynomial (Fin 3) k, intersectionNumber P F (G + A * F) = intersectionNumber P F G) ∧
    -- (8)
    (IsSimplePoint F P →
      (∃ _ : IsDomain (localRing P ⧸ Ideal.span {localEquation P F}),
        IsDiscreteValuationRing (localRing P ⧸ Ideal.span {localEquation P F})) ∧
      (∀ (G' : MvPolynomial (Fin 3) k) (e' : ℕ), G'.IsHomogeneous e' →
        intersectionNumber P F G' = Ring.ord (localRing P ⧸ Ideal.span {localEquation P F})
          (Ideal.Quotient.mk _ (localEquation P G'))) ∧
      ∀ [Fact (Irreducible F)]
        (Q : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))),
        Q.1 = P → ∀ c : HomogeneousLocalization.NumDenSameDeg (homogeneousSubmodule (Fin 3) k)
          (pointIdeal Q.1).toIdeal.primeCompl,
          intersectionNumber P F c.num = Ring.ord (localSubring hF Q).toSubring
            (toLocalSubring hF Q (HomogeneousLocalization.mk c))) := by
  refine ⟨fun c c' hc hc' ↦ ?_, fun a b ha hb ↦ ?_,
    fun i hP ↦ intersectionNumber_eq_affine hF hG hP,
    intersectionNumber_ne_top_iff hF hG, intersectionNumber_eq_zero_iff hF hG,
    fun U n hU hUP ↦ intersectionNumber_mul_left_of_eval_ne_zero hF hU hG hUP,
    fun M Q ↦ intersectionNumber_linearSubst hF hG M Q, intersectionNumber_comm P F G,
    ⟨mul_mult_le_intersectionNumber hF hG, intersectionNumber_eq_mul_mult_iff hF hG hF0 hG0⟩,
    fun s t Fᵢ Gⱼ dF dG r r' hFᵢ hGⱼ hFp hGp ↦ ?_, fun A ↦ intersectionNumber_add_mul P F G A,
    fun hs ↦ ⟨(exists_isDiscreteValuationRing_quotient_iff hF hs.eval_rep_eq_zero).2 hs,
      fun G' e' hG' ↦ intersectionNumber_eq_ord hF hG', fun Q hQ c ↦ ?_⟩⟩
  · rw [← hc, ← hc', intersectionNumber_eq_length_mk]
  · rw [intersectionNumber_smul_left ha, intersectionNumber_smul_right hb]
  · rw [hFp, hGp, intersectionNumber_prod_pow_prod_pow s t hFᵢ hGⱼ]
  · subst hQ
    exact intersectionNumber_eq_ord_localSubring hF Q c

/-- **Singular points and tangent lines of a projective plane curve via partial derivatives.**
Let `F` be a nonzero form of degree `d`.

* (a) `[v]` is a multiple point of `F` iff `F(v) = F_X(v) = F_Y(v) = F_Z(v) = 0` (Problem 5.1),
  in every characteristic.
* (b) At a simple point `P = [v]`, the tangent line is `F_X(v) X + F_Y(v) Y + F_Z(v) Z`, a nonzero
  linear form vanishing at `P`; every tangent at `P` is a nonzero multiple of it (Problem 5.4).
* (c) A line `L = 0` through `P` is tangent to `F` at `P` iff `I(P, F ∩ L) > m_P(F)`; the
  tangent lines at `P` are those of the dehomogenization `F_(i)` in any chart containing `P`
  (the linear factors of its lowest-degree form at the chart point), and `P` is an ordinary
  multiple point of `F` iff its chart point is one of `F_(i)`.
* (d) If `P = [0 : 1 : 0]` and `F = ∑ᵢ Fᵢ(X, Z) Y^{d-i}` with `Fᵢ` a form of degree `i`, then
  `m_P(F)` is the least `m` with `Fₘ ≠ 0`, and the tangent lines at `P` are the linear factors
  of `Fₘ`, with the same multiplicities (Problem 5.5).

Milestone: *Singular points and tangent lines of a projective plane curve via partial
derivatives*. -/
theorem isMultiplePoint_and_isTangentAt_spec (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) :
    -- (a)
    (∀ (v : Fin 3 → k) (hv : v ≠ 0),
      IsMultiplePoint F (mk k v hv) ↔ eval v F = 0 ∧ ∀ i, eval v (pderiv i F) = 0) ∧
    -- (b)
    (∀ P : ℙ k (Fin 3 → k), IsSimplePoint F P →
      (tangentLine F P.rep).IsHomogeneous 1 ∧ tangentLine F P.rep ≠ 0 ∧
        eval P.rep (tangentLine F P.rep) = 0 ∧ IsTangentAt F P (tangentLine F P.rep) ∧
        ∀ L, IsTangentAt F P L → Associated L (tangentLine F P.rep)) ∧
    -- (c)
    (∀ (P : ℙ k (Fin 3 → k)) (L : MvPolynomial (Fin 3) k), L.IsHomogeneous 1 → L ≠ 0 →
      eval P.rep L = 0 → (IsTangentAt F P L ↔ mult F P < intersectionNumber P F L) ∧
        ∀ i : Fin 3, P ∈ affineOpen i → (IsTangentAt F P L ↔
          Affine.IsTangentAt (dehomogenize i F) (affineChart i P)
            (taylor (affineChart i P) (dehomogenize i L)))) ∧
    (∀ (P : ℙ k (Fin 3 → k)) (i : Fin 3), P ∈ affineOpen i → ∀ L' : MvPolynomial (Fin 2) k,
      L'.IsHomogeneous 1 →
        (IsTangentAt F P (aeval (fun j ↦ X (i.succAbove j) - C (affineChart i P j) * X i) L') ↔
          Affine.IsTangentAt (dehomogenize i F) (affineChart i P) L')) ∧
    (∀ (P : ℙ k (Fin 3 → k)) (i : Fin 3), P ∈ affineOpen i →
      (IsOrdinaryMultiplePoint F P ↔
        Affine.IsOrdinaryMultiplePoint (dehomogenize i F) (affineChart i P))) ∧
    -- (d)
    ∀ {G : ℕ → MvPolynomial (Fin 2) k}, (∀ i, (G i).IsHomogeneous i) →
      F = ∑ i ∈ Finset.range (d + 1), rename (Fin.succAbove 1) (G i) * X 1 ^ (d - i) →
      ∀ {m : ℕ}, m ≤ d → (∀ i < m, G i = 0) → G m ≠ 0 →
        mult F (mk k ![0, 1, 0] (by simp)) = m ∧
        Associated (leadingForm F (mk k ![0, 1, 0] (by simp))) (rename (Fin.succAbove 1) (G m)) ∧
        (∀ L : MvPolynomial (Fin 2) k,
          IsTangentAt F (mk k ![0, 1, 0] (by simp)) (rename (Fin.succAbove 1) L) ↔
            L.IsHomogeneous 1 ∧ L ≠ 0 ∧ L ∣ G m) ∧
        ∀ L : MvPolynomial (Fin 2) k,
          tangentMultiplicity F (mk k ![0, 1, 0] (by simp)) (rename (Fin.succAbove 1) L) =
            multiplicity L (G m) :=
  ⟨fun v hv ↦ isMultiplePoint_iff_eval_pderiv hF v hv,
    fun _ hP ↦ ⟨(isTangentAt_def.1 (hP.isTangentAt_tangentLine hF)).1,
      (isTangentAt_def.1 (hP.isTangentAt_tangentLine hF)).2.1,
      (isTangentAt_def.1 (hP.isTangentAt_tangentLine hF)).2.2.1, hP.isTangentAt_tangentLine hF,
      fun _ hL ↦ hP.associated_tangentLine_of_isTangentAt hF hL⟩,
    fun _ _ hL hL0 hLP ↦ ⟨isTangentAt_iff_mult_lt_intersectionNumber hF hF0 hL hL0 hLP,
      fun _ hP ↦ isTangentAt_iff_affine hF hP hL hLP⟩,
    fun _ _ hP _ hL' ↦ isTangentAt_aeval_chart_iff hF hP hL',
    fun _ _ hP ↦ isOrdinaryMultiplePoint_iff_affine hF hP,
    fun hG hFG _ hmd hlt hm ↦ mult_eq_and_isTangentAt_iff_of_eq_sum hG hFG hmd hlt hm⟩

end PlaneCurves.Projective

end
