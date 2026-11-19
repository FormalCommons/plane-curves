/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Center
public import PlaneCurves.FieldTheory.FunctionField.Place.AddValuation

/-!
# Places over a point of a plane curve and the order of a form at a place

Let `k` be an algebraically closed field and `C : F = 0` an irreducible projective plane curve
with function field `k(C)`. Every place `Q` of `k(C)` has a centre `center hF Q ∈ C`. The places
**over** a point `P ∈ C` are those centred at `P`; there are finitely many, and at least one.

For a form `G` of degree `m` and a place `Q`, the **order of `G` at `Q`** is the order at `Q` of
the rational function `G / H`, for any form `H` of degree `m` not vanishing at the centre of `Q`,
for instance `H = Lᵐ` for a linear form `L` with `L(center Q) ≠ 0`. Two such quotients differ by
a unit of `𝒪_{center Q}(C)`, so the order does not depend on `H`. It is `⊤` iff `F ∣ G`,
nonnegative, positive iff `G` vanishes at the centre, and
additive in `G`. In a chart `Xᵢ ≠ 0` containing the centre it is the order of the class of the
dehomogenization `G_(i)`.

## Main definitions

* `PlaneCurves.Projective.placesOver hF P`: the places of `k(C)` centred at `P`.
* `PlaneCurves.Projective.ordForm hF Q hG`: the order `ord_Q(G)` of a form `G` at a place `Q`.

## Main results

* `mem_placesOver_iff`, `mem_placesOver_iff_le`, `placesOver_finite`, `placesOver_nonempty`.
* `ordForm_eq_addValuation_mk`: `ord_Q(G)` is the order of `G / H` for any form `H` of the
  degree of `G` with `H(center Q) ≠ 0`; `ordForm_eq_addValuation_mk_pow` for `H = Lᵐ`.
* `ordForm_eq_addValuation_mk_add`: `ord_Q(G) = ord_Q(G / H) + ord_Q(H)` when `F ∤ H`.
* `ordForm_mul`, `ordForm_eq_top_iff`, `ordForm_nonneg`, `ordForm_pos_iff`, `ordForm_eq_zero_iff`.
* `ordForm_eq_of_dvd_sub`: `ord_Q(G)` depends only on `G` modulo `F`.
* `ordForm_eq_addValuation_chartEquiv_symm`: the order in a chart.
* `mem_placesOver_iff_localSubring_le_map_chartEquiv`, `ordForm_eq_addValuation_map_chartEquiv`:
  the places over a point of a chart, and their orders, read in the affine curve of the chart;
  `mem_placesOver_iff_localSubring_le_map_chartEquiv_of_eq` at given chart coordinates.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.1
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti
open TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
  (hF : F.IsHomogeneous d) [Fact (Irreducible F)]

/-! ### Places over a point -/

/-- The **places over** a point `P` of the irreducible projective plane curve `C : F = 0`: the
places of the function field `k(C)` centred at `P`. -/
def placesOver (P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))) :
    Set (Place k (functionField hF)) :=
  {Q | center hF Q = P}

variable {hF}
variable {P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))}
  {Q : Place k (functionField hF)}

theorem placesOver_def : placesOver hF P = {Q | center hF Q = P} :=
  (rfl)

@[simp]
theorem mem_placesOver_iff : Q ∈ placesOver hF P ↔ center hF Q = P :=
  Iff.rfl

/-- A place lies over `P` iff its valuation ring contains `𝒪_P(C)`. -/
theorem mem_placesOver_iff_le :
    Q ∈ placesOver hF P ↔ (localSubring hF P).toSubring ≤ Q.integers.toSubring :=
  center_eq_iff_le

/-- A place lies over its centre. -/
theorem mem_placesOver_center (Q : Place k (functionField hF)) :
    Q ∈ placesOver hF (center hF Q) :=
  mem_placesOver_iff.2 rfl

variable (hF P) in
/-- Only finitely many places lie over a point. -/
theorem placesOver_finite : (placesOver hF P).Finite :=
  finite_setOf_center_eq hF P

variable (hF P) in
/-- Some place lies over every point. -/
theorem placesOver_nonempty : (placesOver hF P).Nonempty :=
  center_surjective hF P

/-- **Centres along an isomorphism of function fields.** If an isomorphism `e : k(C) ≅ k(D)` of
the function fields of the curves `C : F = 0` and `D : G = 0` carries `𝒪_P(C)` onto `𝒪_{P'}(D)`,
then a place of `k(C)`, moved to `k(D)`, is centred at `P'` iff it is centred at `P`. -/
theorem center_map_eq_iff_of_map_localSubring {G : MvPolynomial (Fin 3) k} {m : ℕ}
    {hG : G.IsHomogeneous m} [Fact (Irreducible G)] (e : functionField hF ≃ₐ[k] functionField hG)
    {P' : zeroLocus (projectivePlaneCurve.ideal hG : Set (MvPolynomial (Fin 3) k))}
    (h : (localSubring hF P).map (e : functionField hF →+* _) = localSubring hG P') :
    center hG (Q.map e) = P' ↔ center hF Q = P := by
  rw [center_eq_iff_le, center_eq_iff_le, ← h, LocalSubring.map_toSubring,
    Subring.map_le_iff_le_comap]
  refine ⟨fun h z hz ↦ ?_, fun h z hz ↦ ?_⟩
  · simpa using (Place.mem_integers_map_iff _ Q).1 (h hz)
  · exact (Place.mem_integers_map_iff _ Q).2 (by simpa using h hz)

/-- Centres do not change along `ProjectiveSpace.functionField.equivOfEq`, the identification of
the function fields of two forms with the same ideal. -/
theorem coe_center_map_equivOfEq {G : MvPolynomial (Fin 3) k} {m : ℕ} {hG : G.IsHomogeneous m}
    [Fact (Irreducible G)] (hI : projectivePlaneCurve.ideal hF = projectivePlaneCurve.ideal hG)
    (Q : Place k (functionField hF)) :
    (center hG (Q.map (ProjectiveSpace.functionField.equivOfEq hI))).1 = (center hF Q).1 :=
  congrArg Subtype.val ((center_map_eq_iff_of_map_localSubring _
    (ProjectiveSpace.map_localSubring_equivOfEq hI (center hF Q) ⟨_, hI ▸ (center hF Q).2⟩
      rfl)).2 rfl)

/-! ### The order of a form at a place -/

/-- The local ring at the centre of `Q` lies in the valuation ring of `Q`. -/
theorem localSubring_center_le (Q : Place k (functionField hF)) :
    (localSubring hF (center hF Q)).toSubring ≤ Q.integers.toSubring :=
  center_eq_iff_le.1 rfl

variable {m m' : ℕ} {G G' H H' : MvPolynomial (Fin 3) k}

/-- A fraction `G / H` with `H` not vanishing at the centre of `Q` has nonnegative order. -/
private theorem addValuation_mk_nonneg (hG : G.IsHomogeneous m) (hH : H.IsHomogeneous m)
    (hHQ : eval (center hF Q).1.rep H ≠ 0) :
    0 ≤ Q.addValuation
      (functionField.mk hG hH (notMem_of_eval_rep_ne_zero (center hF Q).2 hH hHQ)) :=
  Q.addValuation_nonneg_iff.2 (localSubring_center_le Q
    (mem_localSubring_iff.2 ⟨m, G, H, hG, hH, hHQ, rfl⟩))

/-- A fraction `G / H` of forms neither of which vanishes at the centre of `Q` has order `0`. -/
private theorem addValuation_mk_eq_zero (hG : G.IsHomogeneous m) (hH : H.IsHomogeneous m)
    (hGQ : eval (center hF Q).1.rep G ≠ 0) (hHQ : eval (center hF Q).1.rep H ≠ 0) :
    Q.addValuation
      (functionField.mk hG hH (notMem_of_eval_rep_ne_zero (center hF Q).2 hH hHQ)) = 0 := by
  have hGI := notMem_of_eval_rep_ne_zero (center hF Q).2 hG hGQ
  have hHI := notMem_of_eval_rep_ne_zero (center hF Q).2 hH hHQ
  have h1 := addValuation_mk_nonneg hG hH hHQ
  have h2 := addValuation_mk_nonneg hH hG hGQ
  have h3 := congrArg Q.addValuation (functionField.mk_mul_mk_swap hG hH hGI hHI)
  rw [Q.addValuation.map_mul, Q.addValuation.map_one] at h3
  have h1' := Q.addValuation_ne_top_iff.2 (functionField.mk_ne_zero hG hH hHI hGI)
  have h2' := Q.addValuation_ne_top_iff.2 (functionField.mk_ne_zero hH hG hGI hHI)
  lift Q.addValuation (functionField.mk hG hH hHI) to ℤ using h1' with a ha
  lift Q.addValuation (functionField.mk hH hG hGI) to ℤ using h2' with b hb
  norm_cast at h1 h2 h3 ⊢
  omega

/-- The order of `G / H` does not depend on the form `H` not vanishing at the centre of `Q`. -/
private theorem addValuation_mk_eq (hG : G.IsHomogeneous m) (hH : H.IsHomogeneous m)
    (hH' : H'.IsHomogeneous m) (hHQ : eval (center hF Q).1.rep H ≠ 0)
    (hHQ' : eval (center hF Q).1.rep H' ≠ 0) :
    Q.addValuation
        (functionField.mk hG hH' (notMem_of_eval_rep_ne_zero (center hF Q).2 hH' hHQ')) =
      Q.addValuation
        (functionField.mk hG hH (notMem_of_eval_rep_ne_zero (center hF Q).2 hH hHQ)) := by
  have hHI := notMem_of_eval_rep_ne_zero (center hF Q).2 hH hHQ
  have hHI' := notMem_of_eval_rep_ne_zero (center hF Q).2 hH' hHQ'
  have h := functionField.mk_div_mk hG hH hH' hHI hHI'
  rw [div_eq_iff (functionField.mk_ne_zero hH hH' hHI' hHI)] at h
  rw [h, Q.addValuation.map_mul, addValuation_mk_eq_zero hH hH' hHQ hHQ', add_zero]

/-- A coordinate `Xᵢ` not vanishing at the centre of `Q`. -/
private theorem eval_rep_X_choose_ne_zero (Q : Place k (functionField hF)) :
    eval (center hF Q).1.rep (X (center hF Q).1.exists_mem_affineOpen.choose) ≠ 0 := by
  simpa using (mem_affineOpen_iff _ _).1 (center hF Q).1.exists_mem_affineOpen.choose_spec

/-- A coordinate `Xᵢ` not vanishing at the centre of `Q`. -/
private theorem exists_eval_X_ne_zero (Q : Place k (functionField hF)) :
    ∃ i : Fin 3, eval (center hF Q).1.rep (X i) ≠ 0 :=
  ⟨_, eval_rep_X_choose_ne_zero Q⟩

/-- A power of a coordinate not vanishing at the centre of `Q` does not vanish there. -/
private theorem eval_X_pow_ne_zero {i : Fin 3} (hi : eval (center hF Q).1.rep (X i) ≠ 0)
    (m : ℕ) :
    eval (center hF Q).1.rep (X i ^ m) ≠ 0 := by
  simpa using pow_ne_zero m hi

variable (hF) in
/-- The **order of a form** `G` of degree `m` at a place `Q` of `k(C)`: the order at `Q` of the
rational function `G / Lᵐ`, for a linear form `L` not vanishing at the centre of `Q`
(`ordForm_eq_addValuation_mk_pow`); equivalently of `G / H` for any form `H` of degree `m` with
`H(center Q) ≠ 0` (`ordForm_eq_addValuation_mk`). It is `⊤` iff `F ∣ G`
(`ordForm_eq_top_iff`). -/
noncomputable def ordForm (Q : Place k (functionField hF)) {m : ℕ} {G : MvPolynomial (Fin 3) k}
    (hG : G.IsHomogeneous m) : WithTop ℤ :=
  Q.addValuation (functionField.mk hG
    (isHomogeneous_X_pow (center hF Q).1.exists_mem_affineOpen.choose m)
    (notMem_of_eval_rep_ne_zero (center hF Q).2
      (isHomogeneous_X_pow (center hF Q).1.exists_mem_affineOpen.choose m) (by
        simpa using pow_ne_zero m ((mem_affineOpen_iff _ _).1
          (center hF Q).1.exists_mem_affineOpen.choose_spec))))

/-- The definition of `ordForm`, with the coordinate `Xᵢ` it chooses. -/
theorem ordForm_def (hG : G.IsHomogeneous m) :
    ordForm hF Q hG = Q.addValuation (functionField.mk hG
      (isHomogeneous_X_pow (center hF Q).1.exists_mem_affineOpen.choose m)
      (notMem_of_eval_rep_ne_zero (center hF Q).2
        (isHomogeneous_X_pow (center hF Q).1.exists_mem_affineOpen.choose m) (by
          simpa using pow_ne_zero m ((mem_affineOpen_iff _ _).1
            (center hF Q).1.exists_mem_affineOpen.choose_spec)))) :=
  (rfl)

/-- `ord_Q(G)` is the order at `Q` of `G / H`, for any form `H` of the degree of `G` not vanishing
at the centre of `Q`. -/
theorem ordForm_eq_addValuation_mk (hG : G.IsHomogeneous m) (hH : H.IsHomogeneous m)
    (hHQ : eval (center hF Q).1.rep H ≠ 0) :
    ordForm hF Q hG = Q.addValuation
      (functionField.mk hG hH (notMem_of_eval_rep_ne_zero (center hF Q).2 hH hHQ)) := by
  rw [ordForm_def]
  exact addValuation_mk_eq hG hH _ hHQ (eval_X_pow_ne_zero (eval_rep_X_choose_ne_zero Q) m)

/-- `ord_Q(G)` is the order at `Q` of `G / Lᵐ`, for any linear form `L` not vanishing at the
centre of `Q`. -/
theorem ordForm_eq_addValuation_mk_pow {L : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m)
    (hL : L.IsHomogeneous 1) (hLQ : eval (center hF Q).1.rep L ≠ 0) :
    ordForm hF Q hG = Q.addValuation (functionField.mk hG (one_mul m ▸ hL.pow m)
      (notMem_of_eval_rep_ne_zero (center hF Q).2 (one_mul m ▸ hL.pow m)
        (by simpa using pow_ne_zero m hLQ))) :=
  ordForm_eq_addValuation_mk hG _ (by simpa using pow_ne_zero m hLQ)

/-- **`ord_Q(G / H) = ord_Q(G) - ord_Q(H)`**, in the additive form
`ord_Q(G) = ord_Q(G / H) + ord_Q(H)`, for forms `G`, `H` of the same degree with `F ∤ H`. -/
theorem ordForm_eq_addValuation_mk_add (Q : Place k (functionField hF)) (hG : G.IsHomogeneous m)
    (hH : H.IsHomogeneous m) (hFH : ¬ F ∣ H) :
    ordForm hF Q hG = Q.addValuation
      (functionField.mk hG hH (projectivePlaneCurve.notMem_ideal_of_not_dvd hF hFH)) +
      ordForm hF Q hH := by
  obtain ⟨i, hi⟩ := (center hF Q).1.exists_mem_affineOpen
  have hXQ : eval (center hF Q).1.rep (X i ^ m) ≠ 0 := by
    simpa using pow_ne_zero m ((mem_affineOpen_iff _ _).1 hi)
  rw [ordForm_eq_addValuation_mk hG (isHomogeneous_X_pow i m) hXQ,
    ordForm_eq_addValuation_mk hH (isHomogeneous_X_pow i m) hXQ, ← Q.addValuation.map_mul,
    functionField.mk_mul_mk]
  congr 1
  exact functionField.mk_eq_mk_of_mul_eq _ _ _ _ _ _ (by ring)

/-- The order of a form at `Q` in terms of the coordinate functions `Xⱼ / Xᵢ`, for a coordinate
`Xᵢ` not vanishing at the centre of `Q`. -/
theorem ordForm_eq_addValuation_aeval {i : Fin 3} (hi : eval (center hF Q).1.rep (X i) ≠ 0)
    (hG : G.IsHomogeneous m) :
    ordForm hF Q hG = Q.addValuation (aeval (fun j ↦ functionField.mk (isHomogeneous_X k j)
      (isHomogeneous_X k i) (notMem_of_eval_rep_ne_zero (center hF Q).2 (isHomogeneous_X k i) hi))
        G) := by
  rw [functionField.aeval_mk_X]
  exact ordForm_eq_addValuation_mk hG _ (eval_X_pow_ne_zero hi m)

/-- The order of a form at a place depends only on the form and its degree, not on the proof
that it is homogeneous. -/
theorem ordForm_congr (hG : G.IsHomogeneous m) (hG' : G'.IsHomogeneous m') (hGG' : G = G')
    (hm : m = m') : ordForm hF Q hG = ordForm hF Q hG' := by
  subst hGG' hm
  rfl

/-- The order of a product of forms is the sum of the orders. -/
theorem ordForm_mul (hG : G.IsHomogeneous m) (hG' : G'.IsHomogeneous m') :
    ordForm hF Q (hG.mul hG') = ordForm hF Q hG + ordForm hF Q hG' := by
  obtain ⟨i, hi⟩ := exists_eval_X_ne_zero Q
  rw [ordForm_eq_addValuation_aeval hi, ordForm_eq_addValuation_aeval hi,
    ordForm_eq_addValuation_aeval hi, map_mul, Q.addValuation.map_mul]

/-- The order of a form `G` at `Q` is `⊤` iff `G` vanishes on `C`, that is `F ∣ G`. -/
theorem ordForm_eq_top_iff (hG : G.IsHomogeneous m) : ordForm hF Q hG = ⊤ ↔ F ∣ G := by
  rw [ordForm_def, Q.addValuation_eq_top_iff, functionField.mk_eq_zero_iff,
    projectivePlaneCurve.mem_ideal_iff]

/-- The order of a form at `Q` depends only on the form modulo `F`: forms `G`, `G'` of the same
degree with `F ∣ G - G'` have the same order. -/
theorem ordForm_eq_of_dvd_sub (hG : G.IsHomogeneous m) (hG' : G'.IsHomogeneous m)
    (h : F ∣ G - G') : ordForm hF Q hG = ordForm hF Q hG' := by
  rw [ordForm_def, ordForm_def, (functionField.mk_eq_mk_iff _ _ _ _ _ _).2]
  rw [projectivePlaneCurve.mem_ideal_iff, ← sub_mul]
  exact dvd_mul_of_dvd_left h _

/-- The order of a form at a place is nonnegative. -/
theorem ordForm_nonneg (hG : G.IsHomogeneous m) : 0 ≤ ordForm hF Q hG := by
  rw [ordForm_def]
  exact addValuation_mk_nonneg hG _ (eval_X_pow_ne_zero (eval_rep_X_choose_ne_zero Q) m)

/-- The order of a form not vanishing at the centre of `Q` is `0`. -/
theorem ordForm_eq_zero_of_eval_ne_zero (hG : G.IsHomogeneous m)
    (hGQ : eval (center hF Q).1.rep G ≠ 0) : ordForm hF Q hG = 0 := by
  rw [ordForm_eq_addValuation_mk hG hG hGQ, functionField.mk_self, Q.addValuation.map_one]

/-- The order of a form at `Q` is positive iff the form vanishes at the centre of `Q`. -/
theorem ordForm_pos_iff (hG : G.IsHomogeneous m) :
    0 < ordForm hF Q hG ↔ eval (center hF Q).1.rep G = 0 := by
  refine ⟨fun h ↦ by_contra fun hGQ ↦ ?_, fun hGQ ↦ ?_⟩
  · rw [ordForm_eq_zero_of_eval_ne_zero hG hGQ] at h
    exact lt_irrefl _ h
  obtain ⟨i, hi⟩ := exists_eval_X_ne_zero Q
  have hXQ := eval_X_pow_ne_zero hi m
  rw [ordForm_eq_addValuation_mk hG (isHomogeneous_X_pow i m) hXQ]
  let z : (localSubring hF (center hF Q)).toSubring :=
    ⟨_, mem_localSubring_iff.2 ⟨m, G, _, hG, isHomogeneous_X_pow i m, hXQ, rfl⟩⟩
  have hz : z ∈ IsLocalRing.maximalIdeal _ :=
    mem_maximalIdeal_localSubring_iff.2 ⟨m, G, _, hG, _, hXQ, hGQ, rfl⟩
  have hv := (isCenter_iff.1 (isCenter_center Q)).2 z hz
  let w : Q.integers := ⟨z, localSubring_center_le Q z.2⟩
  exact (Q.addValuation_pos_iff (z := w)).2 ((Q.integers.valuation_lt_one_iff w).2 hv)

/-- The order of a form at `Q` is `0` iff the form does not vanish at the centre of `Q`. -/
theorem ordForm_eq_zero_iff (hG : G.IsHomogeneous m) :
    ordForm hF Q hG = 0 ↔ eval (center hF Q).1.rep G ≠ 0 := by
  rw [ne_eq, ← ordForm_pos_iff hG, (ordForm_nonneg hG).lt_iff_ne', not_not]

/-- **The order in a chart.** If the centre of `Q` lies in the chart `Xᵢ ≠ 0`, the order of a
form `G` at `Q` is the order of the class of its dehomogenization `G_(i)` in `k(F_(i))`, carried
to `k(C)` by the inverse of the chart isomorphism `functionField.chartEquiv`. -/
theorem ordForm_eq_addValuation_chartEquiv_symm {i : Fin 3}
    (hQ : (center hF Q).1 ∈ affineOpen i) (hG : G.IsHomogeneous m) :
    haveI := isPrime_span_dehomogenize hF (not_dvd_X_of_mem_affineOpen hF _ hQ)
    ordForm hF Q hG = Q.addValuation
      ((functionField.chartEquiv hF i (not_dvd_X_of_mem_affineOpen hF _ hQ)).symm
        (algebraMap _ _
          (Ideal.Quotient.mk (Ideal.span {dehomogenize i F}) (dehomogenize i G)))) := by
  have hi : eval (center hF Q).1.rep (X i) ≠ 0 := by simpa using (mem_affineOpen_iff i _).1 hQ
  rw [ordForm_eq_addValuation_mk hG (isHomogeneous_X_pow i m) (eval_X_pow_ne_zero hi m)]
  congr 1
  rw [eq_comm, AlgEquiv.symm_apply_eq, functionField.chartEquiv_mk]
  simp only [map_pow, dehomogenize_X, Fin.insertNth_apply_same, one_pow, map_one]
  have := isPrime_span_dehomogenize hF (not_dvd_X_of_mem_affineOpen hF _ hQ)
  exact (div_one _).symm

/-- **Places over a point, in a chart.** A place `Q` of `k(C)` lies over a point `P` of the chart
`Xᵢ ≠ 0` iff the valuation ring of `Q`, carried to `k(F_(i))` by `functionField.chartEquiv`,
contains the local ring of the affine curve `F_(i) = 0` at the chart point of `P`. -/
theorem mem_placesOver_iff_localSubring_le_map_chartEquiv {i : Fin 3} (hP : P.1 ∈ affineOpen i)
    {Q : Place k (functionField hF)} :
    haveI := isPrime_span_dehomogenize hF (not_dvd_X_of_mem_affineOpen hF P hP)
    Q ∈ placesOver hF P ↔ (AffineSpace.localSubring (affineChart i P.1)
        (span_dehomogenize_le_vanishingIdeal hF P hP)).toSubring ≤
      (Q.map (functionField.chartEquiv hF i
        (not_dvd_X_of_mem_affineOpen hF P hP))).integers.toSubring := by
  have := isPrime_span_dehomogenize hF (not_dvd_X_of_mem_affineOpen hF P hP)
  rw [mem_placesOver_iff_le]
  refine ⟨fun h w hw ↦ ?_, fun h z hz ↦ ?_⟩
  · obtain ⟨z, hz⟩ := (localSubring.chartEquiv hF i P hP).surjective ⟨w, hw⟩
    have hw' := congrArg Subtype.val hz
    rw [localSubring.coe_chartEquiv] at hw'
    change w ∈ (Q.map _).integers
    rw [Place.mem_integers_map_iff, show w = _ from hw'.symm, AlgEquiv.symm_apply_apply]
    exact h z.2
  · have := h (localSubring.chartEquiv hF i P hP ⟨z, hz⟩).2
    rw [localSubring.coe_chartEquiv] at this
    change _ ∈ (Q.map _).integers at this
    rwa [Place.mem_integers_map_iff, AlgEquiv.symm_apply_apply] at this

/-- **Places over a point, in a chart, at given chart coordinates.** If the point `P` of the
chart `Xᵢ ≠ 0` has chart coordinates `a`, a place `Q` of `k(C)` lies over `P` iff the valuation
ring of `Q`, carried to `k(F_(i))`, contains the local ring of `F_(i) = 0` at `a`. -/
theorem mem_placesOver_iff_localSubring_le_map_chartEquiv_of_eq {i : Fin 3}
    (hP : P.1 ∈ affineOpen i) {a : Fin 2 → k} (ha : affineChart i P.1 = a)
    [(Ideal.span {dehomogenize i F}).IsPrime]
    {hI : Ideal.span {dehomogenize i F} ≤ vanishingIdeal k {a}} {Q : Place k (functionField hF)} :
    Q ∈ placesOver hF P ↔ (AffineSpace.localSubring a hI).toSubring ≤
      (Q.map (functionField.chartEquiv hF i
        (not_dvd_X_of_mem_affineOpen hF P hP))).integers.toSubring := by
  rw [mem_placesOver_iff_localSubring_le_map_chartEquiv hP,
    AffineSpace.localSubring_congr _ _ ha hI]

/-- **The order of a form in a chart**, as the order at the place carried to `k(F_(i))`. -/
theorem ordForm_eq_addValuation_map_chartEquiv {i : Fin 3} (hP : P.1 ∈ affineOpen i)
    {Q : Place k (functionField hF)} (hQ : Q ∈ placesOver hF P) {m : ℕ}
    {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m) :
    haveI := isPrime_span_dehomogenize hF (not_dvd_X_of_mem_affineOpen hF P hP)
    ordForm hF Q hG = (Q.map (functionField.chartEquiv hF i
        (not_dvd_X_of_mem_affineOpen hF P hP))).addValuation
      (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {dehomogenize i F}) (dehomogenize i G))) := by
  rw [mem_placesOver_iff] at hQ
  subst hQ
  rw [ordForm_eq_addValuation_chartEquiv_symm hP hG, Place.addValuation_map]

end PlaneCurves.Projective

end
