/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.IntersectionNumber
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Bezout.Basic
public import TauCeti.FieldTheory.FunctionField.Divisor.ProductFormula

/-!
# Divisors cut out by forms on the nonsingular model of a plane curve

Let `k` be an algebraically closed field and `C : F = 0` an irreducible projective plane curve of
degree `n`, with function field `K = k(C)`. The points of the nonsingular model of `C` are the
places of `K`. A form `G` of degree `m` with `F ∤ G` **cuts out** the divisor
`div G = ∑_Q ord_Q(G) Q`, where `ord_Q(G)` is the order of `G` at the place `Q`
(`PlaneCurves.Projective.ordForm`). It is effective, its part over a point `P ∈ C` has degree
`I(P, C ∩ G)`, and so it has degree `mn` by Bézout's theorem. A quotient `G / H` of two forms of
the same degree not divisible by `F` is a unit of `K`, with divisor `div G - div H`; every unit of
`K` is such a quotient.

## Main definitions

* `PlaneCurves.Projective.formQuotient hF hG hH hFG hFH`: the unit `G / H` of `k(C)`.
* `PlaneCurves.Projective.formDivisor hF hG`: the divisor `div G` cut out by a form `G`
  (zero when `F ∣ G`).

## Main results

* `coeff_formDivisor`: the coefficient of `div G` at `Q` is `ord_Q(G)`.
* `formDivisor_nonneg`, `coeff_formDivisor_pos_iff`, `formDivisor_mul`,
  `not_dvd_pow_of_not_dvd`, `formDivisor_pow`.
* `principal_formQuotient`: `div (G / H) = div G - div H`; `exists_formQuotient_eq`.
* `sum_coeff_formDivisor_center`: `∑_{Q over P} ord_Q(G) = I(P, C ∩ G)`.
* `degree_formDivisor`: `deg (div G) = n * m`.
* `formDivisor_X_two`: `div Z = (x)_∞ ⊔ (y)_∞` for `x = X / Z`, `y = Y / Z`.
* `linearlyEquivalent_iff_exists_add_formDivisor_eq`: linear equivalence by forms.
* `formDivisor_spec`: the milestone, collecting the above.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §8.1
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti
open TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
  (hF : F.IsHomogeneous d) [Fact (Irreducible F)]

variable {m m' : ℕ} {G G' H : MvPolynomial (Fin 3) k}

/-! ### Quotients of forms -/

/-- The **quotient** `G / H` of two forms of the same degree not divisible by `F`, a unit of the
function field `k(C)`. -/
noncomputable def formQuotient (hG : G.IsHomogeneous m) (hH : H.IsHomogeneous m) (hFG : ¬ F ∣ G)
    (hFH : ¬ F ∣ H) : (functionField hF)ˣ :=
  Units.mk0 (functionField.mk hG hH (projectivePlaneCurve.notMem_ideal_of_not_dvd hF hFH))
    (functionField.mk_ne_zero hG hH _ (projectivePlaneCurve.notMem_ideal_of_not_dvd hF hFG))

variable {hF}

theorem formQuotient_def (hG : G.IsHomogeneous m) (hH : H.IsHomogeneous m) (hFG : ¬ F ∣ G)
    (hFH : ¬ F ∣ H) :
    formQuotient hF hG hH hFG hFH = Units.mk0 (functionField.mk hG hH
      (projectivePlaneCurve.notMem_ideal_of_not_dvd hF hFH))
      (functionField.mk_ne_zero hG hH _ (projectivePlaneCurve.notMem_ideal_of_not_dvd hF hFG)) :=
  (rfl)

@[simp]
theorem coe_formQuotient (hG : G.IsHomogeneous m) (hH : H.IsHomogeneous m) (hFG : ¬ F ∣ G)
    (hFH : ¬ F ∣ H) :
    (formQuotient hF hG hH hFG hFH : functionField hF) =
      functionField.mk hG hH (projectivePlaneCurve.notMem_ideal_of_not_dvd hF hFH) := by
  rw [formQuotient_def, Units.val_mk0]

/-- Every unit of `k(C)` is a quotient of two forms of the same degree not divisible by `F`. -/
theorem exists_formQuotient_eq (z : (functionField hF)ˣ) :
    ∃ (m : ℕ) (G H : MvPolynomial (Fin 3) k) (hG : G.IsHomogeneous m) (hH : H.IsHomogeneous m)
      (hFG : ¬ F ∣ G) (hFH : ¬ F ∣ H), formQuotient hF hG hH hFG hFH = z := by
  obtain ⟨m, G, H, hG, hH, hHI, hz⟩ := functionField.exists_eq_mk (z : functionField hF)
  have hFH : ¬ F ∣ H := (projectivePlaneCurve.mem_ideal_iff hF).not.1 hHI
  have hFG : ¬ F ∣ G := fun h ↦ z.ne_zero (by
    rw [hz, functionField.mk_eq_zero_iff]
    exact (projectivePlaneCurve.mem_ideal_iff hF).2 h)
  exact ⟨m, G, H, hG, hH, hFG, hFH, Units.ext (by rw [coe_formQuotient, hz])⟩

/-! ### The divisor of a form -/

variable (hF) in
/-- A form `G` with `F ∤ G` vanishes at only finitely many points of `C`. -/
theorem finite_setOf_eval_eq_zero (hG : G.IsHomogeneous m) (hFG : ¬ F ∣ G) :
    {P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)) |
      eval P.1.rep G = 0}.Finite := by
  have hrel : IsRelPrime F G := (Fact.out : Irreducible F).isRelPrime_iff_not_dvd.2 hFG
  refine ((finite_zeroLocus_pair_of_isRelPrime hF hG hrel).preimage
    Subtype.val_injective.injOn).subset fun P hP ↦ ?_
  rw [Set.mem_preimage, mem_zeroLocus_iff_eval_rep (by
    rintro f (rfl | rfl); exacts [⟨d, hF⟩, ⟨m, hG⟩])]
  rintro f (rfl | rfl)
  exacts [(mem_zeroLocus_ideal_iff hF).1 P.2.out, hP]

variable [IsAlgClosed k]

/-- The places at which a form `G` with `F ∤ G` has nonzero order are finite in number: they
lie over the finitely many points of `C` where `G` vanishes. -/
theorem finite_setOf_ordForm_ne_zero (hG : G.IsHomogeneous m) (hFG : ¬ F ∣ G) :
    {Q : Place k (functionField hF) | ordForm hF Q hG ≠ 0}.Finite := by
  refine ((finite_setOf_eval_eq_zero hF hG hFG).biUnion
    fun P _ ↦ placesOver_finite hF P).subset fun Q hQ ↦ ?_
  refine Set.mem_biUnion (x := center hF Q) ?_ (mem_placesOver_center Q)
  by_contra h
  exact hQ ((ordForm_eq_zero_iff hG).2 h)

variable (hF) in
/-- The **divisor cut out by a form** `G` of degree `m` on the nonsingular model of `C`:
`div G = ∑_Q ord_Q(G) Q`, the sum running over the places `Q` of `k(C)`
(`coeff_formDivisor`). It is the zero divisor when `F ∣ G`, where every order is `⊤`. -/
noncomputable def formDivisor (hG : G.IsHomogeneous m) : Divisor k (functionField hF) :=
  Finsupp.ofSupportFinite (fun Q ↦ (ordForm hF Q hG).untopD 0) (by
    by_cases hFG : F ∣ G
    · refine Set.finite_empty.subset fun Q hQ ↦ hQ ?_
      simp [(ordForm_eq_top_iff hG).2 hFG]
    · refine (finite_setOf_ordForm_ne_zero hG hFG).subset fun Q hQ h ↦ hQ ?_
      simp [show ordForm hF Q hG = 0 from h])

theorem formDivisor_def (hG : G.IsHomogeneous m) :
    formDivisor hF hG = Finsupp.ofSupportFinite (fun Q ↦ (ordForm hF Q hG).untopD 0) (by
      by_cases hFG : F ∣ G
      · refine Set.finite_empty.subset fun Q hQ ↦ hQ ?_
        simp [(ordForm_eq_top_iff hG).2 hFG]
      · refine (finite_setOf_ordForm_ne_zero hG hFG).subset fun Q hQ h ↦ hQ ?_
        simp [show ordForm hF Q hG = 0 from h]) :=
  (rfl)

theorem coeff_formDivisor_eq_untopD (hG : G.IsHomogeneous m) (Q : Place k (functionField hF)) :
    (formDivisor hF hG).coeff Q = (ordForm hF Q hG).untopD 0 := by
  rw [formDivisor_def]
  rfl

/-- The coefficient of `div G` at a place `Q` is the order `ord_Q(G)`, for `F ∤ G`. -/
theorem coeff_formDivisor (hG : G.IsHomogeneous m) (hFG : ¬ F ∣ G)
    (Q : Place k (functionField hF)) :
    ((formDivisor hF hG).coeff Q : WithTop ℤ) = ordForm hF Q hG := by
  rw [coeff_formDivisor_eq_untopD]
  have := (ordForm_eq_top_iff (Q := Q) hG).not.2 hFG
  lift ordForm hF Q hG to ℤ using this with a
  rfl

/-- A form divisible by `F` cuts out the zero divisor. -/
theorem formDivisor_eq_zero_of_dvd (hG : G.IsHomogeneous m) (hFG : F ∣ G) :
    formDivisor hF hG = 0 :=
  WeilDivisor.ext fun Q ↦ by
    rw [coeff_formDivisor_eq_untopD, (ordForm_eq_top_iff hG).2 hFG]
    rfl

/-- The divisor cut out by a form is effective. -/
theorem formDivisor_nonneg (hG : G.IsHomogeneous m) : 0 ≤ formDivisor hF hG := by
  rw [WeilDivisor.nonneg_iff]
  intro Q
  rw [coeff_formDivisor_eq_untopD]
  rcases eq_or_ne (ordForm hF Q hG) ⊤ with h | h
  · simp [h]
  · lift ordForm hF Q hG to ℤ using h with a ha
    have := ordForm_nonneg (Q := Q) hG
    rw [← ha] at this
    simpa using this

/-- A form `G` with `F ∤ G` has positive coefficient in `div G` at `Q` iff `G` vanishes at the
centre of `Q`. -/
theorem coeff_formDivisor_pos_iff (hG : G.IsHomogeneous m) (hFG : ¬ F ∣ G)
    {Q : Place k (functionField hF)} :
    0 < (formDivisor hF hG).coeff Q ↔ eval (center hF Q).1.rep G = 0 := by
  rw [← ordForm_pos_iff hG, ← coeff_formDivisor hG hFG, WithTop.coe_pos]

/-- `div (G G') = div G + div G'` for forms not divisible by `F`. -/
theorem formDivisor_mul (hG : G.IsHomogeneous m) (hG' : G'.IsHomogeneous m') (hFG : ¬ F ∣ G)
    (hFG' : ¬ F ∣ G') :
    formDivisor hF (hG.mul hG') = formDivisor hF hG + formDivisor hF hG' := by
  have hFGG' : ¬ F ∣ G * G' := fun h ↦
    ((Fact.out : Irreducible F).prime.dvd_or_dvd h).elim hFG hFG'
  refine WeilDivisor.ext fun Q ↦ ?_
  rw [WeilDivisor.coeff_add, ← WithTop.coe_inj, WithTop.coe_add, coeff_formDivisor _ hFGG',
    coeff_formDivisor _ hFG, coeff_formDivisor _ hFG', ordForm_mul]

/-- `div G` depends only on the form `G`, not on the proof of its homogeneity. -/
theorem formDivisor_congr {G' : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m)
    (hG' : G'.IsHomogeneous m') (h : G = G') : formDivisor hF hG = formDivisor hF hG' := by
  subst h
  rcases eq_or_ne G 0 with rfl | h0
  · rw [formDivisor_eq_zero_of_dvd _ (dvd_zero F), formDivisor_eq_zero_of_dvd _ (dvd_zero F)]
  · obtain rfl := hG.inj_right hG' h0
    rfl

/-- A nonzero constant cuts out the zero divisor. -/
@[simp]
theorem formDivisor_one : formDivisor hF (isHomogeneous_one (Fin 3) k) = 0 :=
  WeilDivisor.ext fun Q ↦ by
    rw [coeff_formDivisor_eq_untopD, ordForm_eq_zero_of_eval_ne_zero _ (by simp)]
    rfl

omit [IsAlgClosed k] in
/-- A power of a form not divisible by the irreducible form `F` is not divisible by `F`. -/
theorem not_dvd_pow_of_not_dvd (hFG : ¬ F ∣ G) (n : ℕ) : ¬ F ∣ G ^ n :=
  fun h ↦ hFG ((Fact.out : Irreducible F).prime.dvd_of_dvd_pow h)

/-- `div (Gⁿ) = n • div G` for a form not divisible by `F`. -/
theorem formDivisor_pow (hG : G.IsHomogeneous m) (hFG : ¬ F ∣ G) (n : ℕ) :
    formDivisor hF (hG.pow n) = n • formDivisor hF hG := by
  induction n with
  | zero => rw [formDivisor_congr _ (isHomogeneous_one (Fin 3) k) (pow_zero G), formDivisor_one,
      zero_smul]
  | succ n ih =>
    rw [formDivisor_congr _ ((hG.pow n).mul hG) (pow_succ G n),
      formDivisor_mul (hG.pow n) hG (not_dvd_pow_of_not_dvd hFG n) hFG, ih, succ_nsmul]

/-- **`div (G / H) = div G - div H`**: the principal divisor of a quotient of forms. -/
theorem principal_formQuotient (hG : G.IsHomogeneous m) (hH : H.IsHomogeneous m)
    (hFG : ¬ F ∣ G) (hFH : ¬ F ∣ H) :
    Divisor.principal (functionField.isFunctionField hF) (formQuotient hF hG hH hFG hFH) =
      formDivisor hF hG - formDivisor hF hH := by
  refine WeilDivisor.ext fun Q ↦ ?_
  have h := ordForm_eq_addValuation_mk_add Q hG hH hFH
  rw [← coeff_formDivisor hG hFG, ← coeff_formDivisor hH hFH, Q.addValuation_of_ne_zero
    (functionField.mk_ne_zero hG hH _ (projectivePlaneCurve.notMem_ideal_of_not_dvd hF hFG))] at h
  norm_cast at h
  rw [Divisor.coeff_principal, WeilDivisor.coeff_sub, coe_formQuotient, h]
  ring

/-! ### The divisor of a form over a point, and its degree -/

/-- **`∑_{Q over P} ord_Q(G) = I(P, C ∩ G)`**: the part of `div G` over a point `P ∈ C` has degree
the intersection number of `C` and `G` at `P`, read in `WithTop ℤ`. -/
theorem coe_sum_coeff_formDivisor_center (hG : G.IsHomogeneous m) (hFG : ¬ F ∣ G)
    (P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))) :
    ((∑ Q ∈ (placesOver_finite hF P).toFinset, (formDivisor hF hG).coeff Q : ℤ) : WithTop ℤ) =
      (intersectionNumber P.1 F G).map (Nat.cast : ℕ → ℤ) := by
  rw [map_natCast_intersectionNumber_eq_sum_ordForm hF P hG, WithTop.coe_sum]
  exact Finset.sum_congr rfl fun Q _ ↦ coeff_formDivisor hG hFG Q

/-- **`∑_{Q over P} ord_Q(G) = I(P, C ∩ G)`** for a form `G` with `F ∤ G` and a point `P ∈ C`;
the intersection number is finite (`intersectionNumber_ne_top_of_isRelPrime`). -/
theorem sum_coeff_formDivisor_center (hG : G.IsHomogeneous m) (hFG : ¬ F ∣ G)
    (P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))) :
    ∑ Q ∈ (placesOver_finite hF P).toFinset, (formDivisor hF hG).coeff Q =
      (intersectionNumber P.1 F G).toNat := by
  have h := coe_sum_coeff_formDivisor_center hG hFG P
  rw [← ENat.natCast_toNat (intersectionNumber_ne_top_of_isRelPrime hF hG
    ((Fact.out : Irreducible F).isRelPrime_iff_not_dvd.2 hFG)), ENat.map_natCast] at h
  exact_mod_cast h

/-- **The degree of `div G` is `deg F * deg G`**, by Bézout's theorem, for a form `G` with
`F ∤ G`. -/
theorem degree_formDivisor (hG : G.IsHomogeneous m) (hFG : ¬ F ∣ G) :
    Divisor.degree (formDivisor hF hG) = d * m := by
  classical
  set S := (finite_setOf_eval_eq_zero hF hG hFG).toFinset
  have hsupp : (formDivisor hF hG).support ⊆
      S.biUnion fun P ↦ (placesOver_finite hF P).toFinset := by
    intro Q hQ
    refine Finset.mem_biUnion.2 ⟨center hF Q, ?_,
      (placesOver_finite hF _).mem_toFinset.2 (mem_placesOver_center Q)⟩
    rw [Set.Finite.mem_toFinset]
    by_contra h
    refine WeilDivisor.mem_support_iff.1 hQ ?_
    have := coeff_formDivisor hG hFG Q
    rw [ordForm_eq_zero_of_eval_ne_zero hG h] at this
    exact_mod_cast this
  have hdisj : (S : Set _).PairwiseDisjoint fun P ↦ (placesOver_finite hF P).toFinset := by
    intro P _ P' _ hPP'
    refine Finset.disjoint_left.2 fun Q hQ hQ' ↦ hPP' ?_
    simp only [Set.Finite.mem_toFinset, mem_placesOver_iff] at hQ hQ'
    exact hQ.symm.trans hQ'
  have hrel : IsRelPrime F G := (Fact.out : Irreducible F).isRelPrime_iff_not_dvd.2 hFG
  have hB := sum_intersectionNumber_eq_mul hF hG hrel
    (s := S.map (Function.Embedding.subtype _)) fun P hPF hPG ↦ Finset.mem_map.2
      ⟨⟨P, (mem_zeroLocus_ideal_iff hF).2 hPF⟩, (Set.Finite.mem_toFinset _).2 hPG, rfl⟩
  rw [Finset.sum_map] at hB
  have hN : ∑ P ∈ S, intersectionNumber P.1 F G =
      ((∑ P ∈ S, (intersectionNumber P.1 F G).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun P _ ↦
      (ENat.natCast_toNat (intersectionNumber_ne_top_of_isRelPrime hF hG hrel)).symm
  have hN' : ∑ P ∈ S, (intersectionNumber P.1 F G).toNat = d * m := by
    exact_mod_cast hN.symm.trans hB
  rw [Divisor.degree_apply_of_isAlgClosed (functionField.isFunctionField hF),
    Finset.sum_subset hsupp fun Q _ hQ ↦ Finsupp.notMem_support_iff.1 hQ,
    Finset.sum_biUnion hdisj]
  refine (Finset.sum_congr rfl fun P _ ↦ sum_coeff_formDivisor_center hG hFG P).trans ?_
  rw [← Nat.cast_sum, hN']
  push_cast
  rfl

/-- **`div Z = (x)_∞ ⊔ (y)_∞`**: the line `Z = 0` cuts out the supremum of the pole divisors of
the affine coordinates `x = X / Z` and `y = Y / Z`, when no coordinate line is a component of
`C`. -/
theorem formDivisor_X_two (h0 : ¬ F ∣ X 0) (h1 : ¬ F ∣ X 1) (h2 : ¬ F ∣ X 2) :
    formDivisor hF (isHomogeneous_X k 2) =
      Divisor.poles (functionField.isFunctionField hF)
          (formQuotient hF (isHomogeneous_X k 0) (isHomogeneous_X k 2) h0 h2) ⊔
        Divisor.poles (functionField.isFunctionField hF)
          (formQuotient hF (isHomogeneous_X k 1) (isHomogeneous_X k 2) h1 h2) := by
  refine WeilDivisor.ext fun Q ↦ ?_
  have e : ∀ j (hj : ¬ F ∣ X j), Q.ord (formQuotient hF (isHomogeneous_X k j)
      (isHomogeneous_X k 2) hj h2 : functionField hF) =
        (formDivisor hF (isHomogeneous_X k j)).coeff Q -
          (formDivisor hF (isHomogeneous_X k 2)).coeff Q := fun j hj ↦ by
    rw [← Divisor.coeff_principal (functionField.isFunctionField hF), principal_formQuotient,
      WeilDivisor.coeff_sub]
  have hnn : ∀ j, 0 ≤ (formDivisor hF (isHomogeneous_X k j)).coeff Q := fun j ↦
    WeilDivisor.coeff_nonneg (formDivisor_nonneg _) Q
  have hzero : ∀ j, ¬ F ∣ X j → (center hF Q).1.rep j ≠ 0 →
      (formDivisor hF (isHomogeneous_X k j)).coeff Q = 0 := fun j hj hQ ↦ by
    have := (coeff_formDivisor_pos_iff (Q := Q) (isHomogeneous_X k j) hj).not.2 (by simpa)
    have := hnn j
    omega
  obtain ⟨j, hj⟩ := Function.ne_iff.1 (center hF Q).1.rep_ne_zero
  change _ = (_ ⊔ _ : Divisor k (functionField hF)) Q
  rw [Finsupp.sup_apply]
  change _ = WeilDivisor.coeff _ Q ⊔ WeilDivisor.coeff _ Q
  rw [Divisor.coeff_poles, Divisor.coeff_poles, e 0 h0, e 1 h1]
  have := hnn 0
  have := hnn 1
  have := hnn 2
  fin_cases j
  · have := hzero 0 h0 hj
    omega
  · have := hzero 1 h1 hj
    omega
  · have := hzero 2 h2 hj
    omega

/-! ### Linear equivalence -/

/-- **Linear equivalence by forms** (Fulton, §8.1, Proposition 2(5)): two divisors `D`, `D'` on
the nonsingular model of `C` are linearly equivalent iff `D + div G = D' + div G'` for some forms
`G`, `G'` of the same degree not divisible by `F`. -/
theorem linearlyEquivalent_iff_exists_add_formDivisor_eq {D D' : Divisor k (functionField hF)} :
    (Place.orderSystem (functionField.isFunctionField hF)).LinearlyEquivalent D D' ↔
      ∃ (m : ℕ) (G G' : MvPolynomial (Fin 3) k) (hG : G.IsHomogeneous m)
        (hG' : G'.IsHomogeneous m), ¬ F ∣ G ∧ ¬ F ∣ G' ∧
          D + formDivisor hF hG = D' + formDivisor hF hG' := by
  rw [Divisor.linearlyEquivalent_iff]
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨m, A, B, hA, hB, hFA, hFB, rfl⟩ := exists_formQuotient_eq z
    rw [principal_formQuotient, eq_comm, sub_eq_sub_iff_add_eq_add] at hz
    exact ⟨m, B, A, hB, hA, hFB, hFA, hz.trans (add_comm _ _)⟩
  · rintro ⟨m, G, G', hG, hG', hFG, hFG', h⟩
    refine ⟨formQuotient hF hG' hG hFG' hFG, ?_⟩
    rw [principal_formQuotient, sub_eq_sub_iff_add_eq_add]
    exact (add_comm _ _).trans h.symm

/-! ### The milestone -/

/-- **Divisors cut out by forms on the nonsingular model of a plane curve** (Fulton, §8.1). Let
`k` be algebraically closed and `C : F = 0` an irreducible projective plane curve of degree `d`,
with function field `K = k(C)`. The points of the nonsingular model of `C` are the places `Q` of
`K`, each with a unique centre on `C` (`existsUnique_isCenter`). For a form `G` of degree `m`,
`ord_Q(G)` is the order at `Q` of `G / Lᵐ`, `L` a linear form with `L(center Q) ≠ 0`.

1. `ord_Q(G) ≥ 0`; it is the order of `G / Lᵐ` for *every* such `L`; and `ord_Q(G) > 0` iff
   `G` vanishes at the centre of `Q`.
2. For `F ∤ G`, `div G = ∑_Q ord_Q(G) Q` is effective, `∑_{Q over P} ord_Q(G) = I(P, C ∩ G)` for
   every `P ∈ C`, and `deg (div G) = d m`.
3. `div (G G') = div G + div G'` for `F ∤ G`, `F ∤ G'`; for `G`, `H` of the same degree not
   divisible by `F`, `G / H` is a unit of `K` with `div (G / H) = div G - div H`; and every unit
   `z` of `K` has `deg (div z) = 0`.
4. Two divisors `D`, `D'` are linearly equivalent iff `D + div G = D' + div G'` for some forms
   `G`, `G'` of the same degree not divisible by `F`.

Milestone: *Divisors cut out by forms on the nonsingular model of a plane curve*. -/
theorem formDivisor_spec :
    (∀ (Q : Place k (functionField hF)) {m : ℕ} {G : MvPolynomial (Fin 3) k}
      (hG : G.IsHomogeneous m),
      0 ≤ ordForm hF Q hG ∧
      (∀ {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1)
        (hLQ : eval (center hF Q).1.rep L ≠ 0),
        ordForm hF Q hG = Q.addValuation (functionField.mk hG (one_mul m ▸ hL.pow m)
          (notMem_of_eval_rep_ne_zero (center hF Q).2 (one_mul m ▸ hL.pow m)
            (by simpa using pow_ne_zero m hLQ)))) ∧
      (0 < ordForm hF Q hG ↔ eval (center hF Q).1.rep G = 0)) ∧
    (∀ {m : ℕ} {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m), ¬ F ∣ G →
      0 ≤ formDivisor hF hG ∧
      (∀ P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)),
        ∑ Q ∈ (placesOver_finite hF P).toFinset, (formDivisor hF hG).coeff Q =
          (intersectionNumber P.1 F G).toNat) ∧
      Divisor.degree (formDivisor hF hG) = d * m) ∧
    (∀ {m m' : ℕ} {G G' : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m)
      (hG' : G'.IsHomogeneous m'), ¬ F ∣ G → ¬ F ∣ G' →
      formDivisor hF (hG.mul hG') = formDivisor hF hG + formDivisor hF hG') ∧
    (∀ {m : ℕ} {G H : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m)
      (hH : H.IsHomogeneous m) (hFG : ¬ F ∣ G) (hFH : ¬ F ∣ H),
      Divisor.principal (functionField.isFunctionField hF) (formQuotient hF hG hH hFG hFH) =
        formDivisor hF hG - formDivisor hF hH) ∧
    (∀ z : (functionField hF)ˣ,
      Divisor.degree (Divisor.principal (functionField.isFunctionField hF) z) = 0) ∧
    (∀ D D' : Divisor k (functionField hF),
      (Place.orderSystem (functionField.isFunctionField hF)).LinearlyEquivalent D D' ↔
        ∃ (m : ℕ) (G G' : MvPolynomial (Fin 3) k) (hG : G.IsHomogeneous m)
          (hG' : G'.IsHomogeneous m), ¬ F ∣ G ∧ ¬ F ∣ G' ∧
            D + formDivisor hF hG = D' + formDivisor hF hG') :=
  ⟨fun _ _ _ hG ↦ ⟨ordForm_nonneg hG, fun hL hLQ ↦ ordForm_eq_addValuation_mk_pow hG hL hLQ,
      ordForm_pos_iff hG⟩,
    fun hG hFG ↦ ⟨formDivisor_nonneg hG, sum_coeff_formDivisor_center hG hFG,
      degree_formDivisor hG hFG⟩,
    fun hG hG' hFG hFG' ↦ formDivisor_mul hG hG' hFG hFG',
    fun hG hH hFG hFH ↦ principal_formQuotient hG hH hFG hFH,
    fun z ↦ Divisor.degree_principal _ z,
    fun _ _ ↦ linearlyEquivalent_iff_exists_add_formDivisor_eq⟩

end PlaneCurves.Projective

end
