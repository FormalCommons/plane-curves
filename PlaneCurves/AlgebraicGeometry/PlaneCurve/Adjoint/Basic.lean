/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Divisor
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.OrdinaryMultiplePoint
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Finiteness
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.LinearSystem.Basic
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Basic

/-!
# Adjoint curves of a plane curve with ordinary multiple points

Let `k` be an algebraically closed field and `C : F = 0` an irreducible projective plane curve,
with function field `K = k(C)`. A form `G` is an **adjoint** of `C` if `m_P(G) ≥ m_P(C) - 1` at
every point `P`; only the multiple points of `C` impose a condition. The adjoints of degree `m`,
together with `0` and the multiples of `F`, form a vector space `V_m`, a subspace of the forms of
degree `m`; it is a linear system of plane curves with assigned multiple points.

On the nonsingular model of `C` the **adjoint divisor** is `E = ∑_Q (r_Q - 1) Q`, where `Q` runs
over the places of `K` and `r_Q = m_{c(Q)}(C)` is the multiplicity of `C` at the centre of `Q`.
It is effective and supported on the places over the multiple points. When every multiple point
of `C` is ordinary, exactly `r_P` places lie over a multiple point `P`, so
`deg E = ∑_P m_P(C) (m_P(C) - 1)`; and a form `G` with `F ∤ G` is an adjoint iff
`div G ≥ E`, by the orders of forms at the places over an ordinary multiple point
(`PlaneCurves.Projective.le_mult_iff_forall_le_ordForm`).

For a line `L` with `F ∤ L`, `G ↦ G / Lᵐ` is then a linear map from `V_m` to the Riemann–Roch
space `L(m div L - E)`, whose kernel consists of the multiples of `F`.

## Main definitions

* `PlaneCurves.Projective.IsAdjoint F G`: `G` is an adjoint of `F`.
* `PlaneCurves.Projective.adjointSubmodule F m`: the space `V_m` of adjoints of degree `m`.
* `PlaneCurves.Projective.adjointDivisor hF`: the adjoint divisor `E`.
* `PlaneCurves.Projective.adjointToRiemannRochSpace`: the linear map `V_m → L(m div L - E)`,
  `G ↦ G / Lᵐ`.

## Main results

* `isAdjoint_iff_forall_isMultiplePoint`: only the multiple points impose conditions.
* `isAdjoint_of_dvd`, `mul_mem_adjointSubmodule`: multiples of `F` are adjoints.
* `adjointSubmodule_eq_linearSystem`: `V_m` is a linear system with assigned multiple points.
* `adjointDivisor_nonneg`, `coeff_adjointDivisor_pos_iff`: `E` is effective and supported on the
  places over the multiple points.
* `degree_adjointDivisor`: `deg E = ∑_P m_P(C) (m_P(C) - 1)`.
* `isAdjoint_iff_le_formDivisor`: `G` is an adjoint iff `div G ≥ E`.
* `mem_ker_adjointToRiemannRochSpace_iff`: the kernel of `G ↦ G / Lᵐ` is the multiples of `F`.
* `adjointDivisor_spec`: the milestone.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §8.1 and Problem 7.19
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti
open TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] {F G H : MvPolynomial (Fin 3) k} {d m : ℕ}

/-! ### Adjoint forms -/

/-- A form `G` is an **adjoint** of the plane curve `F` if `m_P(G) ≥ m_P(F) - 1` at every point
`P` of `ℙ²`. Only the multiple points of `F` impose a condition
(`isAdjoint_iff_forall_isMultiplePoint`). For a curve with only ordinary multiple points and
`F ∤ G` this says `div G ≥ E` (`isAdjoint_iff_le_formDivisor`). -/
def IsAdjoint (F G : MvPolynomial (Fin 3) k) : Prop :=
  ∀ P : ℙ k (Fin 3 → k), mult F P - 1 ≤ mult G P

theorem isAdjoint_def : IsAdjoint F G ↔ ∀ P : ℙ k (Fin 3 → k), mult F P - 1 ≤ mult G P :=
  Iff.rfl

/-- At a point that is not a multiple point, `m_P(F) - 1 = 0`. -/
private theorem mult_sub_one_eq_zero {P : ℙ k (Fin 3 → k)} (h : ¬IsMultiplePoint F P) :
    mult F P - 1 = 0 := by
  rw [isMultiplePoint_def, not_le] at h
  exact tsub_eq_zero_of_le (Order.le_of_lt_succ h)

/-- Only the multiple points of `F` impose conditions on adjoints. -/
theorem isAdjoint_iff_forall_isMultiplePoint :
    IsAdjoint F G ↔ ∀ P, IsMultiplePoint F P → mult F P - 1 ≤ mult G P := by
  refine ⟨fun h P _ ↦ h P, fun h P ↦ ?_⟩
  by_cases hP : IsMultiplePoint F P
  · exact h P hP
  · rw [mult_sub_one_eq_zero hP]
    exact zero_le

@[simp]
theorem isAdjoint_zero : IsAdjoint F 0 :=
  fun P ↦ by simp

theorem IsAdjoint.add (hG : IsAdjoint F G) (hH : IsAdjoint F H) : IsAdjoint F (G + H) :=
  fun P ↦ by
    have h := min_orderAt_le_orderAt_add G H P.rep
    rw [← mult_def, ← mult_def, ← mult_def] at h
    exact (le_min (hG P) (hH P)).trans h

theorem IsAdjoint.smul (hG : IsAdjoint F G) (c : k) : IsAdjoint F (c • G) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · intro P
    rw [mult_smul hc]
    exact hG P

/-- A multiple of an adjoint is an adjoint. -/
theorem IsAdjoint.mul_left (hG : IsAdjoint F G) (H : MvPolynomial (Fin 3) k) :
    IsAdjoint F (H * G) :=
  fun P ↦ (hG P).trans (by rw [mult_mul]; exact le_add_self)

/-- The multiples of `F` are adjoints of `F`. -/
theorem isAdjoint_of_dvd (h : F ∣ G) : IsAdjoint F G := by
  obtain ⟨H, rfl⟩ := h
  exact fun P ↦ tsub_le_self.trans (by rw [mult_mul]; exact le_self_add)

/-- Every form is an adjoint of a curve without multiple points. -/
theorem isAdjoint_of_forall_not_isMultiplePoint (h : ∀ P, ¬IsMultiplePoint F P)
    (G : MvPolynomial (Fin 3) k) : IsAdjoint F G :=
  isAdjoint_iff_forall_isMultiplePoint.2 fun P hP ↦ (h P hP).elim

/-- Every form is an adjoint of a nonsingular curve. -/
theorem IsNonsingular.isAdjoint (hF : F.IsHomogeneous d) (hns : IsNonsingular F)
    (G : MvPolynomial (Fin 3) k) : IsAdjoint F G :=
  isAdjoint_of_forall_not_isMultiplePoint (hns.not_isMultiplePoint hF) G

/-! ### The space of adjoints of degree `m` -/

variable (F m) in
/-- The vector space `V_m` of **adjoints of degree `m`** of `F`: the forms `G` of degree `m`
with `m_P(G) ≥ m_P(F) - 1` at every point `P`, including `0` and the multiples of `F`. -/
noncomputable def adjointSubmodule : Submodule k (MvPolynomial (Fin 3) k) where
  carrier := {G | G.IsHomogeneous m ∧ IsAdjoint F G}
  add_mem' hG hH := ⟨hG.1.add hH.1, hG.2.add hH.2⟩
  zero_mem' := ⟨isHomogeneous_zero _ _ _, isAdjoint_zero⟩
  smul_mem' c _ hG := ⟨(mem_homogeneousSubmodule _ _).1
    (Submodule.smul_mem _ c ((mem_homogeneousSubmodule _ _).2 hG.1)), hG.2.smul c⟩

theorem mem_adjointSubmodule_iff :
    G ∈ adjointSubmodule F m ↔ G.IsHomogeneous m ∧ IsAdjoint F G :=
  Iff.rfl

theorem adjointSubmodule_le_homogeneousSubmodule :
    adjointSubmodule F m ≤ homogeneousSubmodule (Fin 3) k m :=
  fun _ hG ↦ (mem_homogeneousSubmodule _ _).2 hG.1

/-- The forms of degree `d + e` divisible by `F` are adjoints. -/
theorem mul_mem_adjointSubmodule (hF : F.IsHomogeneous d) {e : ℕ} (hH : H.IsHomogeneous e) :
    F * H ∈ adjointSubmodule F (d + e) :=
  ⟨hF.mul hH, isAdjoint_of_dvd (dvd_mul_right F H)⟩

/-- For a nonsingular curve, `V_m` is the space of all forms of degree `m`. -/
theorem IsNonsingular.adjointSubmodule_eq (hF : F.IsHomogeneous d) (hns : IsNonsingular F)
    (m : ℕ) : adjointSubmodule F m = homogeneousSubmodule (Fin 3) k m :=
  le_antisymm adjointSubmodule_le_homogeneousSubmodule fun G hG ↦
    ⟨(mem_homogeneousSubmodule _ _).1 hG, hns.isAdjoint hF G⟩

/-- `x - 1 = ↑(x.toNat - 1)` for a finite `x : ℕ∞`. -/
private theorem sub_one_eq_natCast {x : ℕ∞} (hx : x ≠ ⊤) : x - 1 = ((x.toNat - 1 : ℕ) : ℕ∞) := by
  lift x to ℕ using hx
  simp

variable (F) in
/-- The multiplicities `m_P(F) - 1` that the adjoints of `F` must have, for a nonzero form `F`
with finitely many multiple points. -/
noncomputable def adjointConditions (hF0 : F ≠ 0) (hfin : {P | IsMultiplePoint F P}.Finite) :
    ℙ k (Fin 3 → k) →₀ ℕ :=
  Finsupp.ofSupportFinite (fun P ↦ (mult F P).toNat - 1) (hfin.subset fun P hP ↦ by
    by_contra h
    have := mult_sub_one_eq_zero h
    rw [sub_one_eq_natCast (mult_ne_top hF0)] at this
    exact hP (by exact_mod_cast this))

theorem adjointConditions_apply (hF0 : F ≠ 0) (hfin : {P | IsMultiplePoint F P}.Finite)
    (P : ℙ k (Fin 3 → k)) : adjointConditions F hF0 hfin P = (mult F P).toNat - 1 :=
  (rfl)

/-- **`V_m` is a linear system**: the adjoints of degree `m` are the forms of degree `m` with
assigned multiplicities `m_P(F) - 1` at the multiple points `P` of `F`. -/
theorem adjointSubmodule_eq_linearSystem (hF0 : F ≠ 0) (hfin : {P | IsMultiplePoint F P}.Finite)
    (m : ℕ) : adjointSubmodule F m = linearSystem m (adjointConditions F hF0 hfin) := by
  ext G
  rw [mem_adjointSubmodule_iff, mem_linearSystem, isAdjoint_def]
  simp only [adjointConditions_apply, ← sub_one_eq_natCast (mult_ne_top hF0)]

private theorem isHomogeneous_pow_of_one {L : MvPolynomial (Fin 3) k}
    (hL : L.IsHomogeneous 1) (n : ℕ) : (L ^ n).IsHomogeneous n := by
  simpa using hL.pow n

/-! ### The adjoint divisor -/

section Divisor

variable [IsAlgClosed k] {hF : F.IsHomogeneous d} [Fact (Irreducible F)]

variable (hF) in
/-- The multiple points of `C`, as points of `C`, are finite in number. -/
private theorem finite_setOf_isMultiplePoint_center :
    {P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)) |
      IsMultiplePoint F P.1}.Finite :=
  (finite_setOf_isMultiplePoint_of_irreducible hF Fact.out).preimage Subtype.val_injective.injOn

omit [IsAlgClosed k] in
private theorem two_le_toNat_mult_iff {P : ℙ k (Fin 3 → k)} :
    2 ≤ (mult F P).toNat ↔ IsMultiplePoint F P := by
  rw [isMultiplePoint_def, ← natCast_toNat_mult (Fact.out : Irreducible F).ne_zero]
  exact_mod_cast Iff.rfl

variable (hF) in
/-- The **adjoint divisor** `E = ∑_Q (r_Q - 1) Q` on the nonsingular model of `C`, where
`r_Q = m_{c(Q)}(C)` is the multiplicity of `C` at the centre of the place `Q`
(`coeff_adjointDivisor`). -/
noncomputable def adjointDivisor : Divisor k (functionField hF) :=
  Finsupp.ofSupportFinite (fun Q ↦ (((mult F (center hF Q).1).toNat - 1 : ℕ) : ℤ)) (by
    refine ((finite_setOf_isMultiplePoint_center hF).biUnion
      fun P _ ↦ placesOver_finite hF P).subset fun Q hQ ↦ ?_
    refine Set.mem_biUnion (x := center hF Q) ?_ (mem_placesOver_center Q)
    rw [Set.mem_ofPred_eq, ← two_le_toNat_mult_iff]
    have : (mult F (center hF Q).1).toNat - 1 ≠ 0 := by exact_mod_cast Function.mem_support.1 hQ
    omega)

theorem adjointDivisor_def :
    adjointDivisor hF = Finsupp.ofSupportFinite
      (fun Q ↦ (((mult F (center hF Q).1).toNat - 1 : ℕ) : ℤ)) (by
        refine ((finite_setOf_isMultiplePoint_center hF).biUnion
          fun P _ ↦ placesOver_finite hF P).subset fun Q hQ ↦ ?_
        refine Set.mem_biUnion (x := center hF Q) ?_ (mem_placesOver_center Q)
        rw [Set.mem_ofPred_eq, ← two_le_toNat_mult_iff]
        have : (mult F (center hF Q).1).toNat - 1 ≠ 0 := by exact_mod_cast Function.mem_support.1 hQ
        omega) :=
  (rfl)

/-- The coefficient of `E` at `Q` is `r_Q - 1`, for `r_Q` the multiplicity of `C` at the centre
of `Q`. -/
theorem coeff_adjointDivisor (Q : Place k (functionField hF)) :
    (adjointDivisor hF).coeff Q = (((mult F (center hF Q).1).toNat - 1 : ℕ) : ℤ) := by
  rw [adjointDivisor_def]
  rfl

/-- The adjoint divisor is effective. -/
theorem adjointDivisor_nonneg : 0 ≤ adjointDivisor hF :=
  (WeilDivisor.nonneg_iff _).2 fun Q ↦ by
    rw [coeff_adjointDivisor]
    exact Int.natCast_nonneg _

/-- The adjoint divisor is supported on the places over the multiple points of `C`. -/
theorem coeff_adjointDivisor_pos_iff {Q : Place k (functionField hF)} :
    0 < (adjointDivisor hF).coeff Q ↔ IsMultiplePoint F (center hF Q).1 := by
  rw [coeff_adjointDivisor, ← two_le_toNat_mult_iff]
  omega

/-- A nonsingular curve has adjoint divisor `0`. -/
theorem adjointDivisor_eq_zero_of_isNonsingular (hns : IsNonsingular F) : adjointDivisor hF = 0 :=
  WeilDivisor.ext fun Q ↦ by
    have := (coeff_adjointDivisor_pos_iff (Q := Q)).not.2 (hns.not_isMultiplePoint hF _)
    have := WeilDivisor.coeff_nonneg (adjointDivisor_nonneg (hF := hF)) Q
    rw [WeilDivisor.coeff_zero]
    omega

variable (hord : ∀ P, IsMultiplePoint F P → IsOrdinaryMultiplePoint F P)
include hord

/-- **The degree of the adjoint divisor.** If every multiple point of `C` is ordinary, then
`deg E = ∑_P m_P(C) (m_P(C) - 1)`. -/
theorem degree_adjointDivisor :
    Divisor.degree (adjointDivisor hF) =
      ∑ᶠ P : ℙ k (Fin 3 → k), (((mult F P).toNat * ((mult F P).toNat - 1) : ℕ) : ℤ) := by
  classical
  set S := (finite_setOf_isMultiplePoint_center hF).toFinset
  have hsupp : (adjointDivisor hF).support ⊆
      S.biUnion fun P ↦ (placesOver_finite hF P).toFinset := by
    intro Q hQ
    refine Finset.mem_biUnion.2 ⟨center hF Q, ?_,
      (placesOver_finite hF _).mem_toFinset.2 (mem_placesOver_center Q)⟩
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ← coeff_adjointDivisor_pos_iff]
    have := WeilDivisor.mem_support_iff.1 hQ
    have := WeilDivisor.coeff_nonneg (adjointDivisor_nonneg (hF := hF)) Q
    omega
  have hdisj : (S : Set _).PairwiseDisjoint fun P ↦ (placesOver_finite hF P).toFinset := by
    intro P _ P' _ hPP'
    refine Finset.disjoint_left.2 fun Q hQ hQ' ↦ hPP' ?_
    simp only [Set.Finite.mem_toFinset, mem_placesOver_iff] at hQ hQ'
    exact hQ.symm.trans hQ'
  have hP : ∀ P ∈ S, ∑ Q ∈ (placesOver_finite hF P).toFinset, (adjointDivisor hF).coeff Q =
      (((mult F P.1).toNat * ((mult F P.1).toNat - 1) : ℕ) : ℤ) := by
    intro P hPS
    have hPm : IsMultiplePoint F P.1 := (Set.Finite.mem_toFinset _).1 hPS
    rw [Finset.sum_congr rfl fun Q hQ ↦ by
      rw [coeff_adjointDivisor, (mem_placesOver_iff.1 ((Set.Finite.mem_toFinset _).1 hQ))],
      Finset.sum_const, ← Set.ncard_eq_toFinset_card _ (placesOver_finite hF P),
      ncard_placesOver_of_isOrdinaryMultiplePoint (hord _ hPm), nsmul_eq_mul]
    push_cast
    ring
  have hfin : (Function.support fun P : ℙ k (Fin 3 → k) ↦
      (((mult F P).toNat * ((mult F P).toNat - 1) : ℕ) : ℤ)) ⊆
        ↑(S.map (Function.Embedding.subtype _)) := by
    intro P hP
    rw [Function.mem_support] at hP
    have hPm : IsMultiplePoint F P := by
      rw [← two_le_toNat_mult_iff]
      by_contra h
      exact hP (by
        have : (mult F P).toNat - 1 = 0 := by omega
        simp [this])
    have hPF : P ∈ zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)) :=
      (mem_zeroLocus_ideal_iff hF).2 hPm.eval_rep_eq_zero
    exact Finset.mem_map.2 ⟨⟨P, hPF⟩, (Set.Finite.mem_toFinset _).2 hPm, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ hfin, Finset.sum_map,
    Divisor.degree_apply_of_isAlgClosed (functionField.isFunctionField hF),
    Finset.sum_subset hsupp fun Q _ hQ ↦ Finsupp.notMem_support_iff.1 hQ,
    Finset.sum_biUnion hdisj]
  exact Finset.sum_congr rfl hP

/-- **Adjoints and the adjoint divisor** (Fulton, Problem 7.19). If every multiple point of `C`
is ordinary, a form `G` with `F ∤ G` is an adjoint of `C` iff `div G ≥ E`. -/
theorem isAdjoint_iff_le_formDivisor (hG : G.IsHomogeneous m) (hFG : ¬ F ∣ G) :
    IsAdjoint F G ↔ adjointDivisor hF ≤ formDivisor hF hG := by
  have hF0 : F ≠ 0 := (Fact.out : Irreducible F).ne_zero
  have hG0 : G ≠ 0 := fun h ↦ hFG (h ▸ dvd_zero F)
  have hs {P : ℙ k (Fin 3 → k)} : (((mult F P).toNat - 1 : ℕ) : ℕ∞) ≤ mult F P :=
    (sub_one_eq_natCast (mult_ne_top hF0)).symm.trans_le tsub_le_self
  rw [Finsupp.le_def]
  constructor
  · intro h Q
    change (adjointDivisor hF).coeff Q ≤ (formDivisor hF hG).coeff Q
    by_cases hQ : IsMultiplePoint F (center hF Q).1
    · rw [coeff_adjointDivisor, ← WithTop.coe_le_coe, coeff_formDivisor hG hFG]
      refine (le_mult_iff_forall_le_ordForm (hord _ hQ) hG hG0 hs).1 ?_ Q
        (mem_placesOver_center Q)
      rw [← sub_one_eq_natCast (mult_ne_top hF0)]
      exact h _
    · have := (coeff_adjointDivisor_pos_iff (Q := Q)).not.2 hQ
      have := WeilDivisor.coeff_nonneg (formDivisor_nonneg (hF := hF) hG) Q
      omega
  · intro h
    refine isAdjoint_iff_forall_isMultiplePoint.2 fun P hP ↦ ?_
    have hPF : P ∈ zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)) :=
      (mem_zeroLocus_ideal_iff hF).2 hP.eval_rep_eq_zero
    rw [sub_one_eq_natCast (mult_ne_top hF0)]
    refine (le_mult_iff_forall_le_ordForm (P := ⟨P, hPF⟩) (hord _ hP) hG hG0 hs).2
      fun Q hQ ↦ ?_
    have hQE := h Q
    change (adjointDivisor hF).coeff Q ≤ (formDivisor hF hG).coeff Q at hQE
    rw [coeff_adjointDivisor, mem_placesOver_iff.1 hQ] at hQE
    rw [← coeff_formDivisor hG hFG]
    exact_mod_cast hQE

/-! ### Adjoints and Riemann–Roch spaces -/

variable {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1) (hFL : ¬ F ∣ L)
  (hLm : (L ^ m).IsHomogeneous m)

/-- For an adjoint `G` of degree `m`, `G / Lᵐ` lies in `L(m div L - E)`. -/
private theorem mk_mem_riemannRochSpace {G : MvPolynomial (Fin 3) k}
    (hG : G ∈ adjointSubmodule F m) :
    functionField.mk (mem_adjointSubmodule_iff.1 hG).1 hLm
        (projectivePlaneCurve.notMem_ideal_of_not_dvd hF (not_dvd_pow_of_not_dvd hFL m)) ∈
      riemannRochSpace (m • formDivisor hF hL - adjointDivisor hF) := by
  have hG' := (mem_adjointSubmodule_iff.1 hG).1
  by_cases hFG : F ∣ G
  · rw [(functionField.mk_eq_zero_iff _ _ _).2 ((projectivePlaneCurve.mem_ideal_iff hF).2 hFG)]
    exact zero_mem _
  rw [← coe_formQuotient hG' hLm hFG (not_dvd_pow_of_not_dvd hFL m),
    mem_riemannRochSpace_iff_neg_le_ord (Units.ne_zero _)]
  intro Q
  have hE := Finsupp.le_def.1
    ((isAdjoint_iff_le_formDivisor hord hG' hFG).1 (mem_adjointSubmodule_iff.1 hG).2) Q
  change (adjointDivisor hF).coeff Q ≤ (formDivisor hF hG').coeff Q at hE
  rw [← Divisor.coeff_principal (functionField.isFunctionField hF), principal_formQuotient,
    WeilDivisor.coeff_sub, WeilDivisor.coeff_sub, WeilDivisor.coeff_nsmul,
    formDivisor_congr hLm (hL.pow m) rfl, formDivisor_pow hL hFL, WeilDivisor.coeff_nsmul]
  omega

variable (hF) in
/-- The linear map `V_m → L(m div L - E)`, `G ↦ G / Lᵐ`, for a line `L` with `F ∤ L`, when every
multiple point of `C` is ordinary. Its kernel consists of the multiples of `F`
(`mem_ker_adjointToRiemannRochSpace_iff`). -/
noncomputable def adjointToRiemannRochSpace :
    adjointSubmodule F m →ₗ[k] riemannRochSpace (m • formDivisor hF hL - adjointDivisor hF) where
  toFun G := ⟨_, mk_mem_riemannRochSpace hord hL hFL (isHomogeneous_pow_of_one hL m) G.2⟩
  map_add' _ _ := Subtype.ext (functionField.mk_add_mk_self _ _ _ _).symm
  map_smul' c _ := Subtype.ext (functionField.smul_mk c _ _ _ _).symm

/-- `adjointToRiemannRochSpace` sends `G` to `G / Lᵐ`. -/
theorem coe_adjointToRiemannRochSpace_apply (G : adjointSubmodule F m)
    (hLI : L ^ m ∉ projectivePlaneCurve.ideal hF) :
    (adjointToRiemannRochSpace hF hord hL hFL (m := m) G : functionField hF) =
      functionField.mk (mem_adjointSubmodule_iff.1 G.2).1 hLm hLI :=
  (rfl)

/-- The kernel of `G ↦ G / Lᵐ` on `V_m` consists of the multiples of `F`. -/
theorem mem_ker_adjointToRiemannRochSpace_iff {G : adjointSubmodule F m} :
    G ∈ LinearMap.ker (adjointToRiemannRochSpace hF hord hL hFL (m := m)) ↔
      F ∣ (G : MvPolynomial (Fin 3) k) := by
  rw [LinearMap.mem_ker, ← Subtype.coe_inj,
    coe_adjointToRiemannRochSpace_apply hord hL hFL (isHomogeneous_pow_of_one hL m) G
      (projectivePlaneCurve.notMem_ideal_of_not_dvd hF (not_dvd_pow_of_not_dvd hFL m)),
    ZeroMemClass.coe_zero, functionField.mk_eq_zero_iff, projectivePlaneCurve.mem_ideal_iff hF]

end Divisor

/-! ### The milestone -/

/-- **Adjoint curves of a plane curve with ordinary multiple points** (Fulton, §8.1 and
Problem 7.19). Let `k` be algebraically closed and `C : F = 0` an irreducible projective plane
curve of degree `d` all of whose multiple points are ordinary. For a place `Q` of `k(C)` let
`r_Q = m_{c(Q)}(C)` and `E = ∑_Q (r_Q - 1) Q`.

1. `E` is effective, supported on the places centred at multiple points, and
   `deg E = ∑_P m_P(C) (m_P(C) - 1)`.
2. A form `G` with `F ∤ G` satisfies `div G ≥ E` iff `m_P(G) ≥ m_P(C) - 1` at every multiple
   point `P` of `C`.
3. If `C` is nonsingular, then `E = 0` and every form is an adjoint.

Milestone: *Adjoint curves of a plane curve with ordinary multiple points*. -/
theorem adjointDivisor_spec [IsAlgClosed k] (hF : F.IsHomogeneous d) [Fact (Irreducible F)]
    (hord : ∀ P, IsMultiplePoint F P → IsOrdinaryMultiplePoint F P) :
    0 ≤ adjointDivisor hF ∧
    (∀ Q, 0 < (adjointDivisor hF).coeff Q ↔ IsMultiplePoint F (center hF Q).1) ∧
    Divisor.degree (adjointDivisor hF) =
      ∑ᶠ P : ℙ k (Fin 3 → k), (((mult F P).toNat * ((mult F P).toNat - 1) : ℕ) : ℤ) ∧
    (∀ {m : ℕ} {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m), ¬ F ∣ G →
      (adjointDivisor hF ≤ formDivisor hF hG ↔
        ∀ P, IsMultiplePoint F P → mult F P - 1 ≤ mult G P)) ∧
    (IsNonsingular F → adjointDivisor hF = 0 ∧ ∀ G, IsAdjoint F G) :=
  ⟨adjointDivisor_nonneg, fun _ ↦ coeff_adjointDivisor_pos_iff, degree_adjointDivisor hord,
    fun hG hFG ↦ (isAdjoint_iff_le_formDivisor hord hG hFG).symm.trans
      isAdjoint_iff_forall_isMultiplePoint,
    fun hns ↦ ⟨adjointDivisor_eq_zero_of_isNonsingular hns, hns.isAdjoint hF⟩⟩

end PlaneCurves.Projective

end
