/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.CanonicalDivisor.Basic
public import PlaneCurves.FieldTheory.FunctionField.RiemannRoch

/-!
# The Riemann–Roch theorem for plane curves

Let `k` be an algebraically closed field and `K / k` a function field of one variable, of genus
`g`, with a canonical divisor `W`, the divisor of a nonzero Kähler differential. The
Riemann–Roch theorem `ℓ(D) = deg D + 1 - g + ℓ(W - D)` is Tau Ceti's, through the comparison of
Kähler and Weil differentials (`PlaneCurves.isRiemannRochDivisor_kaehlerDifferentialDivisor`).
This file collects it with its corollaries in the form of Fulton's §8.6, and adds its plane form.

Let `C : F = 0` be an irreducible plane curve of degree `d` all of whose multiple points are
ordinary, with adjoint divisor `E`. For a divisor `D` of `k(C)` and a degree `m`, let
`V_m(D)` be the space of forms `G` of degree `m` with `div G ≥ D + E` whenever `F ∤ G`
(`PlaneCurves.Projective.adjointSubmoduleOfDivisor`). For a line `L` with `F ∤ L`, `m < d` and
`D ≥ 0`, the map `G ↦ G / Lᵐ` is an isomorphism `V_m(D) ≅ L(m div L - E - D)`. Since
`(d - 3) div L - E` is canonical, `ℓ(W - D) = dim V_{d-3}(D)` for `D ≥ 0`: the plane form.

Counting with the exact sequence `0 → W_{m-d} → V_m → L(E_m) → 0`, Riemann–Roch in degree
`≥ 2g - 1` and the genus formula shows that the adjoint conditions are independent in degree
`m ≥ d - 3`: `dim V_m = (m + 1)(m + 2)/2 - ∑_P r_P (r_P - 1)/2`, where `r_P = m_P(C)`.

## Main definitions

* `PlaneCurves.Projective.adjointSubmoduleOfDivisor hF m D`: the space `V_m(D)`.

## Main results

* `PlaneCurves.Projective.dim_sub_eq_finrank_adjointSubmoduleOfDivisor`:
  `ℓ(m div L - E - D) = dim V_m(D)` for `m < d` and `D ≥ 0`.
* `PlaneCurves.Projective.dim_sub_eq_finrank_adjointSubmoduleOfDivisor_sub_three`: the plane form
  `ℓ(W - D) = dim V_{d-3}(D)` of the Riemann–Roch theorem.
* `PlaneCurves.isRiemannRochDivisor_kaehlerDifferentialDivisor_spec`: the Riemann–Roch theorem
  with its corollaries.
* `PlaneCurves.Projective.two_mul_finrank_adjointSubmodule_of_le`:
  `2 dim V_m = (m + 1)(m + 2) - ∑_P r_P (r_P - 1)` for `m ≥ d - 3`.
* `PlaneCurves.Projective.finrank_linearSystem_of_le`: the independence of the adjoint conditions
  in degree at least `d - 3`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §8.6 and Problem 8.32
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti TauCeti.AlgebraicGeometry
open Module
open scoped LinearAlgebra.Projectivization

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
  {hF : F.IsHomogeneous d} [Fact (Irreducible F)]

/-! ### Forms with an assigned divisor -/

section Line

variable {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1) (hFL : ¬ F ∣ L) {m : ℕ}
  (hLm : (L ^ m).IsHomogeneous m)

include hL hFL hLm in
/-- For a form `G` of degree `m` with `F ∤ G` and a line `L` with `F ∤ L`,
`G / Lᵐ ∈ L(m div L - E - D)` exactly when `div G ≥ D + E`. -/
theorem mk_mem_riemannRochSpace_iff {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m)
    (hFG : ¬ F ∣ G) (D : Divisor k (functionField hF)) :
    functionField.mk hG hLm
        (projectivePlaneCurve.notMem_ideal_of_not_dvd hF (not_dvd_pow_of_not_dvd hFL m)) ∈
      riemannRochSpace (m • formDivisor hF hL - adjointDivisor hF - D) ↔
      D + adjointDivisor hF ≤ formDivisor hF hG := by
  rw [← coe_formQuotient hG hLm hFG (not_dvd_pow_of_not_dvd hFL m),
    mem_riemannRochSpace_units_iff (functionField.isFunctionField hF), principal_formQuotient,
    formDivisor_congr hLm (hL.pow m) rfl, formDivisor_pow hL hFL,
    show ∀ A B C : Divisor k (functionField hF), A - B + (B - C - D) = A - (D + C) by
      intros; abel, sub_nonneg]

include hL hFL hLm in
/-- A form `G` of degree `m` satisfies `div G ≥ D + E` whenever `F ∤ G` exactly when
`G / Lᵐ ∈ L(m div L - E - D)`. -/
private theorem forall_le_formDivisor_iff_mk_mem {G : MvPolynomial (Fin 3) k}
    (hG : G.IsHomogeneous m) (D : Divisor k (functionField hF)) :
    (∀ _ : ¬ F ∣ G, D + adjointDivisor hF ≤ formDivisor hF hG) ↔
      functionField.mk hG hLm
          (projectivePlaneCurve.notMem_ideal_of_not_dvd hF (not_dvd_pow_of_not_dvd hFL m)) ∈
        riemannRochSpace (m • formDivisor hF hL - adjointDivisor hF - D) := by
  by_cases hFG : F ∣ G
  · rw [(functionField.mk_eq_zero_iff _ _ _).2 ((projectivePlaneCurve.mem_ideal_iff hF).2 hFG)]
    exact iff_of_true (fun h ↦ absurd hFG h) (zero_mem _)
  · rw [mk_mem_riemannRochSpace_iff hL hFL hLm hG hFG]
    exact ⟨fun h ↦ h hFG, fun h _ ↦ h⟩

end Line

omit [IsAlgClosed k] [Fact (Irreducible F)] in
/-- `Lᵐ` is a form of degree `m` for a line `L`. -/
private theorem isHomogeneous_pow_of_one {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1)
    (m : ℕ) : (L ^ m).IsHomogeneous m := by
  simpa using hL.pow m

variable (hF) in
/-- The space `V_m(D)` of the **forms of degree `m` with `div G ≥ D + E`**: the forms `G` of
degree `m` such that `div G ≥ D + E` whenever `F ∤ G`, where `E` is the adjoint divisor. For
`D ≥ 0` and `m < d` these are the adjoints of degree `m` whose divisor is at least `D + E`
(with `0`); for `D = 0` and only ordinary multiple points, they are the adjoints of degree `m`
(`adjointSubmoduleOfDivisor_zero`). -/
noncomputable def adjointSubmoduleOfDivisor (m : ℕ) (D : Divisor k (functionField hF)) :
    Submodule k (MvPolynomial (Fin 3) k) where
  carrier := {G | ∃ hG : G.IsHomogeneous m, ∀ _ : ¬ F ∣ G,
    D + adjointDivisor hF ≤ formDivisor hF hG}
  zero_mem' := ⟨isHomogeneous_zero _ _ m, fun h ↦ absurd (dvd_zero F) h⟩
  add_mem' {G H} := by
    rintro ⟨hG, hG'⟩ ⟨hH, hH'⟩
    obtain ⟨i, hi⟩ := projectivePlaneCurve.exists_not_dvd_X (Fact.out : Irreducible F)
    have hL := isHomogeneous_X k i
    have hLm := isHomogeneous_pow_of_one hL m
    refine ⟨hG.add hH, ?_⟩
    rw [forall_le_formDivisor_iff_mk_mem hL hi hLm] at hG' hH' ⊢
    rw [← functionField.mk_add_mk_self hG hH]
    exact add_mem hG' hH'
  smul_mem' c {G} := by
    rintro ⟨hG, hG'⟩
    obtain ⟨i, hi⟩ := projectivePlaneCurve.exists_not_dvd_X (Fact.out : Irreducible F)
    have hL := isHomogeneous_X k i
    have hLm := isHomogeneous_pow_of_one hL m
    have hcG : (c • G).IsHomogeneous m := by
      simpa [smul_eq_C_mul] using (isHomogeneous_C (Fin 3) c).mul hG
    refine ⟨hcG, ?_⟩
    rw [forall_le_formDivisor_iff_mk_mem hL hi hLm] at hG' ⊢
    rw [← functionField.smul_mk c hG hcG]
    exact Submodule.smul_mem _ c hG'

theorem mem_adjointSubmoduleOfDivisor_iff {m : ℕ} {D : Divisor k (functionField hF)}
    {G : MvPolynomial (Fin 3) k} :
    G ∈ adjointSubmoduleOfDivisor hF m D ↔
      ∃ hG : G.IsHomogeneous m, ∀ _ : ¬ F ∣ G, D + adjointDivisor hF ≤ formDivisor hF hG :=
  Iff.rfl

theorem adjointSubmoduleOfDivisor_le_homogeneousSubmodule (m : ℕ)
    (D : Divisor k (functionField hF)) :
    adjointSubmoduleOfDivisor hF m D ≤ homogeneousSubmodule (Fin 3) k m := fun _ ⟨hG, _⟩ ↦
  (mem_homogeneousSubmodule _ _).2 hG

/-- `V_m(D)` decreases as `D` grows. -/
theorem adjointSubmoduleOfDivisor_anti (m : ℕ) {D D' : Divisor k (functionField hF)}
    (h : D ≤ D') : adjointSubmoduleOfDivisor hF m D' ≤ adjointSubmoduleOfDivisor hF m D :=
  fun _ ⟨hG, hG'⟩ ↦ ⟨hG, fun hFG ↦ (add_le_add_left h _).trans (hG' hFG)⟩

section Map

variable {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1) (hFL : ¬ F ∣ L)

variable (hF) in
/-- The linear map `V_m(D) → L(m div L - E - D)`, `G ↦ G / Lᵐ`, for a line `L` with `F ∤ L`. -/
noncomputable def adjointSubmoduleOfDivisorToRiemannRochSpace (m : ℕ)
    (D : Divisor k (functionField hF)) :
    adjointSubmoduleOfDivisor hF m D →ₗ[k]
      riemannRochSpace (m • formDivisor hF hL - adjointDivisor hF - D) where
  toFun G := ⟨_, (forall_le_formDivisor_iff_mk_mem hL hFL (isHomogeneous_pow_of_one hL m)
    (mem_adjointSubmoduleOfDivisor_iff.1 G.2).1 D).1
    (mem_adjointSubmoduleOfDivisor_iff.1 G.2).2⟩
  map_add' _ _ := Subtype.ext (functionField.mk_add_mk_self _ _ _ _).symm
  map_smul' c _ := Subtype.ext (functionField.smul_mk c _ _ _ _).symm

/-- `adjointSubmoduleOfDivisorToRiemannRochSpace` sends `G` to `G / Lᵐ`. -/
theorem coe_adjointSubmoduleOfDivisorToRiemannRochSpace_apply {m : ℕ}
    {D : Divisor k (functionField hF)} (G : adjointSubmoduleOfDivisor hF m D)
    (hG : (G : MvPolynomial (Fin 3) k).IsHomogeneous m) (hLm : (L ^ m).IsHomogeneous m)
    (hLI : L ^ m ∉ projectivePlaneCurve.ideal hF) :
    (adjointSubmoduleOfDivisorToRiemannRochSpace hF hL hFL m D G : functionField hF) =
      functionField.mk hG hLm hLI :=
  (rfl)

end Map

section Ordinary

variable (hord : ∀ P, IsMultiplePoint F P → IsOrdinaryMultiplePoint F P)
include hord

/-- `V_m(0)` is the space `V_m` of adjoints of degree `m`. -/
theorem adjointSubmoduleOfDivisor_zero (m : ℕ) :
    adjointSubmoduleOfDivisor hF m 0 = adjointSubmodule F m := by
  ext G
  rw [mem_adjointSubmoduleOfDivisor_iff, mem_adjointSubmodule_iff, zero_add]
  refine ⟨fun ⟨hG, h⟩ ↦ ⟨hG, ?_⟩, fun ⟨hG, h⟩ ↦ ⟨hG, fun hFG ↦ ?_⟩⟩
  · by_cases hFG : F ∣ G
    · exact isAdjoint_of_dvd hFG
    · exact (isAdjoint_iff_le_formDivisor hord hG hFG).2 (h hFG)
  · exact (isAdjoint_iff_le_formDivisor hord hG hFG).1 h

/-- For `D ≥ 0`, the forms of `V_m(D)` are adjoints. -/
theorem adjointSubmoduleOfDivisor_le_adjointSubmodule (m : ℕ) {D : Divisor k (functionField hF)}
    (hD : 0 ≤ D) : adjointSubmoduleOfDivisor hF m D ≤ adjointSubmodule F m :=
  (adjointSubmoduleOfDivisor_zero hord m).symm ▸ adjointSubmoduleOfDivisor_anti m hD

variable {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1) (hFL : ¬ F ∣ L)

/-- **`V_m(D) ≅ L(m div L - E - D)`**: for a line `L` with `F ∤ L`, `m < d` and `D ≥ 0`, the map
`G ↦ G / Lᵐ` is bijective. -/
theorem bijective_adjointSubmoduleOfDivisorToRiemannRochSpace {m : ℕ} (hm : m < d)
    {D : Divisor k (functionField hF)} (hD : 0 ≤ D) :
    Function.Bijective (adjointSubmoduleOfDivisorToRiemannRochSpace hF hL hFL m D) := by
  have hLm := isHomogeneous_pow_of_one hL m
  have hLI := projectivePlaneCurve.notMem_ideal_of_not_dvd hF (not_dvd_pow_of_not_dvd hFL m)
  refine ⟨(injective_iff_map_eq_zero _).2 fun G hG0 ↦ ?_, fun f ↦ ?_⟩
  · have h := congrArg Subtype.val hG0
    rw [coe_adjointSubmoduleOfDivisorToRiemannRochSpace_apply hL hFL G
        (mem_adjointSubmoduleOfDivisor_iff.1 G.2).1 hLm hLI,
      ZeroMemClass.coe_zero, functionField.mk_eq_zero_iff, projectivePlaneCurve.mem_ideal_iff hF]
      at h
    by_contra hne
    have hne' : (G : MvPolynomial (Fin 3) k) ≠ 0 := fun h' ↦ hne (Subtype.ext h')
    exact (Fact.out : Irreducible F).not_isUnit
      ((hF.isRelPrime_of_irreducible Fact.out (mem_adjointSubmoduleOfDivisor_iff.1 G.2).1 hne'
        hm) dvd_rfl h)
  · have hle : m • formDivisor hF hL - adjointDivisor hF - D ≤
        m • formDivisor hF hL - adjointDivisor hF := sub_le_self _ hD
    obtain ⟨G, hG⟩ := adjointToRiemannRochSpace_surjective hord hL hFL
      ⟨f, riemannRochSpace_mono hle f.2⟩
    have hGf := congrArg Subtype.val hG
    rw [coe_adjointToRiemannRochSpace_apply hord hL hFL hLm G hLI] at hGf
    have hGD : (G : MvPolynomial (Fin 3) k) ∈ adjointSubmoduleOfDivisor hF m D :=
      ⟨_, (forall_le_formDivisor_iff_mk_mem hL hFL hLm _ D).2 (hGf ▸ f.2)⟩
    exact ⟨⟨G, hGD⟩, Subtype.ext hGf⟩

include hFL in
/-- **`ℓ(m div L - E - D) = dim V_m(D)`** for a line `L` with `F ∤ L`, `m < d` and `D ≥ 0`. -/
theorem dim_sub_eq_finrank_adjointSubmoduleOfDivisor {m : ℕ} (hm : m < d)
    {D : Divisor k (functionField hF)} (hD : 0 ≤ D) :
    Divisor.dim (m • formDivisor hF hL - adjointDivisor hF - D) =
      finrank k (adjointSubmoduleOfDivisor hF m D) := by
  rw [Divisor.dim_def]
  exact (LinearEquiv.ofBijective _
    (bijective_adjointSubmoduleOfDivisorToRiemannRochSpace hord hL hFL hm hD)).finrank_eq.symm

/-- **The plane form of the Riemann–Roch theorem**: for `3 ≤ d`, a canonical divisor `W` of
`k(C)` and `D ≥ 0`, `ℓ(W - D)` is the dimension of the space of adjoints `G` of degree `d - 3`
with `div G ≥ D + E` (with `0`). -/
theorem dim_sub_eq_finrank_adjointSubmoduleOfDivisor_sub_three (hd : 3 ≤ d)
    {W : Divisor k (functionField hF)}
    (hW : (Place.orderSystem (functionField.isFunctionField hF)).divisorClass W =
      canonicalClass (functionField.isFunctionField hF) isIntegrallyClosedIn_of_isAlgClosed)
    {D : Divisor k (functionField hF)} (hD : 0 ≤ D) :
    Divisor.dim (W - D) = finrank k (adjointSubmoduleOfDivisor hF (d - 3) D) := by
  have hK := functionField.isFunctionField hF
  obtain ⟨i, hi⟩ := projectivePlaneCurve.exists_not_dvd_X (Fact.out : Irreducible F)
  have hL : (X i : MvPolynomial (Fin 3) k).IsHomogeneous 1 := isHomogeneous_X k i
  have hE := divisorClass_sub_three_zsmul_formDivisor_sub_adjointDivisor_eq_canonicalClass
    (hF := hF) hord hL hi
  rw [show ((d : ℤ) - 3) • formDivisor hF hL = (d - 3) • formDivisor hF hL by
    rw [← natCast_zsmul, Nat.cast_sub hd, Nat.cast_ofNat]] at hE
  have h1 := Divisor.isRiemannRochDivisor_iff.1
    (isRiemannRochDivisor_of_divisorClass_eq_canonicalClass hK _ hW) D
  have h2 := Divisor.isRiemannRochDivisor_iff.1
    (isRiemannRochDivisor_of_divisorClass_eq_canonicalClass hK _ hE) D
  rw [← dim_sub_eq_finrank_adjointSubmoduleOfDivisor hord hL hi (by omega) hD]
  omega

/-! ### Independence of the adjoint conditions -/

variable (hF) in
include hF in
/-- **The adjoint conditions are independent in degree `m ≥ d - 3`**: if `d ≤ m + 3`, then
`2 dim V_m = (m + 1)(m + 2) - ∑_P r_P (r_P - 1)`, where `r_P = m_P(C)`. -/
theorem two_mul_finrank_adjointSubmodule_of_le {m : ℕ} (hm : d ≤ m + 3) :
    2 * (finrank k (adjointSubmodule F m) : ℤ) = ((m : ℤ) + 1) * ((m : ℤ) + 2) -
      ∑ᶠ P : ℙ k (Fin 3 → k), (((mult F P).toNat * ((mult F P).toNat - 1) : ℕ) : ℤ) := by
  have hK := functionField.isFunctionField hF
  have hg := two_mul_genus_eq hF hord
  have hE := degree_adjointDivisor (hF := hF) hord
  generalize ∑ᶠ P : ℙ k (Fin 3 → k), (((mult F P).toNat * ((mult F P).toNat - 1) : ℕ) : ℤ) = S
    at hg hE ⊢
  obtain ⟨i, hi⟩ := projectivePlaneCurve.exists_not_dvd_X (Fact.out : Irreducible F)
  have hL : (X i : MvPolynomial (Fin 3) k).IsHomogeneous 1 := isHomogeneous_X k i
  have hd0 : d ≠ 0 := hF.degree_ne_zero_of_irreducible Fact.out
  have hdeg (n : ℕ) : Divisor.degree (n • formDivisor hF hL - adjointDivisor hF) = n * d - S := by
    rw [map_sub, map_nsmul, degree_formDivisor hL hi, nsmul_eq_mul, hE]
    ring
  have hRR (n : ℕ) (hn : (d : ℤ) ≤ n + 2) :
      (Divisor.dim (n • formDivisor hF hL - adjointDivisor hF) : ℤ) =
        n * d - S + 1 - genus k (functionField hF) := by
    rw [Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree hK
      isIntegrallyClosedIn_of_isAlgClosed (by
      rw [hdeg]
      have h1 : (1 : ℤ) ≤ d := by omega
      nlinarith [mul_le_mul_of_nonneg_right (show (d : ℤ) - 2 ≤ n by omega)
        (Int.natCast_nonneg d)]),
      hdeg]
  rcases lt_or_ge m d with hmd | hmd
  · have hl : (finrank k (adjointSubmodule F m) : ℤ) =
        Divisor.dim (m • formDivisor hF hL - adjointDivisor hF) := by
      rw [dim_eq_finrank_adjointSubmodule (hF := hF) hord hL hi hmd]
    rcases (show m + 3 = d ∨ m + 2 = d ∨ m + 1 = d by omega) with h | h | h
    · have hf := finrank_adjointSubmodule_sub_three (hF := hF) hord (by omega)
      rw [show d - 3 = m by omega] at hf
      subst h
      push_cast at hg ⊢
      rw [hf]
      linear_combination hg
    · have h' := hRR m (by omega)
      subst h
      push_cast at hg h' ⊢
      linear_combination 2 * hl + 2 * h' - hg
    · have h' := hRR m (by omega)
      subst h
      push_cast at hg h' ⊢
      linear_combination 2 * hl + 2 * h' - hg
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hmd
    have h1 := dim_add_finrank_eq_finrank_adjointSubmodule (hF := hF) hord hL hi e
    rw [finrank_homogeneousSubmodule_fin_three] at h1
    have hW := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (e + 1))
    generalize (e + 1) * (e + 1 + 1) / 2 = A at h1 hW
    have h1' : (Divisor.dim ((d + e) • formDivisor hF hL - adjointDivisor hF) : ℤ) + A =
        finrank k (adjointSubmodule F (d + e)) := by exact_mod_cast h1
    have hW' : (2 : ℤ) * A = (e + 1) * (e + 2) := by exact_mod_cast hW
    have h' := hRR (d + e) (by omega)
    push_cast at h' ⊢
    linear_combination -2 * h1' + 2 * h' - hg + hW'

end Ordinary

omit [IsAlgClosed k] [Fact (Irreducible F)] in
/-- `2 ∑_P (r_P + 1) r_P / 2 = ∑_P (r_P + 1) r_P`. -/
private theorem two_mul_sum_succ_mul_div_two (r : ℙ k (Fin 3 → k) →₀ ℕ) :
    2 * r.sum (fun _ n ↦ (n + 1) * n / 2) = r.sum (fun _ n ↦ (n + 1) * n) := by
  rw [Finsupp.mul_sum]
  refine Finset.sum_congr rfl fun P _ ↦ Nat.two_mul_div_two_of_even ?_
  rw [mul_comm]
  exact Nat.even_mul_succ_self _

/-- **Independence of the adjoint conditions in degree at least `d - 3`** (Fulton,
Problem 8.32). Let `k` be algebraically closed, `r` an assignment of multiplicities `r_P ≥ 0` to
finitely many points `P` of `ℙ²`, and `C : F = 0` an irreducible plane curve of degree `d` with
only ordinary multiple points, all among the points with `r_P > 0`, and `m_P(C) = r_P + 1` at
the multiple points and at every point with `r_P > 0`. Then for every `m ≥ d - 3` the forms of
degree `m` with `m_P ≥ r_P` for all `P` form a space of dimension exactly
`(m + 1)(m + 2)/2 - ∑_P (r_P + 1) r_P / 2`: the conditions are independent.

The book lists the points as `P_1, …, P_s` with `r_i ≥ 0` and `m_{P_i}(C) = r_i + 1`; the points
with `r_i = 0` impose no condition, and are dropped here. In projective terms the linear system
has dimension `m (m + 3)/2 - ∑_P (r_P + 1) r_P / 2`. Compare
`PlaneCurves.Projective.finrank_linearSystem_eq`, which needs `∑_P r_P ≤ m + 1`.

Milestone: *Independence of adjoint conditions in degree at least n − 3*. -/
theorem finrank_linearSystem_of_le (hF : F.IsHomogeneous d)
    (hord : ∀ P, IsMultiplePoint F P → IsOrdinaryMultiplePoint F P)
    {r : ℙ k (Fin 3 → k) →₀ ℕ} (hr : ∀ P, IsMultiplePoint F P ∨ r P ≠ 0 → mult F P = r P + 1)
    {m : ℕ} (hm : d ≤ m + 3) :
    finrank k (linearSystem m r) = (m + 1) * (m + 2) / 2 - r.sum (fun _ n ↦ (n + 1) * n / 2) := by
  have hirr : Irreducible F := Fact.out
  have hfin := finite_setOf_isMultiplePoint_of_irreducible hF hirr
  -- `r_P = m_P(C) - 1` at every point
  have hrP (P : ℙ k (Fin 3 → k)) : r P = (mult F P).toNat - 1 := by
    by_cases h : IsMultiplePoint F P ∨ r P ≠ 0
    · rw [hr P h, ← Nat.cast_one, ← Nat.cast_add, ENat.toNat_natCast, Nat.add_sub_cancel]
    simp only [not_or, not_not] at h
    rw [h.2]
    have h2 : ¬ (2 ≤ mult F P) := fun h' ↦ h.1 (isMultiplePoint_def.2 h')
    rw [← natCast_toNat_mult hirr.ne_zero] at h2
    have : (mult F P).toNat < 2 := by exact_mod_cast not_le.1 h2
    omega
  have hreq : r = adjointConditions F hirr.ne_zero hfin :=
    Finsupp.ext fun P ↦ by rw [adjointConditions_apply, hrP]
  have h2 := two_mul_finrank_adjointSubmodule_of_le hF hord hm
  rw [adjointSubmodule_eq_linearSystem hirr.ne_zero hfin, ← hreq] at h2
  -- the sum over the multiple points is the sum over the support of `r`
  have hS : ∑ᶠ P : ℙ k (Fin 3 → k), (((mult F P).toNat * ((mult F P).toNat - 1) : ℕ) : ℤ) =
      ((r.sum fun _ n ↦ (n + 1) * n : ℕ) : ℤ) := by
    rw [finsum_eq_sum_of_support_subset _ (s := r.support) fun P hP ↦ ?_, Finsupp.sum,
      Nat.cast_sum]
    · refine Finset.sum_congr rfl fun P _ ↦ ?_
      rw [hrP P]
      rcases Nat.eq_zero_or_pos (mult F P).toNat with h0 | h0
      · simp [h0]
      · rw [Nat.sub_add_cancel h0]
    · rw [Function.mem_support] at hP
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hrP P]
      intro h0
      exact hP (by simp [h0])
  rw [hS, ← two_mul_sum_succ_mul_div_two] at h2
  have hA := Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self (m + 1))
  generalize (m + 1) * (m + 1 + 1) / 2 = A at hA ⊢
  have hA' : (2 : ℤ) * A = (m + 1) * (m + 2) := by exact_mod_cast hA
  generalize r.sum (fun _ n ↦ (n + 1) * n / 2) = B at h2
  push_cast at h2
  omega

end PlaneCurves.Projective

/-! ### The Riemann–Roch theorem -/

namespace PlaneCurves

open Projective

variable {k K : Type*} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]

/-- **The Riemann–Roch theorem for the nonsingular model of a curve** (Fulton, §8.6). Let `k` be
algebraically closed, `K / k` a function field of one variable of genus `g`, and `W` a canonical
divisor, the divisor of a nonzero Kähler differential. Then

1. `ℓ(D) = deg D + 1 - g + ℓ(W - D)` for every divisor `D`;
2. `ℓ(W) = g` and `deg W = 2g - 2`;
3. `ℓ(D) = deg D + 1 - g` if `deg D ≥ 2g - 1`;
4. `ℓ(D - P) = ℓ(D) - 1` for every place `P` if `deg D ≥ 2g`;
5. (Clifford) `2 ℓ(D) ≤ deg D + 2` if `ℓ(D) > 0` and `ℓ(W - D) > 0`;
6. `dim_k Ω(D) = ℓ(W - D)`, and the holomorphic differentials form a space of dimension `g`;
7. a divisor `D` with `deg D = 2g - 2` and `ℓ(D) = g` is canonical;
8. if `D + D' = W`, then `2 (ℓ(D) - ℓ(D')) = deg D - deg D'`;
9. (plane form) if `C : F = 0` is an irreducible plane curve of degree `d ≥ 3` with only ordinary
   multiple points, `W` a canonical divisor of `k(C)` and `D ≥ 0`, then `ℓ(W - D)` is the
   dimension of the space of adjoints `G` of degree `d - 3` with `div G ≥ D + E` (with `0`).

Over an algebraically closed field every place has degree one
(`TauCeti.Place.degree_eq_one_of_isAlgClosed_of_isFunctionField`), and a divisor is canonical
exactly when its class is `TauCeti.canonicalClass`
(`PlaneCurves.divisorClass_eq_canonicalClass_iff_exists_kaehlerDifferentialDivisor_eq`). Parts
1–8 hold over every perfect field `k` algebraically closed in `K`, with `P` of degree one in 4.

Milestone: *Riemann–Roch theorem for the nonsingular model of a plane curve*. -/
theorem isRiemannRochDivisor_kaehlerDifferentialDivisor_spec (hK : IsFunctionField k K)
    (ω : Ω[K⁄k]) (hω : ω ≠ 0) :
    (∀ D : Divisor k K, (Divisor.dim D : ℤ) = Divisor.degree D + 1 - genus k K +
      Divisor.dim (kaehlerDifferentialDivisor hK isIntegrallyClosedIn_of_isAlgClosed ω hω - D)) ∧
    Divisor.dim (kaehlerDifferentialDivisor hK isIntegrallyClosedIn_of_isAlgClosed ω hω) =
      genus k K ∧
    Divisor.degree (kaehlerDifferentialDivisor hK isIntegrallyClosedIn_of_isAlgClosed ω hω) =
      2 * (genus k K : ℤ) - 2 ∧
    (∀ D : Divisor k K, 2 * (genus k K : ℤ) - 1 ≤ Divisor.degree D →
      (Divisor.dim D : ℤ) = Divisor.degree D + 1 - genus k K) ∧
    (∀ D : Divisor k K, 2 * (genus k K : ℤ) ≤ Divisor.degree D → ∀ P : Place k K,
      Divisor.dim (D - WeilDivisor.ofPoint P) + 1 = Divisor.dim D) ∧
    (∀ D : Divisor k K, 0 < Divisor.dim D →
      0 < Divisor.dim (kaehlerDifferentialDivisor hK isIntegrallyClosedIn_of_isAlgClosed ω hω - D) →
      2 * (Divisor.dim D : ℤ) ≤ Divisor.degree D + 2) ∧
    (∀ D : Divisor k K,
      finrank k (kaehlerDifferentialFiltration hK isIntegrallyClosedIn_of_isAlgClosed D) =
        Divisor.dim (kaehlerDifferentialDivisor hK isIntegrallyClosedIn_of_isAlgClosed ω hω - D)) ∧
    finrank k (kaehlerDifferentialFiltration hK isIntegrallyClosedIn_of_isAlgClosed 0) =
      genus k K ∧
    (∀ D : Divisor k K, Divisor.degree D = 2 * (genus k K : ℤ) - 2 →
      Divisor.dim D = genus k K → ∃ (ω' : Ω[K⁄k]) (hω' : ω' ≠ 0),
        kaehlerDifferentialDivisor hK isIntegrallyClosedIn_of_isAlgClosed ω' hω' = D) ∧
    (∀ D D' : Divisor k K,
      D + D' = kaehlerDifferentialDivisor hK isIntegrallyClosedIn_of_isAlgClosed ω hω →
      2 * ((Divisor.dim D : ℤ) - Divisor.dim D') = Divisor.degree D - Divisor.degree D') ∧
    (∀ {F : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d) [Fact (Irreducible F)],
      (∀ P, IsMultiplePoint F P → IsOrdinaryMultiplePoint F P) → 3 ≤ d →
      ∀ W D : Divisor k (functionField hF),
        (Place.orderSystem (functionField.isFunctionField hF)).divisorClass W =
          canonicalClass (functionField.isFunctionField hF) isIntegrallyClosedIn_of_isAlgClosed →
        0 ≤ D → Divisor.dim (W - D) = finrank k (adjointSubmoduleOfDivisor hF (d - 3) D)) := by
  have hex : IsIntegrallyClosedIn k K := isIntegrallyClosedIn_of_isAlgClosed
  have hW := isRiemannRochDivisor_kaehlerDifferentialDivisor hK hex ω hω
  refine ⟨Divisor.isRiemannRochDivisor_iff.1 hW, hW.dim_eq hK hex, hW.degree_eq hK hex,
    fun D hD ↦ Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree hK hex hD,
    fun D hD P ↦ Divisor.dim_sub_ofPoint_add_one hK hex hD
      (P.degree_eq_one_of_isAlgClosed_of_isFunctionField hK),
    fun D hD hWD ↦ hW.two_mul_dim_le_degree_add_two hK hex hD hWD,
    fun D ↦ finrank_kaehlerDifferentialFiltration hK hex D hω,
    finrank_kaehlerDifferentialFiltration_zero hK hex,
    fun D hdeg hdim ↦ (divisorClass_eq_canonicalClass_iff_exists_kaehlerDifferentialDivisor_eq
      hK hex D).1 ((divisorClass_eq_canonicalClass_iff hK hex D).2 ⟨hdeg, hdim.ge⟩),
    fun D D' h ↦ hW.two_mul_dim_sub_dim_eq h,
    fun hF _ hord hd _ _ hWc hD ↦
      dim_sub_eq_finrank_adjointSubmoduleOfDivisor_sub_three hord hd hWc hD⟩

end PlaneCurves

end
