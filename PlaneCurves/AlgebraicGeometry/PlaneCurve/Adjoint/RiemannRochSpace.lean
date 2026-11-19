/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Adjoint.Residue
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.LinearSystem.Independence
public import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# Adjoints of degree `m` and the Riemann–Roch spaces `L(E_m)`

Let `k` be an algebraically closed field and `C : F = 0` an irreducible projective plane curve of
degree `d` all of whose multiple points are ordinary, with adjoint divisor `E` on its nonsingular
model. Let `L` be a line with `F ∤ L`, `E_m = m div L - E`, `V_m` the adjoints of degree `m` and
`W_e` the forms of degree `e`. Then the sequence
`0 → W_e → V_{d+e} → L(E_{d+e}) → 0`, `H ↦ F H`, `G ↦ G / L^{d+e}`, is exact, and for `m < d` the
map `V_m → L(E_m)` is an isomorphism. Surjectivity is the adjoint division lemma: for
`f = R / S ∈ L(E_m)`, `div (R Lᵐ) ≥ div S + E`, so `R Lᵐ = A S + B F` and `f = A / Lᵐ`.

Hence `l(E_{d+e}) + dim W_e = dim V_{d+e}` and `l(E_m) = dim V_m` for `m < d`. Since `V_m` is the
linear system with assigned multiplicities `r_P - 1` at the multiple points `P` (`r_P = m_P(C)`),
`dim V_m ≥ (m + 1)(m + 2)/2 - ∑_P r_P (r_P - 1)/2`, with equality once
`∑_P (r_P - 1) ≤ m + 1`.

## Main definitions

* `PlaneCurves.Projective.mulToAdjointSubmodule hF e`: the linear map `W_e → V_{d+e}`,
  `H ↦ F H`.

## Main results

* `mulToAdjointSubmodule_injective`, `range_mulToAdjointSubmodule`,
  `adjointToRiemannRochSpace_surjective`: the sequence is exact.
* `adjointToRiemannRochSpace_injective`: `V_m ≅ L(E_m)` for `m < d`.
* `dim_add_finrank_eq_finrank_adjointSubmodule`, `dim_eq_finrank_adjointSubmodule`: `l(E_m)`.
* `finrank_adjointSubmodule_ge`, `finrank_adjointSubmodule_eq`: the dimension of `V_m`.
* `adjointToRiemannRochSpace_spec`: the milestone.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §8.1 and §8.3
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti Module
open TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {d m : ℕ}

instance finiteDimensional_adjointSubmodule : FiniteDimensional k (adjointSubmodule F m) :=
  Submodule.finiteDimensional_of_le adjointSubmodule_le_homogeneousSubmodule

/-! ### The dimension of `V_m` -/

/-- `∑_P r_P (r_P - 1)/2` as the sum of the conditions `m_P ≥ r_P - 1` that define `V_m`. -/
private theorem sum_adjointConditions (hF0 : F ≠ 0) (hfin : {P | IsMultiplePoint F P}.Finite)
    (g : ℕ → ℕ) (hg : g 0 = 0) :
    (adjointConditions F hF0 hfin).sum (fun _ n ↦ g n) =
      ∑ᶠ P : ℙ k (Fin 3 → k), g ((mult F P).toNat - 1) := by
  rw [Finsupp.sum, finsum_eq_sum_of_support_subset _ fun P hP ↦ ?_]
  · exact Finset.sum_congr rfl fun P _ ↦ by rw [adjointConditions_apply]
  rw [Finset.mem_coe, Finsupp.mem_support_iff, adjointConditions_apply]
  exact fun h ↦ hP (by simp [h, hg])

/-- **A lower bound for the dimension of `V_m`.** With `r_P = m_P(F)`,
`dim V_m ≥ (m + 1)(m + 2)/2 - ∑_P r_P (r_P - 1)/2`. -/
theorem finrank_adjointSubmodule_ge (hF0 : F ≠ 0) (hfin : {P | IsMultiplePoint F P}.Finite)
    (m : ℕ) :
    (m + 1) * (m + 2) / 2 - ∑ᶠ P : ℙ k (Fin 3 → k), (mult F P).toNat * ((mult F P).toNat - 1) / 2 ≤
      finrank k (adjointSubmodule F m) := by
  have h := finrank_linearSystem_ge m (adjointConditions F hF0 hfin)
  rw [← adjointSubmodule_eq_linearSystem, sum_adjointConditions hF0 hfin _ rfl] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  refine finsum_congr fun P ↦ ?_
  rcases Nat.eq_zero_or_pos (mult F P).toNat with h0 | h0
  · simp [h0]
  · rw [Nat.sub_add_cancel h0, mul_comm]

/-- **The dimension of `V_m` in high degree.** With `r_P = m_P(F)`, if
`∑_P (r_P - 1) ≤ m + 1`, then `dim V_m = (m + 1)(m + 2)/2 - ∑_P r_P (r_P - 1)/2`. -/
theorem finrank_adjointSubmodule_eq (hF0 : F ≠ 0) (hfin : {P | IsMultiplePoint F P}.Finite)
    (hm : ∑ᶠ P : ℙ k (Fin 3 → k), ((mult F P).toNat - 1) ≤ m + 1) :
    finrank k (adjointSubmodule F m) =
      (m + 1) * (m + 2) / 2 -
        ∑ᶠ P : ℙ k (Fin 3 → k), (mult F P).toNat * ((mult F P).toNat - 1) / 2 := by
  rw [← sum_adjointConditions hF0 hfin (fun n ↦ n) rfl] at hm
  rw [adjointSubmodule_eq_linearSystem hF0 hfin, finrank_linearSystem_eq hm,
    sum_adjointConditions hF0 hfin _ rfl]
  congr 1
  refine finsum_congr fun P ↦ ?_
  rcases Nat.eq_zero_or_pos (mult F P).toNat with h0 | h0
  · simp [h0]
  · rw [Nat.sub_add_cancel h0, mul_comm]

/-! ### Multiples of `F` -/

variable (hF : F.IsHomogeneous d)

variable (F) in
/-- The linear map `W_e → V_{d+e}`, `H ↦ F H`, from the forms of degree `e` to the adjoints of
degree `d + e`. -/
noncomputable def mulToAdjointSubmodule (e : ℕ) :
    homogeneousSubmodule (Fin 3) k e →ₗ[k] adjointSubmodule F (d + e) where
  toFun H := ⟨F * H, mul_mem_adjointSubmodule hF ((mem_homogeneousSubmodule _ _).1 H.2)⟩
  map_add' _ _ := Subtype.ext (mul_add _ _ _)
  map_smul' _ _ := Subtype.ext (mul_smul_comm _ _ _)

@[simp]
theorem coe_mulToAdjointSubmodule_apply {e : ℕ} (H : homogeneousSubmodule (Fin 3) k e) :
    (mulToAdjointSubmodule F hF e H : MvPolynomial (Fin 3) k) = F * H :=
  (rfl)

/-- `H ↦ F H` is injective for `F ≠ 0`. -/
theorem mulToAdjointSubmodule_injective (hF0 : F ≠ 0) (e : ℕ) :
    Function.Injective (mulToAdjointSubmodule F hF e) := fun _ _ h ↦
  Subtype.ext (mul_left_cancel₀ hF0 (congrArg Subtype.val h))

/-! ### The exact sequence -/

section Exact

variable [IsAlgClosed k] {hF} [Fact (Irreducible F)]
  (hord : ∀ P, IsMultiplePoint F P → IsOrdinaryMultiplePoint F P)
  {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1) (hFL : ¬ F ∣ L)
include hord

/-- The image of `H ↦ F H` is the kernel of `G ↦ G / L^{d+e}`. -/
theorem range_mulToAdjointSubmodule (e : ℕ) :
    LinearMap.range (mulToAdjointSubmodule F hF e) =
      LinearMap.ker (adjointToRiemannRochSpace hF hord hL hFL (m := d + e)) := by
  ext G
  rw [mem_ker_adjointToRiemannRochSpace_iff, LinearMap.mem_range]
  refine ⟨fun ⟨H, hH⟩ ↦ hH ▸ dvd_mul_right _ _, fun ⟨H, hH⟩ ↦ ?_⟩
  have hF0 : F ≠ 0 := (Fact.out : Irreducible F).ne_zero
  have hG := (mem_adjointSubmodule_iff.1 G.2).1
  rw [hH] at hG
  have hHe : H.IsHomogeneous e := by
    rcases eq_or_ne H 0 with rfl | hH0
    · exact isHomogeneous_zero _ _ _
    have h := (hG.of_mul_right hF0 : H.IsHomogeneous H.totalDegree)
    rwa [show H.totalDegree = e by
      have := hG.totalDegree (mul_ne_zero hF0 hH0)
      rw [totalDegree_mul_of_isDomain hF0 hH0, hF.totalDegree hF0] at this
      omega] at h
  exact ⟨⟨H, (mem_homogeneousSubmodule _ _).2 hHe⟩, Subtype.ext hH.symm⟩

/-- For `m < d`, `G ↦ G / Lᵐ` is injective on `V_m`: no nonzero form of degree `m` is a
multiple of `F`. -/
theorem adjointToRiemannRochSpace_injective (hm : m < d) :
    Function.Injective (adjointToRiemannRochSpace hF hord hL hFL (m := m)) := by
  refine (LinearMap.ker_eq_bot (R := k) (M := adjointSubmodule F m)
    (M₂ := riemannRochSpace (m • formDivisor hF hL - adjointDivisor hF))
    (f := adjointToRiemannRochSpace hF hord hL hFL (m := m))).1
    ((Submodule.eq_bot_iff _).2 fun G hG ↦ ?_)
  rw [mem_ker_adjointToRiemannRochSpace_iff] at hG
  by_contra hG0
  have hG0 : (G : MvPolynomial (Fin 3) k) ≠ 0 := fun h ↦ hG0 (Subtype.ext h)
  have hF0 : F ≠ 0 := (Fact.out : Irreducible F).ne_zero
  have := totalDegree_le_of_dvd_of_isDomain hG hG0
  rw [hF.totalDegree hF0, (mem_adjointSubmodule_iff.1 G.2).1.totalDegree hG0] at this
  omega

/-- **Adjoints compute `L(E_m)`.** Every `f ∈ L(m div L - E)` is `G / Lᵐ` for an adjoint `G` of
degree `m`: writing `f = R / S`, the adjoint division lemma gives `R Lᵐ = G S + B F`. -/
theorem adjointToRiemannRochSpace_surjective :
    Function.Surjective (adjointToRiemannRochSpace hF hord hL hFL (m := m)) := by
  rintro ⟨f, hf⟩
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, map_zero _⟩
  have hLm : (L ^ m).IsHomogeneous m := by simpa using hL.pow m
  have hFLm := not_dvd_pow_of_not_dvd hFL m
  obtain ⟨e, R, S, hR, hS, hFR, hFS, hu⟩ := exists_formQuotient_eq (Units.mk0 f hf0)
  have hfu : f = formQuotient hF hR hS hFR hFS := by rw [hu, Units.val_mk0]
  have hRL : (R * L ^ m).IsHomogeneous (e + m) := hR.mul hLm
  have hdivRL : formDivisor hF hRL = formDivisor hF hR + m • formDivisor hF hL := by
    rw [formDivisor_mul hR hLm hFR hFLm, formDivisor_congr hLm (hL.pow m) rfl,
      formDivisor_pow hL hFL]
  -- `div f + m div L - E ≥ 0`, that is `div (R Lᵐ) ≥ div S + E`.
  have hle : formDivisor hF hS + adjointDivisor hF ≤ formDivisor hF hRL := by
    intro Q
    have h := (mem_riemannRochSpace_iff_neg_le_ord hf0).1 hf Q
    rw [hfu, ← Divisor.coeff_principal (functionField.isFunctionField hF),
      principal_formQuotient] at h
    rw [hdivRL]
    simp only [WeilDivisor.coeff_sub, WeilDivisor.coeff_nsmul] at h
    change (formDivisor hF hS).coeff Q + (adjointDivisor hF).coeff Q ≤
      (formDivisor hF hR).coeff Q + (m • formDivisor hF hL).coeff Q
    rw [WeilDivisor.coeff_nsmul]
    omega
  obtain ⟨G, B, hG, -, -, -, hGB⟩ :=
    exists_isHomogeneous_mul_add_mul_eq_of_le_formDivisor hord hRL hS hFS (Or.inr hle)
  rw [Nat.add_sub_cancel_left] at hG
  have hdvd : F ∣ G * S - R * L ^ m := ⟨-B, by rw [← hGB]; ring⟩
  have hadj : IsAdjoint F G := by
    by_cases hFG : F ∣ G
    · exact isAdjoint_of_dvd hFG
    refine (isAdjoint_iff_le_formDivisor (hF := hF) hord hG hFG).2 ?_
    have hGS : formDivisor hF (hG.mul hS) = formDivisor hF hRL :=
      (formDivisor_eq_of_dvd_sub (hG.mul hS) (by rw [add_comm]; exact hRL) hdvd).trans
        (formDivisor_congr _ _ rfl)
    rw [formDivisor_mul hG hS hFG hFS] at hGS
    rw [← hGS, add_comm (formDivisor hF hG)] at hle
    exact le_of_add_le_add_left hle
  refine ⟨⟨G, mem_adjointSubmodule_iff.2 ⟨hG, hadj⟩⟩, Subtype.ext ?_⟩
  change _ = f
  rw [coe_adjointToRiemannRochSpace_apply hord hL hFL hLm _
      (projectivePlaneCurve.notMem_ideal_of_not_dvd hF hFLm), hfu, coe_formQuotient,
    functionField.mk_eq_mk_iff, projectivePlaneCurve.mem_ideal_iff hF]
  exact hdvd

include hFL in
/-- **`l(E_m)` in degree `m ≥ d`.** `l(E_{d+e}) + dim W_e = dim V_{d+e}`. -/
theorem dim_add_finrank_eq_finrank_adjointSubmodule (e : ℕ) :
    Divisor.dim ((d + e) • formDivisor hF hL - adjointDivisor hF) +
        finrank k (homogeneousSubmodule (Fin 3) k e) =
      finrank k (adjointSubmodule F (d + e)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (K := k) (V := adjointSubmodule F (d + e))
    (V₂ := riemannRochSpace ((d + e) • formDivisor hF hL - adjointDivisor hF))
    (adjointToRiemannRochSpace hF hord hL hFL (m := d + e))
  rwa [LinearMap.range_eq_top.2 (adjointToRiemannRochSpace_surjective hord hL hFL), finrank_top,
    ← range_mulToAdjointSubmodule hord hL hFL,
    LinearMap.finrank_range_of_inj
      (mulToAdjointSubmodule_injective hF (Fact.out : Irreducible F).ne_zero e),
    ← Divisor.dim_def] at h

include hFL in
/-- **`l(E_m)` in degree `m < d`.** `l(E_m) = dim V_m`. -/
theorem dim_eq_finrank_adjointSubmodule (hm : m < d) :
    Divisor.dim (m • formDivisor hF hL - adjointDivisor hF) =
      finrank k (adjointSubmodule F m) := by
  rw [Divisor.dim_def]
  exact (LinearEquiv.ofBijective (adjointToRiemannRochSpace hF hord hL hFL (m := m))
    ⟨adjointToRiemannRochSpace_injective hord hL hFL hm,
      adjointToRiemannRochSpace_surjective hord hL hFL⟩).finrank_eq.symm

end Exact

/-! ### The milestone -/

/-- **Adjoints of degree `m` compute the Riemann–Roch spaces `L(E_m)`** (Fulton, §8.1 and §8.3).
Let `k` be algebraically closed and `C : F = 0` an irreducible projective plane curve of degree
`d` all of whose multiple points are ordinary, with adjoint divisor `E`. Let `L` be a line with
`F ∤ L` and `E_m = m div L - E`; let `V_m` be the adjoints of degree `m` and `W_e` the forms of
degree `e`. With `r_P = m_P(C)`:

1. the sequence `0 → W_e → V_{d+e} → L(E_{d+e}) → 0`, `H ↦ F H`, `G ↦ G / L^{d+e}`, is exact;
2. for every `m`, every `f ∈ L(E_m)` is `G / Lᵐ` for an adjoint `G` of degree `m`
   (`coe_adjointToRiemannRochSpace_apply`), and `V_m ≅ L(E_m)` for `m < d`;
3. `l(E_{d+e}) + dim W_e = dim V_{d+e}`, and `l(E_m) = dim V_m` for `m < d`;
4. `dim V_m ≥ (m + 1)(m + 2)/2 - ∑_P r_P (r_P - 1)/2`, with equality if
   `∑_P (r_P - 1) ≤ m + 1`.

The book writes `W_{m-d}`, with `W_{m-d} = 0` for `m < d`, and takes `L = Z` meeting `C` in `d`
distinct points; any line with `F ∤ L` will do.

Milestone: *Adjoints of degree m compute the Riemann–Roch spaces L(E_m)*. -/
theorem adjointToRiemannRochSpace_spec [IsAlgClosed k] (hF : F.IsHomogeneous d)
    [Fact (Irreducible F)] (hord : ∀ P, IsMultiplePoint F P → IsOrdinaryMultiplePoint F P)
    {L : MvPolynomial (Fin 3) k} (hL : L.IsHomogeneous 1) (hFL : ¬ F ∣ L) :
    (∀ e, Function.Injective (mulToAdjointSubmodule F hF e)) ∧
    (∀ e, LinearMap.range (mulToAdjointSubmodule F hF e) =
      LinearMap.ker (adjointToRiemannRochSpace hF hord hL hFL (m := d + e))) ∧
    (∀ m, Function.Surjective (adjointToRiemannRochSpace hF hord hL hFL (m := m))) ∧
    (∀ m < d, Function.Injective (adjointToRiemannRochSpace hF hord hL hFL (m := m))) ∧
    (∀ e, Divisor.dim ((d + e) • formDivisor hF hL - adjointDivisor hF) +
        finrank k (homogeneousSubmodule (Fin 3) k e) = finrank k (adjointSubmodule F (d + e))) ∧
    (∀ m < d, Divisor.dim (m • formDivisor hF hL - adjointDivisor hF) =
      finrank k (adjointSubmodule F m)) ∧
    (∀ m, (m + 1) * (m + 2) / 2 -
        ∑ᶠ P : ℙ k (Fin 3 → k), (mult F P).toNat * ((mult F P).toNat - 1) / 2 ≤
      finrank k (adjointSubmodule F m)) ∧
    (∀ m, ∑ᶠ P : ℙ k (Fin 3 → k), ((mult F P).toNat - 1) ≤ m + 1 →
      finrank k (adjointSubmodule F m) = (m + 1) * (m + 2) / 2 -
        ∑ᶠ P : ℙ k (Fin 3 → k), (mult F P).toNat * ((mult F P).toNat - 1) / 2) := by
  have hirr : Irreducible F := Fact.out
  have hfin := finite_setOf_isMultiplePoint_of_irreducible hF hirr
  exact ⟨mulToAdjointSubmodule_injective hF hirr.ne_zero, range_mulToAdjointSubmodule hord hL hFL,
    fun _ ↦ adjointToRiemannRochSpace_surjective hord hL hFL,
    fun _ hm ↦ adjointToRiemannRochSpace_injective hord hL hFL hm,
    dim_add_finrank_eq_finrank_adjointSubmodule hord hL hFL,
    fun _ hm ↦ dim_eq_finrank_adjointSubmodule hord hL hFL hm,
    finrank_adjointSubmodule_ge hirr.ne_zero hfin,
    fun _ hm ↦ finrank_adjointSubmodule_eq hirr.ne_zero hfin hm⟩

end PlaneCurves.Projective

end
