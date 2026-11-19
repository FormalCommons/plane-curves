/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.CurveLocalRing
public import PlaneCurves.FieldTheory.FunctionField.ResidueRing
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.LinearSubvariety
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.PlaneCurveDimension
public import Mathlib.RingTheory.Valuation.LocalSubring
public import TauCeti.FieldTheory.FunctionField.Place.Zeros
public import TauCeti.FieldTheory.FunctionField.Place.Existence

/-!
# The centre of a valuation ring on a projective plane curve

Let `k` be a field, `C : F = 0` an irreducible projective plane curve with function field `k(C)`,
`ψ : k(C) → L` a `k`-embedding into a field `L`, and `R` a valuation subring of `L`. Then `R` is
*centred* at a point `P ∈ C` if it dominates `ψ(𝒪_P(C))`.

If `k` is algebraically closed, `k ⊆ R` and `ψ(k(C)) ⊄ R`, then `R` has exactly one centre on
`C` (Fulton, §7.1, Theorem 1). Uniqueness: for `P ≠ Q` a line `ℓ` through `P` and not `Q` gives
`ℓ / Xᵢ ∈ 𝔪_P(C)` with inverse in `𝒪_Q(C)`. Existence: among the coordinates choose `Xᵢ` with
`ψ(Xₗ / Xᵢ) ∈ R` for all `l`; the residue ring of `k[X₀/Xᵢ, X₁/Xᵢ, X₂/Xᵢ]` at the centre of `R`
is `k` (`ValuationSubring.exists_forall_valuation_lt_one_iff_eval_eq_zero`), and the residues
of the `Xₗ / Xᵢ` are the coordinates of the centre. The centre is defined through the maximal
ideal of `R`, so `R` may have a residue field larger than `k`.

For a place `Q` of `k(C)` (`L = k(C)`, `R` the valuation ring of `Q`) this gives the centre map
`center hF : Place k (functionField hF) → C`; it is surjective, by Chevalley's extension theorem,
and has finite fibres, since the places centred at `P` are zeros of a nonzero element of
`𝔪_P(C)`.

## Main definitions

* `PlaneCurves.Projective.IsCenter hF ψ R P`: `R` dominates `ψ(𝒪_P(C))`.
* `PlaneCurves.Projective.center hF Q`: the centre of a place `Q` of `k(C)`, for `k`
  algebraically closed.

## Main results

* `isCenter_iff`: `R` is centred at `P` iff `ψ(𝒪_P(C)) ⊆ R` and `ψ(𝔪_P(C))` has valuation `< 1`.
* `IsCenter.eq`: a valuation ring has at most one centre.
* `existsUnique_isCenter`: the milestone, existence and uniqueness of the centre.
* `isCenter_iff_forall_mem`: if `ψ(k(C)) ⊄ R`, `R` is centred at `P` iff `ψ(𝒪_P(C)) ⊆ R`.
* `not_isCenter_of_forall_mem`: if `ψ(k(C)) ⊆ R`, `R` is centred at no point.
* `exists_ne_zero_mem_maximalIdeal_localSubring`: `𝔪_P(C) ≠ 0`.
* `center_eq_iff`, `center_eq_iff_le`: the centre of `Q` is the point `P` whose local ring is
  dominated by, equivalently contained in, the valuation ring of `Q`.
* `center_surjective`, `finite_setOf_center_eq`: the centre map is surjective, with finite fibres.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.1
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace HomogeneousLocalization
open TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {d : ℕ} (hF : F.IsHomogeneous d)
  [Fact (Irreducible F)] {L : Type*} [Field L] [Algebra k L]

/-- A valuation subring `R` of a field `L`, with a `k`-embedding `ψ : k(C) → L` of the function
field of the irreducible plane curve `C : F = 0`, is **centred** at the point `P ∈ C` if `R`
dominates the image `ψ(𝒪_P(C))` of the local ring of `C` at `P`: `ψ(𝒪_P(C)) ⊆ R` and
`ψ(𝔪_P(C)) ⊆ 𝔪_R` (`isCenter_iff`). -/
def IsCenter (ψ : functionField hF →ₐ[k] L) (R : ValuationSubring L)
    (P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))) : Prop :=
  (localSubring hF P).map (ψ : functionField hF →+* L) ≤ R.toLocalSubring

theorem isCenter_def (ψ : functionField hF →ₐ[k] L) (R : ValuationSubring L)
    (P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))) :
    IsCenter hF ψ R P ↔
      (localSubring hF P).map (ψ : functionField hF →+* L) ≤ R.toLocalSubring :=
  Iff.rfl

variable {hF} {ψ : functionField hF →ₐ[k] L} {R : ValuationSubring L}
  {P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))}

/-- `R` is centred at `P` iff `ψ` maps `𝒪_P(C)` into `R` and `𝔪_P(C)` into the maximal ideal of
`R`, the elements of valuation `< 1`. -/
theorem isCenter_iff : IsCenter hF ψ R P ↔
    (∀ z ∈ (localSubring hF P).toSubring, ψ z ∈ R) ∧
      ∀ z : (localSubring hF P).toSubring, z ∈ IsLocalRing.maximalIdeal _ →
        R.valuation (ψ z) < 1 := by
  rw [isCenter_def, LocalSubring.le_def]
  constructor
  · rintro ⟨h, hloc⟩
    have hmem : ∀ z ∈ (localSubring hF P).toSubring, ψ z ∈ R := fun z hz ↦
      h ⟨z, hz, rfl⟩
    refine ⟨hmem, fun z hz ↦ ?_⟩
    by_contra hlt
    have hv : R.valuation (ψ z) = 1 :=
      le_antisymm ((R.valuation_le_one_iff _).2 (hmem z z.2)) (not_lt.1 hlt)
    have hu : IsUnit (⟨ψ z, hmem z z.2⟩ : R) := (R.valuation_eq_one_iff _).2 hv
    have hu' := isUnit_of_map_unit (Subring.inclusion h)
      (⟨ψ z, ⟨z, z.2, rfl⟩⟩ : ((localSubring hF P).map (ψ : functionField hF →+* L)).toSubring) hu
    obtain ⟨⟨w, hw⟩, hzw⟩ := hu'.exists_right_inv
    obtain ⟨w', hw', rfl⟩ := hw
    refine (IsLocalRing.mem_maximalIdeal _).1 hz (isUnit_iff_exists_inv.2 ⟨⟨w', hw'⟩, ?_⟩)
    refine Subtype.ext (ψ.injective ?_)
    simpa using congrArg Subtype.val hzw
  · rintro ⟨hmem, hmax⟩
    have h : ((localSubring hF P).map (ψ : functionField hF →+* L)).toSubring ≤
        R.toLocalSubring.toSubring := by
      rintro _ ⟨z, hz, rfl⟩
      exact hmem z hz
    refine ⟨h, ⟨fun ⟨a, ha⟩ hau ↦ ?_⟩⟩
    obtain ⟨z, hz, rfl⟩ := ha
    by_cases hzu : IsUnit (⟨z, hz⟩ : (localSubring hF P).toSubring)
    · obtain ⟨⟨w, hw⟩, hzw⟩ := hzu.exists_right_inv
      refine isUnit_iff_exists_inv.2 ⟨⟨ψ w, ⟨w, hw, rfl⟩⟩, Subtype.ext ?_⟩
      simpa [← map_mul] using congrArg (fun x ↦ ψ x.1) hzw
    · have := hmax ⟨z, hz⟩ ((IsLocalRing.mem_maximalIdeal _).2 hzu)
      have hv := (R.valuation_eq_one_iff (⟨ψ z, hmem z hz⟩ : R)).1 hau
      exact absurd hv (ne_of_lt this)


variable {Q : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))}

/-- **Uniqueness of the centre.** A valuation subring is centred at most at one point of `C`: for
`P ≠ Q` there is `z = ℓ / Xᵢ ∈ 𝔪_P(C)` with `1 / z = Xᵢ / ℓ ∈ 𝒪_Q(C)`. -/
theorem IsCenter.eq (hP : IsCenter hF ψ R P) (hQ : IsCenter hF ψ R Q) : P = Q := by
  by_contra hne
  obtain ⟨a, haP, haQ⟩ :=
    exists_sum_C_mul_X_mem_zeroLocus_notMem_zeroLocus fun h ↦ hne (Subtype.ext h)
  have hℓ := isHomogeneous_sum_C_mul_X a
  have hS : ∀ f ∈ ({∑ j, C (a j) * X j} : Set (MvPolynomial (Fin 3) k)), ∃ d, f.IsHomogeneous d :=
    by simpa using ⟨1, hℓ⟩
  rw [mem_zeroLocus_iff_eval_rep hS, Set.forall_mem_singleton] at haP haQ
  obtain ⟨i, hi⟩ := P.1.exists_mem_affineOpen
  rw [mem_affineOpen_iff] at hi
  have hiP : eval P.1.rep (X i) ≠ 0 := by simpa using hi
  have hXi := notMem_of_eval_rep_ne_zero P.2 (isHomogeneous_X k i) hiP
  have hℓI := notMem_of_eval_rep_ne_zero Q.2 hℓ haQ
  set z := functionField.mk hℓ (isHomogeneous_X k i) hXi
  set w := functionField.mk (isHomogeneous_X k i) hℓ hℓI
  have hzw : z * w = 1 := functionField.mk_mul_mk_swap _ _ hℓI hXi
  have hz := (isCenter_iff.1 hP).2 ⟨z, mem_localSubring_iff.2 ⟨1, _, _, hℓ, _, hiP, rfl⟩⟩
    (mem_maximalIdeal_localSubring_iff.2 ⟨1, _, _, hℓ, _, hiP, haP, rfl⟩)
  have hw := (isCenter_iff.1 hQ).1 w (mem_localSubring_iff.2 ⟨1, _, _, _, hℓ, haQ, rfl⟩)
  have := mul_lt_one_of_lt_of_le hz ((R.valuation_le_one_iff _).2 hw)
  rw [← map_mul, ← map_mul, hzw, map_one, map_one] at this
  exact lt_irrefl _ this

/-- Some `Xⱼ / Xᵢ`, with `Xᵢ ∉ (F)`, maps to an element of maximal valuation among the
`Xₗ / Xᵢ`: then every `Xₗ / Xⱼ` maps into `R`. -/
private theorem exists_forall_mem :
    ∃ (j : Fin 3) (hj : X j ∉ projectivePlaneCurve.ideal hF), ∀ l,
      ψ (functionField.mk (isHomogeneous_X k l) (isHomogeneous_X k j) hj) ∈ R := by
  obtain ⟨i, hi⟩ := projectivePlaneCurve.exists_not_dvd_X (Fact.out : Irreducible F)
  have hi' : X i ∉ projectivePlaneCurve.ideal hF := (projectivePlaneCurve.mem_ideal_iff hF).not.2 hi
  set c : Fin 3 → functionField hF := fun l ↦
    functionField.mk (isHomogeneous_X k l) (isHomogeneous_X k i) hi'
  obtain ⟨j, hj⟩ := Finite.exists_max fun l ↦ R.valuation (ψ (c l))
  have hcj : c j ≠ 0 := by
    intro h
    have := hj i
    simp only [c, h, functionField.mk_self, map_zero, map_one] at this
    exact zero_lt_one.not_ge this
  have hj' : X j ∉ projectivePlaneCurve.ideal hF := fun h ↦
    hcj ((functionField.mk_eq_zero_iff _ _ _).2 h)
  refine ⟨j, hj', fun l ↦ ?_⟩
  rw [← R.valuation_le_one_iff, ← functionField.mk_div_mk _ _ (isHomogeneous_X k i) hj' hi',
    map_div₀, map_div₀]
  have : R.valuation (ψ (c j)) ≠ 0 := by simpa using hcj
  exact (div_le_one₀ (zero_lt_iff.2 this)).2 (hj l)


/-- **Existence of the centre.** Let `k` be algebraically closed and `R` a valuation subring of
`L` containing `k` but not `ψ(k(C))`. Then `R` is centred at some point of `C`: choose `i` with
`Xᵢ ∉ (F)` such that `R` contains every `ψ(Xₗ / Xᵢ)`; the residue ring of `k[X₀/Xᵢ, X₁/Xᵢ, X₂/Xᵢ]`
at the centre of `R` is `k`, and the residues of the `Xₗ / Xᵢ` are the coordinates of the
point. -/
theorem exists_isCenter [IsAlgClosed k] (hkR : ∀ c : k, algebraMap k L c ∈ R)
    (hR : ∃ z, ψ z ∉ R) : ∃ P, IsCenter hF ψ R P := by
  obtain ⟨i, hi, hc⟩ := exists_forall_mem (ψ := ψ) (R := R)
  set c : Fin 3 → functionField hF := fun l ↦
    functionField.mk (isHomogeneous_X k l) (isHomogeneous_X k i) hi
  have hdiv : ∀ {m : ℕ} {f g : MvPolynomial (Fin 3) k} (hf : f.IsHomogeneous m)
      (hg : g.IsHomogeneous m) (hgI : g ∉ projectivePlaneCurve.ideal hF),
      R.valuation (ψ (functionField.mk hf hg hgI)) =
        R.valuation (ψ (aeval c f)) / R.valuation (ψ (aeval c g)) := fun hf hg hgI ↦ by
    rw [functionField.mk_eq_aeval_div_aeval hi, map_div₀, map_div₀]
  have hle : ∀ f, R.valuation (ψ (aeval c f)) ≤ 1 := fun f ↦ by
    rw [R.valuation_le_one_iff, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    induction f using MvPolynomial.induction_on with
    | C a => simpa using hkR a
    | add p q hp hq => simpa using add_mem hp hq
    | mul_X p l hp => simpa using mul_mem hp (hc l)
  have h0 : ∃ f : MvPolynomial (Fin 3) k, aeval c f ≠ 0 ∧ R.valuation (ψ (aeval c f)) < 1 := by
    by_contra! h
    obtain ⟨z, hz⟩ := hR
    obtain ⟨m, f, g, hf, hg, hgI, rfl⟩ := functionField.exists_eq_mk z
    have hg0 : aeval c g ≠ 0 := by
      rw [functionField.aeval_mk_X hi hg]
      exact functionField.mk_ne_zero _ _ _ hgI
    refine hz ((R.valuation_le_one_iff _).1 ?_)
    rw [hdiv, le_antisymm (hle g) (h g hg0), div_one]
    exact hle f
  obtain ⟨a, ha⟩ := ValuationSubring.exists_forall_valuation_lt_one_iff_eval_eq_zero
    (functionField.isFunctionField hF) c ψ R hkR hc h0
  have ha0 : a ≠ 0 := by
    intro h0
    have := (ha (X i)).2 (by simp [h0])
    simp [c, functionField.mk_self] at this
  obtain ⟨P, hP⟩ : ∃ P, P = Projectivization.mk k a ha0 := ⟨_, rfl⟩
  have hval : ∀ {m : ℕ} {f : MvPolynomial (Fin 3) k}, f.IsHomogeneous m →
      (eval P.rep f = 0 ↔ eval a f = 0) := fun hf ↦ by
    rw [← mem_pointIdeal_iff_of_isHomogeneous hf, hP,
      mem_pointIdeal_mk_iff_of_isHomogeneous hf ha0]
  have hPC : P ∈ zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)) := by
    rw [mem_zeroLocus_ideal_iff, hval hF, ← ha, functionField.aeval_mk_X hi hF,
      (functionField.mk_eq_zero_iff _ _ _).2 ((projectivePlaneCurve.mem_ideal_iff hF).2 dvd_rfl)]
    simp
  have hunit : ∀ {m : ℕ} {g : MvPolynomial (Fin 3) k}, g.IsHomogeneous m →
      eval P.rep g ≠ 0 → R.valuation (ψ (aeval c g)) = 1 := fun hg hgP ↦
    le_antisymm (hle _) (not_lt.1 fun h ↦ hgP ((hval hg).2 ((ha _).1 h)))
  refine ⟨⟨P, hPC⟩, isCenter_iff.2 ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩⟩
  · obtain ⟨m, f, g, hf, hg, hgP, rfl⟩ := mem_localSubring_iff.1 hz
    rw [← R.valuation_le_one_iff, hdiv, hunit hg hgP, div_one]
    exact hle f
  · obtain ⟨m, f, g, hf, hg, hgP, hfP, hz⟩ := mem_maximalIdeal_localSubring_iff.1 hz
    rw [hz, hdiv, hunit hg hgP, div_one, ha, ← hval hf]
    exact hfP


/-- **The centre of a discrete valuation ring on a projective curve.** Let `k` be algebraically
closed, `C : F = 0` an irreducible projective plane curve, `ψ : k(C) → L` a `k`-embedding and `R`
a valuation subring of `L` (for instance a discrete valuation ring) containing `k` but not
`ψ(k(C))`. Then there is exactly one point `P ∈ C` such that `R` dominates `ψ(𝒪_P(C))`.

Milestone: *Centre of a discrete valuation ring on a projective curve*. -/
theorem existsUnique_isCenter [IsAlgClosed k] (hkR : ∀ c : k, algebraMap k L c ∈ R)
    (hR : ∃ z, ψ z ∉ R) : ∃! P, IsCenter hF ψ R P :=
  let ⟨P, hP⟩ := exists_isCenter hkR hR
  ⟨P, hP, fun _ hQ ↦ hQ.eq hP⟩

variable (hF P) in
/-- The maximal ideal of `𝒪_P(C)` is not zero: it contains `G / Xᵢᵐ` for a form `G ∉ (F)` of
degree `m` with `G(P) = 0`, which exists since `k(C)` has transcendence degree one, not zero. -/
theorem exists_ne_zero_mem_maximalIdeal_localSubring [IsAlgClosed k] :
    ∃ z : (localSubring hF P).toSubring, z ∈ IsLocalRing.maximalIdeal _ ∧ z ≠ 0 := by
  obtain ⟨i, hi⟩ := P.1.exists_mem_affineOpen
  rw [mem_affineOpen_iff] at hi
  have hiP : eval P.1.rep (X i) ≠ 0 := by simpa using hi
  have hXi := notMem_of_eval_rep_ne_zero P.2 (isHomogeneous_X k i) hiP
  obtain ⟨m, G, hG, hGP, hGI⟩ : ∃ (m : ℕ) (G : MvPolynomial (Fin 3) k), G.IsHomogeneous m ∧
      eval P.1.rep G = 0 ∧ G ∉ projectivePlaneCurve.ideal hF := by
    by_contra! h
    have hle : pointIdeal P.1 ≤ projectivePlaneCurve.ideal hF := by
      rw [← HomogeneousIdeal.toIdeal_homogeneousCore_eq_self (pointIdeal P.1),
        ← toIdeal_le_toIdeal_iff]
      refine Ideal.span_le.2 ?_
      rintro _ ⟨⟨x, m, hx⟩, hxP, rfl⟩
      have hx' : x.IsHomogeneous m := (mem_homogeneousSubmodule _ _).1 hx
      exact h m x hx' ((mem_pointIdeal_iff_of_isHomogeneous hx').1 hxP)
    have := (trdeg_functionField_eq_zero_iff hXi).2 ⟨P.1,
      (le_antisymm ((mem_zeroLocus_iff_le_pointIdeal _).1 P.2) hle).trans (pointIdeal_def _)⟩
    rw [(functionField.isFunctionField hF).trdeg_eq_one] at this
    exact one_ne_zero this
  have hXP : eval P.1.rep (X i ^ m) ≠ 0 := by simpa using pow_ne_zero m hi
  refine ⟨⟨_, mem_localSubring_iff.2 ⟨m, G, _, hG, isHomogeneous_X_pow i m, hXP, rfl⟩⟩,
    mem_maximalIdeal_localSubring_iff.2 ⟨m, G, _, hG, _, hXP, hGP, rfl⟩, fun h ↦ ?_⟩
  exact functionField.mk_ne_zero _ _ _ hGI (congrArg Subtype.val h)

/-- If `R` contains `ψ(k(C))`, then it is centred at no point of `C`. -/
theorem not_isCenter_of_forall_mem [IsAlgClosed k] (hR : ∀ z, ψ z ∈ R) : ¬ IsCenter hF ψ R P := by
  intro h
  obtain ⟨z, hzm, hz0⟩ := exists_ne_zero_mem_maximalIdeal_localSubring hF P
  have hz0' : (z : functionField hF) ≠ 0 := fun h ↦ hz0 (Subtype.ext h)
  have := mul_lt_one_of_lt_of_le ((isCenter_iff.1 h).2 z hzm)
    ((R.valuation_le_one_iff _).2 (hR (z : functionField hF)⁻¹))
  rw [← map_mul, ← map_mul, mul_inv_cancel₀ hz0', map_one, map_one] at this
  exact lt_irrefl _ this

/-- If `R` does not contain `ψ(k(C))`, then `R` is centred at `P` as soon as it contains
`ψ(𝒪_P(C))`: the elements of `𝒪_P(C)` mapping to the maximal ideal of `R` form a nonzero prime,
which is maximal since `𝒪_P(C)` has transcendence degree one. -/
theorem isCenter_iff_forall_mem (hR : ∃ z, ψ z ∉ R) :
    IsCenter hF ψ R P ↔ ∀ z ∈ (localSubring hF P).toSubring, ψ z ∈ R := by
  refine ⟨fun h ↦ (isCenter_iff.1 h).1, fun hmem ↦ isCenter_iff.2 ⟨hmem, ?_⟩⟩
  let θ : (localSubring hF P).toSubring →+* R :=
    ((ψ : functionField hF →+* L).comp (localSubring hF P).toSubring.subtype).codRestrict R
      fun z ↦ hmem z z.2
  let p := (IsLocalRing.maximalIdeal R).comap θ
  have hp : ∀ z, z ∈ p ↔ R.valuation (ψ z) < 1 := fun z ↦ R.valuation_lt_one_iff (θ z)
  have hp0 : p ≠ ⊥ := by
    intro hp0
    obtain ⟨w, hw⟩ := hR
    obtain ⟨i, hi⟩ := P.1.exists_mem_affineOpen
    rw [mem_affineOpen_iff] at hi
    obtain ⟨m, f, g, hf, hg, hgI, rfl⟩ := functionField.exists_eq_mk w
    have hXP : eval P.1.rep (X i ^ m) ≠ 0 := by simpa using pow_ne_zero m hi
    let zf : (localSubring hF P).toSubring :=
      ⟨_, mem_localSubring_iff.2 ⟨m, f, _, hf, isHomogeneous_X_pow i m, hXP, rfl⟩⟩
    let zg : (localSubring hF P).toSubring :=
      ⟨_, mem_localSubring_iff.2 ⟨m, g, _, hg, isHomogeneous_X_pow i m, hXP, rfl⟩⟩
    have hzg : R.valuation (ψ zg) = 1 := by
      refine le_antisymm ((R.valuation_le_one_iff _).2 (hmem _ zg.2)) (not_lt.1 fun h ↦ ?_)
      have := (hp zg).2 h
      rw [hp0, Ideal.mem_bot] at this
      exact functionField.mk_ne_zero _ _ _ hgI (congrArg Subtype.val this)
    refine hw ((R.valuation_le_one_iff _).1 ?_)
    rw [← functionField.mk_div_mk hf hg (isHomogeneous_X_pow i m) hgI
      (notMem_of_eval_rep_ne_zero P.2 (isHomogeneous_X_pow i m) hXP), map_div₀, map_div₀]
    change R.valuation (ψ zf) / R.valuation (ψ zg) ≤ 1
    rw [hzg, div_one, R.valuation_le_one_iff]
    exact hmem _ zf.2
  let φ : (localSubring hF P).toSubring →ₐ[k] functionField hF :=
    { toRingHom := (localSubring hF P).toSubring.subtype, commutes' := fun _ ↦ rfl }
  have htr : Algebra.trdeg k (localSubring hF P).toSubring ≤ 1 :=
    (functionField.isFunctionField hF).trdeg_eq_one ▸ trdeg_le_of_injective φ Subtype.val_injective
  have heq : p = IsLocalRing.maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal_of_trdeg_le_one htr hp0)
  intro z hz
  rw [← heq] at hz
  exact (hp z).1 hz


/-! ### The centre of a place of `k(C)` -/

section Place

open TauCeti

variable (hF)

/-- A valuation of a place `Q` of `k(C)` is `< 1` exactly when the valuation of its valuation
ring is. -/
private theorem Place.valuation_lt_one_iff (Q : Place k (functionField hF))
    {z : functionField hF} : Q.integers.valuation z < 1 ↔ Q.valuation z < 1 := by
  rw [Place.integers_def]
  exact (Valuation.isEquiv_valuation_valuationSubring Q.valuation).lt_one_iff_lt_one.symm

/-- The valuation ring of a place of `k(C)` is not all of `k(C)`. -/
private theorem Place.exists_notMem_integers (Q : Place k (functionField hF)) :
    ∃ z, AlgHom.id k (functionField hF) z ∉ Q.integers := by
  obtain ⟨z, -, hz⟩ := Q.exists_ne_zero_ord_eq (-1)
  refine ⟨z, fun h ↦ ?_⟩
  rw [AlgHom.id_apply, Place.mem_integers_iff_ord_nonneg, hz] at h
  exact absurd h (by decide)

variable [IsAlgClosed k]

/-- The **centre** of a place `Q` of the function field `k(C)` of an irreducible projective plane
curve `C : F = 0` over an algebraically closed field: the unique point `P ∈ C` such that the
valuation ring of `Q` dominates `𝒪_P(C)` (`center_eq_iff`). -/
noncomputable def center (Q : Place k (functionField hF)) :
    zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)) :=
  (exists_isCenter Q.algebraMap_mem_integers (Place.exists_notMem_integers hF Q)).choose

variable {hF}

/-- The valuation ring of a place dominates the local ring of `C` at its centre. -/
theorem isCenter_center (Q : Place k (functionField hF)) :
    IsCenter hF (AlgHom.id k _) Q.integers (center hF Q) :=
  (exists_isCenter Q.algebraMap_mem_integers (Place.exists_notMem_integers hF Q)).choose_spec

/-- The centre of a place `Q` is `P` iff the valuation ring of `Q` dominates `𝒪_P(C)`. -/
theorem center_eq_iff {Q : Place k (functionField hF)} :
    center hF Q = P ↔ IsCenter hF (AlgHom.id k _) Q.integers P :=
  ⟨fun h ↦ h ▸ isCenter_center Q, (isCenter_center Q).eq⟩

/-- The centre of a place `Q` is `P` iff `𝒪_P(C)` lies in the valuation ring of `Q`. -/
theorem center_eq_iff_le {Q : Place k (functionField hF)} :
    center hF Q = P ↔ (localSubring hF P).toSubring ≤ Q.integers.toSubring := by
  rw [center_eq_iff, isCenter_iff_forall_mem]
  · rfl
  · exact Place.exists_notMem_integers hF Q

variable (hF) in
/-- Every point of `C` is the centre of some place of `k(C)`: by Chevalley's extension theorem,
some place dominates `𝒪_P(C)`. -/
theorem center_surjective : Function.Surjective (center hF) := by
  intro P
  obtain ⟨z, hzm, hz0⟩ := exists_ne_zero_mem_maximalIdeal_localSubring hF P
  obtain ⟨Q, hQ1, hQ2⟩ := Place.exists_forall_mem_integers_and_valuation_lt_one
    (functionField.isFunctionField hF) (R := (localSubring hF P).toSubring)
    (fun c ↦ (algebraMap k (localSubring hF P).toSubring c).2)
    (IsLocalRing.maximalIdeal.isMaximal _).ne_top
    ((Submodule.ne_bot_iff _).2 ⟨z, hzm, hz0⟩)
  exact ⟨Q, center_eq_iff.2 (isCenter_iff.2 ⟨fun z hz ↦ hQ1 ⟨z, hz⟩,
    fun z hz ↦ (Place.valuation_lt_one_iff hF Q).2 (hQ2 z hz)⟩)⟩

variable (hF P) in
/-- Only finitely many places of `k(C)` have a given centre `P`: they are zeros of a nonzero
element of the maximal ideal of `𝒪_P(C)`. -/
theorem finite_setOf_center_eq : {Q : Place k (functionField hF) | center hF Q = P}.Finite := by
  obtain ⟨z, hzm, hz0⟩ := exists_ne_zero_mem_maximalIdeal_localSubring hF P
  refine (Place.finite_setOf_ord_pos (functionField.isFunctionField hF) z).subset fun Q hQ ↦ ?_
  have := (isCenter_iff.1 (center_eq_iff.1 hQ)).2 z hzm
  rw [AlgHom.id_apply, Place.valuation_lt_one_iff] at this
  exact (Q.valuation_lt_one_iff_ord_pos fun h ↦ hz0 (Subtype.ext h)).1 this

end Place

end PlaneCurves.Projective

end
