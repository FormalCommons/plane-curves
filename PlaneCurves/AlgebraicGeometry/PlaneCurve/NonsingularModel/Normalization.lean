/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.RegularFunctions
public import PlaneCurves.RingTheory.Conductor
public import PlaneCurves.RingTheory.Japanese
public import TauCeti.RingTheory.UniversallyJapanese

/-!
# The normalization of a plane curve near a point

Let `C : F = 0` be an irreducible projective plane curve over an algebraically closed field `k`,
with function field `K = k(C)`. Its nonsingular model is the set of places of `K`, each with its
centre on `C`. This file compares rings of functions on `C` with their integral closures in `K`,
which are holomorphy rings of sets of places.

For a form `G` of degree `m` with `F ∤ G`, the places at which the ring `A_G` of fractions
`H / Gʳ` is regular are those centred in `D(G) = {P | G(P) ≠ 0}`. So the integral closure of `A_G`
in `K` is the ring of the places over `D(G)`, and it is a finite `A_G`-module since `A_G` is a
finitely generated `k`-domain, hence Japanese.

Locally, at a point `P ∈ C`, the integral closure of `𝒪_P(C)` in `K` is the holomorphy ring of the
places over `P`. It is a finite `𝒪_P(C)`-module, since `𝒪_P(C)` is a localization of some `A_G`.
So a nonzero `t ∈ 𝒪_P(C)` carries it into `𝒪_P(C)`, and a function whose order at every place
over `P` is large enough is regular at `P`.

## Main results

* `setOf_awaySubalgebra_subset_integers`: the places at which `A_G` is regular are the places
  centred in `D(G)`.
* `restrictScalars_integralClosure_awaySubalgebra`: the integral closure of `A_G` in `K` is the
  holomorphy ring of the places centred in `D(G)`.
* `finite_integralClosure_awaySubalgebra`: it is a finite `A_G`-module.
* `isJapanese_awaySubalgebra`, `isJapanese_localSubring`: `A_G` and `𝒪_P(C)` are Japanese.
* `integralClosure_localSubring`: the integral closure of `𝒪_P(C)` in `K` is the holomorphy ring
  of the places over `P`.
* `finite_integralClosure_localSubring`: it is a finite `𝒪_P(C)`-module.
* `exists_ne_zero_mul_mem_localSubring`: a nonzero `t ∈ 𝒪_P(C)` carries it into `𝒪_P(C)`.
* `exists_forall_le_addValuation_mem_localSubring`: a function of large enough order at every
  place over `P` lies in `𝒪_P(C)`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.5
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti TauCeti.Ring
open TauCeti.AlgebraicGeometry

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
  (hF : F.IsHomogeneous d) [Fact (Irreducible F)]

/-! ### The integral closure of `A_G` -/

variable {m : ℕ} {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m) (hFG : ¬ F ∣ G)

/-- A place centred at a zero of `G` is not regular on `A_G`: for a coordinate `Xᵢ` not vanishing
at the centre, `Xᵢᵐ / G ∈ A_G` has a pole there. -/
private theorem not_subset_integers_of_eval_eq_zero {Q : Place k (functionField hF)}
    (hGQ : eval (center hF Q).1.rep G = 0) :
    ¬ (awaySubalgebra hF hG hFG : Set (functionField hF)) ⊆ Q.integers := by
  intro h
  obtain ⟨i, hi⟩ := (center hF Q).1.exists_mem_affineOpen
  have hXQ : eval (center hF Q).1.rep (X i ^ m) ≠ 0 := by
    simpa using pow_ne_zero m ((mem_affineOpen_iff _ _).1 hi)
  have hXI := notMem_of_eval_rep_ne_zero (center hF Q).2 (isHomogeneous_X_pow i m) hXQ
  have hGI := projectivePlaneCurve.notMem_ideal_of_not_dvd hF hFG
  have hmem : functionField.mk (isHomogeneous_X_pow i m) hG hGI ∈ Q.integers := by
    refine h (mem_awaySubalgebra_iff.2
      ⟨1, X i ^ m, by rw [mul_one]; exact isHomogeneous_X_pow i m, ?_⟩)
    exact functionField.mk_eq_mk_of_mul_eq _ _ _ _ _ _ (by ring)
  have hpos := (ordForm_pos_iff (Q := Q) hG).2 hGQ
  rw [ordForm_eq_addValuation_mk hG (isHomogeneous_X_pow i m) hXQ] at hpos
  have hnonneg := Q.addValuation_nonneg_iff.2 hmem
  have hone := congrArg Q.addValuation (functionField.mk_mul_mk_swap hG
    (isHomogeneous_X_pow i m) hGI hXI)
  rw [AddValuation.map_mul, AddValuation.map_one] at hone
  exact (lt_of_lt_of_le hpos (le_add_of_nonneg_right hnonneg)).ne' hone

/-- **The places at which `A_G` is regular** are the places centred in `D(G)`. -/
theorem setOf_awaySubalgebra_subset_integers :
    {Q : Place k (functionField hF) |
        (awaySubalgebra hF hG hFG : Set (functionField hF)) ⊆ Q.integers} =
      center hF ⁻¹' {P | eval P.1.rep G ≠ 0} := by
  ext Q
  refine ⟨fun h hGQ ↦ not_subset_integers_of_eval_eq_zero hF hG hFG hGQ h,
    fun hGQ z hz ↦ ?_⟩
  exact localSubring_center_le Q (awaySubalgebra_le_localSubring hF hG hFG hGQ hz)

/-- **The integral closure of `A_G`** in `k(C)` is the holomorphy ring of the places centred in
`D(G)`. -/
theorem restrictScalars_integralClosure_awaySubalgebra :
    (integralClosure (awaySubalgebra hF hG hFG) (functionField hF)).restrictScalars k =
      holomorphyRing (center hF ⁻¹' {P | eval P.1.rep G ≠ 0}) := by
  rw [restrictScalars_integralClosure_eq_holomorphyRing (functionField.isFunctionField hF),
    setOf_awaySubalgebra_subset_integers]

omit [IsAlgClosed k] in
/-- The module structure of the integral closure in `k(C)` of a `k`-subalgebra `S` over `S`. This
shortcut spares instance search a slow detour through the normed instances on `k(C)`. -/
noncomputable instance moduleIntegralClosure (S : Subalgebra k (functionField hF)) :
    Module S (integralClosure S (functionField hF)) :=
  @Algebra.toModule _ _ _ _ (Subalgebra.algebra _)

omit [IsAlgClosed k] in
/-- `A_G` is a Japanese domain: it is a domain of finite type over the field `k`. -/
instance isJapanese_awaySubalgebra : IsJapanese (awaySubalgebra hF hG hFG) :=
  IsUniversallyJapanese.isJapanese k _

omit [IsAlgClosed k] in
/-- **The integral closure of `A_G` in `k(C)` is a finite `A_G`-module**: `A_G` is Japanese, and
`k(C)` is a finitely generated extension of its fraction field. -/
theorem finite_integralClosure_awaySubalgebra :
    Module.Finite (awaySubalgebra hF hG hFG) (integralClosure (awaySubalgebra hF hG hFG)
      (functionField hF)) := by
  have := (functionField.isFunctionField hF).essFiniteType
  have : Algebra.EssFiniteType (awaySubalgebra hF hG hFG) (functionField hF) :=
    .of_comp k _ _
  exact IsJapanese.finite_integralClosure_of_injective Subtype.val_injective

/-! ### The local form at a point -/

variable (P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)))

omit [IsAlgClosed k] in
/-- **The local ring at a point is Japanese**: it is the localization of the ring `A_{Xᵢ}` of
a coordinate `Xᵢ` not vanishing at `P`. -/
instance isJapanese_localSubring : IsJapanese (localSubring hF P).toSubring := by
  obtain ⟨i, hi⟩ := P.1.exists_mem_affineOpen
  have hXP : eval P.1.rep (X i) ≠ 0 := by simpa using (mem_affineOpen_iff _ _).1 hi
  have hFX : ¬ F ∣ X i := fun h ↦ notMem_of_eval_rep_ne_zero P.2 (isHomogeneous_X k i) hXP
    ((projectivePlaneCurve.mem_ideal_iff hF).2 h)
  let := (awaySubalgebraInclusion hF (isHomogeneous_X k i) hFX hXP).toAlgebra
  have := isLocalization_localSubring_awaySubalgebra hF (isHomogeneous_X k i) hFX one_ne_zero hXP
  exact isJapanese_of_isLocalization (R := awaySubalgebra hF (isHomogeneous_X k i) hFX)
    ((IsLocalRing.maximalIdeal (localSubring hF P).toSubring).comap
      (awaySubalgebraInclusion hF (isHomogeneous_X k i) hFX hXP)).primeCompl _

/-- **The integral closure of `𝒪_P(C)`** in `k(C)` is the holomorphy ring of the places over
`P`. -/
theorem integralClosure_localSubring :
    (integralClosure (localSubring hF P).toSubring (functionField hF)).toSubring =
      (holomorphyRing (placesOver hF P)).toSubring := by
  ext z
  simp only [Subalgebra.mem_toSubring]
  refine ⟨fun hz ↦ mem_holomorphyRing_iff.2 fun Q hQ ↦ Q.mem_integers_of_isIntegral
    (fun r ↦ mem_placesOver_iff_le.1 hQ r.2) hz, fun hz ↦ ?_⟩
  have h := restrictScalars_integralClosure_eq_holomorphyRing (functionField.isFunctionField hF)
    (regularFunctions hF {P})
  have hset : {Q : Place k (functionField hF) |
      (regularFunctions hF {P} : Set (functionField hF)) ⊆ Q.integers} = placesOver hF P := by
    ext Q
    rw [mem_placesOver_iff_le, ← regularFunctions_singleton hF P]
    exact Iff.rfl
  rw [hset] at h
  have hz' : z ∈ (integralClosure (regularFunctions hF {P}) (functionField hF)).restrictScalars k
    := h ▸ hz
  change IsIntegral (localSubring hF P).toSubring z
  rw [← regularFunctions_singleton hF P]
  exact hz'

omit [IsAlgClosed k] in
/-- **The integral closure of `𝒪_P(C)` in `k(C)` is a finite `𝒪_P(C)`-module.** -/
theorem finite_integralClosure_localSubring :
    Module.Finite (localSubring hF P).toSubring
      (integralClosure (localSubring hF P).toSubring (functionField hF)) :=
  IsJapanese.finite_integralClosure (functionField hF) (functionField hF)

/-- **A conductor element at a point**: some nonzero `t ∈ 𝒪_P(C)` carries every function regular
at the places over `P` into `𝒪_P(C)`. -/
theorem exists_ne_zero_mul_mem_localSubring :
    ∃ t ∈ (localSubring hF P).toSubring, t ≠ 0 ∧
      ∀ z ∈ holomorphyRing (placesOver hF P), t * z ∈ (localSubring hF P).toSubring := by
  have := finite_integralClosure_localSubring hF P
  obtain ⟨a, ha, hac⟩ := TauCeti.Algebra.exists_mem_conductor_of_isLocalization
    (A := (localSubring hF P).toSubring)
    (B := integralClosure (localSubring hF P).toSubring (functionField hF))
    (L := functionField hF) (nonZeroDivisors _) Subtype.val_injective
  refine ⟨a, a.2, fun h ↦ nonZeroDivisors.ne_zero ha (Subtype.ext h), fun z hz ↦ ?_⟩
  have hz' : z ∈ integralClosure (localSubring hF P).toSubring (functionField hF) := by
    rw [← Subalgebra.mem_toSubring, integralClosure_localSubring]
    exact hz
  obtain ⟨c, hc⟩ := TauCeti.Algebra.mem_conductor_iff.1 hac ⟨z, hz'⟩
  have hc' : (c : functionField hF) = a * z := congrArg Subtype.val hc
  exact hc' ▸ c.2

/-- **Large orders over a point give regularity at the point**: for some `e`, every function whose
order at each place over `P` is at least `e` lies in `𝒪_P(C)`. -/
theorem exists_forall_le_addValuation_mem_localSubring :
    ∃ e : ℕ, ∀ z : functionField hF,
      (∀ Q ∈ placesOver hF P, (e : WithTop ℤ) ≤ Q.addValuation z) →
        z ∈ (localSubring hF P).toSubring := by
  obtain ⟨t, -, ht0, ht⟩ := exists_ne_zero_mul_mem_localSubring hF P
  refine ⟨(placesOver_finite hF P).toFinset.sup fun Q ↦ (Q.ord t).toNat, fun z hz ↦ ?_⟩
  rcases eq_or_ne z 0 with rfl | hz0
  · exact zero_mem _
  have hzt : z / t ∈ holomorphyRing (placesOver hF P) :=
    mem_holomorphyRing_iff_forall_ord_nonneg.2 fun Q hQ ↦ by
      have h := hz Q hQ
      rw [Q.addValuation_of_ne_zero hz0] at h
      have hle := Finset.le_sup (f := fun Q ↦ (Q.ord t).toNat)
        ((placesOver_finite hF P).mem_toFinset.2 hQ)
      have h' : ((((placesOver_finite hF P).toFinset.sup fun Q ↦ (Q.ord t).toNat : ℕ) : ℤ)) ≤
          Q.ord z := by exact_mod_cast h
      rw [Q.ord_div hz0 ht0]
      have := Int.self_le_toNat (Q.ord t)
      omega
  simpa [mul_div_cancel₀ _ ht0] using ht _ hzt

end PlaneCurves.Projective

end
