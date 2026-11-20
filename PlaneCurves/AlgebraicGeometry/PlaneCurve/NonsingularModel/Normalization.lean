/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.SimplePoint
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Finiteness
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.RegularFunctions
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.LinearSubvariety
public import PlaneCurves.FieldTheory.FunctionField.HolomorphyRing.Length
public import PlaneCurves.RingTheory.Adjoin.FG
public import PlaneCurves.RingTheory.Conductor
public import PlaneCurves.RingTheory.Japanese
public import PlaneCurves.RingTheory.KrullDimension.TrdegOne
public import TauCeti.FieldTheory.FunctionField.AffineModel.IntegralClosure
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus
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

For every set `U` of points of `C`, the ring `Γ(U)` of functions regular on `U` has as its integral
closure in `K` the ring `Γ(U')` of the places centred in `U`: a place centred outside `U` is the
pole of some function regular on `U`. Near a point `P`, a basic open set `U = D(G)` avoiding a
given finite set has a finitely generated ring `Γ(U)`, caught between `A_G` and its integral
closure, and the normalization `Γ(U')` is an affine model of `K`, finite over `Γ(U)`, with
`Γ(U')/Γ(U)` finite-dimensional over `k`.

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
* `setOf_regularFunctions_subset_integers`, `restrictScalars_integralClosure_regularFunctions`:
  the places at which `Γ(U)` is regular are those centred in `U`, so the integral closure of
  `Γ(U)` in `K` is `Γ(U')`, for every set `U`.
* `regularFunctions_univ`: a function regular at every point of `C` is constant.
* `exists_basicOpen_normalization`: a basic open neighbourhood `D(G)` of `P` avoiding a finite
  set.
* `finiteType_regularFunctions_basicOpen`, `isFractionRing_regularFunctions_basicOpen`,
  `finiteType_holomorphyRing_basicOpen`, `isDedekindDomain_holomorphyRing_basicOpen`,
  `isFractionRing_holomorphyRing_basicOpen`, `finite_integralClosure_regularFunctions_basicOpen`,
  `exists_ne_zero_mul_mem_regularFunctions_basicOpen`, `finite_quotient_regularFunctions_basicOpen`:
  the rings of `D(G)` and of the places over it.
* `finite_normalization_spec`: finiteness of the normalization of a plane curve near a point.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.5, Lemma 2 and Problem 7.20
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti TauCeti.Ring
open TauCeti.AlgebraicGeometry PlaneCurves.Projective

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
/-- The algebra structure of the integral closure in `k(C)` of a `k`-subalgebra `S` over `S`, a
shortcut like `moduleIntegralClosure`. -/
noncomputable instance algebraIntegralClosure (S : Subalgebra k (functionField hF)) :
    Algebra S (integralClosure S (functionField hF)) :=
  Subalgebra.algebra _

omit [IsAlgClosed k] in
/-- The action of a `k`-subalgebra `S` of `k(C)` on its integral closure in `k(C)`, a shortcut
like `moduleIntegralClosure`. -/
noncomputable instance smulIntegralClosure (S : Subalgebra k (functionField hF)) :
    SMul S (integralClosure S (functionField hF)) :=
  Algebra.toSMul

omit [IsAlgClosed k] in
/-- The integral closure in `k(C)` of a `k`-subalgebra `S` is an `S`-algebra between `S` and
`k(C)`. -/
instance isScalarTower_integralClosure (S : Subalgebra k (functionField hF)) :
    IsScalarTower S (integralClosure S (functionField hF)) (functionField hF) :=
  ⟨fun x y z ↦ mul_assoc (x : functionField hF) y z⟩

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

/-! ### The integral closure of `Γ(U)`, for every set `U` -/

variable {hF} in
/-- A place `Q` not centred in `U` is not regular on `Γ(U)`: some `w ∈ Γ(U)` has a pole at `Q`.
Such a `w` is built from a function `x` whose only pole is `Q` and a function `y` regular away
from `Q` with large orders at the places over the multiple points of `C` in `U`. -/
private theorem exists_mem_regularFunctions_ord_neg
    {U : Set (zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)))}
    {Q : Place k (functionField hF)} (hQ : center hF Q ∉ U) :
    ∃ w ∈ regularFunctions hF U, Q.ord w < 0 := by
  classical
  have hK := functionField.isFunctionField hF
  set M : Set (zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))) :=
    {P' | P' ∈ U ∧ IsMultiplePoint F P'.1}
  have hM : M.Finite :=
    (((finite_setOf_isMultiplePoint_of_irreducible hF Fact.out).preimage
      Subtype.val_injective.injOn).subset fun P' hP' ↦ hP'.2)
  have hZ : (center hF ⁻¹' M).Finite := hM.preimage' fun P' _ ↦
    (placesOver_finite hF P').subset fun _ hR ↦ mem_placesOver_iff.2 hR
  choose e he using fun P' ↦ exists_forall_le_addValuation_mem_localSubring hF P'
  set E : ℕ := hM.toFinset.sup e
  obtain ⟨u, hu0, hu⟩ := exists_holomorphyRing_forall_ord_eq (S := hZ.toFinset) fun _ ↦ E
  obtain ⟨y, hy0, hy, hyu⟩ := exists_ne_zero_mem_holomorphyRing_and_mul_mem hK
    (S := {Q}ᶜ) (Q := Q) (by simp) (u : functionField hF)⁻¹
  obtain ⟨x, hxQ, hx⟩ := Q.exists_ord_neg_and_forall_ne_ord_nonneg hK
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxQ
  set N : ℕ := (Q.ord y).toNat + 1
  have hw0 : x ^ N * y ≠ 0 := mul_ne_zero (pow_ne_zero _ hx0) hy0
  have hord : ∀ R : Place k (functionField hF), R.ord (x ^ N * y) = N * R.ord x + R.ord y :=
    fun R ↦ by rw [R.ord_mul (pow_ne_zero _ hx0) hy0, R.ord_pow]
  have hyR : ∀ R : Place k (functionField hF), R ≠ Q → 0 ≤ R.ord y := fun R hR ↦
    mem_holomorphyRing_iff_forall_ord_nonneg.1 hy R hR
  have hR : ∀ R : Place k (functionField hF), R ≠ Q → 0 ≤ R.ord (x ^ N * y) := fun R hRQ ↦ by
    rw [hord]
    exact add_nonneg (mul_nonneg (by positivity) (hx R hRQ)) (hyR R hRQ)
  have hRZ : ∀ R ∈ center hF ⁻¹' M, (E : ℤ) ≤ R.ord (x ^ N * y) := fun R hRM ↦ by
    have hRQ : R ≠ Q := by rintro rfl; exact hQ hRM.1
    have h := mem_holomorphyRing_iff_forall_ord_nonneg.1 hyu R hRQ
    rw [R.ord_mul hy0 (inv_ne_zero hu0), R.ord_inv, hu R (hZ.mem_toFinset.2 hRM)] at h
    rw [hord]
    have := mul_nonneg (Int.natCast_nonneg N) (hx R hRQ)
    omega
  refine ⟨x ^ N * y, mem_regularFunctions_iff.2 fun P' hP' ↦ ?_, ?_⟩
  · by_cases hm : IsMultiplePoint F P'.1
    · refine he P' _ fun R hR ↦ ?_
      have hle : e P' ≤ E := Finset.le_sup (hM.mem_toFinset.2 ⟨hP', hm⟩)
      have h := hRZ R (show center hF R ∈ M from (mem_placesOver_iff.1 hR) ▸ ⟨hP', hm⟩)
      rw [R.addValuation_of_ne_zero hw0]
      exact_mod_cast (show (e P' : ℤ) ≤ R.ord (x ^ N * y) by omega)
    · have hs : IsSimplePoint F P'.1 := by
        by_contra h
        exact hm (isMultiplePoint_iff_not_isSimplePoint.2 ⟨(mem_zeroLocus_ideal_iff hF).1 P'.2, h⟩)
      have hne : placeAt hF hs ≠ Q := by
        rintro rfl
        exact hQ ((center_placeAt hs).symm ▸ hP')
      rw [← integers_toSubring_placeAt hs, ValuationSubring.mem_toSubring]
      exact (placeAt hF hs).mem_integers_iff_ord_nonneg.2 (hR _ hne)
  · rw [hord]
    have h1 : (Q.ord y) ≤ (Q.ord y).toNat := Int.self_le_toNat _
    have h2 : ((N : ℕ) : ℤ) = (Q.ord y).toNat + 1 := by push_cast [N]; rfl
    nlinarith

/-- **The places at which `Γ(U)` is regular** are the places centred in `U`, for every set `U` of
points of `C`. -/
theorem setOf_regularFunctions_subset_integers
    (U : Set (zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)))) :
    {Q : Place k (functionField hF) |
        (regularFunctions hF U : Set (functionField hF)) ⊆ Q.integers} = center hF ⁻¹' U := by
  ext Q
  refine ⟨fun h ↦ ?_, fun hQ z hz ↦
    localSubring_center_le Q (mem_regularFunctions_iff.1 hz _ hQ)⟩
  by_contra hQ
  obtain ⟨w, hw, hwQ⟩ := exists_mem_regularFunctions_ord_neg hQ
  exact hwQ.not_ge (Q.mem_integers_iff_ord_nonneg.1 (h hw))

/-- **The integral closure of `Γ(U)`** in `k(C)` is the ring `Γ(U')` of the places centred in
`U`, for every set `U` of points of `C`. This is the last sentence of Problem 7.20 (c) of
Fulton, for every subset `U` and not only for open ones. -/
theorem restrictScalars_integralClosure_regularFunctions
    (U : Set (zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)))) :
    (integralClosure (regularFunctions hF U) (functionField hF)).restrictScalars k =
      holomorphyRing (center hF ⁻¹' U) := by
  rw [restrictScalars_integralClosure_eq_holomorphyRing (functionField.isFunctionField hF),
    setOf_regularFunctions_subset_integers]

/-- **A function regular at every point of `C` is constant.** -/
@[simp]
theorem regularFunctions_univ : regularFunctions hF Set.univ = ⊥ := by
  refine le_bot_iff.1 ((regularFunctions_le_holomorphyRing hF Set.univ).trans ?_)
  rw [Set.preimage_univ, holomorphyRing_univ (functionField.isFunctionField hF),
    IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure k _),
    IntermediateField.bot_toSubalgebra]

/-! ### The ring of a basic open set `D(G)` -/

include hG hFG in
omit [IsAlgClosed k] [Fact (Irreducible F)] in
/-- A form not divisible by `F` with a zero on `C` has positive degree. -/
private theorem ne_zero_of_exists_eval_eq_zero
    (hz : ∃ Q : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)),
      eval Q.1.rep G = 0) : m ≠ 0 := by
  rintro rfl
  obtain ⟨Q, hQ⟩ := hz
  have hG0 : G ≠ 0 := by rintro rfl; exact hFG (dvd_zero F)
  have hGC := totalDegree_eq_zero_iff_eq_C.1 (hG.totalDegree hG0)
  rw [hGC, eval_C] at hQ
  exact hG0 (by rw [hGC, hQ, C_0])

include hG hFG in
/-- **`Γ(D(G))` is a finitely generated `k`-algebra**: it lies between `A_G` and the integral
closure of `A_G` in `k(C)`, which is a finite `A_G`-module. -/
theorem finiteType_regularFunctions_basicOpen :
    Algebra.FiniteType k (regularFunctions hF {P | eval P.1.rep G ≠ 0}) := by
  have hfin := finite_integralClosure_awaySubalgebra hF hG hFG
  have : IsNoetherianRing (awaySubalgebra hF hG hFG) := Algebra.FiniteType.isNoetherianRing k _
  refine (Subalgebra.fg_iff_finiteType _).1 <| Subalgebra.fg_of_le_of_subset_fg
    ((Subalgebra.fg_iff_finiteType _).2 inferInstance)
    (awaySubalgebra_le_regularFunctions hF hG hFG)
    (M := Subalgebra.toSubmodule (integralClosure (awaySubalgebra hF hG hFG) (functionField hF)))
    (Module.Finite.iff_fg.1 hfin) fun z hz ↦ ?_
  have h := regularFunctions_le_holomorphyRing hF _ hz
  rw [← restrictScalars_integralClosure_awaySubalgebra hF hG hFG] at h
  exact h

include hG hFG in
omit [IsAlgClosed k] in
/-- **`k(C)` is the fraction field of `Γ(D(G))`**, if `G` has a zero on `C`: it is already the
fraction field of `A_G ⊆ Γ(D(G))`. -/
theorem isFractionRing_regularFunctions_basicOpen
    (hz : ∃ Q : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)),
      eval Q.1.rep G = 0) :
    IsFractionRing (regularFunctions hF {P | eval P.1.rep G ≠ 0}) (functionField hF) := by
  have := isFractionRing_awaySubalgebra hF hG hFG (ne_zero_of_exists_eval_eq_zero hF hG hFG hz)
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := awaySubalgebra hF hG hFG) z
  exact ⟨⟨_, awaySubalgebra_le_regularFunctions hF hG hFG a.2⟩,
    ⟨_, awaySubalgebra_le_regularFunctions hF hG hFG b.2⟩, rfl⟩

include hG hFG in
/-- **The integral closure of `Γ(D(G))` in `k(C)` is a finite `Γ(D(G))`-module**: `Γ(D(G))` is
a domain of finite type over `k`, hence Japanese. -/
theorem finite_integralClosure_regularFunctions_basicOpen :
    Module.Finite (regularFunctions hF {P | eval P.1.rep G ≠ 0})
      (integralClosure (regularFunctions hF {P | eval P.1.rep G ≠ 0}) (functionField hF)) := by
  have := finiteType_regularFunctions_basicOpen hF hG hFG
  have : IsJapanese (regularFunctions hF {P | eval P.1.rep G ≠ 0}) :=
    IsUniversallyJapanese.isJapanese k _
  have := (functionField.isFunctionField hF).essFiniteType
  have : Algebra.EssFiniteType (regularFunctions hF {P | eval P.1.rep G ≠ 0})
    (functionField hF) := .of_comp k _ _
  exact IsJapanese.finite_integralClosure_of_injective Subtype.val_injective

include hG hFG in
/-- Only finitely many places are centred outside `D(G)`: the zeros of `G` on `C` are finitely
many, and so are the places over each. -/
theorem finite_compl_preimage_center_basicOpen :
    (center hF ⁻¹' {P | eval P.1.rep G ≠ 0})ᶜ.Finite := by
  rw [← Set.preimage_compl]
  have hfin : {P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)) |
      eval P.1.rep G ≠ 0}ᶜ.Finite := by
    refine ((finite_zeroLocus_pair_of_isRelPrime hF hG
      ((Fact.out : Irreducible F).isRelPrime_iff_not_dvd.2 hFG)).preimage
      Subtype.val_injective.injOn).subset fun P hP ↦ ?_
    rw [Set.mem_preimage, mem_zeroLocus_iff_eval_rep (by
      rintro f (rfl | rfl)
      exacts [⟨d, hF⟩, ⟨m, hG⟩])]
    rintro f (rfl | rfl)
    · exact (mem_zeroLocus_ideal_iff hF).1 P.2
    · exact not_not.1 hP
  exact hfin.preimage' fun P _ ↦
    (placesOver_finite hF P).subset fun _ hR ↦ mem_placesOver_iff.2 hR

include hG hFG in
/-- **The ring of the places over `D(G)` is a finitely generated `k`-algebra.** -/
theorem finiteType_holomorphyRing_basicOpen :
    Algebra.FiniteType k (holomorphyRing (center hF ⁻¹' {P | eval P.1.rep G ≠ 0})) := by
  have h := finiteType_holomorphyRing_compl (functionField.isFunctionField hF)
    (finite_compl_preimage_center_basicOpen hF hG hFG)
  rwa [compl_compl] at h

include hG hFG in
/-- **The ring of the places over `D(G)` is a Dedekind domain.** -/
theorem isDedekindDomain_holomorphyRing_basicOpen :
    IsDedekindDomain (holomorphyRing (center hF ⁻¹' {P | eval P.1.rep G ≠ 0})) := by
  have h := isDedekindDomain_holomorphyRing_compl (functionField.isFunctionField hF)
    (finite_compl_preimage_center_basicOpen hF hG hFG)
  rwa [compl_compl] at h

/-- **`k(C)` is the fraction field of the ring of the places over `D(G)`**, if `G` has a zero on
`C`: a place over that zero is not centred in `D(G)`. -/
theorem isFractionRing_holomorphyRing_basicOpen
    (hz : ∃ Q : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)),
      eval Q.1.rep G = 0) :
    IsFractionRing (holomorphyRing (center hF ⁻¹' {P | eval P.1.rep G ≠ 0}))
      (functionField hF) := by
  obtain ⟨Q, hQ⟩ := hz
  obtain ⟨R, hR⟩ := placesOver_nonempty hF Q
  refine isFractionRing_holomorphyRing (functionField.isFunctionField hF) ⟨R, fun h ↦ h ?_⟩
  rwa [mem_placesOver_iff.1 hR]

include hG hFG in
/-- **A conductor element on `D(G)`**, if `G` has a zero on `C`: some nonzero `t ∈ Γ(D(G))`
carries the ring of the places over `D(G)` into `Γ(D(G))`. -/
theorem exists_ne_zero_mul_mem_regularFunctions_basicOpen
    (hz : ∃ Q : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)),
      eval Q.1.rep G = 0) :
    ∃ t ∈ regularFunctions hF {P | eval P.1.rep G ≠ 0}, t ≠ 0 ∧
      ∀ z ∈ holomorphyRing (center hF ⁻¹' {P | eval P.1.rep G ≠ 0}),
        t * z ∈ regularFunctions hF {P | eval P.1.rep G ≠ 0} := by
  have := finite_integralClosure_regularFunctions_basicOpen hF hG hFG
  have := isFractionRing_regularFunctions_basicOpen hF hG hFG hz
  obtain ⟨a, ha, hac⟩ := TauCeti.Algebra.exists_mem_conductor_of_isLocalization
    (A := regularFunctions hF {P | eval P.1.rep G ≠ 0})
    (B := integralClosure (regularFunctions hF {P | eval P.1.rep G ≠ 0}) (functionField hF))
    (L := functionField hF) (nonZeroDivisors _) Subtype.val_injective
  refine ⟨a, a.2, fun h ↦ nonZeroDivisors.ne_zero ha (Subtype.ext h), fun z hz' ↦ ?_⟩
  rw [← restrictScalars_integralClosure_regularFunctions] at hz'
  obtain ⟨c, hc⟩ := TauCeti.Algebra.mem_conductor_iff.1 hac ⟨z, hz'⟩
  have hc' : (c : functionField hF) = a * z := congrArg Subtype.val hc
  exact hc' ▸ c.2

include hG hFG in
/-- **`Γ(D(G)')/Γ(D(G))` is finite-dimensional**, if `G` has a zero on `C`: the cokernel of
`Γ(D(G)) ↪ Γ(D(G)')` embeds into `Γ(D(G))/(t)` by `z ↦ t z`, for a conductor element `t`, and
that quotient of the ring of a curve is finite-dimensional over `k`. -/
theorem finite_quotient_regularFunctions_basicOpen
    (hz : ∃ Q : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)),
      eval Q.1.rep G = 0) :
    Module.Finite k (holomorphyRing (center hF ⁻¹' {P | eval P.1.rep G ≠ 0}) ⧸
      LinearMap.range (Subalgebra.inclusion
        (regularFunctions_le_holomorphyRing hF {P | eval P.1.rep G ≠ 0})).toLinearMap) := by
  obtain ⟨t, ht, ht0, htz⟩ := exists_ne_zero_mul_mem_regularFunctions_basicOpen hF hG hFG hz
  have := finiteType_regularFunctions_basicOpen hF hG hFG
  have := isFractionRing_regularFunctions_basicOpen hF hG hFG hz
  have htr : Algebra.trdeg k (regularFunctions hF {P | eval P.1.rep G ≠ 0}) ≤ 1 := by
    have h := Algebra.lift_trdeg_eq_of_isFractionRing k
      (regularFunctions hF {P | eval P.1.rep G ≠ 0}) (functionField hF)
    rw [Cardinal.lift_id, Cardinal.lift_id, (functionField.isFunctionField hF).trdeg_eq_one] at h
    exact h.le
  have ht0' : (⟨t, ht⟩ : regularFunctions hF {P | eval P.1.rep G ≠ 0}) ≠ 0 :=
    fun h ↦ ht0 (congrArg Subtype.val h)
  have := Module.finite_quotient_span_singleton_of_trdeg_le_one htr ht0'
  let f : holomorphyRing (center hF ⁻¹' {P | eval P.1.rep G ≠ 0}) →ₗ[k]
      regularFunctions hF {P | eval P.1.rep G ≠ 0} ⧸
        Ideal.span {(⟨t, ht⟩ : regularFunctions hF {P | eval P.1.rep G ≠ 0})} :=
    (Ideal.Quotient.mkₐ k _).toLinearMap ∘ₗ
      { toFun z := ⟨t * z, htz z z.2⟩
        map_add' _ _ := Subtype.ext (mul_add _ _ _)
        map_smul' _ _ := Subtype.ext (mul_smul_comm _ _ _) }
  have hker : LinearMap.ker f = LinearMap.range (Subalgebra.inclusion
      (regularFunctions_le_holomorphyRing hF {P | eval P.1.rep G ≠ 0})).toLinearMap := by
    ext z
    simp only [LinearMap.mem_ker, f, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton',
      LinearMap.mem_range]
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨a, Subtype.ext ?_⟩
      have ha' : (a : functionField hF) * t = t * z := congrArg Subtype.val ha
      exact mul_right_cancel₀ ht0 (ha'.trans (mul_comm _ _))
    · rintro ⟨y, rfl⟩
      exact ⟨y, Subtype.ext (mul_comm _ _)⟩
  exact Module.Finite.of_injective (Submodule.liftQ _ f hker.ge)
    (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ hker.le))

/-! ### The milestone -/

/-- **A basic open neighbourhood avoiding a finite set.** For a point `P` of `C` and a finite set
`S` of points of `C` not containing `P`, there is a form `G` not divisible by `F` with
`G(P) ≠ 0`, vanishing on `S` and at some point of `C`. So `D(G)` is a neighbourhood of `P`
disjoint from `S`, and not all of `C`. -/
theorem exists_basicOpen_normalization
    (P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)))
    {S : Set (zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)))}
    (hS : S.Finite) (hPS : P ∉ S) :
    ∃ (m : ℕ) (G : MvPolynomial (Fin 3) k) (_ : G.IsHomogeneous m) (_ : ¬ F ∣ G),
      eval P.1.rep G ≠ 0 ∧ (∀ s ∈ S, eval s.1.rep G = 0) ∧
      ∃ Q : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)),
        eval Q.1.rep G = 0 := by
  classical
  have hinf : (zeroLocus (projectivePlaneCurve.ideal hF :
      Set (MvPolynomial (Fin 3) k))).Infinite :=
    zeroLocus_ideal hF ▸ zeroLocus_singleton_infinite (n := 2) le_rfl hF
      (hF.degree_ne_zero_of_irreducible Fact.out)
  obtain ⟨P₀, hP₀, hP₀P⟩ := (hinf.sdiff (Set.finite_singleton P.1)).nonempty
  obtain ⟨m, G, hG, hGP, hGS⟩ := exists_isHomogeneous_eval_rep_ne_zero_forall_eval_rep_eq_zero
    P.1 ((hS.image Subtype.val).insert P₀) (by
      rintro (h | ⟨s, hs, h⟩)
      · exact hP₀P h.symm
      · exact hPS (Subtype.ext h ▸ hs))
  refine ⟨m, G, hG, fun ⟨H, hH⟩ ↦ hGP ?_, hGP, fun s hs ↦ hGS s.1 (Or.inr ⟨s, hs, rfl⟩),
    ⟨P₀, hP₀⟩, hGS P₀ (Or.inl rfl)⟩
  rw [hH, eval_mul, (mem_zeroLocus_ideal_iff hF).1 P.2, zero_mul]

/-- **Finiteness of the normalization of a plane curve near a point.** Let `C : F = 0` be an
irreducible projective plane curve over an algebraically closed field, with nonsingular model
the places of `k(C)` and their centres. For `P ∈ C` and a finite `S ⊆ C` with `P ∉ S` there is
a basic open set `U = D(G) ∋ P` with `U ∩ S = ∅`, whose ring `Γ(U)` is a finitely generated
`k`-algebra with fraction field `k(C)`, such that (1) the ring `Γ(U')` of the places `U'` over
`U` is an affine model of `k(C)`, (2) the integral closure of `Γ(U)` is a finite `Γ(U)`-module,
(3) `t Γ(U') ⊆ Γ(U)` for some `t ≠ 0` in `Γ(U)`, and (4) `Γ(U') / Γ(U)` is finite-dimensional
over `k`. Moreover, for every `U ⊆ C`, `Γ(U')` is the integral closure of `Γ(U)` in `k(C)`.

In (1), `Γ(U')` is a finitely generated `k`-algebra and a Dedekind domain with fraction field
`k(C)`; Tau Ceti's `holomorphyRingHeightOneSpectrumEquiv` then identifies the places over `U`
with the maximal ideals of `Γ(U')`.

Milestone: *Finiteness of the normalization of a plane curve near a point*. -/
theorem finite_normalization_spec
    (P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)))
    {S : Set (zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)))}
    (hS : S.Finite) (hPS : P ∉ S) :
    (∃ U : Set (zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))),
      (∃ (m : ℕ) (G : MvPolynomial (Fin 3) k), G.IsHomogeneous m ∧ ¬ F ∣ G ∧
        U = {P' | eval P'.1.rep G ≠ 0}) ∧
      P ∈ U ∧ Disjoint U S ∧
      Algebra.FiniteType k (regularFunctions hF U) ∧
      IsFractionRing (regularFunctions hF U) (functionField hF) ∧
      -- (1)
      Algebra.FiniteType k (holomorphyRing (center hF ⁻¹' U)) ∧
      IsDedekindDomain (holomorphyRing (center hF ⁻¹' U)) ∧
      IsFractionRing (holomorphyRing (center hF ⁻¹' U)) (functionField hF) ∧
      -- (2)
      Module.Finite (regularFunctions hF U)
        (integralClosure (regularFunctions hF U) (functionField hF)) ∧
      -- (3)
      (∃ t ∈ regularFunctions hF U, t ≠ 0 ∧
        ∀ z ∈ holomorphyRing (center hF ⁻¹' U), t * z ∈ regularFunctions hF U) ∧
      -- (4)
      Module.Finite k (holomorphyRing (center hF ⁻¹' U) ⧸
        LinearMap.range
          (Subalgebra.inclusion (regularFunctions_le_holomorphyRing hF U)).toLinearMap)) ∧
    ∀ U : Set (zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))),
      (integralClosure (regularFunctions hF U) (functionField hF)).restrictScalars k =
        holomorphyRing (center hF ⁻¹' U) := by
  obtain ⟨m, G, hG, hFG, hGP, hGS, hz⟩ := exists_basicOpen_normalization hF P hS hPS
  exact ⟨⟨_, ⟨m, G, hG, hFG, rfl⟩, hGP, Set.disjoint_left.2 fun s hs hsS ↦ hs (hGS s hsS),
    finiteType_regularFunctions_basicOpen hF hG hFG,
    isFractionRing_regularFunctions_basicOpen hF hG hFG hz,
    finiteType_holomorphyRing_basicOpen hF hG hFG,
    isDedekindDomain_holomorphyRing_basicOpen hF hG hFG,
    isFractionRing_holomorphyRing_basicOpen hF hz,
    finite_integralClosure_regularFunctions_basicOpen hF hG hFG,
    exists_ne_zero_mul_mem_regularFunctions_basicOpen hF hG hFG hz,
    finite_quotient_regularFunctions_basicOpen hF hG hFG hz⟩,
    restrictScalars_integralClosure_regularFunctions hF⟩

end PlaneCurves.Projective

end
