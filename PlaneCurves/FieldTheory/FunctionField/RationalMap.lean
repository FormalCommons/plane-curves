/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.LocalRing.LocalSubring
public import PlaneCurves.RingTheory.KrullDimension.TrdegOne
public import TauCeti.FieldTheory.FunctionField.Basic

/-!
# Rational maps of curves

Following the function-field representation of rational maps (Fulton, §6.6), a dominating
rational map `C' ⇢ C` of affine curves with coordinate rings `R`, `R'` and function fields
`K = k(C)`, `K' = k(C')` is a `k`-algebra map `φ : K →ₐ[k] K'`. A rational map `C' ⇢ C` that may
be constant is a `k`-algebra map `ψ : R →ₐ[k] K'`. Points of `C` are maximal ideals of `R`, and
local rings are local subrings of the function field. The map is defined at a point `P'` of `C'`
with value `Q` when `𝒪_{P'}(C')` dominates `φ(𝒪_Q(C))`, in Mathlib's domination order on
`LocalSubring`.

## Main definitions

* `LocalSubring.atPrime K p`: the localization `R_p` of a domain `R` at a prime `p`, as a local
  subring of the fraction field `K`.
* `LocalSubring.IsCentre B ψ p`: `ψ : R →+* L` maps `R` into the local subring `B` of the field
  `L`, and `p` is the preimage of the maximal ideal of `B`.

## Main results

* `LocalSubring.le_iff_of_field`: domination of local subrings of a field in terms of inverses.
* `LocalSubring.map_atPrime_le_iff`: `B` dominates `φ(R_p)` iff `p` is the centre of `B` on `R`.
* `LocalSubring.IsCentre.isMaximal`: the centre of a local ring of a finitely generated domain
  at a maximal ideal is a maximal ideal.
* `LocalSubring.finite_setOf_not_forall_mem_atPrime`: a rational map to an affine variety is
  defined at all but finitely many points of a curve.
* `TauCeti.IsFunctionField.finite_of_isFunctionField`: a function field of one variable is
  finite over every function field below it.
* `PlaneCurves.dominatingRationalMap_spec`: the milestone *Dominating rational maps correspond
  to function-field embeddings*, in its curve form.
* `PlaneCurves.birational_spec`: the milestone *Birational equivalence is isomorphism of
  function fields*, in its curve form.
* `PlaneCurves.rationalMap_dominating_or_constant`: the milestone *Rational maps between curves
  are constant or finite*.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §6.6, Propositions 11 and 12, Problems 6.24,
  6.26 and 6.45
-/

public section

open IsLocalRing

namespace Subring

variable {L : Type*} [Field L]

/-- An element of a subring of a field is a unit there iff it is nonzero and its inverse lies in
the subring. -/
theorem isUnit_mk_iff {S : Subring L} {x : L} (hx : x ∈ S) :
    IsUnit (⟨x, hx⟩ : S) ↔ x ≠ 0 ∧ x⁻¹ ∈ S := by
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun ⟨h0, hi⟩ ↦ ?_⟩
  · have h1 : x * ((u⁻¹ : Sˣ) : L) = 1 := by
      have := congrArg Subtype.val u.mul_inv
      rwa [hu] at this
    refine ⟨left_ne_zero_of_mul_eq_one h1, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h1]
    exact (u⁻¹ : Sˣ).1.2
  · exact IsUnit.of_mul_eq_one (⟨x⁻¹, hi⟩ : S) (Subtype.ext (mul_inv_cancel₀ h0))

end Subring

namespace LocalSubring

section Field

variable {L L' : Type*} [Field L] [Field L']

/-- For local subrings `A`, `B` of a field, `B` dominates `A` iff `A ⊆ B` and every element of
`A` whose inverse lies in `B` has its inverse in `A`. -/
theorem le_iff_of_field {A B : LocalSubring L} :
    A ≤ B ↔ A.toSubring ≤ B.toSubring ∧ ∀ x ∈ A.toSubring, x⁻¹ ∈ B.toSubring →
      x⁻¹ ∈ A.toSubring := by
  refine ⟨fun ⟨h, hl⟩ ↦ ⟨h, fun x hx hxB ↦ ?_⟩, fun ⟨h, hl⟩ ↦ ⟨h, ⟨fun ⟨x, hx⟩ hu ↦ ?_⟩⟩⟩
  · rcases eq_or_ne x 0 with rfl | h0
    · simp
    · have : IsUnit (Subring.inclusion h ⟨x, hx⟩) :=
        (Subring.isUnit_mk_iff (h hx)).2 ⟨h0, hxB⟩
      exact ((Subring.isUnit_mk_iff hx).1 (hl.map_nonunit _ this)).2
  · have := (Subring.isUnit_mk_iff (h hx)).1 hu
    exact (Subring.isUnit_mk_iff hx).2 ⟨this.1, hl x hx this.2⟩

/-- The image of local subrings of a field under a field homomorphism preserves domination. -/
theorem map_mono (f : L →+* L') {A B : LocalSubring L} (h : A ≤ B) : A.map f ≤ B.map f := by
  rw [le_iff_of_field] at h ⊢
  refine ⟨fun _ ⟨x, hx, e⟩ ↦ ⟨x, h.1 hx, e⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
  rw [← map_inv₀] at hyx ⊢
  rw [f.injective hyx] at hy
  exact ⟨x⁻¹, h.2 x hx hy, rfl⟩

/-- Mapping a local subring by the identity gives it back. -/
@[simp]
theorem map_id (A : LocalSubring L) : A.map (RingHom.id L) = A :=
  LocalSubring.ext (Subring.map_id _)

/-- Mapping a local subring by two homomorphisms in turn is mapping it by their composite. -/
theorem map_map (f : L →+* L') {L'' : Type*} [Field L''] (g : L' →+* L'') (A : LocalSubring L) :
    (A.map f).map g = A.map (g.comp f) :=
  LocalSubring.ext (Subring.map_map _ _ _)

/-- Mapping a local subring by an isomorphism of algebras and then by its inverse gives it back. -/
theorem map_symm_map {k : Type*} [CommRing k] [Algebra k L] [Algebra k L'] (φ : L ≃ₐ[k] L')
    (A : LocalSubring L) : (A.map (φ : L →+* L')).map (φ.symm : L' →+* L) = A := by
  rw [map_map]
  convert map_id A
  ext x
  simp

end Field

section IsCentre

variable {R L : Type*} [CommRing R] [Field L]

/-- Let `B` be a local subring of a field `L`, and `ψ : R →+* L`. The ideal `p` of `R` is the
*centre* of `B` on `R` (through `ψ`) if `ψ` maps `R` into `B` and `p` is the preimage of the
maximal ideal of `B`: `a ∉ p` iff `ψ a` is a unit of `B`. Geometrically, `B` is the local ring of
a point `P'`, `ψ` a rational map to the affine variety of `R`, and the map is defined at `P'`,
with value the point of `p`. -/
def IsCentre (B : LocalSubring L) (ψ : R →+* L) (p : Ideal R) : Prop :=
  ∀ a : R, ψ a ∈ B.toSubring ∧ (a ∉ p ↔ ψ a ≠ 0 ∧ (ψ a)⁻¹ ∈ B.toSubring)

theorem isCentre_def (B : LocalSubring L) (ψ : R →+* L) (p : Ideal R) :
    B.IsCentre ψ p ↔
      ∀ a : R, ψ a ∈ B.toSubring ∧ (a ∉ p ↔ ψ a ≠ 0 ∧ (ψ a)⁻¹ ∈ B.toSubring) :=
  Iff.rfl

variable {B : LocalSubring L} {ψ : R →+* L} {p q : Ideal R}

/-- A local subring with a centre on `R` contains the image of `R`. -/
theorem IsCentre.mem (h : B.IsCentre ψ p) (a : R) : ψ a ∈ B.toSubring := (h a).1

/-- An element of `R` lies outside the centre iff its image is a unit of the local subring. -/
theorem IsCentre.notMem_iff (h : B.IsCentre ψ p) (a : R) :
    a ∉ p ↔ ψ a ≠ 0 ∧ (ψ a)⁻¹ ∈ B.toSubring :=
  (h a).2

/-- The centre is unique. -/
theorem IsCentre.unique (hp : B.IsCentre ψ p) (hq : B.IsCentre ψ q) : p = q := by
  ext a
  exact not_iff_not.1 ((hp.notMem_iff a).trans (hq.notMem_iff a).symm)

/-- If `ψ` maps `R` into `B`, the preimage of the maximal ideal of `B` is the centre. -/
theorem isCentre_comap (h : ∀ a, ψ a ∈ B.toSubring) :
    B.IsCentre ψ ((maximalIdeal B.toSubring).comap (ψ.codRestrict _ h)) := fun a ↦
  ⟨h a, by
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact Subring.isUnit_mk_iff (h a)⟩

/-- `B` has a centre on `R` iff `ψ` maps `R` into `B`. -/
theorem exists_isCentre_iff : (∃ p, B.IsCentre ψ p) ↔ ∀ a, ψ a ∈ B.toSubring :=
  ⟨fun ⟨_, h⟩ ↦ h.mem, fun h ↦ ⟨_, isCentre_comap h⟩⟩

/-- The centre is the preimage of the maximal ideal. -/
theorem IsCentre.eq_comap (hp : B.IsCentre ψ p) :
    p = (maximalIdeal B.toSubring).comap (ψ.codRestrict _ hp.mem) :=
  hp.unique (isCentre_comap _)

/-- The centre is a prime ideal. -/
theorem IsCentre.isPrime (hp : B.IsCentre ψ p) : p.IsPrime := by
  rw [hp.eq_comap]
  exact Ideal.comap_isPrime _ _

/-- The kernel of `ψ` lies in the centre. -/
theorem IsCentre.ker_le (hp : B.IsCentre ψ p) : RingHom.ker ψ ≤ p := fun a ha ↦ by
  by_contra h
  exact ((hp.notMem_iff a).1 h).1 ha

/-- If the kernel of `ψ` is a maximal ideal, it is the centre of every local subring with a
centre: a rational map with this kernel is constant. -/
theorem IsCentre.eq_ker (hp : B.IsCentre ψ p) (hk : (RingHom.ker ψ).IsMaximal) :
    p = RingHom.ker ψ :=
  (hk.eq_of_le hp.isPrime.ne_top hp.ker_le).symm

end IsCentre

section atPrime

variable {R : Type*} [CommRing R] [IsDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- The localization `R_p` of a domain `R` at a prime ideal `p`, as a local subring of the
fraction field `K` of `R`: the elements `a / s` of `K` with `s ∉ p`. For `R` the coordinate ring
of an affine variety and `p` the ideal of a point `P`, this is the local ring `𝒪_P`. -/
noncomputable def atPrime (p : Ideal R) [p.IsPrime] : LocalSubring K :=
  letI := IsLocalization.AtPrime.isLocalRing
    (Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors) p
  ⟨(Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors).toSubring⟩

/-- The underlying subring of `R_p` is Mathlib's `Localization.subalgebra.ofField`. -/
theorem atPrime_toSubring (p : Ideal R) [p.IsPrime] : (atPrime K p).toSubring =
    (Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors).toSubring :=
  (rfl)

variable (p : Ideal R) [p.IsPrime]

noncomputable instance : Algebra R (atPrime K p).toSubring :=
  inferInstanceAs (Algebra R
    (Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors))

instance : IsScalarTower R (atPrime K p).toSubring K :=
  inferInstanceAs (IsScalarTower R
    (Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors) K)

instance : IsLocalization.AtPrime (atPrime K p).toSubring p :=
  inferInstanceAs (IsLocalization p.primeCompl
    (Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors))

variable {K p}

/-- The elements of `R_p` are the fractions `a / s` with `s ∉ p`. -/
theorem mem_atPrime_iff {x : K} :
    x ∈ (atPrime K p).toSubring ↔
      ∃ a s : R, s ∉ p ∧ x = algebraMap R K a * (algebraMap R K s)⁻¹ := by
  change (∃ a s, ∃ _ : s ∈ p.primeCompl, _) ↔ _
  simp only [exists_prop]
  rfl

/-- The elements of `R` lie in `R_p`. -/
theorem algebraMap_mem_atPrime (a : R) : algebraMap R K a ∈ (atPrime K p).toSubring :=
  ⟨a, 1, p.primeCompl.one_mem, by simp⟩

/-- The inverse of an element of `R` outside `p` lies in `R_p`. -/
theorem inv_algebraMap_mem_atPrime {s : R} (hs : s ∉ p) :
    (algebraMap R K s)⁻¹ ∈ (atPrime K p).toSubring :=
  ⟨1, s, hs, by simp⟩

/-- For `a ≠ 0`, `1 / a` lies in `R_p` iff `a ∉ p`. -/
theorem inv_algebraMap_mem_atPrime_iff {a : R} (ha : a ≠ 0) :
    (algebraMap R K a)⁻¹ ∈ (atPrime K p).toSubring ↔ a ∉ p := by
  refine ⟨fun h ↦ ?_, inv_algebraMap_mem_atPrime⟩
  have hu : IsUnit (algebraMap R (atPrime K p).toSubring a) :=
    (Subring.isUnit_mk_iff (algebraMap_mem_atPrime a)).2
      ⟨(map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ha, h⟩
  exact (IsLocalization.AtPrime.isUnit_to_map_iff _ p a).1 hu

/-- The localization at the zero ideal is the whole fraction field. -/
theorem atPrime_toSubring_eq_top (hp : p = ⊥) : (atPrime K p).toSubring = ⊤ := by
  refine eq_top_iff.2 fun x _ ↦ ?_
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  exact ⟨a, s, by simpa [hp] using nonZeroDivisors.ne_zero hs, div_eq_mul_inv _ _⟩

/-- **Domination by a local ring of a domain.** Let `φ : K →+* L` be a homomorphism from the
fraction field of `R` to a field. A local subring `B` of `L` dominates `φ(R_p)` iff `p` is the
centre of `B` on `R`. -/
theorem map_atPrime_le_iff {L : Type*} [Field L] (φ : K →+* L) {B : LocalSubring L} :
    (atPrime K p).map φ ≤ B ↔ B.IsCentre (φ.comp (algebraMap R K)) p := by
  rw [le_iff_of_field]
  constructor
  · rintro ⟨hle, hinv⟩ a
    have hmem : φ (algebraMap R K a) ∈ ((atPrime K p).map φ).toSubring :=
      ⟨_, algebraMap_mem_atPrime a, rfl⟩
    refine ⟨hle hmem, ⟨fun ha ↦ ?_, fun ⟨h0, hi⟩ ↦ ?_⟩⟩
    · have ha0 : a ≠ 0 := by rintro rfl; exact ha p.zero_mem
      refine ⟨by simpa using ha0, hle ?_⟩
      exact ⟨_, inv_algebraMap_mem_atPrime ha, by simp⟩
    · have ha0 : a ≠ 0 := by rintro rfl; simp at h0
      obtain ⟨y, hy, hyx⟩ := hinv _ hmem hi
      rw [← map_inv₀] at hyx
      rw [φ.injective hyx] at hy
      exact (inv_algebraMap_mem_atPrime_iff ha0).1 hy
  · intro h
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, ⟨a, s, hs, rfl⟩, rfl⟩
      simp only [map_mul, map_inv₀]
      exact mul_mem ((h a).1) ((h.notMem_iff s).1 hs).2
    · rintro _ ⟨x, ⟨a, s, hs, rfl⟩, rfl⟩ hi
      have hs0 : s ≠ 0 := by rintro rfl; exact hs p.zero_mem
      rcases eq_or_ne a 0 with rfl | ha0
      · simp
      have hsu := (h.notMem_iff s).1 hs
      have ha : a ∉ p := by
        rw [h.notMem_iff]
        refine ⟨by simpa using ha0, ?_⟩
        have hφa : φ (algebraMap R K a) ≠ 0 := by simpa using ha0
        have hφs : φ (algebraMap R K s) ≠ 0 := by simpa using hs0
        have : (φ.comp (algebraMap R K) a)⁻¹ =
            (φ (algebraMap R K a * (algebraMap R K s)⁻¹))⁻¹ * (φ (algebraMap R K s))⁻¹ := by
          simp only [RingHom.comp_apply, map_mul, map_inv₀, mul_inv, inv_inv]
          field_simp
        rw [this]
        exact mul_mem hi hsu.2
      refine ⟨algebraMap R K s * (algebraMap R K a)⁻¹, ⟨s, a, ha, rfl⟩, ?_⟩
      simp

/-- The local rings of a domain at two primes are equal, or even one dominates the other, only
if the primes are equal. -/
theorem eq_of_atPrime_le {q : Ideal R} [q.IsPrime] (h : atPrime K p ≤ atPrime K q) : p = q := by
  have hp := (map_atPrime_le_iff (p := p) (RingHom.id K) (B := atPrime K q)).1 (by rwa [map_id])
  have hq := (map_atPrime_le_iff (p := q) (RingHom.id K) (B := atPrime K q)).1 (by rw [map_id])
  exact hp.unique hq

end atPrime

end LocalSubring

namespace AlgHom

/-- The kernel of an algebra map from a commutative `k`-algebra to a field that is integral over
the field `k` is a maximal ideal. -/
theorem isMaximal_ker_of_isIntegral {k A L : Type*} [Field k] [CommRing A] [Field L]
    [Algebra k A] [Algebra k L] [Algebra.IsIntegral k L] (χ : A →ₐ[k] L) :
    (RingHom.ker χ).IsMaximal := by
  have : IsDomain (A ⧸ RingHom.ker χ) :=
    (Ideal.Quotient.isDomain_iff_prime _).2 (RingHom.ker_isPrime _)
  have : Algebra.IsIntegral k (A ⧸ RingHom.ker χ) :=
    Algebra.IsIntegral.of_injective _ (Ideal.kerLiftAlg_injective χ)
  exact Ideal.Quotient.maximal_of_isField _
    ((Algebra.IsIntegral.isField_iff_isField (algebraMap k _).injective).1 (Field.toIsField k))

end AlgHom

namespace LocalSubring

variable {k R R' K' : Type*} [Field k] [CommRing R] [Algebra k R] [CommRing R'] [IsDomain R']
  [Algebra k R'] [Field K'] [Algebra R' K'] [IsFractionRing R' K'] [Algebra k K']
  [IsScalarTower k R' K']

/-- The constants `k` lie in every local ring `R'_p` of a `k`-domain. -/
theorem algebraMap_mem_atPrime_of_tower (p : Ideal R') [p.IsPrime] (c : k) :
    algebraMap k K' c ∈ (atPrime K' p).toSubring := by
  rw [IsScalarTower.algebraMap_apply k R' K']
  exact algebraMap_mem_atPrime _

/-- **The centre of a local ring of a finitely generated algebra is a maximal ideal.** Let `R'`
be a finitely generated `k`-domain with fraction field `K'`, `m'` a maximal ideal of `R'`, and
`ψ : R →ₐ[k] K'`. If `p` is the centre of `R'_{m'}` on `R`, then `p` is maximal: the value of a
rational map at a point is a point. -/
theorem IsCentre.isMaximal [Algebra.FiniteType k R'] {m' : Ideal R'} [m'.IsMaximal]
    {ψ : R →ₐ[k] K'} {p : Ideal R} (hp : (atPrime K' m').IsCentre (ψ : R →+* K') p) :
    p.IsMaximal := by
  let B := (atPrime K' m').toSubring
  let := Ideal.Quotient.field m'
  have : Module.Finite k (R' ⧸ m') := finite_of_finite_type_of_isJacobsonRing k _
  let e : (R' ⧸ m') ≃ₐ[R'] (B ⧸ maximalIdeal B) :=
    ((Ideal.quotientEquivAlgOfEq R' (pow_one m')).symm.trans
      (IsLocalization.AtPrime.equivQuotMaximalIdealPow m' B 1)).trans
      (Ideal.quotientEquivAlgOfEq R' (pow_one _))
  let ψ' : R →+* B := (ψ : R →+* K').codRestrict _ hp.mem
  let χ : R →ₐ[k] R' ⧸ m' :=
    { toRingHom := e.symm.toRingHom.comp ((Ideal.Quotient.mk _).comp ψ')
      commutes' := fun c ↦ by
        have : ψ' (algebraMap k R c) = algebraMap R' B (algebraMap k R' c) := by
          ext
          simp only [ψ', RingHom.codRestrict_apply, AlgHom.coe_toRingHom, AlgHom.commutes]
          rw [IsScalarTower.algebraMap_apply k R' K']
          rfl
        change e.symm (Ideal.Quotient.mk _ (ψ' (algebraMap k R c))) = _
        rw [this, Ideal.Quotient.mk_algebraMap, AlgEquiv.commutes,
          ← IsScalarTower.algebraMap_apply] }
  have hker : RingHom.ker χ = p := by
    rw [hp.eq_comap]
    ext a
    simp [χ, ψ', B, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem, mem_maximalIdeal]
  rw [← hker]
  exact AlgHom.isMaximal_ker_of_isIntegral χ

/-- A `k`-algebra map `ψ : R →ₐ[k] K'` maps `R` into `R'_p` iff it maps a set of generators of the
`k`-algebra `R` into it. -/
theorem forall_mem_atPrime_iff_of_adjoin_eq_top {ι : Type*} {y : ι → R}
    (hy : Algebra.adjoin k (Set.range y) = ⊤) (ψ : R →ₐ[k] K') (p : Ideal R') [p.IsPrime] :
    (∀ a, ψ a ∈ (atPrime K' p).toSubring) ↔ ∀ i, ψ (y i) ∈ (atPrime K' p).toSubring := by
  refine ⟨fun h i ↦ h (y i), fun h a ↦ ?_⟩
  have ha : a ∈ Algebra.adjoin k (Set.range y) := hy ▸ Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | algebraMap c => rw [AlgHom.commutes]; exact algebraMap_mem_atPrime_of_tower p c
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

/-- **Existence of the value.** Let `R'` be a finitely generated `k`-domain, `m'` a maximal ideal
of `R'`, and `ψ : R →ₐ[k] K'`. Then `R'_{m'}` has a centre on `R` that is a maximal ideal iff `ψ`
maps `R` into `R'_{m'}`. -/
theorem exists_isCentre_maximalSpectrum_iff [Algebra.FiniteType k R'] {m' : Ideal R'}
    [m'.IsMaximal] {ψ : R →ₐ[k] K'} :
    (∃ Q : MaximalSpectrum R, (atPrime K' m').IsCentre (ψ : R →+* K') Q.asIdeal) ↔
      ∀ a, ψ a ∈ (atPrime K' m').toSubring := by
  refine ⟨fun ⟨_, h⟩ ↦ h.mem, fun h ↦ ?_⟩
  obtain ⟨p, hp⟩ := (exists_isCentre_iff (ψ := (ψ : R →+* K'))).2 h
  exact ⟨⟨p, hp.isMaximal⟩, hp⟩

/-- **The domain of a rational map is cofinite.** Let `R` be a finitely generated `k`-algebra and
`R'` a finitely generated `k`-domain of transcendence degree at most one (the coordinate ring of
a curve) with fraction field `K'`. A `k`-algebra map `ψ : R →ₐ[k] K'` maps `R` into `R'_{m'}` for
all but finitely many maximal ideals `m'` of `R'`. -/
theorem finite_setOf_not_forall_mem_atPrime [Algebra.FiniteType k R] [Algebra.FiniteType k R']
    (h : Algebra.trdeg k R' ≤ 1) (ψ : R →ₐ[k] K') :
    {m' : MaximalSpectrum R' | ¬ ∀ a, ψ a ∈ (atPrime K' m'.asIdeal).toSubring}.Finite := by
  have := Algebra.FiniteType.isNoetherianRing k R'
  have := Ring.krullDimLE_one_of_trdeg_le_one h
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k R).FG)
  have hy : Algebra.adjoin k (Set.range ((↑) : s → R)) = ⊤ := by simpa using hs
  refine (s.finite_toSet.biUnion fun y _ ↦
    MaximalSpectrum.finite_setOf_notMem_ofField K' (ψ y)).subset fun m' hm' ↦ ?_
  rw [Set.mem_ofPred_eq, forall_mem_atPrime_iff_of_adjoin_eq_top hy] at hm'
  push Not at hm'
  obtain ⟨⟨y, hy⟩, hm'⟩ := hm'
  exact Set.mem_biUnion hy hm'

end LocalSubring

namespace TauCeti.IsFunctionField

/-- **Function fields are finite over function fields below them.** If `K` and `K'` are algebraic
function fields of one variable over `k` and `K'` is a `K`-algebra compatibly with `k`, then `K'`
is a finite extension of `K`. -/
theorem finite_of_isFunctionField {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K]
    [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] (hK : IsFunctionField k K)
    (hK' : IsFunctionField k K') : Module.Finite K K' := by
  have := hK'.essFiniteType
  have : Algebra.EssFiniteType K K' := .of_comp k K K'
  have := hK.isAlgebraic_of_isFunctionField hK'
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end TauCeti.IsFunctionField

namespace PlaneCurves

open LocalSubring TauCeti

variable {k R R' K K' : Type*} [Field k] [CommRing R] [IsDomain R] [Algebra k R] [CommRing R']
  [IsDomain R'] [Algebra k R'] [Field K] [Algebra R K] [IsFractionRing R K] [Algebra k K]
  [IsScalarTower k R K] [Field K'] [Algebra R' K'] [IsFractionRing R' K'] [Algebra k K']
  [IsScalarTower k R' K']

/-- **Dominating rational maps correspond to function-field embeddings** (curve form). Let `R`,
`R'` be finitely generated `k`-domains, the coordinate rings of affine varieties `C` and `C'`,
with fraction fields `K = k(C)` and `K' = k(C')`, and let `C'` be a curve (`R'` of transcendence
degree at most one). A `k`-algebra map `φ : K →ₐ[k] K'` is a dominating rational map `C' ⇢ C`;
it is defined at a point `P'` of `C'` (a maximal ideal of `R'`), with value a point `Q` of `C`
(a maximal ideal of `R`), when `𝒪_{P'}(C')` dominates `φ(𝒪_Q(C))`. Then:

1. `𝒪_{P'}(C')` dominates `φ(𝒪_Q(C))` iff `Q` is the centre of `𝒪_{P'}(C')` on `R`: `φ` maps
  `R` into `𝒪_{P'}(C')`, and `a ∈ R` vanishes at `Q` iff `φ(a)` vanishes at `P'`;
2. there is at most one such `Q`;
3. if `R` is generated by the `y i`, such a `Q` exists iff every `φ (y i)` lies in
  `𝒪_{P'}(C')`;
4. such a `Q` exists for all but finitely many `P'`.

Milestone: *Dominating rational maps correspond to function-field embeddings*. -/
theorem dominatingRationalMap_spec [Algebra.FiniteType k R] [Algebra.FiniteType k R']
    (h : Algebra.trdeg k R' ≤ 1) (φ : K →ₐ[k] K') {ι : Type*} {y : ι → R}
    (hy : Algebra.adjoin k (Set.range y) = ⊤) :
    (∀ (P : MaximalSpectrum R') (Q : MaximalSpectrum R),
      (atPrime K Q.asIdeal).map (φ : K →+* K') ≤ atPrime K' P.asIdeal ↔
        (atPrime K' P.asIdeal).IsCentre ((φ : K →+* K').comp (algebraMap R K)) Q.asIdeal) ∧
    (∀ (P : MaximalSpectrum R') (Q₁ Q₂ : MaximalSpectrum R),
      (atPrime K Q₁.asIdeal).map (φ : K →+* K') ≤ atPrime K' P.asIdeal →
      (atPrime K Q₂.asIdeal).map (φ : K →+* K') ≤ atPrime K' P.asIdeal → Q₁ = Q₂) ∧
    (∀ P : MaximalSpectrum R',
      (∃ Q : MaximalSpectrum R, (atPrime K Q.asIdeal).map (φ : K →+* K') ≤ atPrime K' P.asIdeal)
        ↔ ∀ i, φ (algebraMap R K (y i)) ∈ (atPrime K' P.asIdeal).toSubring) ∧
    {P : MaximalSpectrum R' | ¬ ∃ Q : MaximalSpectrum R,
      (atPrime K Q.asIdeal).map (φ : K →+* K') ≤ atPrime K' P.asIdeal}.Finite := by
  let ψ : R →ₐ[k] K' := φ.comp (IsScalarTower.toAlgHom k R K)
  have key (P : MaximalSpectrum R') (Q : MaximalSpectrum R) :=
    map_atPrime_le_iff (p := Q.asIdeal) (φ : K →+* K') (B := atPrime K' P.asIdeal)
  have hex (P : MaximalSpectrum R') :
      (∃ Q : MaximalSpectrum R, (atPrime K Q.asIdeal).map (φ : K →+* K') ≤
        atPrime K' P.asIdeal) ↔ ∀ a, ψ a ∈ (atPrime K' P.asIdeal).toSubring := by
    simp_rw [key]
    exact exists_isCentre_maximalSpectrum_iff (ψ := ψ)
  refine ⟨key, fun P Q₁ Q₂ h₁ h₂ ↦ MaximalSpectrum.ext (((key P Q₁).1 h₁).unique
    ((key P Q₂).1 h₂)), fun P ↦ (hex P).trans (forall_mem_atPrime_iff_of_adjoin_eq_top hy ψ _),
    ?_⟩
  simp_rw [hex]
  exact finite_setOf_not_forall_mem_atPrime h ψ

/-- Let `φ : K ≃ₐ[k] K'` be an isomorphism of the function fields of affine curves, with
coordinate rings `R` and `R'`. For all but finitely many points `P` of the curve of `R'`, there is
a point `Q` of the curve of `R` whose local ring `φ` maps onto that of `P`. -/
theorem finite_compl_setOf_exists_map_atPrime_eq [Algebra.FiniteType k R]
    [Algebra.FiniteType k R'] (hR : Algebra.trdeg k R ≤ 1) (hR' : Algebra.trdeg k R' ≤ 1)
    (φ : K ≃ₐ[k] K') :
    {P : MaximalSpectrum R' | ∃ Q : MaximalSpectrum R,
      (atPrime K Q.asIdeal).map (φ : K →+* K') = atPrime K' P.asIdeal}ᶜ.Finite := by
  have := Algebra.FiniteType.isNoetherianRing k R'
  have := Ring.krullDimLE_one_of_trdeg_le_one hR'
  let ψ : R →ₐ[k] K' := (φ : K →ₐ[k] K').comp (IsScalarTower.toAlgHom k R K)
  let ψ' : R' →ₐ[k] K := (φ.symm : K' →ₐ[k] K).comp (IsScalarTower.toAlgHom k R' K')
  let D : Set (MaximalSpectrum R) := {Q | ∀ b, ψ' b ∈ (atPrime K Q.asIdeal).toSubring}
  have hD : Dᶜ.Finite := finite_setOf_not_forall_mem_atPrime hR ψ'
  have hD' := finite_setOf_not_forall_mem_atPrime hR' ψ
  -- The points `P` with value a given point `Q ∉ D` are finite in number.
  have hfib : ∀ Q ∈ Dᶜ, {P : MaximalSpectrum R' |
      (atPrime K Q.asIdeal).map (φ : K →+* K') ≤ atPrime K' P.asIdeal}.Finite := by
    intro Q hQ
    have hQ0 : Q.asIdeal ≠ ⊥ := fun h0 ↦ hQ fun b ↦ by
      rw [atPrime_toSubring_eq_top h0]
      exact Subring.mem_top _
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
    refine (MaximalSpectrum.finite_setOf_notMem_ofField K' (ψ a)⁻¹).subset fun P hP ↦ ?_
    have hc := (map_atPrime_le_iff _).1 hP
    have hψa : ψ a ≠ 0 := by simpa [ψ] using ha0
    have := (hc.notMem_iff a).not
    simp only [not_not, ha, true_iff, not_and, not_not] at this
    exact this hψa
  refine (hD'.union (hD.biUnion hfib)).subset fun P hP ↦ ?_
  by_contra hcon
  simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hcon
  obtain ⟨hPD, hfibP⟩ := hcon
  obtain ⟨Q, hQ⟩ := exists_isCentre_maximalSpectrum_iff.2 (not_not.1 hPD)
  have hle : (atPrime K Q.asIdeal).map (φ : K →+* K') ≤ atPrime K' P.asIdeal :=
    (map_atPrime_le_iff _).2 hQ
  have hQD : Q ∈ D := by
    by_contra hQD
    exact hfibP Q hQD hle
  obtain ⟨P', hP'⟩ := exists_isCentre_maximalSpectrum_iff.2 hQD
  have hle' : (atPrime K' P'.asIdeal).map (φ.symm : K' →+* K) ≤ atPrime K Q.asIdeal :=
    (map_atPrime_le_iff _).2 hP'
  have h1 := (map_mono (φ : K →+* K') hle').trans hle
  rw [show ((atPrime K' P'.asIdeal).map (φ.symm : K' →+* K)).map (φ : K →+* K') =
    atPrime K' P'.asIdeal from map_symm_map φ.symm _] at h1
  obtain rfl : P' = P := MaximalSpectrum.ext (eq_of_atPrime_le h1)
  refine hP ⟨Q, le_antisymm hle ?_⟩
  have h2 := map_mono (φ : K →+* K') hle'
  rwa [show ((atPrime K' P'.asIdeal).map (φ.symm : K' →+* K)).map (φ : K →+* K') =
    atPrime K' P'.asIdeal from map_symm_map φ.symm _] at h2
/-- **Birational equivalence is isomorphism of function fields** (curve form). Let `R`, `R'` be
finitely generated `k`-domains of transcendence degree at most one, the coordinate rings of affine
curves `C` and `C'`, with fraction fields `K = k(C)` and `K' = k(C')`, and let
`φ : K ≃ₐ[k] K'` be an isomorphism of `k`-algebras (a birational equivalence). There are cofinite
sets `U` of points of `C` and `U'` of points of `C'` (maximal ideals) and a bijection
`e : U' ≃ U` such that `φ` maps `𝒪_{e P}(C)` onto `𝒪_P(C')` for every `P ∈ U'`.

Milestone: *Birational equivalence is isomorphism of function fields*. -/
theorem birational_spec [Algebra.FiniteType k R] [Algebra.FiniteType k R']
    (hR : Algebra.trdeg k R ≤ 1) (hR' : Algebra.trdeg k R' ≤ 1) (φ : K ≃ₐ[k] K') :
    ∃ (U : Set (MaximalSpectrum R)) (U' : Set (MaximalSpectrum R')), Uᶜ.Finite ∧ U'ᶜ.Finite ∧
      ∃ e : U' ≃ U, ∀ P : U',
        (atPrime K (e P).1.asIdeal).map (φ : K →+* K') = atPrime K' P.1.asIdeal := by
  have hiff (P : MaximalSpectrum R') (Q : MaximalSpectrum R) :
      (atPrime K' P.asIdeal).map (φ.symm : K' →+* K) = atPrime K Q.asIdeal ↔
        (atPrime K Q.asIdeal).map (φ : K →+* K') = atPrime K' P.asIdeal := by
    constructor <;> rintro h <;> rw [← h]
    · exact map_symm_map φ.symm _
    · exact map_symm_map φ _
  have hQ {P : MaximalSpectrum R'} {Q₁ Q₂ : MaximalSpectrum R}
      (h₁ : (atPrime K Q₁.asIdeal).map (φ : K →+* K') = atPrime K' P.asIdeal)
      (h₂ : (atPrime K Q₂.asIdeal).map (φ : K →+* K') = atPrime K' P.asIdeal) : Q₁ = Q₂ :=
    MaximalSpectrum.ext (((map_atPrime_le_iff _).1 h₁.le).unique ((map_atPrime_le_iff _).1 h₂.le))
  let U' := {P : MaximalSpectrum R' | ∃ Q : MaximalSpectrum R,
    (atPrime K Q.asIdeal).map (φ : K →+* K') = atPrime K' P.asIdeal}
  let U := {Q : MaximalSpectrum R | ∃ P : MaximalSpectrum R',
    (atPrime K' P.asIdeal).map (φ.symm : K' →+* K) = atPrime K Q.asIdeal}
  let f : U' → U := fun P ↦ ⟨P.2.choose, P.1, (hiff _ _).2 P.2.choose_spec⟩
  have hf : Function.Bijective f := by
    refine ⟨fun P₁ P₂ h ↦ Subtype.ext (MaximalSpectrum.ext (eq_of_atPrime_le (K := K') ?_)),
      fun Q ↦ ?_⟩
    · have h₁ := P₁.2.choose_spec
      have h₂ := P₂.2.choose_spec
      rw [show P₁.2.choose = P₂.2.choose from congrArg Subtype.val h, h₂] at h₁
      exact h₁.symm.le
    · obtain ⟨P, hP⟩ := Q.2
      have hP' := (hiff _ _).1 hP
      exact ⟨⟨P, _, hP'⟩, Subtype.ext (hQ (Exists.choose_spec (p := fun Q : MaximalSpectrum R ↦
        (atPrime K Q.asIdeal).map (φ : K →+* K') = atPrime K' P.asIdeal) ⟨_, hP'⟩) hP')⟩
  refine ⟨U, U', finite_compl_setOf_exists_map_atPrime_eq hR' hR φ.symm,
    finite_compl_setOf_exists_map_atPrime_eq hR hR' φ, Equiv.ofBijective f hf,
    fun P ↦ P.2.choose_spec⟩

/-- **Rational maps between curves are constant or finite.** Let `R` be a `k`-domain, the
coordinate ring of an affine curve `C`, with fraction field `K = k(C)`, let `K' = k(C')` be the
function field of a curve `C'`, and let `ψ : R →ₐ[k] K'`, a rational map `C' ⇢ C`. Either `ψ`
extends to a `k`-embedding `φ : K →ₐ[k] K'` (`ψ` is dominating) and `K'` is a finite extension of
`φ(K)`, or `ψ` is constant: there is a point `Q` of `C` that is the value of `ψ` at every local
subring of `K'` at which `ψ` is defined.

Milestone: *Rational maps between curves are constant or finite*. -/
theorem rationalMap_dominating_or_constant (hK : IsFunctionField k K)
    (hK' : IsFunctionField k K') (ψ : R →ₐ[k] K') :
    (∃ φ : K →ₐ[k] K', φ.comp (IsScalarTower.toAlgHom k R K) = ψ ∧ (φ : K →+* K').Finite) ∨
      ∃ Q : MaximalSpectrum R, ∀ (B : LocalSubring K') (p : Ideal R),
        B.IsCentre (ψ : R →+* K') p → p = Q.asIdeal := by
  by_cases hinj : Function.Injective ψ
  · refine .inl ⟨IsFractionRing.liftAlgHom (K := K) hinj, ?_, ?_⟩
    · ext a
      simp
    · let φ := IsFractionRing.liftAlgHom (K := K) hinj
      let := (φ : K →+* K').toAlgebra
      have : IsScalarTower k K K' := .of_algebraMap_eq fun c ↦ (φ.commutes c).symm
      exact hK.finite_of_isFunctionField hK'
  · have : (RingHom.ker (ψ : R →+* K')).IsPrime := RingHom.ker_isPrime _
    have hne : RingHom.ker (ψ : R →+* K') ≠ ⊥ := fun h ↦
      hinj ((RingHom.injective_iff_ker_eq_bot _).2 h)
    have hmax := Ideal.IsPrime.isMaximal_of_trdeg_fractionRing_le_one (k := k) K
      hK.trdeg_eq_one.le hne
    exact .inr ⟨⟨_, hmax⟩, fun B p hp ↦ hp.eq_ker hmax⟩

end PlaneCurves
