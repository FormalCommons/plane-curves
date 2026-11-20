/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.CanonicalDivisor
public import TauCeti.FieldTheory.FunctionField.Differential.Comparison
public import TauCeti.FieldTheory.FunctionField.Differential.Independence
public import TauCeti.FieldTheory.FunctionField.Frobenius

/-!
# The divisor of a Kähler differential

Let `K / k` be an algebraic function field of one variable over a perfect field `k`, with `k`
algebraically closed in `K`. A nonzero Kähler differential `ω ∈ Ω[K⁄k]` has an order
`ord_P (ω) = ord_P (ω / dt)` at each place `P`, `t` a uniformizer at `P`, and a divisor
`div (ω) = ∑_P ord_P (ω) P`.

Here `div (ω)` is *defined* as the divisor `TauCeti.weilDifferentialDivisor` of the Weil
differential that corresponds to `ω` under the Kähler–Weil comparison
`TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating`, built from a separating element
that exists because `k` is perfect. The comparison does not depend on that element, and the order
at `P` is then the book's `ord_P (ω / dt)`, because the Weil differential `dt` of a uniformizer
has order zero at `P`. So every result of Tau Ceti about canonical divisors of Weil differentials
applies to the divisors of Kähler differentials, among them the Riemann–Roch theorem.

## Main definitions

* `PlaneCurves.kaehlerDifferentialDivisor`: the divisor `div (ω)` of a nonzero Kähler
  differential.
* `PlaneCurves.kaehlerDifferentialFiltration`: the space `Ω(D)` of the Kähler differentials `ω`
  with `ω = 0` or `div ω ≥ D`.

## Main results

* `PlaneCurves.kaehlerDifferentialDivisor_eq`: `div (ω)` is the divisor of the Weil differential
  attached to `ω` by the comparison built from any separating element.
* `PlaneCurves.coeff_kaehlerDifferentialDivisor_of_eq_smul_D` and
  `PlaneCurves.coeff_kaehlerDifferentialDivisor`: the order at `P` is `ord_P (ω / dt)` for every
  uniformizer `t` at `P`.
* `PlaneCurves.kaehlerDifferentialDivisor_smul`: `div (f ω) = div f + div ω`.
* `PlaneCurves.divisorClass_kaehlerDifferentialDivisor`: `div (ω)` represents Tau Ceti's
  canonical class.
* `PlaneCurves.divisorClass_eq_canonicalClass_iff_exists_kaehlerDifferentialDivisor_eq`: the
  divisors of nonzero Kähler differentials are exactly the divisors of the canonical class.
* `PlaneCurves.isRiemannRochDivisor_kaehlerDifferentialDivisor`: the Riemann–Roch theorem
  `ℓ(D) = deg D + 1 - g + ℓ(div ω - D)`.
* `PlaneCurves.finrank_kaehlerDifferentialFiltration`: `dim_k Ω(D) = ℓ(div ω - D)`; and
  `PlaneCurves.finrank_kaehlerDifferentialFiltration_zero`: the holomorphic differentials form a
  space of dimension `g`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §8.4, §8.5 and §8.6
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][Stichtenoth2009], §IV.3
-/

public section

noncomputable section

open KaehlerDifferential TauCeti

open scoped IntermediateField

namespace TauCeti

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- The Kähler–Weil comparison sends a nonzero Kähler differential to a nonzero Weil
differential. -/
theorem coe_kaehlerDifferentialEquivWeilDifferentialOfSeparating_ne_zero
    (hK : IsFunctionField k K) (hex : IsIntegrallyClosedIn k K) {x : K}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ K] {ω : Ω[K⁄k]} (hω : ω ≠ 0) :
    letI := weilDifferentialSpaceModule hK
    ((kaehlerDifferentialEquivWeilDifferentialOfSeparating hK hex hx ω :
      Module.Dual k ↥(repartitionSpace k K))) ≠ 0 := by
  let := weilDifferentialSpaceModule hK
  simpa using hω

end TauCeti

namespace KaehlerDifferential

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [PerfectField k]

/-- Every Kähler differential of a function field over a perfect field is a multiple `f ω₀` of
a given nonzero one. -/
theorem exists_smul_eq_of_ne_zero (hK : IsFunctionField k K) {ω₀ : Ω[K⁄k]} (hω₀ : ω₀ ≠ 0)
    (ω : Ω[K⁄k]) : ∃ f : K, f • ω₀ = ω := by
  obtain ⟨x, hx, hsep⟩ := hK.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  exact (finrank_eq_one_iff_of_ne_zero' ω₀ hω₀).1
    (finrank_kaehlerDifferential_eq_one_of_separating hx) ω

end KaehlerDifferential

namespace PlaneCurves

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [PerfectField k]
  (hK : IsFunctionField k K) (hex : IsIntegrallyClosedIn k K)

/-- The **divisor `div (ω)` of a nonzero Kähler differential** `ω` of a function field `K / k`
over a perfect field, with `k` algebraically closed in `K`: the divisor of the Weil differential
that corresponds to `ω` under the Kähler–Weil comparison. Its coefficient at a place `P` is the
order `ord_P (ω / dt)` for a uniformizer `t` at `P` (`coeff_kaehlerDifferentialDivisor`). -/
def kaehlerDifferentialDivisor (ω : Ω[K⁄k]) (hω : ω ≠ 0) : Divisor k K :=
  letI := weilDifferentialSpaceModule hK
  have hx := hK.exists_transcendental_and_isSeparable_adjoin_of_perfectField.choose_spec
  letI := hx.2
  weilDifferentialDivisor hK hex
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating hK hex hx.1 ω).2
    (coe_kaehlerDifferentialEquivWeilDifferentialOfSeparating_ne_zero hK hex hx.1 hω)

/-- `div (ω)` is the divisor of the Weil differential attached to `ω` by the Kähler–Weil
comparison built from any separating element `x`. -/
theorem kaehlerDifferentialDivisor_eq {x : K} (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ K] (ω : Ω[K⁄k]) (hω : ω ≠ 0) :
    letI := weilDifferentialSpaceModule hK
    kaehlerDifferentialDivisor hK hex ω hω =
      weilDifferentialDivisor hK hex
        (kaehlerDifferentialEquivWeilDifferentialOfSeparating hK hex hx ω).2
        (coe_kaehlerDifferentialEquivWeilDifferentialOfSeparating_ne_zero hK hex hx hω) := by
  let := weilDifferentialSpaceModule hK
  have hy := hK.exists_transcendental_and_isSeparable_adjoin_of_perfectField.choose_spec
  let := hy.2
  rw [kaehlerDifferentialDivisor]
  exact weilDifferentialDivisor_congr hK hex
    (by rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq hK hex hy.1 hx]) _ _ _ _

/-- The divisor of a Kähler differential does not depend on the proof that it is nonzero. -/
theorem kaehlerDifferentialDivisor_congr {ω₁ ω₂ : Ω[K⁄k]} (h : ω₁ = ω₂) (hω₁ : ω₁ ≠ 0)
    (hω₂ : ω₂ ≠ 0) :
    kaehlerDifferentialDivisor hK hex ω₁ hω₁ = kaehlerDifferentialDivisor hK hex ω₂ hω₂ := by
  subst h
  rfl

/-- **The order of `z dt` at `P` is `ord_P z`** for a uniformizer `t` at `P`: the coefficient
of `div (ω)` at `P` is `ord_P (ω / dt)`. -/
theorem coeff_kaehlerDifferentialDivisor_of_eq_smul_D {P : Place k K} {t : K} (ht : P.ord t = 1)
    {ω : Ω[K⁄k]} (hω : ω ≠ 0) {z : K} (h : ω = z • D k K t) :
    (kaehlerDifferentialDivisor hK hex ω hω).coeff P = P.ord z := by
  let := weilDifferentialSpaceModule hK
  obtain ⟨htr, hsep⟩ := P.transcendental_and_isSeparable_adjoin_of_ord_eq_one hK ht
  have := P.isSeparable_residueField_of_perfectField hK
  have hchain : ((kaehlerDifferentialEquivWeilDifferentialOfSeparating hK hex htr ω :
      Module.Dual k ↥(repartitionSpace k K))) =
        repartitionDualMul hK z (weilDifferentialOfSeparating hK htr) := by
    rw [h, map_smul, kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self,
      coe_weilDifferentialSpaceModule_smul]
  rw [kaehlerDifferentialDivisor_eq hK hex htr, coeff_weilDifferentialDivisor,
    weilDifferentialOrder_eq_ord_add_of_eq_repartitionDualMul hK hex _ _
      (weilDifferentialOfSeparating hK htr).2
      (by simpa using weilDifferentialOfSeparating_ne_zero hK htr) hchain P,
    weilDifferentialOrder_weilDifferentialOfSeparating_eq_zero hK hex htr ht, add_zero]

/-- **The order of a Kähler differential at a place** (Fulton, §8.5): for a uniformizer `t` at
`P`, the coefficient of `div (ω)` at `P` is `ord_P (ω / dt)`, the order of the coordinate of `ω`
in the basis `dt`. -/
theorem coeff_kaehlerDifferentialDivisor {P : Place k K} {t : K} (ht : P.ord t = 1)
    (htr : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ K] (ω : Ω[K⁄k]) (hω : ω ≠ 0) :
    (kaehlerDifferentialDivisor hK hex ω hω).coeff P =
      P.ord ((kaehlerBasisOfSeparating htr).coord () ω) :=
  coeff_kaehlerDifferentialDivisor_of_eq_smul_D hK hex ht hω <| by
    simpa using ((kaehlerBasisOfSeparating htr).sum_repr ω).symm

/-- **The transformation law** `div (f ω) = div f + div ω` for a nonzero function `f`. -/
theorem kaehlerDifferentialDivisor_smul {f : K} (hf : f ≠ 0) {ω : Ω[K⁄k]} (hω : ω ≠ 0) :
    kaehlerDifferentialDivisor hK hex (f • ω) (smul_ne_zero hf hω) =
      Divisor.principal hK (Units.mk0 f hf) + kaehlerDifferentialDivisor hK hex ω hω := by
  let := weilDifferentialSpaceModule hK
  have hx := hK.exists_transcendental_and_isSeparable_adjoin_of_perfectField.choose_spec
  let := hx.2
  rw [kaehlerDifferentialDivisor_eq hK hex hx.1, kaehlerDifferentialDivisor_eq hK hex hx.1,
    ← weilDifferentialDivisor_repartitionDualMul]
  exact weilDifferentialDivisor_congr hK hex
    (by rw [map_smul, coe_weilDifferentialSpaceModule_smul, Units.val_mk0]) _ _ _ _

/-- The divisor of every nonzero Kähler differential represents Tau Ceti's canonical class. -/
@[simp]
theorem divisorClass_kaehlerDifferentialDivisor (ω : Ω[K⁄k]) (hω : ω ≠ 0) :
    (Place.orderSystem hK).divisorClass (kaehlerDifferentialDivisor hK hex ω hω) =
      canonicalClass hK hex := by
  let := weilDifferentialSpaceModule hK
  have hx := hK.exists_transcendental_and_isSeparable_adjoin_of_perfectField.choose_spec
  let := hx.2
  rw [kaehlerDifferentialDivisor_eq hK hex hx.1, divisorClass_weilDifferentialDivisor]

/-- **Order and divisor of a differential**: over a perfect field `k` algebraically closed in the
function field `K`, a divisor represents Tau Ceti's canonical class, defined through Weil
differentials, exactly when it is the divisor `div (ω)` of a nonzero Kähler differential. Here
`div (ω)` has coefficient `ord_P (ω / dt)` at `P`, for any uniformizer `t` at `P`
(`coeff_kaehlerDifferentialDivisor`), and satisfies `div (f ω) = div f + div ω`
(`kaehlerDifferentialDivisor_smul`); so the canonical divisors of the book form exactly one
linear-equivalence class, `canonicalClass`. An algebraically closed `k` is perfect and
algebraically closed in `K` (`TauCeti.isIntegrallyClosedIn_of_isAlgClosed`).

Milestone: *Order and divisor of a differential on the nonsingular model*. -/
theorem divisorClass_eq_canonicalClass_iff_exists_kaehlerDifferentialDivisor_eq
    (D : Divisor k K) :
    (Place.orderSystem hK).divisorClass D = canonicalClass hK hex ↔
      ∃ (ω : Ω[K⁄k]) (hω : ω ≠ 0), kaehlerDifferentialDivisor hK hex ω hω = D := by
  refine ⟨fun hD ↦ ?_, fun ⟨ω, hω, h⟩ ↦ h ▸ divisorClass_kaehlerDifferentialDivisor hK hex ω hω⟩
  let := weilDifferentialSpaceModule hK
  have hx := hK.exists_transcendental_and_isSeparable_adjoin_of_perfectField.choose_spec
  let := hx.2
  obtain ⟨η, hηmem, hη0, hηD⟩ := exists_isGreatest_of_divisorClass_eq_canonicalClass hK hex hD
  let e := kaehlerDifferentialEquivWeilDifferentialOfSeparating hK hex hx.1
  have hω : e.symm ⟨η, hηmem⟩ ≠ 0 := by simpa [e] using hη0
  refine ⟨e.symm ⟨η, hηmem⟩, hω, ?_⟩
  rw [kaehlerDifferentialDivisor_eq hK hex hx.1]
  refine (isGreatest_weilDifferentialDivisor hK hex _ _).unique ?_
  simpa [e] using hηD

/-- **The Riemann–Roch theorem for Kähler differentials**: the divisor `W` of a nonzero Kähler
differential satisfies `ℓ(D) = deg D + 1 - g + ℓ(W - D)` for every divisor `D`. -/
theorem isRiemannRochDivisor_kaehlerDifferentialDivisor (ω : Ω[K⁄k]) (hω : ω ≠ 0) :
    (kaehlerDifferentialDivisor hK hex ω hω).IsRiemannRochDivisor (genus k K) :=
  isRiemannRochDivisor_of_divisorClass_eq_canonicalClass hK hex
    (divisorClass_kaehlerDifferentialDivisor hK hex ω hω)

/-! ### The spaces `Ω(D)` -/

/-- For a nonzero `ω₀` with divisor `W`, the multiple `f ω₀` is zero or has `div (f ω₀) ≥ D`
exactly when `f ∈ L(W - D)`. -/
private theorem forall_le_kaehlerDifferentialDivisor_smul_iff (D : Divisor k K) {ω₀ : Ω[K⁄k]}
    (hω₀ : ω₀ ≠ 0) (f : K) :
    (∀ hω : f • ω₀ ≠ 0, D ≤ kaehlerDifferentialDivisor hK hex (f • ω₀) hω) ↔
      f ∈ riemannRochSpace (kaehlerDifferentialDivisor hK hex ω₀ hω₀ - D) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have h := mem_riemannRochSpace_units_iff hK (z := Units.mk0 f hf)
    (D := kaehlerDifferentialDivisor hK hex ω₀ hω₀ - D)
  rw [Units.val_mk0] at h
  rw [h, ← add_sub_assoc, sub_nonneg, ← kaehlerDifferentialDivisor_smul hK hex hf hω₀]
  exact ⟨fun h' ↦ h' (smul_ne_zero hf hω₀), fun h' _ ↦ h'⟩

/-- The **space `Ω(D)` of differentials bounded by a divisor `D`** (Fulton, §8.6): the Kähler
differentials `ω` of `K / k` with `ω = 0` or `div ω ≥ D`, a `k`-subspace of `Ω[K⁄k]`. The
holomorphic differentials are `Ω(0)`. -/
def kaehlerDifferentialFiltration (D : Divisor k K) : Submodule k Ω[K⁄k] where
  carrier := {ω | ∀ hω : ω ≠ 0, D ≤ kaehlerDifferentialDivisor hK hex ω hω}
  zero_mem' h := absurd rfl h
  add_mem' {a b} ha hb := by
    obtain ⟨x, hx, hsep⟩ := hK.exists_transcendental_and_isSeparable_adjoin_of_perfectField
    have h0 := D_ne_zero_of_separating hx
    obtain ⟨f, rfl⟩ := KaehlerDifferential.exists_smul_eq_of_ne_zero hK h0 a
    obtain ⟨g, rfl⟩ := KaehlerDifferential.exists_smul_eq_of_ne_zero hK h0 b
    simp only [Set.mem_ofPred_eq, forall_le_kaehlerDifferentialDivisor_smul_iff hK hex D h0,
      ← add_smul] at ha hb ⊢
    exact add_mem ha hb
  smul_mem' c {a} ha := by
    obtain ⟨x, hx, hsep⟩ := hK.exists_transcendental_and_isSeparable_adjoin_of_perfectField
    have h0 := D_ne_zero_of_separating hx
    obtain ⟨f, rfl⟩ := KaehlerDifferential.exists_smul_eq_of_ne_zero hK h0 a
    simp only [Set.mem_ofPred_eq, forall_le_kaehlerDifferentialDivisor_smul_iff hK hex D h0]
      at ha ⊢
    rw [← smul_assoc, forall_le_kaehlerDifferentialDivisor_smul_iff hK hex D h0]
    exact Submodule.smul_mem _ c ha

theorem mem_kaehlerDifferentialFiltration_iff {D : Divisor k K} {ω : Ω[K⁄k]} :
    ω ∈ kaehlerDifferentialFiltration hK hex D ↔
      ∀ hω : ω ≠ 0, D ≤ kaehlerDifferentialDivisor hK hex ω hω :=
  Iff.rfl

/-- A nonzero differential lies in `Ω(D)` exactly when `div ω ≥ D`. -/
theorem mem_kaehlerDifferentialFiltration_iff_le {D : Divisor k K} {ω : Ω[K⁄k]} (hω : ω ≠ 0) :
    ω ∈ kaehlerDifferentialFiltration hK hex D ↔ D ≤ kaehlerDifferentialDivisor hK hex ω hω :=
  ⟨fun h ↦ h hω, fun h _ ↦ h⟩

/-- For a nonzero `ω₀`, `f ω₀ ∈ Ω(D)` exactly when `f ∈ L(div ω₀ - D)`. -/
theorem smul_mem_kaehlerDifferentialFiltration_iff (D : Divisor k K) {ω₀ : Ω[K⁄k]}
    (hω₀ : ω₀ ≠ 0) (f : K) :
    f • ω₀ ∈ kaehlerDifferentialFiltration hK hex D ↔
      f ∈ riemannRochSpace (kaehlerDifferentialDivisor hK hex ω₀ hω₀ - D) :=
  forall_le_kaehlerDifferentialDivisor_smul_iff hK hex D hω₀ f

/-- **Duality** `L(W - D) ≅ Ω(D)` (Fulton, §8.6, Proposition 9): for a nonzero Kähler
differential `ω₀` with divisor `W`, the map `f ↦ f ω₀` is a `k`-linear isomorphism from
`L(W - D)` onto `Ω(D)`. -/
def riemannRochSpaceEquivKaehlerDifferentialFiltration (D : Divisor k K) {ω₀ : Ω[K⁄k]}
    (hω₀ : ω₀ ≠ 0) :
    riemannRochSpace (kaehlerDifferentialDivisor hK hex ω₀ hω₀ - D) ≃ₗ[k]
      kaehlerDifferentialFiltration hK hex D :=
  LinearEquiv.ofBijective
    { toFun := fun f : riemannRochSpace (kaehlerDifferentialDivisor hK hex ω₀ hω₀ - D) ↦
        ⟨(f : K) • ω₀, (smul_mem_kaehlerDifferentialFiltration_iff hK hex D hω₀ (f : K)).2 f.2⟩
      map_add' f g := Subtype.ext (by simp [add_smul])
      map_smul' c f := Subtype.ext (by simp [smul_assoc]) }
    ⟨fun f g h ↦ Subtype.ext (smul_left_injective K hω₀ (congrArg Subtype.val h)), fun ω ↦ by
      obtain ⟨f, hf⟩ := KaehlerDifferential.exists_smul_eq_of_ne_zero hK hω₀ ω
      exact ⟨⟨f, (smul_mem_kaehlerDifferentialFiltration_iff hK hex D hω₀ f).1 (hf ▸ ω.2)⟩,
        Subtype.ext hf⟩⟩

@[simp]
theorem coe_riemannRochSpaceEquivKaehlerDifferentialFiltration_apply (D : Divisor k K)
    {ω₀ : Ω[K⁄k]} (hω₀ : ω₀ ≠ 0)
    (f : riemannRochSpace (kaehlerDifferentialDivisor hK hex ω₀ hω₀ - D)) :
    (riemannRochSpaceEquivKaehlerDifferentialFiltration hK hex D hω₀ f : Ω[K⁄k]) =
      (f : K) • ω₀ :=
  (rfl)

/-- **`δ(D) = ℓ(W - D)`** (Fulton, §8.6, Proposition 9(1)): for a nonzero Kähler differential
`ω₀` with divisor `W`, the space `Ω(D)` has dimension `ℓ(W - D)`. -/
theorem finrank_kaehlerDifferentialFiltration (D : Divisor k K) {ω₀ : Ω[K⁄k]} (hω₀ : ω₀ ≠ 0) :
    Module.finrank k (kaehlerDifferentialFiltration hK hex D) =
      Divisor.dim (kaehlerDifferentialDivisor hK hex ω₀ hω₀ - D) := by
  rw [Divisor.dim_def]
  exact (riemannRochSpaceEquivKaehlerDifferentialFiltration hK hex D hω₀).finrank_eq.symm

/-- **The holomorphic differentials form a space of dimension `g`** (Fulton, §8.6,
Proposition 9(2)). -/
theorem finrank_kaehlerDifferentialFiltration_zero :
    Module.finrank k (kaehlerDifferentialFiltration hK hex 0) = genus k K := by
  obtain ⟨x, hx, hsep⟩ := hK.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  have h0 := D_ne_zero_of_separating hx
  rw [finrank_kaehlerDifferentialFiltration hK hex 0 h0, sub_zero]
  exact (isRiemannRochDivisor_kaehlerDifferentialDivisor hK hex _ h0).dim_eq hK hex

end PlaneCurves

end
