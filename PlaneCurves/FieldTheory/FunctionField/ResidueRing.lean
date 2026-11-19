/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Residue rings of subrings of a function field of one variable

Let `k` be a field and `R` a `k`-algebra that is a domain of transcendence degree at most one
over `k`. Then the quotient of `R` by any nonzero ideal is algebraic over `k`
(`Ideal.isAlgebraic_quotient_of_trdeg_le_one`). Hence every nonzero prime ideal of `R` is
maximal (`Ideal.IsPrime.isMaximal_of_trdeg_le_one`), and if `k` is algebraically closed, the
map from `k` to the residue field is bijective
(`Ideal.bijective_algebraMap_quotient_of_trdeg_le_one`).

Every `k`-subalgebra of an algebraic function field of one variable over `k` is such a domain,
which gives Fulton's statement
(`TauCeti.IsFunctionField.isAlgebraic_quotient_and_isMaximal_and_bijective`).

The proof is Fulton's: for `x ∈ R` transcendental over `k` and `0 ≠ y ∈ I`, the element `y` is
algebraic over `k[x]`, so `I` meets `k[x]` in a nonzero element `f(x)`, and `f` kills the
residue of `x`.

As an application, let `k` be algebraically closed, `c : σ → K` and `R` a valuation subring of a
field `L ⊇ K` containing `k` and the `c l`. If the centre of `R` on `k[c]` is not zero, it is a
`k`-point: there is `a : σ → k` such that `f(c)` lies in the maximal ideal of `R` iff `f(a) = 0`
(`ValuationSubring.exists_forall_valuation_lt_one_iff_eval_eq_zero`).

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §6.5, Proposition 9(3)
-/

public section

variable {k R : Type*} [Field k] [CommRing R] [IsDomain R] [Algebra k R]

/-- In a domain of transcendence degree at most one over a field `k`, an element `x`
transcendental over `k` is a transcendence basis, so every element is algebraic over `k[x]`. -/
theorem Transcendental.isAlgebraic_adjoin_of_trdeg_le_one
    (h : Algebra.trdeg k R ≤ 1) {x : R} (hx : Transcendental k x) (y : R) :
    IsAlgebraic (Algebra.adjoin k {x}) y := by
  have hb : IsTranscendenceBasis k (fun _ : Unit ↦ x) :=
    ((algebraicIndependent_unique_type_iff).mpr hx).isTranscendenceBasis_of_lift_trdeg_le_of_finite
      (by simpa using h)
  have := hb.isAlgebraic
  rw [Set.range_const] at this
  exact Algebra.IsAlgebraic.isAlgebraic y

namespace Ideal

/-- The quotient of a domain of transcendence degree at most one over a field `k` by a nonzero
ideal is algebraic over `k`. -/
theorem isAlgebraic_quotient_of_trdeg_le_one (h : Algebra.trdeg k R ≤ 1) {I : Ideal R}
    (hI : I ≠ ⊥) : Algebra.IsAlgebraic k (R ⧸ I) := by
  refine ⟨fun z ↦ ?_⟩
  obtain ⟨x, rfl⟩ := Quotient.mk_surjective z
  by_cases hx : IsAlgebraic k x
  · exact hx.algHom (Quotient.mkₐ k I)
  obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hne := under_ne_bot_of_algebraic_mem hy0 hyI
    (Transcendental.isAlgebraic_adjoin_of_trdeg_le_one h hx y)
  obtain ⟨⟨a, ha⟩, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨f, rfl⟩ := ha
  refine ⟨f, fun hf ↦ ha0 ?_, ?_⟩
  · ext
    simp [hf]
  · have := Polynomial.aeval_algHom_apply (Quotient.mkₐ k I) x f
    rw [Quotient.mkₐ_eq_mk] at this
    rw [this]
    exact Quotient.eq_zero_iff_mem.mpr haI

/-- In a domain of transcendence degree at most one over a field, every nonzero prime ideal is
maximal. -/
theorem IsPrime.isMaximal_of_trdeg_le_one (h : Algebra.trdeg k R ≤ 1) {p : Ideal R}
    [p.IsPrime] (hp : p ≠ ⊥) : p.IsMaximal := by
  have := isAlgebraic_quotient_of_trdeg_le_one h hp
  exact Quotient.maximal_of_isField p
    (isField_of_isIntegral_of_isField' (Field.toIsField k))

/-- In a domain of transcendence degree at most one over an algebraically closed field `k`,
the map from `k` to the residue field of a nonzero prime ideal is bijective. -/
theorem bijective_algebraMap_quotient_of_trdeg_le_one [IsAlgClosed k]
    (h : Algebra.trdeg k R ≤ 1) {p : Ideal R} [p.IsPrime] (hp : p ≠ ⊥) :
    Function.Bijective (algebraMap k (R ⧸ p)) := by
  have := isAlgebraic_quotient_of_trdeg_le_one h hp
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

end Ideal

namespace TauCeti.IsFunctionField

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A `k`-subalgebra of an algebraic function field of one variable over `k` has transcendence
degree at most one over `k`. -/
theorem trdeg_subalgebra_le_one (hK : IsFunctionField k K) (R : Subalgebra k K) :
    Algebra.trdeg k R ≤ 1 :=
  hK.trdeg_eq_one ▸ trdeg_le_of_injective R.val Subtype.val_injective

/-- **Residue rings of subrings of a function field.** Let `K` be an algebraic function field
of one variable over a field `k`, `R` a `k`-subalgebra of `K` and `p` a nonzero prime ideal of
`R`. Then `R ⧸ p` is algebraic over `k`, `p` is maximal, and if `k` is algebraically closed,
the natural map `k → R ⧸ p` is bijective.

Milestone: *Residue rings of subrings of a function field of one variable*. -/
theorem isAlgebraic_quotient_and_isMaximal_and_bijective (hK : IsFunctionField k K)
    (R : Subalgebra k K) {p : Ideal R} [p.IsPrime] (hp : p ≠ ⊥) :
    Algebra.IsAlgebraic k (R ⧸ p) ∧ p.IsMaximal ∧
      (IsAlgClosed k → Function.Bijective (algebraMap k (R ⧸ p))) :=
  ⟨Ideal.isAlgebraic_quotient_of_trdeg_le_one (hK.trdeg_subalgebra_le_one R) hp,
    Ideal.IsPrime.isMaximal_of_trdeg_le_one (hK.trdeg_subalgebra_le_one R) hp,
    fun _ ↦ Ideal.bijective_algebraMap_quotient_of_trdeg_le_one
      (hK.trdeg_subalgebra_le_one R) hp⟩

end TauCeti.IsFunctionField

/-! ### Centres of valuation rings on finitely generated subalgebras -/

section ValuationSubring

open MvPolynomial

variable {k K L : Type*} [Field k] [Field K] [Algebra k K] [Field L] [Algebra k L]

/-- **The centre of a valuation ring on a finitely generated subalgebra.** Let `k` be
algebraically closed, `K` a function field of one variable over `k`, `c : σ → K`, and `R` a
valuation subring of `L ⊇ K` containing `k` and the `ψ (c l)`, whose maximal ideal contains some
nonzero `ψ (f(c))`. Then the elements `f(c)` with `ψ (f(c))` in the maximal ideal of `R` are
those with `f(a) = 0`, for a point `a ∈ kˢ`. -/
theorem ValuationSubring.exists_forall_valuation_lt_one_iff_eval_eq_zero [IsAlgClosed k]
    (hK : TauCeti.IsFunctionField k K) {σ : Type*} (c : σ → K) (ψ : K →ₐ[k] L)
    (R : ValuationSubring L) (hkR : ∀ a : k, algebraMap k L a ∈ R) (hc : ∀ l, ψ (c l) ∈ R)
    (h0 : ∃ f : MvPolynomial σ k, aeval c f ≠ 0 ∧ R.valuation (ψ (aeval c f)) < 1) :
    ∃ a : σ → k, ∀ f : MvPolynomial σ k, R.valuation (ψ (aeval c f)) < 1 ↔ eval a f = 0 := by
  have hψ : ∀ f : MvPolynomial σ k, ψ (aeval c f) ∈ R := fun f ↦ by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval, aeval_def]
    exact eval₂_mem (fun _ _ ↦ hkR _) hc
  let θ : (aeval c).range →+* R :=
    ((ψ : K →+* L).comp (aeval c).range.val.toRingHom).codRestrict R
      (by rintro ⟨_, f, rfl⟩; exact hψ f)
  let p := (IsLocalRing.maximalIdeal R).comap θ
  have hmem_p : ∀ f, (⟨aeval c f, f, rfl⟩ : (aeval c).range) ∈ p ↔
      R.valuation (ψ (aeval c f)) < 1 := fun f ↦ R.valuation_lt_one_iff ⟨_, hψ f⟩
  have hp0 : p ≠ ⊥ := by
    obtain ⟨f, hf0, hf⟩ := h0
    intro hp
    have := (hmem_p f).2 hf
    rw [hp, Ideal.mem_bot] at this
    exact hf0 (congrArg Subtype.val this)
  have hbij := Ideal.bijective_algebraMap_quotient_of_trdeg_le_one
    (hK.trdeg_subalgebra_le_one (aeval c).range) hp0
  choose a ha using fun l ↦ hbij.2 (Ideal.Quotient.mk p ⟨c l, X l, aeval_X c l⟩)
  let π : MvPolynomial σ k →ₐ[k] (aeval c).range ⧸ p :=
    (Ideal.Quotient.mkₐ k p).comp (aeval c).rangeRestrict
  have hπ : ∀ g, π g = Ideal.Quotient.mk p ⟨aeval c g, g, rfl⟩ := fun g ↦ by
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rfl
  have h : π = (Algebra.ofId k ((aeval c).range ⧸ p)).comp (aeval a) := by
    refine MvPolynomial.algHom_ext fun l ↦ ?_
    rw [hπ (X l), AlgHom.comp_apply, aeval_X a l, Algebra.ofId_apply, ha l]
    congr 2
    exact aeval_X c l
  refine ⟨a, fun f ↦ ?_⟩
  rw [← hmem_p, ← Ideal.Quotient.eq_zero_iff_mem, ← hπ f, h, AlgHom.comp_apply,
    Algebra.ofId_apply, map_eq_zero_iff _ hbij.1, aeval_eq_eval]


end ValuationSubring

end
