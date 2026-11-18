/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.GoingUp

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

end
