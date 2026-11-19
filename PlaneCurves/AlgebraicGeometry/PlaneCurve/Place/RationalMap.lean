/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Center
public import PlaneCurves.RingTheory.Valuation.ValuationSubring

/-!
# Rational maps from a curve to a projective plane curve

Let `k` be algebraically closed, `C : F = 0` an irreducible projective plane curve with function
field `K = k(C)`, and `C'` a curve with function field `L = k(C')`, an algebraic function field
of one variable over `k`. A dominating rational map `f : C' ⇢ C` is a `k`-embedding
`ψ : K →ₐ[k] L`; it is defined at a point `P'` of `C'`, with value `P ∈ C`, when `𝒪_{P'}(C')`
dominates `ψ(𝒪_P(C))` (Fulton, §6.6, Proposition 11). A rational map that is not dominating is
constant, and so defined everywhere.

If `P'` is a simple point, `𝒪_{P'}(C')` is a discrete valuation ring with fraction field `L`, and
it does not contain `ψ(K)`: `L` is algebraic over `ψ(K)`, so a valuation ring containing `ψ(K)` is
all of `L` (`ValuationSubring.eq_top_of_forall_algebraMap_mem`). By Theorem 1 of §7.1
(`PlaneCurves.Projective.existsUnique_isCenter`) it dominates `ψ(𝒪_P(C))` for exactly one
`P ∈ C`: `f` is defined at `P'` (Fulton, §7.1, Corollary 1). For a nonsingular `C'`, whose
points are the places of `L`, every place has a value, so `f` is a morphism.

## Main results

* `PlaneCurves.Projective.exists_notMem_of_ne_top`: a valuation subring `R ≠ L` does not contain
  `ψ(k(C))`.
* `PlaneCurves.Projective.existsUnique_isCenter_of_ne_top`: a valuation subring `R ≠ L` of `L`
  containing `k` is centred at exactly one point of `C`.
* `PlaneCurves.Projective.existsUnique_map_le_of_isDiscreteValuationRing`: a local subring of
  `L` that is a discrete valuation ring containing `k`, with fraction field `L`, dominates
  `ψ(𝒪_P(C))` for exactly one `P ∈ C`.
* `PlaneCurves.Projective.existsUnique_isCenter_integers`: every place of `L` is centred at
  exactly one point of `C`.
* `PlaneCurves.Projective.rationalMap_definedAt_simplePoint`: the milestone, both forms.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §6.6, Proposition 11, and §7.1, Theorem 1 and
  Corollary 1
-/

public section

open MvPolynomial TauCeti TauCeti.AlgebraicGeometry PlaneCurves.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] {F : MvPolynomial (Fin 3) k} {d : ℕ} {hF : F.IsHomogeneous d}
  [Fact (Irreducible F)] {L : Type*} [Field L] [Algebra k L]

/-- Let `ψ : k(C) → L` be a `k`-embedding of the function field of `C` into an algebraic function
field `L` of one variable. A valuation subring `R ≠ L` of `L` does not contain `ψ(k(C))`, since
`L` is algebraic over `ψ(k(C))`. -/
theorem exists_notMem_of_ne_top (hL : IsFunctionField k L) (ψ : functionField hF →ₐ[k] L)
    {R : ValuationSubring L} (hR : R ≠ ⊤) : ∃ z, ψ z ∉ R := by
  let := (ψ : functionField hF →+* L).toAlgebra
  have : IsScalarTower k (functionField hF) L := ⟨fun c x y ↦ by
    change ψ (c • x) * y = c • (ψ x * y)
    rw [map_smul, smul_mul_assoc]⟩
  have := (functionField.isFunctionField hF).isAlgebraic_of_isFunctionField hL
  exact ValuationSubring.exists_algebraMap_notMem_of_ne_top (E := functionField hF) hR

/-- Let `k` be algebraically closed, `C : F = 0` an irreducible projective plane curve, and
`ψ : k(C) → L` a `k`-embedding into an algebraic function field `L` of one variable. A valuation
subring `R ≠ L` of `L` containing `k` dominates `ψ(𝒪_P(C))` for exactly one point `P ∈ C`. -/
theorem existsUnique_isCenter_of_ne_top [IsAlgClosed k] (hL : IsFunctionField k L)
    (ψ : functionField hF →ₐ[k] L) {R : ValuationSubring L}
    (hkR : ∀ c : k, algebraMap k L c ∈ R) (hR : R ≠ ⊤) : ∃! P, IsCenter hF ψ R P :=
  existsUnique_isCenter hkR (exists_notMem_of_ne_top hL ψ hR)

/-- **A rational map to a projective curve is defined at a simple point.** Let `k` be
algebraically closed, `C : F = 0` an irreducible projective plane curve, `ψ : k(C) → L` a
`k`-embedding into an algebraic function field `L` of one variable, and `B` a local subring of
`L` containing `k` that is a discrete valuation ring with fraction field `L` (the local ring of a
simple point of a curve with function field `L`). Then `B` dominates `ψ(𝒪_P(C))` for exactly one
point `P ∈ C`. -/
theorem existsUnique_map_le_of_isDiscreteValuationRing [IsAlgClosed k]
    (hL : IsFunctionField k L) (ψ : functionField hF →ₐ[k] L) (B : LocalSubring L)
    [IsDiscreteValuationRing B.toSubring] [IsFractionRing B.toSubring L]
    (hkB : ∀ c : k, algebraMap k L c ∈ B.toSubring) :
    ∃! P, (localSubring hF P).map (ψ : functionField hF →+* L) ≤ B := by
  have := existsUnique_isCenter_of_ne_top hL ψ
    (fun c ↦ LocalSubring.mem_toValuationSubring.2 (hkB c)) B.toValuationSubring_ne_top
  simpa only [isCenter_def, LocalSubring.toLocalSubring_toValuationSubring] using this

/-- Let `k` be algebraically closed, `C : F = 0` an irreducible projective plane curve, and
`ψ : k(C) → L` a `k`-embedding into an algebraic function field `L` of one variable. The
valuation ring of every place of `L` dominates `ψ(𝒪_P(C))` for exactly one point `P ∈ C`. -/
theorem existsUnique_isCenter_integers [IsAlgClosed k] (hL : IsFunctionField k L)
    (ψ : functionField hF →ₐ[k] L) (Q : Place k L) : ∃! P, IsCenter hF ψ Q.integers P :=
  existsUnique_isCenter_of_ne_top hL ψ Q.algebraMap_mem_integers Q.integers_ne_top

/-- **Rational maps from a curve to a projective curve are defined at simple points.** Let `k` be
algebraically closed, `C : F = 0` an irreducible projective plane curve with function field
`k(C)`, and `C'` a curve with function field `L`, an algebraic function field of one variable
over `k`. A dominating rational map `C' ⇢ C` is a `k`-embedding `ψ : k(C) → L`; it is defined at
a point of `C'` with local ring `B`, with value `P ∈ C`, if `B` dominates `ψ(𝒪_P(C))`.

1. If `B ⊆ L` is the local ring of a simple point, a discrete valuation ring containing `k`
  with fraction field `L`, then `ψ` is defined there, with a unique value `P`.
2. If `C'` is nonsingular, its points are the places of `L`, and `ψ` is a morphism: at every
  place `Q` of `L` it is defined, with a unique value.

A rational map that is not dominating is constant, and defined everywhere.

Milestone: *Rational maps from a curve to a projective curve are defined at simple points*. -/
theorem rationalMap_definedAt_simplePoint [IsAlgClosed k] (hL : IsFunctionField k L)
    (ψ : functionField hF →ₐ[k] L) :
    (∀ (B : LocalSubring L) [IsDiscreteValuationRing B.toSubring] [IsFractionRing B.toSubring L],
      (∀ c : k, algebraMap k L c ∈ B.toSubring) →
        ∃! P, (localSubring hF P).map (ψ : functionField hF →+* L) ≤ B) ∧
    ∀ Q : Place k L, ∃! P, IsCenter hF ψ Q.integers P :=
  ⟨fun B _ _ hkB ↦ existsUnique_map_le_of_isDiscreteValuationRing hL ψ B hkB,
    existsUnique_isCenter_integers hL ψ⟩

end PlaneCurves.Projective

end
