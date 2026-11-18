/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Consequences.GenusZero
public import TauCeti.FieldTheory.FunctionField.Consequences.PointSeparation
public import TauCeti.FieldTheory.FunctionField.Divisor.Equiv
public import TauCeti.FieldTheory.FunctionField.Place.ConstantField
public import TauCeti.FieldTheory.FunctionField.Place.Existence
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc

/-!
# Genus-zero criteria for function fields

Let `F / k` be an algebraic function field of one variable that has two places of degree one, for
example any function field over an algebraically closed field `k`. Then the following are
equivalent
(`TauCeti.tfae_genus_eq_zero`; Fulton, §8.2, Corollary to Proposition 4):

1. `F` is rational: `F ≃ₐ[k] k(t)`;
2. some `x ∈ F` has a zero divisor `(x)₀` of degree one;
3. `ℓ(P) > 1` for some place `P` of degree one;
4. `F` has genus zero;
5. every divisor of degree zero is principal: the degree-zero class group `Cl⁰(F)` is trivial.

Each implication is stated under the hypotheses its proof needs. Tau Ceti has the steps
`1 → 4` (`TauCeti.genus_eq_zero_of_algHom_ratFunc`) and
`4 → 1` given a divisor of degree one
(`TauCeti.nonempty_algEquiv_ratFunc_of_genus_eq_zero_of_divisor_degree_eq_one`); this file adds
the others.

## Main results

* `TauCeti.nonempty_algEquiv_ratFunc_of_degree_zeros_eq_one`: a function with a single simple zero
  generates `F`, so `F` is rational.
* `TauCeti.Divisor.dim_ofPoint_eq_two_of_genus_eq_zero`: in genus zero, `ℓ(P) = 2` at every
  place of degree one.
* `TauCeti.genus_eq_zero_of_one_lt_dim_ofPoint`: `ℓ(P) > 1` at a place of degree one forces
  genus zero.
* `TauCeti.Divisor.exists_degree_zeros_eq_one_of_one_lt_dim_ofPoint`: `ℓ(P) > 1` at a place of
  degree one gives a function whose zero divisor has degree one.
* `TauCeti.Divisor.ker_degreeClass_eq_bot_of_algEquiv_ratFunc`: a rational function field has
  trivial `Cl⁰`.
* `TauCeti.genus_eq_zero_of_ker_degreeClass_eq_bot`: trivial `Cl⁰` and two places of degree one
  force genus zero.
* `TauCeti.tfae_genus_eq_zero`, `TauCeti.tfae_genus_eq_zero_of_isAlgClosed`: the five conditions
  are equivalent.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §8.2, Corollary to Proposition 4
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][Stichtenoth2009], Proposition 1.6.3
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **A function with a single simple zero makes a function field rational**: if the zero
divisor `(x)₀` has degree one, then `[F : k(x)] = 1`, so `F = k(x)` and `F ≃ₐ[k] k(t)`. -/
theorem nonempty_algEquiv_ratFunc_of_degree_zeros_eq_one (hF : IsFunctionField k F) {x : Fˣ}
    (hx : Divisor.degree (Divisor.zeros hF x) = 1) :
    Nonempty (F ≃ₐ[k] RatFunc k) := by
  have hxt : Transcendental k (x : F) := by
    intro hxa
    have h0 : Divisor.zeros hF x = 0 := WeilDivisor.ext fun Q ↦ by
      simp [Q.ord_eq_zero_of_isAlgebraic hxa]
    simp [h0] at hx
  rw [Divisor.degree_zeros hF x hxt] at hx
  have htop : IntermediateField.adjoin k {(x : F)} = ⊤ :=
    IntermediateField.finrank_eq_one_iff_eq_top.mp (by exact_mod_cast hx)
  exact ⟨((RatFunc.algEquivOfTranscendental (x : F) hxt).trans
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)).symm⟩

namespace Divisor

/-- **In genus zero `ℓ(P) = 2`** at every place `P` of degree one, by Riemann–Roch. -/
theorem dim_ofPoint_eq_two_of_genus_eq_zero (hF : IsFunctionField k F) (hg : genus k F = 0)
    {P : Place k F} (hP : P.degree = 1) :
    dim (WeilDivisor.ofPoint P : Divisor k F) = 2 := by
  have h := dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree hF
    (P.isIntegrallyClosedIn_of_degree_eq_one hP) (D := WeilDivisor.ofPoint P)
    (by simp [hg, hP])
  rw [degree_ofPoint, hP, hg] at h
  omega

/-- **A function with a single simple pole**: if `ℓ(P) > 1` at a place `P` of degree one, some
function has zero divisor of degree one. -/
theorem exists_degree_zeros_eq_one_of_one_lt_dim_ofPoint (hF : IsFunctionField k F)
    {P : Place k F} (hP : P.degree = 1) (h : 1 < dim (WeilDivisor.ofPoint P : Divisor k F)) :
    ∃ x : Fˣ, degree (zeros hF x) = 1 := by
  have hex := P.isIntegrallyClosedIn_of_degree_eq_one hP
  obtain ⟨z, hzP, hz0⟩ : ∃ z ∈ riemannRochSpace (WeilDivisor.ofPoint P : Divisor k F),
      z ∉ riemannRochSpace (0 : Divisor k F) := by
    by_contra! hle
    have heq : riemannRochSpace (WeilDivisor.ofPoint P : Divisor k F) =
        riemannRochSpace (0 : Divisor k F) :=
      le_antisymm hle (riemannRochSpace_mono (WeilDivisor.ofPoint_nonneg P))
    have h1 := dim_zero_of_isIntegrallyClosedIn hF hex
    rw [dim_def] at h h1
    rw [heq] at h
    omega
  have hzt : Transcendental k z := fun hza ↦
    hz0 ((mem_riemannRochSpace_zero_iff hF).mpr hza.isIntegral)
  have hle := finrank_adjoin_le_degree_of_mem_riemannRochSpace hF
    (WeilDivisor.ofPoint_nonneg P) hzP
  rw [degree_ofPoint, hP] at hle
  have : FiniteDimensional (IntermediateField.adjoin k {z}) F := hF.finiteDimensional_adjoin hzt
  have hpos := Module.finrank_pos (R := IntermediateField.adjoin k {z}) (M := F)
  refine ⟨Units.mk0 z hzt.ne_zero, ?_⟩
  rw [degree_zeros hF (Units.mk0 z hzt.ne_zero) (by rw [Units.val_mk0]; exact hzt),
    Units.val_mk0]
  omega

/-- **A rational function field has trivial degree-zero class group**: `Cl⁰(F)` is trivial for
every `F ≃ₐ[k] k(t)`. -/
theorem ker_degreeClass_eq_bot_of_algEquiv_ratFunc (hF : IsFunctionField k F)
    (e : F ≃ₐ[k] RatFunc k) : (degreeClass hF).ker = ⊥ := by
  let φ := degreeZeroClassGroupEquivOfRingEquiv (RingEquiv.refl k) e.toRingEquiv
    (fun c ↦ by simp) hF (IsFunctionField.ratFunc k)
  have : Subsingleton (degreeClass (IsFunctionField.ratFunc k)).ker := by
    rw [ker_degreeClass_ratFunc_eq_bot]
    infer_instance
  have : Subsingleton (degreeClass hF).ker := φ.toEquiv.subsingleton
  exact AddSubgroup.eq_bot_of_subsingleton _

end Divisor

/-- **`ℓ(P) > 1` forces genus zero**: in positive genus `ℓ(P) = 1` at every place of degree
one (`TauCeti.Divisor.dim_ofPoint_eq_one_of_genus_pos`). -/
theorem genus_eq_zero_of_one_lt_dim_ofPoint (hF : IsFunctionField k F) {P : Place k F}
    (hP : P.degree = 1) (h : 1 < Divisor.dim (WeilDivisor.ofPoint P : Divisor k F)) :
    genus k F = 0 := by
  by_contra hg
  have := Divisor.dim_ofPoint_eq_one_of_genus_pos hF (P.isIntegrallyClosedIn_of_degree_eq_one hP)
    (Nat.pos_of_ne_zero hg) hP
  omega

/-- **A trivial degree-zero class group forces genus zero**, given two distinct places `P` and
`Q` of degree one: in positive genus `P - Q` is not principal
(`TauCeti.Place.eq_of_linearlyEquivalent_ofPoint_of_genus_pos`). The second place is needed:
over the field with two elements, the elliptic function field of `y² + y = x³ + x + 1` has a
single place of degree one and trivial `Cl⁰`. -/
theorem genus_eq_zero_of_ker_degreeClass_eq_bot (hF : IsFunctionField k F) {P Q : Place k F}
    (hP : P.degree = 1) (hQ : Q.degree = 1) (hPQ : P ≠ Q)
    (h : (Divisor.degreeClass hF).ker = ⊥) :
    genus k F = 0 := by
  by_contra hg
  have hD : (Place.orderSystem hF).divisorClass
      (WeilDivisor.ofPoint P - WeilDivisor.ofPoint Q) ∈ (Divisor.degreeClass hF).ker := by
    rw [AddMonoidHom.mem_ker, Divisor.degreeClass_divisorClass]
    simp [hP, hQ]
  rw [h, AddSubgroup.mem_bot, Divisor.divisorClass_eq_zero_iff] at hD
  exact hPQ (Place.eq_of_linearlyEquivalent_ofPoint_of_genus_pos hF (Nat.pos_of_ne_zero hg) hP
    ((Divisor.linearlyEquivalent_iff hF).mpr hD))

/-- **Genus-zero criteria for a function field** (Fulton, §8.2, Corollary to Proposition 4): for
a function field `F / k` with two places of degree one, the following are equivalent:
`F` is rational; some function has a zero divisor of degree one; `ℓ(P) > 1` for some place `P`
of degree one; `F` has genus zero; every divisor of degree zero is principal.

The first four are equivalent as soon as there is one place of degree one; the second is needed
only for the last condition (see `TauCeti.genus_eq_zero_of_ker_degreeClass_eq_bot`). -/
theorem tfae_genus_eq_zero (hF : IsFunctionField k F)
    (hP : {P : Place k F | P.degree = 1}.Nontrivial) :
    List.TFAE [Nonempty (F ≃ₐ[k] RatFunc k),
      ∃ x : Fˣ, Divisor.degree (Divisor.zeros hF x) = 1,
      ∃ P : Place k F, P.degree = 1 ∧ 1 < Divisor.dim (WeilDivisor.ofPoint P : Divisor k F),
      genus k F = 0,
      (Divisor.degreeClass hF).ker = ⊥] := by
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := hP
  tfae_have 1 → 4 := fun ⟨e⟩ ↦ genus_eq_zero_of_algHom_ratFunc e.toAlgHom
  tfae_have 4 → 3 := fun hg ↦
    ⟨P, hP, by rw [Divisor.dim_ofPoint_eq_two_of_genus_eq_zero hF hg hP]; norm_num⟩
  tfae_have 3 → 2 := fun ⟨R, hR, h⟩ ↦
    Divisor.exists_degree_zeros_eq_one_of_one_lt_dim_ofPoint hF hR h
  tfae_have 2 → 1 := fun ⟨x, hx⟩ ↦ nonempty_algEquiv_ratFunc_of_degree_zeros_eq_one hF hx
  tfae_have 1 → 5 := fun ⟨e⟩ ↦ Divisor.ker_degreeClass_eq_bot_of_algEquiv_ratFunc hF e
  tfae_have 5 → 4 := genus_eq_zero_of_ker_degreeClass_eq_bot hF hP hQ hPQ
  tfae_finish

/-- **Genus-zero criteria over an algebraically closed field** (Fulton, §8.2, Corollary to
Proposition 4): for a function field `F / k` with `k` algebraically closed, the following are
equivalent: `F` is rational; some function has a zero divisor of degree one; `ℓ(P) > 1` for some
place `P`; `F` has genus zero; every divisor of degree zero is principal. -/
theorem tfae_genus_eq_zero_of_isAlgClosed [IsAlgClosed k] (hF : IsFunctionField k F) :
    List.TFAE [Nonempty (F ≃ₐ[k] RatFunc k),
      ∃ x : Fˣ, Divisor.degree (Divisor.zeros hF x) = 1,
      ∃ P : Place k F, 1 < Divisor.dim (WeilDivisor.ofPoint P : Divisor k F),
      genus k F = 0,
      (Divisor.degreeClass hF).ker = ⊥] := by
  have hdeg := fun P : Place k F ↦ P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF
  have h := tfae_genus_eq_zero hF (Place.infinite_setOf_degree_eq_one hF).nontrivial
  simpa only [hdeg, true_and] using h

end TauCeti

end
