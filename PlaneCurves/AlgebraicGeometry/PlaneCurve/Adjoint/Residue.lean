/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Adjoint.Basic
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.Conductor
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Noether.Conditions

/-!
# The residue theorem of Brill and Noether

Let `k` be an algebraically closed field and `C : F = 0` an irreducible projective plane curve of
degree `d` all of whose multiple points are ordinary, with adjoint divisor `E` on its nonsingular
model.

**The adjoint division lemma.** Let `R`, `S` be forms of degrees `r`, `s`, with `F ∤ S`, such that
`div R ≥ div S + E` or `F ∣ R`. Then `R = A S + B F` for forms `A`, `B` of degrees `r - s` and
`r - d`. By Max Noether's fundamental theorem it is enough that Noether's conditions hold for
`F`, `S`, `R` at every point `P` of `C`: at a multiple point `P` of multiplicity `r_P`, the
inequality says `ord_Q(R) ≥ ord_Q(S) + r_P - 1` at the places `Q` over `P`, which is
Proposition 3 of §7.5; at a simple point `P`, the only place `Q` over `P` has
`ord_Q(G) = I(P, C ∩ G)`, so the inequality is `I(P, C ∩ S) ≤ I(P, C ∩ R)`, the simple-point
criterion.

**The residue theorem** (Fulton, §8.1). Let `D`, `D'` be linearly equivalent divisors with `D'`
effective, and `G` a form of degree `m` with `F ∤ G` and `div G = D + E + A` for an effective
divisor `A`. Then there is an adjoint `G'` of degree `m`, with `F ∤ G'`, such that
`div G' = D' + E + A`. Choose forms `H`, `H'` of the same degree with `F ∤ H`, `F ∤ H'` and
`D + div H = D' + div H'`. Then `div (G H) = div H' + D' + E + A ≥ div H' + E`, so the division
lemma writes `G H = G' H' + B F` with `deg G' = m`; and `div G' = div (G H) - div H' = D' + E + A`.

The book takes `D` effective and `G` an adjoint; neither is needed.

## Main results

* `PlaneCurves.Projective.exists_isHomogeneous_mul_add_mul_eq_of_le_formDivisor`: the adjoint
  division lemma.
* `PlaneCurves.Projective.exists_mem_adjointSubmodule_formDivisor_eq`: the residue theorem, the
  milestone.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §8.1, Residue Theorem
-/

public section

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace TauCeti
open TauCeti.AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace PlaneCurves.Projective

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {d : ℕ}
  {hF : F.IsHomogeneous d} [Fact (Irreducible F)]

/-- Noether's conditions for `F`, `S`, `R` at a point `P` of `C`, when every multiple point of `C`
is ordinary, `F ∤ R`, `F ∤ S` and `div S + E ≤ div R`. -/
private theorem noetherConditionsAt_of_le_formDivisor
    (hord : ∀ P, IsMultiplePoint F P → IsOrdinaryMultiplePoint F P)
    {r s : ℕ} {R S : MvPolynomial (Fin 3) k} (hR : R.IsHomogeneous r) (hS : S.IsHomogeneous s)
    (hFR : ¬F ∣ R) (hFS : ¬F ∣ S)
    (hle : formDivisor hF hS + adjointDivisor hF ≤ formDivisor hF hR)
    (P : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k))) :
    NoetherConditionsAt P.1 F S R := by
  have hPF : P.1 ∈ zeroLocus {F} := by
    rw [mem_zeroLocus_singleton_iff hF]
    simpa using (mem_zeroLocus_ideal_iff hF).1 P.2
  have hcoeff (Q : Place k (functionField hF)) :
      (formDivisor hF hS).coeff Q + (adjointDivisor hF).coeff Q ≤ (formDivisor hF hR).coeff Q :=
    hle Q
  rcases isSimplePoint_or_isMultiplePoint hF hPF with hP | hP
  · refine noetherConditionsAt_of_isSimplePoint hF hS hR hP ?_
    obtain ⟨Q, hQ⟩ := placesOver_nonempty hF P
    rw [mem_placesOver_iff] at hQ
    have hE : (adjointDivisor hF).coeff Q = 0 := by
      have h1 := (coeff_adjointDivisor_pos_iff (Q := Q)).not.2
        (by rw [hQ]; exact fun h ↦ h.not_isSimplePoint hP)
      have h2 := WeilDivisor.coeff_nonneg (adjointDivisor_nonneg (hF := hF)) Q
      omega
    have h := hcoeff Q
    rw [hE, add_zero, coeff_formDivisor_of_isSimplePoint hS hFS (by rwa [hQ]),
      coeff_formDivisor_of_isSimplePoint hR hFR (by rwa [hQ]), hQ] at h
    have hrel (G : MvPolynomial (Fin 3) k) (hFG : ¬F ∣ G) : IsRelPrime F G :=
      (Fact.out : Irreducible F).isRelPrime_iff_not_dvd.2 hFG
    rw [← ENat.natCast_toNat (intersectionNumber_ne_top_of_isRelPrime hF hS (hrel S hFS)),
      ← ENat.natCast_toNat (intersectionNumber_ne_top_of_isRelPrime hF hR (hrel R hFR))]
    exact_mod_cast h
  · refine noetherConditionsAt_of_forall_le_ordForm (hord _ hP) hS hR hFS fun Q hQ ↦ ?_
    have h := hcoeff Q
    rw [coeff_adjointDivisor, mem_placesOver_iff.1 hQ] at h
    rw [← coeff_formDivisor hS hFS, ← coeff_formDivisor hR hFR]
    exact_mod_cast h

/-- **The adjoint division lemma.** Let `k` be algebraically closed and `C : F = 0` an irreducible
projective plane curve of degree `d` all of whose multiple points are ordinary, with adjoint
divisor `E`. Let `R`, `S` be forms of degrees `r`, `s` with `F ∤ S`, such that
`div R ≥ div S + E` or `F ∣ R`. Then `R = A S + B F` for forms `A` of degree `r - s` and `B` of
degree `r - d`, with `A = 0` if `r < s` and `B = 0` if `r < d`. -/
theorem exists_isHomogeneous_mul_add_mul_eq_of_le_formDivisor
    (hord : ∀ P, IsMultiplePoint F P → IsOrdinaryMultiplePoint F P)
    {r s : ℕ} {R S : MvPolynomial (Fin 3) k} (hR : R.IsHomogeneous r) (hS : S.IsHomogeneous s)
    (hFS : ¬F ∣ S)
    (hle : F ∣ R ∨ formDivisor hF hS + adjointDivisor hF ≤ formDivisor hF hR) :
    ∃ A B : MvPolynomial (Fin 3) k, A.IsHomogeneous (r - s) ∧ B.IsHomogeneous (r - d) ∧
      (r < s → A = 0) ∧ (r < d → B = 0) ∧ A * S + B * F = R := by
  obtain ⟨B, A, hB, hA, hB0, hA0, h⟩ :=
    (exists_isHomogeneous_mul_add_mul_eq_iff_forall_noetherConditionsAt hF hS hR
      ((Fact.out : Irreducible F).isRelPrime_iff_not_dvd.2 hFS)).2 fun P hPF _ ↦ by
        by_cases hFR : F ∣ R
        · obtain ⟨B, rfl⟩ := hFR
          exact noetherConditionsAt_of_mem_span_pair hF hS
            (Ideal.mem_span_pair.2 ⟨B, 0, by ring⟩)
        · exact noetherConditionsAt_of_le_formDivisor hord hR hS hFR hFS (hle.resolve_left hFR)
            ⟨P, (mem_zeroLocus_ideal_iff hF).2 hPF⟩
  exact ⟨A, B, hA, hB, hA0, hB0, by rw [← h]; ring⟩

/-- **The residue theorem of Brill and Noether** (Fulton, §8.1). Let `k` be algebraically closed
and `C : F = 0` an irreducible projective plane curve all of whose multiple points are ordinary,
with adjoint divisor `E` on its nonsingular model. Let `D`, `D'` be linearly equivalent divisors,
`D'` effective, and `G` a form of degree `m` with `F ∤ G` and `div G = D + E + A` for an effective
divisor `A`. Then there is an adjoint `G'` of degree `m`, with `F ∤ G'`, such that
`div G' = D' + E + A`.

The book also assumes `D` effective and `G` an adjoint; the proof uses neither. It writes
`div G` only for `F ∤ G`, which is assumed here.

Milestone: *Brill–Noether residue theorem for plane curves*. -/
theorem exists_mem_adjointSubmodule_formDivisor_eq
    (hord : ∀ P, IsMultiplePoint F P → IsOrdinaryMultiplePoint F P)
    {D D' A : Divisor k (functionField hF)}
    (hDD' : (Place.orderSystem (functionField.isFunctionField hF)).LinearlyEquivalent D D')
    (hD' : 0 ≤ D') (hA : 0 ≤ A) {m : ℕ} {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous m)
    (hFG : ¬F ∣ G) (hGD : formDivisor hF hG = D + adjointDivisor hF + A) :
    ∃ (G' : MvPolynomial (Fin 3) k) (hG' : G' ∈ adjointSubmodule F m), ¬F ∣ G' ∧
      formDivisor hF (mem_adjointSubmodule_iff.1 hG').1 = D' + adjointDivisor hF + A := by
  have hprime := (Fact.out : Irreducible F).prime
  obtain ⟨n, H, H', hH, hH', hFH, hFH', hDH⟩ :=
    linearlyEquivalent_iff_exists_add_formDivisor_eq.1 hDD'
  have hFGH : ¬F ∣ G * H := fun h ↦ (hprime.dvd_or_dvd h).elim hFG hFH
  have hGH : formDivisor hF (hG.mul hH) = formDivisor hF hH' + (D' + adjointDivisor hF + A) := by
    rw [formDivisor_mul hG hH hFG hFH, hGD]
    linear_combination (norm := abel_nf) hDH
  obtain ⟨G', B, hG', -, -, -, hGB⟩ :=
    exists_isHomogeneous_mul_add_mul_eq_of_le_formDivisor hord (hG.mul hH) hH' hFH' (Or.inr (by
      rw [hGH, add_assoc, add_le_add_iff_left]
      exact le_add_of_nonneg_left (add_nonneg hD' hA) |>.trans_eq (by abel)))
  rw [Nat.add_sub_cancel] at hG'
  have hFG' : ¬F ∣ G' := fun h ↦
    hFGH (hGB ▸ dvd_add (dvd_mul_of_dvd_left h _) (dvd_mul_left _ _))
  have hdiv : formDivisor hF hG' = D' + adjointDivisor hF + A := by
    have h := formDivisor_eq_of_dvd_sub (hF := hF) (hG'.mul hH') (hG.mul hH)
      ⟨-B, by rw [← hGB]; ring⟩
    rw [hGH, formDivisor_mul hG' hH' hFG' hFH'] at h
    exact add_right_cancel (h.trans (add_comm _ _))
  have hE : adjointDivisor hF ≤ formDivisor hF hG' := by
    rw [hdiv, add_assoc]
    exact (le_add_of_nonneg_right hA).trans (le_add_of_nonneg_left hD')
  exact ⟨G',
    mem_adjointSubmodule_iff.2 ⟨hG', (isAdjoint_iff_le_formDivisor hord hG' hFG').2 hE⟩,
    hFG', hdiv⟩

end PlaneCurves.Projective

end
