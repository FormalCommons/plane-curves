/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.AffineSpace.QuotientPiLocalRing
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Bezout.Basic
public import PlaneCurves.RingTheory.Ideal.Span
public import PlaneCurves.RingTheory.MvPolynomial.HomogeneousIdeal

/-!
# Max Noether's fundamental theorem

Let `F`, `G` and `H` be forms in `k[X₀, …, Xₙ]` and `P` a point of `ℙⁿ`. **Noether's conditions**
hold at `P` (with respect to `F`, `G`, `H`) if `H_* ∈ (F_*, G_*)` in the local ring `𝒪_P(ℙⁿ)`;
here, as for intersection numbers, this is stated with the localized ideal
`localIdeal P (F, G)`, which needs no choice of a linear form `L` with `L(P) ≠ 0`. They hold at
every `P` where `F` or `G` does not vanish, and at every `P` if `H ∈ (F, G)`.

**Max Noether's fundamental theorem** (Fulton, §5.5) is the converse for plane curves: let `k`
be algebraically closed and `F`, `G` forms in `k[X, Y, Z]` with no common component. A form `H`
lies in `(F, G)` if and only if Noether's conditions hold at every point of `V(F) ∩ V(G)`; and
then `H = A F + B G` with `A` and `B` forms of degrees `deg H - deg F` and `deg H - deg G` (a form
of negative degree meaning `0`).

The proof is Fulton's. A projective change of coordinates moves the finitely many common zeros
off the line `Z = 0`, and does not change Noether's conditions. In the chart `Z ≠ 0`, the local
conditions say that the image of `H_*` in `∏_P 𝒪_P(𝔸²)/(F_*, G_*) ≅ k[X, Y]/(F_*, G_*)` is zero,
so `H_* ∈ (F_*, G_*)`; Step 2 of the proof of Bézout's theorem gives `H ∈ (F, G)`. The degrees of
`A` and `B` come from homogeneous components.

## Main definitions

* `PlaneCurves.Projective.NoetherConditionsAt P F G H`: `H_* ∈ (F_*, G_*)` in `𝒪_P(ℙⁿ)`.

## Main results

* `noetherConditionsAt_iff`: Noether's conditions in terms of the local equations.
* `noetherConditionsAt_of_mem_span_pair`, `noetherConditionsAt_of_eval_ne_zero`: they hold if
  `H ∈ (F, G)`, and at points off `V(F) ∩ V(G)`.
* `noetherConditionsAt_linearSubst_iff`: they are invariant under projective changes of
  coordinates.
* `dehomogenize_mem_span_pair_of_forall_noetherConditionsAt`: in a chart containing finitely
  many common zeros of `F_*` and `G_*`, Noether's conditions give `H_* ∈ (F_*, G_*)`.
* `mem_span_pair_iff_forall_noetherConditionsAt`: Max Noether's theorem, `H ∈ (F, G)` iff
  Noether's conditions hold at every point of `V(F) ∩ V(G)`.
* `exists_isHomogeneous_mul_add_mul_eq_iff_forall_noetherConditionsAt`: its degree form.
* `noetherConditionsAt_spec`: the milestone, both forms.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.5
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {n : ℕ} {P : ℙ k (Fin (n + 1) → k)}
  {F G H : MvPolynomial (Fin (n + 1)) k} {d e r : ℕ}

/-! ### Noether's conditions -/

variable (P F G H) in
/-- **Noether's conditions** at a point `P` of `ℙⁿ`, for polynomials `F`, `G` and `H`: the local
equation `H_*` lies in the localized ideal of `(F, G)` in `𝒪_P(ℙⁿ)`. For forms `F` and `G` this
says `H_* ∈ (F_*, G_*)` (`noetherConditionsAt_iff`), Fulton's condition, which does not depend on
the linear form used to define the local equations. -/
def NoetherConditionsAt : Prop :=
  localEquation P H ∈ localIdeal P (Ideal.span {F, G})

theorem noetherConditionsAt_def :
    NoetherConditionsAt P F G H ↔ localEquation P H ∈ localIdeal P (Ideal.span {F, G}) :=
  Iff.rfl

/-- For forms `F` and `G`, Noether's conditions at `P` say `H_* ∈ (F_*, G_*)` in `𝒪_P(ℙⁿ)`. -/
theorem noetherConditionsAt_iff (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e) :
    NoetherConditionsAt P F G H ↔
      localEquation P H ∈ Ideal.span {localEquation P F, localEquation P G} := by
  rw [noetherConditionsAt_def, localIdeal_span_pair hF hG]

/-- Noether's conditions hold everywhere for `H ∈ (F, G)`, with `F` and `G` forms. -/
theorem noetherConditionsAt_of_mem_span_pair (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e)
    (h : H ∈ Ideal.span {F, G}) : NoetherConditionsAt P F G H := by
  rw [noetherConditionsAt_iff hF hG, ← Set.image_pair, ← Ideal.map_span]
  exact Ideal.mem_map_of_mem _ h

/-- Noether's conditions hold at every point `P` where one of the forms `F` and `G` does not
vanish: then `(F_*, G_*)` is the unit ideal. -/
theorem noetherConditionsAt_of_eval_ne_zero (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e)
    (h : eval P.rep F ≠ 0 ∨ eval P.rep G ≠ 0) : NoetherConditionsAt P F G H := by
  suffices Ideal.span {localEquation P F, localEquation P G} = ⊤ by
    simp [noetherConditionsAt_iff hF hG, this]
  rcases h with h | h
  · exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp))
      ((isUnit_localEquation_iff hF).2 h)
  · exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp))
      ((isUnit_localEquation_iff hG).2 h)

/-- **Noether's conditions under a change of coordinates.** For an invertible matrix `M` with
projective change of coordinates `T`, Noether's conditions for `F^T`, `G^T`, `H^T` hold at `Q`
iff Noether's conditions for `F`, `G`, `H` hold at `T(Q)`. -/
theorem noetherConditionsAt_linearSubst_iff (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e)
    (hH : H.IsHomogeneous r) (M : GL (Fin (n + 1)) k) (Q : ℙ k (Fin (n + 1) → k)) :
    NoetherConditionsAt Q (linearSubst M.1 F) (linearSubst M.1 G) (linearSubst M.1 H) ↔
      NoetherConditionsAt (map M.1.mulVecLin (Matrix.mulVec_injective_of_isUnit M.isUnit) Q)
        F G H := by
  rw [noetherConditionsAt_iff (hF.linearSubst _) (hG.linearSubst _), noetherConditionsAt_iff hF hG]
  exact Ideal.mem_span_pair_iff_of_ringEquiv (localRing.linearSubstEquiv rfl).toRingEquiv
    (associated_linearSubstEquiv_localEquation hF M rfl)
    (associated_linearSubstEquiv_localEquation hG M rfl)
    (associated_linearSubstEquiv_localEquation hH M rfl)

/-- **Noether's conditions in a chart.** Let `k` be algebraically closed and `F`, `G`, `H` forms
such that the dehomogenizations `F_*`, `G_*` at `Xᵢ = 1` have finitely many common zeros. If
Noether's conditions hold at every point of the chart `Xᵢ ≠ 0`, then `H_* ∈ (F_*, G_*)` in
`k[X₁, …, Xₙ]`: its image in `∏_P 𝒪_P(𝔸ⁿ)/(F_*, G_*) ≅ k[X₁, …, Xₙ]/(F_*, G_*)` is zero. -/
theorem dehomogenize_mem_span_pair_of_forall_noetherConditionsAt [IsAlgClosed k]
    (hF : F.IsHomogeneous d) (hG : G.IsHomogeneous e) (hH : H.IsHomogeneous r) {i : Fin (n + 1)}
    (hV : (zeroLocus k (Ideal.span {dehomogenize i F, dehomogenize i G})).Finite)
    (hN : ∀ P ∈ affineOpen i, NoetherConditionsAt P F G H) :
    dehomogenize i H ∈ Ideal.span {dehomogenize i F, dehomogenize i G} := by
  set I := Ideal.span {dehomogenize i F, dehomogenize i G}
  rw [← Ideal.Quotient.eq_zero_iff_mem,
    ← map_eq_zero_iff _ (AffineSpace.quotientPiLocalRingAlgEquiv I hV).injective]
  funext ⟨x, hx⟩
  obtain ⟨P, hP, rfl⟩ : ∃ P ∈ affineOpen i, affineChart i P = x :=
    ⟨_, by simp, (affineChart i).right_inv (by simp)⟩
  rw [AffineSpace.quotientPiLocalRingAlgEquiv_mk, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.map_span, Set.image_pair]
  exact (Ideal.mem_span_pair_iff_of_ringEquiv (localRing.chartEquiv i hP).toRingEquiv
    (associated_chartEquiv_localEquation hF hP) (associated_chartEquiv_localEquation hG hP)
    (associated_chartEquiv_localEquation hH hP)).2 ((noetherConditionsAt_iff hF hG).1 (hN P hP))

/-! ### Max Noether's fundamental theorem -/

variable [IsAlgClosed k] {F G H : MvPolynomial (Fin 3) k} {m : ℕ}

/-- **Max Noether's theorem in good coordinates.** Let `k` be algebraically closed and `F`, `G`
relatively prime forms in `k[X, Y, Z]` whose common zeros all lie in the chart `Xᵢ ≠ 0`. A form
`H` for which Noether's conditions hold at every point lies in `(F, G)`. -/
theorem mem_span_pair_of_forall_noetherConditionsAt_of_forall_mem_affineOpen
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous e) (hH : H.IsHomogeneous r)
    (hFG : IsRelPrime F G) {i : Fin 3}
    (h : ∀ P : ℙ k (Fin 3 → k), eval P.rep F = 0 → eval P.rep G = 0 → P ∈ affineOpen i)
    (hN : ∀ P : ℙ k (Fin 3 → k), NoetherConditionsAt P F G H) : H ∈ Ideal.span {F, G} :=
  mem_span_pair_of_dehomogenize_mem hF hG hH (isRelPrime_bind₁_update_X_zero hF hG h)
    (dehomogenize_mem_span_pair_of_forall_noetherConditionsAt hF hG hH
      (finite_zeroLocus_span_pair_of_isRelPrime (isRelPrime_dehomogenize hF hG hFG) k)
      fun P _ ↦ hN P)

/-- **Max Noether's fundamental theorem.** Let `k` be algebraically closed, `F` and `G` forms in
`k[X, Y, Z]` with no common component, and `H` a form. Then `H ∈ (F, G)` if and only if Noether's
conditions hold at every point of `V(F) ∩ V(G)`. -/
theorem mem_span_pair_iff_forall_noetherConditionsAt (hF : F.IsHomogeneous m)
    (hG : G.IsHomogeneous e) (hH : H.IsHomogeneous r) (hFG : IsRelPrime F G) :
    H ∈ Ideal.span {F, G} ↔ ∀ P : ℙ k (Fin 3 → k), eval P.rep F = 0 → eval P.rep G = 0 →
      NoetherConditionsAt P F G H := by
  refine ⟨fun h P _ _ ↦ noetherConditionsAt_of_mem_span_pair hF hG h, fun hN ↦ ?_⟩
  have hN' (P : ℙ k (Fin 3 → k)) : NoetherConditionsAt P F G H := by
    by_cases hP : eval P.rep F = 0 ∧ eval P.rep G = 0
    · exact hN P hP.1 hP.2
    · exact noetherConditionsAt_of_eval_ne_zero hF hG (not_and_or.1 hP)
  have hZ : ∀ P : ℙ k (Fin 3 → k), eval P.rep F = 0 → eval P.rep G = 0 →
      P ∈ zeroLocus {F, G} := fun P hPF hPG ↦ by
    rw [mem_zeroLocus_iff_eval_rep (by rintro f (rfl | rfl); exacts [⟨m, hF⟩, ⟨e, hG⟩])]
    rintro f (rfl | rfl)
    exacts [hPF, hPG]
  obtain ⟨M, hM⟩ :=
    exists_linearSubst_forall_mem_affineOpen_last (finite_zeroLocus_pair_of_isRelPrime hF hG hFG)
  set φ := (linearSubstAlgEquiv M).toRingEquiv
  have hφ (p : MvPolynomial (Fin 3) k) : Associated (φ p) (linearSubst M.1 p) := by
    rw [show φ p = linearSubst M.1 p from linearSubstAlgEquiv_apply M p]
  refine (Ideal.mem_span_pair_iff_of_ringEquiv φ (hφ F) (hφ G) (hφ H)).1 ?_
  refine mem_span_pair_of_forall_noetherConditionsAt_of_forall_mem_affineOpen
    (hF.linearSubst _) (hG.linearSubst _) (hH.linearSubst _) ?_ (i := Fin.last 2)
    (fun Q hQF hQG ↦ hM Q (hZ _ ((eval_rep_linearSubst_eq_zero_iff M hF Q).1 hQF)
      ((eval_rep_linearSubst_eq_zero_iff M hG Q).1 hQG)))
    fun Q ↦ (noetherConditionsAt_linearSubst_iff hF hG hH M Q).2 (hN' _)
  exact IsRelPrime.of_map (linearSubstAlgEquiv M).symm (by
    rwa [← linearSubstAlgEquiv_apply, ← linearSubstAlgEquiv_apply, AlgEquiv.symm_apply_apply,
      AlgEquiv.symm_apply_apply])

/-- **Max Noether's fundamental theorem, degree form.** Let `k` be algebraically closed, `F` and
`G` forms of degrees `m` and `e` in `k[X, Y, Z]` with no common component, and `H` a form of
degree `r`. Then `H = A F + B G` for forms `A` of degree `r - m` and `B` of degree `r - e`, with
`A = 0` if `r < m` and `B = 0` if `r < e`, if and only if Noether's conditions hold at every point
of `V(F) ∩ V(G)`. -/
theorem exists_isHomogeneous_mul_add_mul_eq_iff_forall_noetherConditionsAt
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous e) (hH : H.IsHomogeneous r)
    (hFG : IsRelPrime F G) :
    (∃ A B : MvPolynomial (Fin 3) k, A.IsHomogeneous (r - m) ∧ B.IsHomogeneous (r - e) ∧
      (r < m → A = 0) ∧ (r < e → B = 0) ∧ A * F + B * G = H) ↔
      ∀ P : ℙ k (Fin 3 → k), eval P.rep F = 0 → eval P.rep G = 0 →
        NoetherConditionsAt P F G H := by
  rw [← mem_span_pair_iff_forall_noetherConditionsAt hF hG hH hFG]
  refine ⟨fun ⟨A, B, _, _, _, _, h⟩ ↦ Ideal.mem_span_pair.2 ⟨A, B, h⟩, fun h ↦ ?_⟩
  obtain ⟨A, B, hA, hB, hA0, hB0, hAB⟩ := Ideal.exists_homogeneous_mul_add_mul_eq_of_mem_span_pair
    ((mem_homogeneousSubmodule _ _).2 hF) ((mem_homogeneousSubmodule _ _).2 hG)
    ((mem_homogeneousSubmodule _ _).2 hH) h
  exact ⟨A, B, (mem_homogeneousSubmodule _ _).1 hA, (mem_homogeneousSubmodule _ _).1 hB, hA0,
    hB0, hAB⟩

/-- **Max Noether's fundamental theorem** (Fulton, §5.5). Let `k` be algebraically closed, `F`
and `G` forms of degrees `m` and `e` in `k[X, Y, Z]` with no common component, and `H` a form of
degree `r`; constants are allowed. Noether's conditions at `P`, `H_* ∈ (F_*, G_*)` in
`𝒪_P(ℙ²)`, hold automatically at points off `V(F) ∩ V(G)`, and:

1. `H ∈ (F, G)` if and only if Noether's conditions hold at every point of `V(F) ∩ V(G)`;
2. `H = A F + B G` for forms `A` of degree `r - m` and `B` of degree `r - e` (with `A = 0` if
   `r < m` and `B = 0` if `r < e`) if and only if Noether's conditions hold at every point of
   `V(F) ∩ V(G)`.

Milestone: *Max Noether's fundamental theorem*. -/
theorem noetherConditionsAt_spec (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous e)
    (hH : H.IsHomogeneous r) (hFG : IsRelPrime F G) :
    (∀ P : ℙ k (Fin 3 → k), eval P.rep F ≠ 0 ∨ eval P.rep G ≠ 0 →
      NoetherConditionsAt P F G H) ∧
    (H ∈ Ideal.span {F, G} ↔ ∀ P : ℙ k (Fin 3 → k), eval P.rep F = 0 → eval P.rep G = 0 →
      NoetherConditionsAt P F G H) ∧
    ((∃ A B : MvPolynomial (Fin 3) k, A.IsHomogeneous (r - m) ∧ B.IsHomogeneous (r - e) ∧
      (r < m → A = 0) ∧ (r < e → B = 0) ∧ A * F + B * G = H) ↔
      ∀ P : ℙ k (Fin 3 → k), eval P.rep F = 0 → eval P.rep G = 0 →
        NoetherConditionsAt P F G H) :=
  ⟨fun _ ↦ noetherConditionsAt_of_eval_ne_zero hF hG,
    mem_span_pair_iff_forall_noetherConditionsAt hF hG hH hFG,
    exists_isHomogeneous_mul_add_mul_eq_iff_forall_noetherConditionsAt hF hG hH hFG⟩

end PlaneCurves.Projective

end
