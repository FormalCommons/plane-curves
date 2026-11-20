/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module


public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Place.QuadraticTransformation
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.QuadraticTransformation.Resolution.Basic
public import PlaneCurves.FieldTheory.FunctionField.PlaneModel

/-!
# Strong forms of the reduction to ordinary multiple points

The reduction of `Resolution/Basic.lean` can be continued to arbitrarily large degree: a
quadratic transformation centred at a point off the curve that is not terrible doubles the degree
and changes neither `N` nor `g*`.

Finitely many places of `k(F)` can moreover be centred at simple points of the last curve: once
the multiple points are ordinary, a quadratic transformation centred at an ordinary multiple
point moves the places centred there to points over the centre, which are simple, and moves the
other places with their centres. With a plane model of a function field of one variable, this
gives plane models with only ordinary multiple points of every such field, of arbitrarily large
degree, with finitely many given places centred at simple points (Fulton, Problem 7.21).

## Main results

* `PlaneCurves.Projective.exists_reduction_avoiding_of_le_degree`: the reduction along a finite
  set of simple points, without the bound on the number of steps, to a curve of degree at least
  any given `d`.
* `PlaneCurves.Projective.exists_reduction_places`: the reduction, to arbitrarily large degree,
  with finitely many given places centred at simple points.
* `PlaneCurves.Projective.exists_planeModel_ordinary`: a function field of one variable has
  plane models with only ordinary multiple points, of arbitrarily large degree, with finitely
  many given places centred at simple points.
* `PlaneCurves.Projective.reduction_ordinaryMultiplePoints`: **reduction of a plane curve to
  ordinary multiple points by quadratic transformations**, with its strong forms.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §7.4, Problems 7.13 and 7.14, §7.5, Problem 7.21,
  and Appendix A
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti TauCeti.AlgebraicGeometry PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type*} [Field k] {F G : MvPolynomial (Fin 3) k} {P : ℙ k (Fin 3 → k)} {n m : ℕ}


private theorem exists_isChain_cons_getLast_eq {α : Type*} {R : α → α → Prop} {a b c : α}
    {l₁ l₂ : List α} (h₁ : List.IsChain R (a :: l₁))
    (e₁ : (a :: l₁).getLast (List.cons_ne_nil a l₁) = b) (h₂ : List.IsChain R (b :: l₂))
    (e₂ : (b :: l₂).getLast (List.cons_ne_nil b l₂) = c) :
    ∃ l : List α, List.IsChain R (a :: l) ∧ (a :: l).getLast (List.cons_ne_nil a l) = c := by
  induction l₁ generalizing a with
  | nil => exact ⟨l₂, by simp_all⟩
  | cons x l ih =>
    obtain ⟨hax, h⟩ := List.isChain_cons_cons.1 h₁
    obtain ⟨l', hl', e⟩ := ih h (by simpa using e₁)
    exact ⟨x :: l', List.isChain_cons_cons.2 ⟨hax, hl'⟩, by simpa using e⟩

/-- A quadratic transformation centred at a point off the curve that is not terrible doubles the
degree and keeps the virtual genus and the number of non-ordinary multiple points; it comes with
the data of `exists_reduction_avoiding` for a finite set `S` of simple points. -/
private theorem exists_avoids_two_mul [IsAlgClosed k] (hF : F.IsHomogeneous n)
    [Fact (Irreducible F)] {S : Set (ℙ k (Fin 3 → k))} (hS : S.Finite)
    (hSF : ∀ P ∈ S, IsSimplePoint F P) :
    ∃ (G : MvPolynomial (Fin 3) k) (hG : G.IsHomogeneous (2 * n)) (hirrG : Irreducible G),
      IsQuadraticTransform F G ∧
      (nonOrdinaryMultiplePoints G).ncard = (nonOrdinaryMultiplePoints F).ncard ∧
      virtualGenus G = virtualGenus F ∧
      haveI := Fact.mk hirrG
      ∃ B φ e, IsPointCorrespondence hF hG S B φ e := by
  have hirr : Irreducible F := Fact.out
  have hT : {Q : ℙ k (Fin 3 → k) | IsTerriblePoint F Q.rep}.Finite :=
    Set.Subsingleton.finite fun P hP Q hQ ↦ by
      simpa using hP.mk_eq_mk hF hirr P.rep_ne_zero Q.rep_ne_zero hQ
  obtain ⟨P, hP, hPT⟩ := exists_eval_rep_ne_zero_notMem (n := 2) two_ne_zero hF hirr.ne_zero hT
  have hP0 : mult F P = 0 := nonpos_iff_eq_zero.1 (not_lt.1 (mt mult_pos_iff_eval_rep.1 hP))
  have hPS : P ∉ S := fun h ↦ (mult_eq_zero_iff hF).1 hP0 ((hSF P h).mem_zeroLocus hF)
  obtain ⟨G, d, hG, hirrG, h, B, φ, e, hA⟩ :=
    exists_isPointCorrespondence_of_not_isTerriblePoint hF hPT hS hSF hPS
  obtain rfl : d = 2 * n := hG.inj_right (by simpa [hP0] using h.isHomogeneous hF) hirrG.ne_zero
  exact ⟨G, hG, hirrG, h.isQuadraticTransform,
    h.ncard_nonOrdinaryMultiplePoints_eq hF (Or.inl (by simp [hP0])),
    (h.virtualGenus_eq hF hirr (Or.inl (by simp [hP0]))).1, B, φ, e, hA⟩

/-- Quadratic transformations centred at points off the curve raise the degree beyond any `d`,
keeping the virtual genus and the number of non-ordinary multiple points, with the data of
`exists_reduction_avoiding` for a finite set `S` of simple points. -/
private theorem exists_avoids_le_degree [IsAlgClosed k] (hF : F.IsHomogeneous n)
    [Fact (Irreducible F)] {S : Set (ℙ k (Fin 3 → k))} (hS : S.Finite)
    (hSF : ∀ P ∈ S, IsSimplePoint F P) (d : ℕ) :
    ∃ (l : List (MvPolynomial (Fin 3) k)) (G : MvPolynomial (Fin 3) k) (m : ℕ)
      (hG : G.IsHomogeneous m) (hirrG : Irreducible G),
      List.IsChain IsQuadraticTransform (F :: l) ∧ (F :: l).getLast (List.cons_ne_nil F l) = G ∧
      d ≤ m ∧ (nonOrdinaryMultiplePoints G).ncard = (nonOrdinaryMultiplePoints F).ncard ∧
      virtualGenus G = virtualGenus F ∧
      haveI := Fact.mk hirrG
      ∃ B φ e, IsPointCorrespondence hF hG S B φ e := by
  induction hμ : d - n using Nat.strong_induction_on generalizing F n S with
  | _ μ ih =>
  have hirr : Irreducible F := Fact.out
  by_cases hd : d ≤ n
  · exact ⟨[], F, n, hF, hirr, List.isChain_singleton F, rfl, hd, rfl, rfl, _, _, _,
      isPointCorrespondence_refl hF hSF⟩
  have hn := hF.degree_ne_zero_of_irreducible hirr
  obtain ⟨G₁, hG₁, hirr₁, h₁, hN₁, hg₁, B₁, φ₁, e₁, hA₁⟩ := exists_avoids_two_mul hF hS hSF
  have := Fact.mk hirr₁
  have hS₁ : ∀ P ∈ φ₁ '' S, IsSimplePoint G₁ P := by
    rintro _ ⟨s, hs, rfl⟩
    exact hA₁.2.2.2.2.2.1 s ⟨(hSF s hs).mem_zeroLocus hF, Set.disjoint_left.1 hA₁.2.1 hs⟩
  obtain ⟨l, G, m, hG, hirrG, hc, hlG, hdm, hN, hg, B₂, φ₂, e₂, hA₂⟩ :=
    ih (d - 2 * n) (by omega) hG₁ (hS.image φ₁) hS₁ rfl
  have := Fact.mk hirrG
  exact ⟨G₁ :: l, G, m, hG, hirrG, List.isChain_cons_cons.2 ⟨h₁, hc⟩, by simpa using hlG, hdm,
    hN.trans hN₁, hg.trans hg₁, _, _, _, IsPointCorrespondence.trans hA₁ hA₂⟩

/-- **Reduction to ordinary multiple points, along a finite set of simple points, to arbitrarily
large degree** (Fulton, Problems 7.13 and 7.14 (b)). Let `F` be an irreducible form over an
algebraically closed field, `S` a finite set of simple points of `F`, and `d` a natural number.
There is a finite sequence `F = F₁, …, F_m = G` of quadratic transformations such that `G` is an
irreducible form of degree at least `d` with only ordinary multiple points and `g*(G) ≤ g*(F)`.
Moreover there are a finite set `B` of points, disjoint from `S` and containing the multiple
points of `F`, a map `φ : ℙ² → ℙ²` and an isomorphism `e : k(F) ≅ k(G)` such that `φ` is injective
on `V(F) ∖ B`, its image `φ(V(F) ∖ B)` is cofinite in `V(G)` and consists of simple points of
`G`, and `e` carries the local ring of `F` at each point `R` of `V(F) ∖ B` onto the local ring of
`G` at `φ R`. -/
theorem exists_reduction_avoiding_of_le_degree [IsAlgClosed k] (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) {S : Set (ℙ k (Fin 3 → k))} (hS : S.Finite)
    (hSF : ∀ P ∈ S, IsSimplePoint F P) (d : ℕ) :
    ∃ (l : List (MvPolynomial (Fin 3) k)) (G : MvPolynomial (Fin 3) k) (m : ℕ)
      (hG : G.IsHomogeneous m) (hirrG : Irreducible G),
      List.IsChain IsQuadraticTransform (F :: l) ∧ (F :: l).getLast (List.cons_ne_nil F l) = G ∧
      (∀ Q, IsMultiplePoint G Q → IsOrdinaryMultiplePoint G Q) ∧ d ≤ m ∧
      virtualGenus G ≤ virtualGenus F ∧
      haveI := Fact.mk hirr
      haveI := Fact.mk hirrG
      ∃ (B : Set (ℙ k (Fin 3 → k))) (φ : ℙ k (Fin 3 → k) → ℙ k (Fin 3 → k))
        (e : functionField hF ≃ₐ[k] functionField hG),
        B.Finite ∧ Disjoint S B ∧ {Q | IsMultiplePoint F Q} ⊆ B ∧
        Set.InjOn φ (zeroLocus {F} \ B) ∧ (zeroLocus {G} \ φ '' (zeroLocus {F} \ B)).Finite ∧
        (∀ R ∈ zeroLocus {F} \ B, IsSimplePoint G (φ R)) ∧
        ∀ (R : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)))
          (R' : zeroLocus (projectivePlaneCurve.ideal hG : Set (MvPolynomial (Fin 3) k))),
          R.1 ∉ B → φ R.1 = R'.1 →
            (localSubring hF R).map (e : functionField hF →+* _) = localSubring hG R' := by
  have := Fact.mk hirr
  obtain ⟨l₁, G₁, d₁, hG₁, hirr₁, hc₁, hl₁, hord₁, -, -, hg₁, B₁, φ₁, e₁, hA₁⟩ :=
    exists_reduction_avoiding hF hirr hS hSF
  have := Fact.mk hirr₁
  have hS₁ : ∀ P ∈ φ₁ '' S, IsSimplePoint G₁ P := by
    rintro _ ⟨s, hs, rfl⟩
    exact hA₁.2.2.2.2.2.1 s ⟨(hSF s hs).mem_zeroLocus hF, Set.disjoint_left.1 hA₁.2.1 hs⟩
  obtain ⟨l₂, G, m, hG, hirrG, hc₂, hl₂, hdm, hN, hg, B₂, φ₂, e₂, hA₂⟩ :=
    exists_avoids_le_degree hG₁ (hS.image φ₁) hS₁ d
  have := Fact.mk hirrG
  obtain ⟨l, hc, hl⟩ := exists_isChain_cons_getLast_eq hc₁ hl₁ hc₂ hl₂
  exact ⟨l, G, m, hG, hirrG, hc, hl,
    forall_isOrdinaryMultiplePoint_of_ncard_le hG hirrG hN.le hord₁, hdm, hg.trans_le hg₁, _, _,
    _, IsPointCorrespondence.trans hA₁ hA₂⟩

/-! ### Places along a sequence of quadratic transformations -/

section Places

open Matrix (mulVec_injective_of_isUnit)

variable [IsAlgClosed k] {hF : F.IsHomogeneous n} [Fact (Irreducible F)] {d : ℕ}
  {hG : G.IsHomogeneous d} [Fact (Irreducible G)]

/-- One quadratic transformation of `G`, through the change of coordinates of `M`, with an
isomorphism `k(F) ≅ k(G)` continued to the new curve `H`: a place whose centre is `T R` with `R`
off the fundamental triangle moves to `Q(R)`, and one centred at the ordinary multiple point
`T [0 : 0 : 1]` moves to a simple point. -/
private theorem exists_algEquiv_center_properTransform_linearSubst
    (e : functionField hF ≃ₐ[k] functionField hG) (M : GL (Fin 3) k)
    (hE : IsExcellentPosition (linearSubst M.1 G)) :
    ∃ (d' : ℕ) (hH : (properTransform (linearSubst M.1 G)).IsHomogeneous d')
      (hirrH : Irreducible (properTransform (linearSubst M.1 G))),
      IsQuadraticTransformAt G (map M.1.mulVecLin (mulVec_injective_of_isUnit M.isUnit)
        (fundamentalPoint 2)) (properTransform (linearSubst M.1 G)) ∧
      haveI := Fact.mk hirrH
      ∃ e' : functionField hF ≃ₐ[k] functionField hH,
        (∀ (p : Place k (functionField hF)) (R : ℙ k (Fin 3 → k)), R ∉ fundamentalTriangle →
          map M.1.mulVecLin (mulVec_injective_of_isUnit M.isUnit) R = (center hG (p.map e)).1 →
            (center hH (p.map e')).1 = quadraticMap R) ∧
        (IsOrdinaryMultiplePoint G (map M.1.mulVecLin (mulVec_injective_of_isUnit M.isUnit)
            (fundamentalPoint 2)) → ∀ p : Place k (functionField hF),
          (center hG (p.map e)).1 = map M.1.mulVecLin (mulVec_injective_of_isUnit M.isUnit)
            (fundamentalPoint 2) → IsSimplePoint (properTransform (linearSubst M.1 G))
              (center hH (p.map e')).1) := by
  have h : IsQuadraticTransformAt G (map M.1.mulVecLin (mulVec_injective_of_isUnit M.isUnit)
      (fundamentalPoint 2)) (properTransform (linearSubst M.1 G)) :=
    isQuadraticTransformAt_def.2 ⟨M.1, _, rfl, hE, rfl⟩
  have hirrH := h.irreducible hG Fact.out
  have := Fact.mk hirrH
  have hH := h.isHomogeneous hG
  refine ⟨_, hH, hirrH, h, e.trans (linearSubstQuadraticFunctionFieldEquiv hG M hE.not_X_dvd hH
    rfl), fun p R hR hRp ↦ ?_, fun hP p hp ↦ ?_⟩
  · rw [← Place.map_map]
    exact center_map_linearSubstQuadraticFunctionFieldEquiv hG M hH rfl _ _ hR hRp
  · rw [← Place.map_map]
    exact (center_map_linearSubstQuadraticFunctionFieldEquiv_mem_pointsOverCentre hG M hH rfl hE
      _ hp (hp ▸ hP)).2

/-- At a non-terrible multiple point `P`, ordinary, of a curve `G` with only ordinary multiple
points, one quadratic transformation lowers the number of places of a finite set `Ps` centred at
multiple points, if some place of `Ps` is centred at `P`. -/
private theorem exists_isQuadraticTransform_ncard_lt
    {Ps : Set (Place k (functionField hF))} (hPs : Ps.Finite)
    (hord : ∀ Q, IsMultiplePoint G Q → IsOrdinaryMultiplePoint G Q)
    (e : functionField hF ≃ₐ[k] functionField hG) {p₀ : Place k (functionField hF)}
    (hp₀ : p₀ ∈ Ps) (hm : IsMultiplePoint G (center hG (p₀.map e)).1)
    (ht : ¬IsTerriblePoint G (center hG (p₀.map e)).1.rep) :
    ∃ (H : MvPolynomial (Fin 3) k) (d' : ℕ) (hH : H.IsHomogeneous d') (hirrH : Irreducible H),
      IsQuadraticTransform G H ∧ (∀ Q, IsMultiplePoint H Q → IsOrdinaryMultiplePoint H Q) ∧
      haveI := Fact.mk hirrH
      ∃ e' : functionField hF ≃ₐ[k] functionField hH,
        {p ∈ Ps | IsMultiplePoint H (center hH (p.map e')).1}.ncard <
          {p ∈ Ps | IsMultiplePoint G (center hG (p.map e)).1}.ncard := by
  set P := (center hG (p₀.map e)).1
  set S := (fun p ↦ (center hG (p.map e)).1) '' Ps \ {P}
  obtain ⟨M, hM, hTP, hE, hav⟩ := exists_isExcellentPosition_avoiding hG Fact.out ht
    ((hPs.image _).sdiff (t := {P})) (fun h ↦ h.2 rfl)
  obtain ⟨M', rfl⟩ : ∃ M' : GL (Fin 3) k, M'.1 = M :=
    ⟨Matrix.nonsingInvUnit M (Matrix.isUnit_det_of_mulVecLin_injective hM), rfl⟩
  have hTP' : map M'.1.mulVecLin (mulVec_injective_of_isUnit M'.isUnit) (fundamentalPoint 2) = P :=
    hTP
  have hav' : ∀ R, map M'.1.mulVecLin (mulVec_injective_of_isUnit M'.isUnit) R ∈ S →
      R ∉ fundamentalTriangle := hav
  obtain ⟨d', hH, hirrH, h, e', hoff, hon⟩ :=
    exists_algEquiv_center_properTransform_linearSubst e M' hE
  rw [hTP'] at h hon
  have := Fact.mk hirrH
  have hPo := hord P hm
  have hsub : {p ∈ Ps | IsMultiplePoint (properTransform (linearSubst M'.1 G))
      (center hH (p.map e')).1} ⊆ {p ∈ Ps | IsMultiplePoint G (center hG (p.map e)).1} := by
    rintro p ⟨hp, hpm⟩
    refine ⟨hp, ?_⟩
    by_cases hc : (center hG (p.map e)).1 = P
    · exact (hpm.not_isSimplePoint (hon hPo p hc)).elim
    obtain ⟨R, hR⟩ := (bijective_map_mulVecLin M').2 (center hG (p.map e)).1
    have hRt := hav' R (by rw [hR]; exact ⟨⟨p, hp, rfl⟩, hc⟩)
    rwa [hoff p R hRt hR, isMultiplePoint_def, mult_properTransform_linearSubst_quadraticMap hG
      (mulVec_injective_of_isUnit M'.isUnit) hRt, hR, ← isMultiplePoint_def] at hpm
  exact ⟨_, d', hH, hirrH, h.isQuadraticTransform,
    h.forall_isOrdinaryMultiplePoint hG hH hirrH hord (Or.inr hPo), e',
    Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).2
      ⟨p₀, ⟨hp₀, hm⟩, fun h ↦ h.2.not_isSimplePoint (hon hPo p₀ rfl)⟩)
      (hPs.subset (Set.sep_subset _ _))⟩

/-- One or two quadratic transformations of a curve `G` with only ordinary multiple points lower
the number of places of a finite set `Ps` centred at multiple points, if some place of `Ps` is
centred at a multiple point; if that point is terrible, an auxiliary quadratic transformation,
centred at a simple point or a point off the curve, first makes it not terrible. -/
private theorem exists_isChain_ncard_lt
    {Ps : Set (Place k (functionField hF))} (hPs : Ps.Finite)
    (hord : ∀ Q, IsMultiplePoint G Q → IsOrdinaryMultiplePoint G Q)
    (e : functionField hF ≃ₐ[k] functionField hG) {p₀ : Place k (functionField hF)}
    (hp₀ : p₀ ∈ Ps) (hm : IsMultiplePoint G (center hG (p₀.map e)).1) :
    ∃ (l : List (MvPolynomial (Fin 3) k)) (H : MvPolynomial (Fin 3) k) (d' : ℕ)
      (hH : H.IsHomogeneous d') (hirrH : Irreducible H),
      List.IsChain IsQuadraticTransform (G :: l) ∧ (G :: l).getLast (List.cons_ne_nil G l) = H ∧
      (∀ Q, IsMultiplePoint H Q → IsOrdinaryMultiplePoint H Q) ∧
      haveI := Fact.mk hirrH
      ∃ e' : functionField hF ≃ₐ[k] functionField hH,
        {p ∈ Ps | IsMultiplePoint H (center hH (p.map e')).1}.ncard <
          {p ∈ Ps | IsMultiplePoint G (center hG (p.map e)).1}.ncard := by
  set P := (center hG (p₀.map e)).1
  by_cases ht : IsTerriblePoint G P.rep
  swap
  · obtain ⟨H, d', hH, hirrH, h, hordH, e', hlt⟩ :=
      exists_isQuadraticTransform_ncard_lt hPs hord e hp₀ hm ht
    exact ⟨[H], H, d', hH, hirrH, by simpa using h, rfl, hordH, e', hlt⟩
  set C := (fun p ↦ (center hG (p.map e)).1) '' Ps
  obtain ⟨Q, -, -, hQ1, M, hM, hTQ, hE, hav, hnt⟩ :=
    exists_isQuadraticTransformAt_of_isTerriblePoint hG Fact.out ht (hPs.image _ : C.Finite)
  obtain ⟨M', rfl⟩ : ∃ M' : GL (Fin 3) k, M'.1 = M :=
    ⟨Matrix.nonsingInvUnit M (Matrix.isUnit_det_of_mulVecLin_injective hM), rfl⟩
  have hTQ' : map M'.1.mulVecLin (mulVec_injective_of_isUnit M'.isUnit) (fundamentalPoint 2) = Q :=
    hTQ
  have hav' : ∀ R, map M'.1.mulVecLin (mulVec_injective_of_isUnit M'.isUnit) R ∈ insert P C →
      R ∉ fundamentalTriangle := hav
  obtain ⟨d₁, hH₁, hirr₁, h₁, e₁, hoff, -⟩ :=
    exists_algEquiv_center_properTransform_linearSubst e M' hE
  rw [hTQ'] at h₁
  have := Fact.mk hirr₁
  have hord₁ := h₁.forall_isOrdinaryMultiplePoint hG hH₁ hirr₁ hord (Or.inl hQ1)
  -- every centre moves off the triangle, with its multiplicity
  have hmove (p : Place k (functionField hF)) (hp : p ∈ Ps) :
      ∃ R, R ∉ fundamentalTriangle ∧
        map M'.1.mulVecLin (mulVec_injective_of_isUnit M'.isUnit) R = (center hG (p.map e)).1 ∧
        (center hH₁ (p.map e₁)).1 = quadraticMap R ∧
        (IsMultiplePoint (properTransform (linearSubst M'.1 G)) (center hH₁ (p.map e₁)).1 ↔
          IsMultiplePoint G (center hG (p.map e)).1) := by
    obtain ⟨R, hR⟩ := (bijective_map_mulVecLin M').2 (center hG (p.map e)).1
    have hRt := hav' R (by rw [hR]; exact Set.mem_insert_of_mem _ ⟨p, hp, rfl⟩)
    refine ⟨R, hRt, hR, hoff p R hRt hR, ?_⟩
    rw [hoff p R hRt hR, isMultiplePoint_def, isMultiplePoint_def,
      mult_properTransform_linearSubst_quadraticMap hG (mulVec_injective_of_isUnit M'.isUnit) hRt,
      hR]
  obtain ⟨R₀, -, hR₀, hc₀, hm₀⟩ := hmove p₀ hp₀
  obtain ⟨H, d', hH, hirrH, h, hordH, e', hlt⟩ :=
    exists_isQuadraticTransform_ncard_lt hPs hord₁ e₁ hp₀ (hm₀.2 hm)
      (by rw [hc₀]; exact hnt R₀ hR₀)
  refine ⟨[_, H], H, d', hH, hirrH, by simpa using ⟨h₁.isQuadraticTransform, h⟩, rfl, hordH, e',
    hlt.trans_le (Set.ncard_le_ncard (fun p ⟨hp, hpm⟩ ↦ ⟨hp,
      let ⟨_, _, _, _, hi⟩ := hmove p hp; hi.1 hpm⟩)
      (hPs.subset (Set.sep_subset _ _)))⟩

/-- Quadratic transformations carry a curve `G` with only ordinary multiple points to one where
every place of a finite set `Ps` is centred at a simple point, along an isomorphism of function
fields continuing a given `k(F) ≅ k(G)`. -/
private theorem exists_isChain_isSimplePoint_center
    {Ps : Set (Place k (functionField hF))} (hPs : Ps.Finite)
    (hord : ∀ Q, IsMultiplePoint G Q → IsOrdinaryMultiplePoint G Q)
    (e : functionField hF ≃ₐ[k] functionField hG) :
    ∃ (l : List (MvPolynomial (Fin 3) k)) (H : MvPolynomial (Fin 3) k) (d' : ℕ)
      (hH : H.IsHomogeneous d') (hirrH : Irreducible H),
      List.IsChain IsQuadraticTransform (G :: l) ∧ (G :: l).getLast (List.cons_ne_nil G l) = H ∧
      (∀ Q, IsMultiplePoint H Q → IsOrdinaryMultiplePoint H Q) ∧
      haveI := Fact.mk hirrH
      ∃ e' : functionField hF ≃ₐ[k] functionField hH,
        ∀ p ∈ Ps, IsSimplePoint H (center hH (p.map e')).1 := by
  induction hμ : {p ∈ Ps | IsMultiplePoint G (center hG (p.map e)).1}.ncard
    using Nat.strong_induction_on generalizing G d with
  | _ μ ih =>
  have hirrG : Irreducible G := Fact.out
  by_cases h0 : ∀ p ∈ Ps, IsSimplePoint G (center hG (p.map e)).1
  · exact ⟨[], G, d, hG, hirrG, List.isChain_singleton G, rfl, hord, e, h0⟩
  push Not at h0
  obtain ⟨p₀, hp₀, hs₀⟩ := h0
  obtain ⟨l₁, H₁, d₁, hH₁, hirr₁, hc₁, hl₁, hord₁, e₁, hlt⟩ := exists_isChain_ncard_lt hPs hord e
    hp₀ ((isSimplePoint_or_isMultiplePoint hG (coe_center_mem_zeroLocus _)).resolve_left hs₀)
  have := Fact.mk hirr₁
  obtain ⟨l₂, H, d', hH, hirrH, hc₂, hl₂, hordH, e', hs⟩ := ih _ (hμ ▸ hlt) hord₁ e₁ rfl
  obtain ⟨l, hc, hl⟩ := exists_isChain_cons_getLast_eq hc₁ hl₁ hc₂ hl₂
  exact ⟨l, H, d', hH, hirrH, hc, hl, hordH, e', hs⟩

end Places

/-- **Reduction to ordinary multiple points, with given places centred at simple points**
(Fulton, Problem 7.21 (a), (c), and §7.4, Theorem 2). Let `F` be an irreducible form over an
algebraically closed field, `Ps` a finite set of places of its function field `k(F)`, and `d` a
natural number. There is a finite sequence `F = F₁, …, F_m = G` of quadratic transformations such
that `G` is an irreducible form of degree at least `d` with only ordinary multiple points and
`g*(G) ≤ g*(F)`, and an isomorphism `e : k(F) ≅ k(G)` under which every place of `Ps` is centred
at a simple point of `G`. -/
theorem exists_reduction_places [IsAlgClosed k] (hF : F.IsHomogeneous n) [Fact (Irreducible F)]
    {Ps : Set (Place k (functionField hF))} (hPs : Ps.Finite) (d : ℕ) :
    ∃ (l : List (MvPolynomial (Fin 3) k)) (G : MvPolynomial (Fin 3) k) (m : ℕ)
      (hG : G.IsHomogeneous m) (hirrG : Irreducible G),
      List.IsChain IsQuadraticTransform (F :: l) ∧ (F :: l).getLast (List.cons_ne_nil F l) = G ∧
      (∀ Q, IsMultiplePoint G Q → IsOrdinaryMultiplePoint G Q) ∧ d ≤ m ∧
      virtualGenus G ≤ virtualGenus F ∧
      haveI := Fact.mk hirrG
      ∃ e : functionField hF ≃ₐ[k] functionField hG,
        ∀ p ∈ Ps, IsSimplePoint G (center hG (p.map e)).1 := by
  have hirr : Irreducible F := Fact.out
  obtain ⟨l₁, G₁, d₁, hc₁, hl₁, hG₁, hirr₁, hord₁, -, -, hg₁⟩ := exists_reduction hF hirr
  have := Fact.mk hirr₁
  have hr₁ := List.relationReflTransGen_of_exists_isChain_cons l₁ hc₁ hl₁
  obtain ⟨e₁⟩ := nonempty_algEquiv_of_reflTransGen_isQuadraticTransform hr₁ hF hG₁
  obtain ⟨l₂, G₂, d₂, hG₂, hirr₂, hc₂, hl₂, -, e₂, hs₂⟩ :=
    exists_isChain_isSimplePoint_center hPs hord₁ e₁
  have := Fact.mk hirr₂
  have hg₂ := virtualGenus_le_of_reflTransGen_isQuadraticTransform
    (List.relationReflTransGen_of_exists_isChain_cons l₂ hc₂ hl₂) hG₁ hirr₁
  set S := (fun p ↦ (center hG₂ (p.map e₂)).1) '' Ps
  obtain ⟨l₃, G, m, hG, hirrG, hc₃, hl₃, hord, hdm, hg, B, φ, e₃, -, hSB, -, -, -, hsimple, hloc⟩ :=
    exists_reduction_avoiding_of_le_degree hG₂ hirr₂ (hPs.image _ : S.Finite)
      (by rintro _ ⟨p, hp, rfl⟩; exact hs₂ p hp) d
  have := Fact.mk hirrG
  obtain ⟨l', hc', hl'⟩ := exists_isChain_cons_getLast_eq hc₁ hl₁ hc₂ hl₂
  obtain ⟨l, hc, hl⟩ := exists_isChain_cons_getLast_eq hc' hl' hc₃ hl₃
  refine ⟨l, G, m, hG, hirrG, hc, hl, hord, hdm, hg.trans (hg₂.trans hg₁), e₂.trans e₃,
    fun p hp ↦ ?_⟩
  have hcB : (center hG₂ (p.map e₂)).1 ∉ B := Set.disjoint_left.1 hSB ⟨p, hp, rfl⟩
  have hsφ := hsimple _ ⟨coe_center_mem_zeroLocus _, hcB⟩
  have h := (center_map_eq_iff_of_map_localSubring e₃ (hloc (center hG₂ (p.map e₂))
    ⟨_, (zeroLocus_ideal hG).ge (hsφ.mem_zeroLocus hG)⟩ hcB rfl)).2 rfl
  rw [← Place.map_map, h]
  exact hsφ

/-- **A plane model of a function field** with only ordinary multiple points and given places at
simple points. Over an algebraically closed field `k`, every function field `K` of one variable
over `k` is the function field of irreducible plane curves of arbitrarily large degree with only
ordinary multiple points, under an isomorphism `K ≅ k(G)` that centres finitely many given places
of `K` at simple points of `G`. -/
theorem exists_planeModel_ordinary [IsAlgClosed k] {K : Type*} [Field K] [Algebra k K]
    (hK : IsFunctionField k K) {Ps : Set (Place k K)} (hPs : Ps.Finite) (d : ℕ) :
    ∃ (G : MvPolynomial (Fin 3) k) (m : ℕ) (hG : G.IsHomogeneous m) (hirrG : Irreducible G),
      (∀ Q, IsMultiplePoint G Q → IsOrdinaryMultiplePoint G Q) ∧ d ≤ m ∧
      haveI := Fact.mk hirrG
      ∃ e : K ≃ₐ[k] functionField hG, ∀ p ∈ Ps, IsSimplePoint G (center hG (p.map e)).1 := by
  obtain ⟨-, -, f, hirrf, -, -, ⟨e₀⟩⟩ := hK.exists_ker_aeval_eq_span_singleton_of_perfectField
  set F := homogenize (2 : Fin 3) f.totalDegree f
  have hF : F.IsHomogeneous f.totalDegree := isHomogeneous_homogenize _ _ f
  have hirr : Irreducible F := irreducible_homogenize_totalDegree hirrf
  have := Fact.mk hirr
  have hX : ¬ X 2 ∣ F := not_X_dvd_homogenize_totalDegree hirrf.ne_zero
  have hi : ¬ F ∣ X 2 := fun h ↦ hX (hirr.dvd_symm prime_X.irreducible h)
  have hf : Ideal.span {dehomogenize (2 : Fin 3) F} = Ideal.span {f} := by
    rw [dehomogenize_homogenize_totalDegree]
  have := isPrime_span_dehomogenize hF hi
  have : (Ideal.span {f}).IsPrime := hf ▸ this
  set e₁ : K ≃ₐ[k] functionField hF :=
    e₀.trans ((functionField.chartEquiv hF 2 hi).trans
      (AffineSpace.functionField.equivOfEq hf)).symm
  obtain ⟨-, G, m, hG, hirrG, -, -, hord, hdm, -, e, he⟩ :=
    exists_reduction_places hF (hPs.image (·.map e₁)) d
  have := Fact.mk hirrG
  refine ⟨G, m, hG, hirrG, hord, hdm, e₁.trans e, fun p hp ↦ ?_⟩
  rw [← Place.map_map]
  exact he _ ⟨p, hp, rfl⟩

universe u in
/-- **Reduction of a plane curve to ordinary multiple points by quadratic transformations**
(Fulton, §7.4, Theorem 2, Problems 7.13, 7.14 (b) and 7.21 (a), (c), and Appendix A). Over an
algebraically closed field `k`:

1. every irreducible plane curve `F` is carried by a finite sequence of quadratic
   transformations to a curve with only ordinary multiple points;
2. in characteristic zero, by at most `N(F) + g*(F)` of them, `N(F)` being the number of
   non-ordinary multiple points of `F` and `g*` the virtual genus;
3. for a finite set `S` of simple points of `F` and any `d`, the last curve can be taken of degree
   at least `d`, with a finite set `B` disjoint from `S`, a map `φ` and an isomorphism of function
   fields `e : k(F) ≅ k(G)` such that `φ` is injective on `V(F) ∖ B`, with image a cofinite set
   of simple points of `G`, and `e` carries local rings of `F` at points of `V(F) ∖ B` onto local
   rings of `G` at their images: an open neighbourhood of `S` is isomorphic to an open subset of
   the last curve consisting of simple points;
4. for a finite set `Ps` of places of `k(F)` and any `d`, the last curve can be taken of degree at
   least `d` with every place of `Ps` centred at a simple point; and every function field of one
   variable over `k` has such plane models, for any finite set of its places.

All parts hold in every characteristic except the bound of the second.

Milestone: *Reduction of a plane curve to ordinary multiple points by quadratic
transformations*. -/
theorem reduction_ordinaryMultiplePoints [IsAlgClosed k] :
    (∀ {n : ℕ} {F : MvPolynomial (Fin 3) k}, F.IsHomogeneous n → Irreducible F →
      ∃ l : List (MvPolynomial (Fin 3) k), List.IsChain IsQuadraticTransform (F :: l) ∧
        ∀ Q, IsMultiplePoint ((F :: l).getLast (List.cons_ne_nil F l)) Q →
          IsOrdinaryMultiplePoint ((F :: l).getLast (List.cons_ne_nil F l)) Q) ∧
    (CharZero k → ∀ {n : ℕ} {F : MvPolynomial (Fin 3) k}, F.IsHomogeneous n → Irreducible F →
      ∃ l : List (MvPolynomial (Fin 3) k), List.IsChain IsQuadraticTransform (F :: l) ∧
        (∀ Q, IsMultiplePoint ((F :: l).getLast (List.cons_ne_nil F l)) Q →
          IsOrdinaryMultiplePoint ((F :: l).getLast (List.cons_ne_nil F l)) Q) ∧
        (l.length : ℤ) ≤ (nonOrdinaryMultiplePoints F).ncard + virtualGenus F) ∧
    (∀ {n : ℕ} {F : MvPolynomial (Fin 3) k} (hF : F.IsHomogeneous n) (hirr : Irreducible F)
      {S : Set (ℙ k (Fin 3 → k))}, S.Finite → (∀ P ∈ S, IsSimplePoint F P) → ∀ d : ℕ,
      ∃ (l : List (MvPolynomial (Fin 3) k)) (G : MvPolynomial (Fin 3) k) (m : ℕ)
        (hG : G.IsHomogeneous m) (hirrG : Irreducible G),
        List.IsChain IsQuadraticTransform (F :: l) ∧ (F :: l).getLast (List.cons_ne_nil F l) = G ∧
        (∀ Q, IsMultiplePoint G Q → IsOrdinaryMultiplePoint G Q) ∧ d ≤ m ∧
        virtualGenus G ≤ virtualGenus F ∧
        haveI := Fact.mk hirr
        haveI := Fact.mk hirrG
        ∃ (B : Set (ℙ k (Fin 3 → k))) (φ : ℙ k (Fin 3 → k) → ℙ k (Fin 3 → k))
          (e : functionField hF ≃ₐ[k] functionField hG),
          B.Finite ∧ Disjoint S B ∧ {Q | IsMultiplePoint F Q} ⊆ B ∧
          Set.InjOn φ (zeroLocus {F} \ B) ∧ (zeroLocus {G} \ φ '' (zeroLocus {F} \ B)).Finite ∧
          (∀ R ∈ zeroLocus {F} \ B, IsSimplePoint G (φ R)) ∧
          ∀ (R : zeroLocus (projectivePlaneCurve.ideal hF : Set (MvPolynomial (Fin 3) k)))
            (R' : zeroLocus (projectivePlaneCurve.ideal hG : Set (MvPolynomial (Fin 3) k))),
            R.1 ∉ B → φ R.1 = R'.1 →
              (localSubring hF R).map (e : functionField hF →+* _) = localSubring hG R') ∧
    ((∀ {n : ℕ} {F : MvPolynomial (Fin 3) k} (hF : F.IsHomogeneous n) [Fact (Irreducible F)]
      {Ps : Set (Place k (functionField hF))}, Ps.Finite → ∀ d : ℕ,
      ∃ (l : List (MvPolynomial (Fin 3) k)) (G : MvPolynomial (Fin 3) k) (m : ℕ)
        (hG : G.IsHomogeneous m) (hirrG : Irreducible G),
        List.IsChain IsQuadraticTransform (F :: l) ∧ (F :: l).getLast (List.cons_ne_nil F l) = G ∧
        (∀ Q, IsMultiplePoint G Q → IsOrdinaryMultiplePoint G Q) ∧ d ≤ m ∧
        virtualGenus G ≤ virtualGenus F ∧
        haveI := Fact.mk hirrG
        ∃ e : functionField hF ≃ₐ[k] functionField hG,
          ∀ p ∈ Ps, IsSimplePoint G (center hG (p.map e)).1) ∧
      ∀ (K : Type u) [Field K] [Algebra k K], IsFunctionField k K →
        ∀ {Ps : Set (Place k K)}, Ps.Finite → ∀ d : ℕ,
        ∃ (G : MvPolynomial (Fin 3) k) (m : ℕ) (hG : G.IsHomogeneous m) (hirrG : Irreducible G),
          (∀ Q, IsMultiplePoint G Q → IsOrdinaryMultiplePoint G Q) ∧ d ≤ m ∧
          haveI := Fact.mk hirrG
          ∃ e : K ≃ₐ[k] functionField hG, ∀ p ∈ Ps, IsSimplePoint G (center hG (p.map e)).1) := by
  refine ⟨fun hF hirr ↦ ?_, fun _ _ _ hF hirr ↦ ?_,
    fun hF hirr _ hS hSF d ↦ exists_reduction_avoiding_of_le_degree hF hirr hS hSF d,
    fun hF _ _ hPs d ↦ exists_reduction_places hF hPs d,
    fun _ _ _ hK _ hPs d ↦ exists_planeModel_ordinary hK hPs d⟩
  · obtain ⟨l, G, d, hc, hl, -, -, hord, -⟩ := exists_reduction hF hirr
    exact ⟨l, hc, hl ▸ hord⟩
  · obtain ⟨l, G, d, hc, hl, -, -, hord, -, h0, -⟩ := exists_reduction hF hirr
    exact ⟨l, hc, hl ▸ hord, h0 inferInstance⟩

end PlaneCurves.Projective

end
