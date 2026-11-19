/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.HilbertSamuel
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.Multiplicity
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.SimplePoint
public import TauCeti.RingTheory.OrderOfVanishing

/-!
# Ordinary multiple points through the local ring

Let `F ∈ k[X, Y]`, `P` a point with `m = m_P(F) ≥ 2`, `𝒪 = 𝒪_P(𝔸²) ⧸ (F)` the local ring of the
curve at `P` and `𝔪` its maximal ideal. Fulton's Problem 3.24 characterizes the ordinary multiple
points through `𝒪` alone: `P` is ordinary iff there are `g₁, …, gₘ ∈ 𝔪` whose residues in
`𝔪 / 𝔪²` are pairwise linearly independent (nonzero and pairwise non-proportional) and with
`ℓ(𝒪 ⧸ (gᵢ)) > m` for all `i`. As `m` is itself determined by `𝒪`
(`PlaneCurves.Affine.orderAt_eq_of_ringEquiv`), being an ordinary multiple point is an invariant
of the ring `𝒪`.

We state the linear independence of the residues of `g, h ∈ 𝔪` in `𝔪 / 𝔪²` ring-theoretically:
`a g + b h ∈ 𝔪²` forces `a, b ∈ 𝔪`. For `g`, `h` the images of polynomials `G`, `H` vanishing at
`P`, and `m ≥ 2`, this says that `α G + β H` has order at least `2` at `P` only for
`α = β = 0`: the differentials of `G` and `H` at `P` are linearly independent.

Part (a) of Problem 3.24, that the linear forms map isomorphically onto `𝔪 / 𝔪²`, is
`PlaneCurves.Affine.exists_linearEquiv_gradedPiece_one`.

## Main results

* `PlaneCurves.Affine.IsOrdinaryMultiplePoint.exists_isTangentAt`: Problem 3.24(b), the tangents
  `Lᵢ` at an ordinary multiple point satisfy `I(P, F ∩ Lᵢ) > m` and have pairwise independent
  differentials.
* `PlaneCurves.Affine.isOrdinaryMultiplePoint_of_lt_intersectionNumber`: Problem 3.24(c).
* `PlaneCurves.Affine.isOrdinaryMultiplePoint_iff_exists_ord`: Problem 3.24(d), in the local ring
  `𝒪_P(𝔸²) ⧸ (F)`.
* `PlaneCurves.Affine.isOrdinaryMultiplePoint_iff_of_ringEquiv`: isomorphic local rings of plane
  curves have ordinary multiple points together.
* `PlaneCurves.Affine.isOrdinaryMultiplePoint_iff_of_algEquiv_away`: the case of an isomorphism
  of localizations `k[X, Y][1/h] ≅ k[X, Y][1/h']` compatible with the values and sending `F` to a
  unit times `G`.
* `PlaneCurves.Affine.isOrdinaryMultiplePoint_iff_exists_ord_and_iff_of_ringEquiv`: the
  local-ring characterization of ordinary multiple points.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.3, Problem 3.24
-/

public section

open MvPolynomial IsLocalRing Ideal

namespace PlaneCurves

namespace Affine

open AffineSpace localRing

variable {k : Type*} [Field k] {F G H L L' : MvPolynomial (Fin 2) k} {P : Fin 2 → k}

/-- No point is an ordinary multiple point of the zero polynomial: its leading form `0` is not
squarefree. -/
theorem not_isOrdinaryMultiplePoint_zero :
    ¬IsOrdinaryMultiplePoint (0 : MvPolynomial (Fin 2) k) P := fun h ↦ by
  have := (isOrdinaryMultiplePoint_def.1 h).2
  rw [leadingFormAt_zero] at this
  exact not_squarefree_zero this

/-! ### Independent differentials -/

/-- For `G`, `H` vanishing at `P`, `α G + β H` has order at least two at `P` iff the
differentials satisfy `α dG(P) + β dH(P) = 0`. -/
theorem two_le_orderAt_C_mul_add_C_mul_iff (hG : eval P G = 0) (hH : eval P H = 0) (α β : k) :
    2 ≤ (C α * G + C β * H).orderAt P ↔
      ∀ i, α * eval P (pderiv i G) + β * eval P (pderiv i H) = 0 := by
  rw [two_le_orderAt_iff]
  simp [hG, hH]

/-- If `α G + β H` has order at least two at `P` only for `α = β = 0`, and `G(P) = 0`, then `P`
is a simple point of `G`. -/
theorem orderAt_eq_one_of_forall_two_le_orderAt (hG : eval P G = 0)
    (h : ∀ α β : k, 2 ≤ (C α * G + C β * H).orderAt P → α = 0 ∧ β = 0) : G.orderAt P = 1 := by
  rw [orderAt_eq_one_iff]
  refine ⟨hG, ?_⟩
  by_contra! hd
  have := (h 1 0 (by rw [two_le_orderAt_iff]; simp [hG, hd])).1
  exact one_ne_zero this

/-- If `G`, `H` vanish at `P` and `α G + β H` has order at least two at `P` only for
`α = β = 0`, then the tangents of `G` and `H` at `P` are not associated. -/
theorem not_associated_leadingFormAt_of_forall_two_le_orderAt (hG : eval P G = 0)
    (hH : eval P H = 0)
    (h : ∀ α β : k, 2 ≤ (C α * G + C β * H).orderAt P → α = 0 ∧ β = 0) :
    ¬Associated (G.leadingFormAt P) (H.leadingFormAt P) := by
  have hG1 := orderAt_eq_one_of_forall_two_le_orderAt hG h
  have hH1 := orderAt_eq_one_of_forall_two_le_orderAt (H := G) hH fun α β hαβ ↦
    (h β α (by rwa [add_comm])).symm
  rintro ⟨u, hu⟩
  obtain ⟨c, -, hc⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
  rw [leadingFormAt_eq_sum_pderiv hG1, leadingFormAt_eq_sum_pderiv hH1, hc] at hu
  have hd (j : Fin 2) : c * eval P (pderiv j G) = eval P (pderiv j H) := by
    have := congr(eval P (pderiv j $hu))
    fin_cases j <;> simpa [Pi.single_apply, mul_comm] using this
  have := (h c (-1) ((two_le_orderAt_C_mul_add_C_mul_iff hG hH c (-1)).2 fun i ↦ by
    rw [← hd i]; ring)).2
  exact one_ne_zero (neg_eq_zero.1 this)

/-- For non-associated nonzero linear forms `L`, `L'`, the lines `L(X - P) = 0` and
`L'(X - P) = 0` have independent differentials: `α L(X - P) + β L'(X - P)` has order at least two
at `P` only for `α = β = 0`. -/
theorem forall_two_le_orderAt_taylor (hL : L.IsHomogeneous 1) (hL₀ : L ≠ 0)
    (hL' : L'.IsHomogeneous 1) (hL'₀ : L' ≠ 0) (h : ¬Associated L L') (α β : k) :
    2 ≤ (C α * taylor (-P) L + C β * taylor (-P) L').orderAt P → α = 0 ∧ β = 0 := by
  intro h2
  have hsum : C α * L + C β * L' = 0 := by
    by_contra hne
    have hhom : (C α * L + C β * L').IsHomogeneous 1 :=
      ((isHomogeneous_C _ α).mul hL).add ((isHomogeneous_C _ β).mul hL')
    have h1 := hhom.orderAt_zero hne
    have : taylor (-P) (C α * L + C β * L') = C α * taylor (-P) L + C β * taylor (-P) L' := by
      simp
    rw [← this, orderAt_taylor, add_neg_cancel, h1] at h2
    norm_num at h2
  rcases eq_or_ne α 0 with rfl | hα
  · refine ⟨rfl, ?_⟩
    simpa [hL'₀] using hsum
  · exfalso
    have hβ : β ≠ 0 := by
      rintro rfl
      simp [hα, hL₀] at hsum
    refine h ((associated_unit_mul_left L (C α) ((isUnit_iff_ne_zero.2 hα).map C)).symm.trans ?_)
    rw [eq_neg_of_add_eq_zero_left hsum, ← neg_mul, ← map_neg]
    exact associated_unit_mul_left L' (C (-β)) ((isUnit_iff_ne_zero.2 (neg_ne_zero.2 hβ)).map C)

/-! ### Residues in `𝔪 / 𝔪²` -/

/-- **Independent residues in `𝔪 / 𝔪²`.** Let `m_P(F) ≥ 2`, `G`, `H` polynomials vanishing at
`P` and `g`, `h` their images in `𝒪 = 𝒪_P(𝔸²) ⧸ (F)`, with maximal ideal `𝔪`. The residues of
`g` and `h` in `𝔪 / 𝔪²` are linearly independent (`a g + b h ∈ 𝔪²` forces `a, b ∈ 𝔪`) iff
`α G + β H` has order at least two at `P` only for `α = β = 0`. -/
theorem forall_mul_add_mul_mem_sq_iff (hF : 2 ≤ F.orderAt P) (hG : eval P G = 0)
    (hH : eval P H = 0) :
    (∀ a b : localRing k P ⧸ span {algebraMap _ (localRing k P) F},
      a * Ideal.Quotient.mk _ (algebraMap _ _ G) + b * Ideal.Quotient.mk _ (algebraMap _ _ H) ∈
          (maximalIdeal (localRing k P)).map (Ideal.Quotient.mk _) ^ 2 →
        a ∈ (maximalIdeal (localRing k P)).map (Ideal.Quotient.mk _) ∧
          b ∈ (maximalIdeal (localRing k P)).map (Ideal.Quotient.mk _)) ↔
      ∀ α β : k, 2 ≤ (C α * G + C β * H).orderAt P → α = 0 ∧ β = 0 := by
  have hF0 : eval P F = 0 := orderAt_pos_iff.1 (lt_of_lt_of_le (by norm_num) hF)
  have mem1 := mk_mem_map_maximalIdeal_iff hF0
  constructor
  · intro h α β hαβ
    have := h (Ideal.Quotient.mk _ (algebraMap _ _ (C α : MvPolynomial (Fin 2) k)))
      (Ideal.Quotient.mk _ (algebraMap _ _ (C β : MvPolynomial (Fin 2) k))) (by
        simp only [← map_mul, ← map_add]
        rw [mk_mem_map_maximalIdeal_pow_iff (by exact_mod_cast hF),
          algebraMap_mem_maximalIdeal_pow_iff]
        exact_mod_cast hαβ)
    rw [mem1, mem1, localRing.algebraMap_mem_maximalIdeal_iff,
      localRing.algebraMap_mem_maximalIdeal_iff] at this
    simpa using this
  · intro h a b hab
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    simp only [← map_mul, ← map_add] at hab
    rw [mk_mem_map_maximalIdeal_pow_iff (by exact_mod_cast hF)] at hab
    rw [mem1, mem1, ← evalAt_eq_zero_iff, ← evalAt_eq_zero_iff]
    refine h _ _ ?_
    rw [← Nat.cast_ofNat, ← algebraMap_mem_maximalIdeal_pow_iff]
    -- `x - x(P) ∈ 𝔪_P` for every `x ∈ 𝒪_P(𝔸²)`
    have hsub (x : localRing k P) :
        x - algebraMap (MvPolynomial (Fin 2) k) _ (C (evalAt k P x)) ∈ maximalIdeal _ := by
      rw [← evalAt_eq_zero_iff, map_sub, evalAt_algebraMap, eval_C, sub_self]
    have key : algebraMap _ (localRing k P) (C (evalAt k P a) * G + C (evalAt k P b) * H) =
        (a * algebraMap _ _ G + b * algebraMap _ _ H) -
          ((a - algebraMap (MvPolynomial (Fin 2) k) _ (C (evalAt k P a))) * algebraMap _ _ G +
            (b - algebraMap (MvPolynomial (Fin 2) k) _ (C (evalAt k P b))) * algebraMap _ _ H) := by
      simp only [map_add, map_mul]
      ring
    rw [key]
    refine sub_mem hab ?_
    rw [sq]
    exact add_mem (mul_mem_mul (hsub a) (localRing.algebraMap_mem_maximalIdeal_iff.2 hG))
      (mul_mem_mul (hsub b) (localRing.algebraMap_mem_maximalIdeal_iff.2 hH))

/-! ### Problem 3.24 -/

section IsAlgClosed

variable [IsAlgClosed k]

/-- **Problem 3.24(b).** At an ordinary multiple point `P` of multiplicity `m`, over an
algebraically closed field, the `m` tangents `L₁, …, Lₘ` (every tangent is a multiple of one of
them) satisfy `I(P, F ∩ Lᵢ) > m`, and the lines `Lᵢ(X - P) = 0` have pairwise independent
differentials at `P`. -/
theorem IsOrdinaryMultiplePoint.exists_isTangentAt (h : IsOrdinaryMultiplePoint F P) {m : ℕ}
    (hm : F.orderAt P = m) :
    ∃ L : Fin m → MvPolynomial (Fin 2) k, (∀ i, IsTangentAt F P (L i)) ∧
      (∀ L', IsTangentAt F P L' → ∃ i, Associated L' (L i)) ∧
      (∀ i, (m : ℕ∞) < intersectionNumber P F (taylor (-P) (L i))) ∧
      Pairwise fun i j ↦ ∀ α β : k,
        2 ≤ (C α * taylor (-P) (L i) + C β * taylor (-P) (L j)).orderAt P → α = 0 ∧ β = 0 := by
  have hF : F ≠ 0 := by
    rintro rfl
    exact not_isOrdinaryMultiplePoint_zero h
  obtain ⟨s, hs, hpair, hcov⟩ := exists_finset_isTangentAt (P := P) hF
  have hcard : s.card = m := by
    have := ((isOrdinaryMultiplePoint_iff hs hpair hcov hF).1 h).2
    rw [hm] at this
    exact_mod_cast this
  let e : s ≃ Fin m := s.equivFinOfCardEq hcard
  refine ⟨fun i ↦ e.symm i, fun i ↦ hs _ (e.symm i).2, fun L' hL' ↦ ?_, fun i ↦ ?_, ?_⟩
  · obtain ⟨L, hL, hL'L⟩ := hcov L' hL'
    exact ⟨e ⟨L, hL⟩, by simpa using hL'L⟩
  · have := hs _ (e.symm i).2
    rw [← hm]
    exact (isTangentAt_iff_orderAt_lt_intersectionNumber hF this.isHomogeneous this.ne_zero).1 this
  · intro i j hij
    have hi := hs _ (e.symm i).2
    have hj := hs _ (e.symm j).2
    refine forall_two_le_orderAt_taylor hi.isHomogeneous hi.ne_zero hj.isHomogeneous hj.ne_zero
      (hpair (e.symm i).2 (e.symm j).2 fun h' ↦ hij ?_)
    exact e.symm.injective (Subtype.ext h')

/-- **Problem 3.24(c).** Over an algebraically closed field, let `m = m_P(F) ≥ 2` and
`G₁, …, Gₘ` polynomials vanishing at `P` with pairwise independent differentials at `P` (for
`i ≠ j`, `α Gᵢ + β Gⱼ` has order at least two at `P` only for `α = β = 0`) and
`I(P, F ∩ Gᵢ) > m`. Then `P` is an ordinary multiple point of `F`. -/
theorem isOrdinaryMultiplePoint_of_lt_intersectionNumber {m : ℕ} (hm : F.orderAt P = m)
    (h2 : 2 ≤ m) {G : Fin m → MvPolynomial (Fin 2) k} (hG : ∀ i, eval P (G i) = 0)
    (hind : Pairwise fun i j ↦ ∀ α β : k,
      2 ≤ (C α * G i + C β * G j).orderAt P → α = 0 ∧ β = 0)
    (hI : ∀ i, (m : ℕ∞) < intersectionNumber P F (G i)) :
    IsOrdinaryMultiplePoint F P := by
  classical
  have hF : F ≠ 0 := by
    rintro rfl
    simp at hm
  have := Fin.nontrivial_iff_two_le.2 h2
  have hG1 (i : Fin m) : (G i).orderAt P = 1 := by
    obtain ⟨j, hj⟩ := exists_ne i
    exact orderAt_eq_one_of_forall_two_le_orderAt (hG i) (hind hj.symm)
  have hG0 (i : Fin m) : G i ≠ 0 := by
    rintro h
    simpa [h] using hG1 i
  -- the tangent `Lᵢ` of `Gᵢ` at `P` is tangent to `F`
  have htan (i : Fin m) : IsTangentAt F P ((G i).leadingFormAt P) := by
    have hhom : ((G i).leadingFormAt P).IsHomogeneous 1 := by
      simpa [hG1 i] using isHomogeneous_leadingFormAt (G i) P
    have hirr := irreducible_of_isHomogeneous_one hhom (leadingFormAt_ne_zero (hG0 i))
    refine isTangentAt_def.2 ⟨hhom, leadingFormAt_ne_zero (hG0 i), ?_⟩
    have hne : ¬IsRelPrime (F.leadingFormAt P) ((G i).leadingFormAt P) := by
      rw [← intersectionNumber_eq_mul_orderAt_iff hF (hG0 i), hm, hG1 i, mul_one]
      exact (hI i).ne'
    rw [isRelPrime_comm, hirr.isRelPrime_iff_not_dvd, not_not] at hne
    exact hne
  have hna : Pairwise fun i j ↦ ¬Associated ((G i).leadingFormAt P) ((G j).leadingFormAt P) :=
    fun i j hij ↦ not_associated_leadingFormAt_of_forall_two_le_orderAt (hG i) (hG j) (hind hij)
  obtain ⟨s, hs, hpair, hcov⟩ := exists_finset_isTangentAt (P := P) hF
  rw [isOrdinaryMultiplePoint_iff hs hpair hcov hF, hm]
  refine ⟨isMultiplePoint_def.2 (hm ▸ by exact_mod_cast h2), ?_⟩
  -- `m ≤ |s|`: the tangents `Lᵢ` are associated to distinct members of `s`
  choose f hfs hf using fun i ↦ hcov _ (htan i)
  have hle : m ≤ s.card := by
    have := Finset.card_le_card_of_injOn f (s := Finset.univ) (fun i _ ↦ hfs i)
      (fun i _ j _ hij ↦ by
        by_contra hne
        exact hna hne ((hf i).trans (hij ▸ (hf j).symm)))
    simpa using this
  -- `|s| ≤ m`: the multiplicities of the tangents in `s` add up to `m`
  have hsum := sum_tangentMultiplicity hs hpair hcov hF
  rw [hm, Nat.cast_inj] at hsum
  have hge : s.card ≤ m := by
    rw [← hsum, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun L hL ↦
      (tangentMultiplicity_pos_iff hF (hs L hL).isHomogeneous (hs L hL).ne_zero).2 (hs L hL)
  exact_mod_cast le_antisymm hge hle

/-- **Problem 3.24(d).** Over an algebraically closed field, let `m = m_P(F)` and
`𝒪 = 𝒪_P(𝔸²) ⧸ (F)` be the local ring of `F` at `P`, with maximal ideal `𝔪`. Then `P` is an
ordinary multiple point of `F` iff `m ≥ 2` and there are `g₁, …, gₘ ∈ 𝔪` whose residues in
`𝔪 / 𝔪²` are pairwise linearly independent (for `i ≠ j`, `a gᵢ + b gⱼ ∈ 𝔪²` forces `a, b ∈ 𝔪`)
and with `ℓ(𝒪 ⧸ (gᵢ)) > m` for all `i`. -/
theorem isOrdinaryMultiplePoint_iff_exists_ord
    [IsLocalRing (localRing k P ⧸ span {algebraMap _ (localRing k P) F})] {m : ℕ}
    (hm : F.orderAt P = m) :
    IsOrdinaryMultiplePoint F P ↔ 2 ≤ m ∧
      ∃ g : Fin m → localRing k P ⧸ span {algebraMap _ (localRing k P) F},
        (∀ i, g i ∈ maximalIdeal _) ∧
        (Pairwise fun i j ↦ ∀ a b, a * g i + b * g j ∈ maximalIdeal _ ^ 2 →
          a ∈ maximalIdeal _ ∧ b ∈ maximalIdeal _) ∧
        ∀ i, (m : ℕ∞) < Ring.ord _ (g i) := by
  rw [← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective]
  constructor
  · intro h
    have h2 : 2 ≤ m := by
      exact_mod_cast hm ▸ isMultiplePoint_def.1 (isOrdinaryMultiplePoint_def.1 h).1
    have hF2 : 2 ≤ F.orderAt P := by rw [hm]; exact_mod_cast h2
    obtain ⟨L, hL, -, hI, hind⟩ := h.exists_isTangentAt hm
    have hev (i : Fin m) : eval P (taylor (-P) (L i)) = 0 := by
      rw [eval_taylor, add_neg_cancel, eval_zero, constantCoeff_eq]
      exact (hL i).isHomogeneous.coeff_eq_zero (by simp)
    refine ⟨h2, fun i ↦ Ideal.Quotient.mk _ (algebraMap _ _ (taylor (-P) (L i))), fun i ↦ ?_,
      fun i j hij ↦ (forall_mul_add_mul_mem_sq_iff hF2 (hev i) (hev j)).2 (hind hij),
      fun i ↦ ?_⟩
    · exact mem_map_of_mem _ (localRing.algebraMap_mem_maximalIdeal_iff.2 (hev i))
    · rw [← intersectionNumber_eq_ord]
      exact hI i
  · rintro ⟨h2, g, hgm, hind, hord⟩
    have hF2 : 2 ≤ F.orderAt P := by rw [hm]; exact_mod_cast h2
    choose G u hu hGu using fun i ↦ exists_mul_isUnit_eq_mk _ (g i)
    have hF0 : eval P F = 0 := orderAt_pos_iff.1 (lt_of_lt_of_le (by norm_num) hF2)
    have hev (i : Fin m) : eval P (G i) = 0 := by
      have := (mul_unit_mem_iff_mem _ (hu i)).2 (hgm i)
      rwa [hGu i, mk_mem_map_maximalIdeal_iff hF0,
        localRing.algebraMap_mem_maximalIdeal_iff] at this
    refine isOrdinaryMultiplePoint_of_lt_intersectionNumber hm h2 hev
      (fun i j hij ↦ (forall_mul_add_mul_mem_sq_iff hF2 (hev i) (hev j)).1 fun a b hab ↦ ?_)
      fun i ↦ ?_
    · rw [← hGu, ← hGu, ← mul_assoc, ← mul_assoc, mul_right_comm a, mul_right_comm b] at hab
      obtain ⟨ha, hb⟩ := hind hij _ _ hab
      exact ⟨(mul_unit_mem_iff_mem _ (hu i)).1 ha, (mul_unit_mem_iff_mem _ (hu j)).1 hb⟩
    · rw [intersectionNumber_eq_ord, ← hGu]
      exact (hord i).trans_eq (Ring.ord_mul_of_isUnit_right (hu i) (g i)).symm

/-- The condition of `isOrdinaryMultiplePoint_iff_exists_ord` is invariant under ring
isomorphisms of local rings. -/
private theorem exists_ord_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) {m : ℕ}
    (h : ∃ g : Fin m → R, (∀ i, g i ∈ maximalIdeal R) ∧
      (Pairwise fun i j ↦ ∀ a b, a * g i + b * g j ∈ maximalIdeal R ^ 2 →
        a ∈ maximalIdeal R ∧ b ∈ maximalIdeal R) ∧ ∀ i, (m : ℕ∞) < Ring.ord R (g i)) :
    ∃ g : Fin m → S, (∀ i, g i ∈ maximalIdeal S) ∧
      (Pairwise fun i j ↦ ∀ a b, a * g i + b * g j ∈ maximalIdeal S ^ 2 →
        a ∈ maximalIdeal S ∧ b ∈ maximalIdeal S) ∧ ∀ i, (m : ℕ∞) < Ring.ord S (g i) := by
  obtain ⟨g, hgm, hind, hord⟩ := h
  have hmem (n : ℕ) (x : R) : e x ∈ maximalIdeal S ^ n ↔ x ∈ maximalIdeal R ^ n := by
    rw [← map_ringEquiv_maximalIdeal e, ← Ideal.map_pow, ← comap_symm, mem_comap,
      RingEquiv.symm_apply_apply]
  have hmem1 (x : R) : e x ∈ maximalIdeal S ↔ x ∈ maximalIdeal R := by
    simp
  refine ⟨fun i ↦ e (g i), fun i ↦ (hmem1 _).2 (hgm i), fun i j hij a b hab ↦ ?_,
    fun i ↦ by rw [TauCeti.Ring.ord_ringEquiv]; exact hord i⟩
  rw [← e.apply_symm_apply a, ← e.apply_symm_apply b, ← map_mul, ← map_mul, ← map_add,
    hmem] at hab
  rw [← e.apply_symm_apply a, ← e.apply_symm_apply b, hmem1, hmem1]
  exact hind hij _ _ hab

/-- **Ordinariness is determined by the local ring.** Over an algebraically closed field, if
`F(P) = 0`, `G(Q) = 0` and the local rings `𝒪_P(𝔸²) ⧸ (F)` and `𝒪_Q(𝔸²) ⧸ (G)` are isomorphic as
rings, then `P` is an ordinary multiple point of `F` iff `Q` is one of `G`. -/
theorem isOrdinaryMultiplePoint_iff_of_ringEquiv {Q : Fin 2 → k} (hF : eval P F = 0)
    (hG : eval Q G = 0)
    (e : (localRing k P ⧸ span {algebraMap _ (localRing k P) F}) ≃+*
      (localRing k Q ⧸ span {algebraMap _ (localRing k Q) G})) :
    IsOrdinaryMultiplePoint F P ↔ IsOrdinaryMultiplePoint G Q := by
  have := isLocalRing_quotient_span_singleton hF
  have := isLocalRing_quotient_span_singleton hG
  have hFG := orderAt_eq_of_ringEquiv hF hG e
  cases hm : F.orderAt P using ENat.recTopCoe with
  | top =>
    rw [hm, eq_comm, orderAt_eq_top_iff] at hFG
    rw [orderAt_eq_top_iff] at hm
    subst hm hFG
    exact iff_of_false not_isOrdinaryMultiplePoint_zero not_isOrdinaryMultiplePoint_zero
  | coe m =>
    rw [hm] at hFG
    rw [isOrdinaryMultiplePoint_iff_exists_ord hm, isOrdinaryMultiplePoint_iff_exists_ord hFG.symm]
    exact and_congr_right fun _ ↦
      ⟨exists_ord_of_ringEquiv (R := localRing k P ⧸ span {algebraMap _ (localRing k P) F})
        (S := localRing k Q ⧸ span {algebraMap _ (localRing k Q) G}) e,
        exists_ord_of_ringEquiv (R := localRing k Q ⧸ span {algebraMap _ (localRing k Q) G})
        (S := localRing k P ⧸ span {algebraMap _ (localRing k P) F}) e.symm⟩

/-- Ordinary multiple points are preserved by an isomorphism
`e : k[X, Y][1/h] ≅ k[X, Y][1/h']` with `(e x)(Q) = x(P)` that sends `F` to a unit times `G`. -/
theorem isOrdinaryMultiplePoint_iff_of_algEquiv_away {h h' : MvPolynomial (Fin 2) k}
    {Q : Fin 2 → k} (hF : eval P F = 0) (hG : eval Q G = 0)
    (e : Localization.Away h ≃ₐ[k] Localization.Away h') (hP : eval P h ≠ 0)
    (hQ : eval Q h' ≠ 0)
    (he : (Localization.awayLift (eval Q) h' (isUnit_iff_ne_zero.2 hQ)).comp
      (e : Localization.Away h →+* Localization.Away h') =
      Localization.awayLift (eval P) h (isUnit_iff_ne_zero.2 hP))
    (u : (Localization.Away h')ˣ) (hFG : e (algebraMap _ _ F) = u * algebraMap _ _ G) :
    IsOrdinaryMultiplePoint F P ↔ IsOrdinaryMultiplePoint G Q :=
  isOrdinaryMultiplePoint_iff_of_ringEquiv hF hG (quotientEquivOfAway e hP hQ he u hFG).toRingEquiv

/-- **Local-ring characterization of ordinary multiple points** (Fulton, Problem 3.24). Let `k`
be algebraically closed, `F ∈ k[X, Y]`, `P` a point with `m = m_P(F)`, and `𝒪 = 𝒪_P(𝔸²) ⧸ (F)`
the local ring of `F` at `P` (for irreducible `F` it is `𝒪_P(F)`, by
`AffineSpace.localRing.quotient_iso`), with maximal ideal `𝔪`. Part (a), that the linear forms
map isomorphically onto `𝔪 / 𝔪²` when `m ≥ 2`, is `exists_linearEquiv_gradedPiece_one`.

* (b) If `P` is an ordinary multiple point, its tangents `L₁, …, Lₘ` satisfy
  `I(P, F ∩ Lᵢ(X - P)) > m`, and the lines `Lᵢ(X - P)` have pairwise independent differentials
  at `P`, that is, pairwise linearly independent residues in `𝔪 / 𝔪²`.
* (c) Conversely, if `m ≥ 2` and `G₁, …, Gₘ` vanish at `P`, have pairwise independent
  differentials at `P` and satisfy `I(P, F ∩ Gᵢ) > m`, then `P` is an ordinary multiple point.
* (d) Hence `P` is an ordinary multiple point iff `m ≥ 2` and there are `g₁, …, gₘ ∈ 𝔪` with
  pairwise linearly independent residues in `𝔪 / 𝔪²` and `ℓ(𝒪 ⧸ (gᵢ)) > m`. So being an
  ordinary multiple point depends only on `𝒪`: if `F(P) = 0`, `G(Q) = 0` and
  `𝒪 ≅ 𝒪_Q(𝔸²) ⧸ (G)` as rings, then `P` is ordinary on `F` iff `Q` is ordinary on `G`.

Milestone: *Local-ring characterization of ordinary multiple points*. -/
theorem isOrdinaryMultiplePoint_iff_exists_ord_and_iff_of_ringEquiv {m : ℕ}
    (hm : F.orderAt P = m) :
    (IsOrdinaryMultiplePoint F P →
      ∃ L : Fin m → MvPolynomial (Fin 2) k, (∀ i, IsTangentAt F P (L i)) ∧
        (∀ L', IsTangentAt F P L' → ∃ i, Associated L' (L i)) ∧
        (∀ i, (m : ℕ∞) < intersectionNumber P F (taylor (-P) (L i))) ∧
        Pairwise fun i j ↦ ∀ α β : k,
          2 ≤ (C α * taylor (-P) (L i) + C β * taylor (-P) (L j)).orderAt P → α = 0 ∧ β = 0) ∧
    (2 ≤ m → ∀ G : Fin m → MvPolynomial (Fin 2) k, (∀ i, eval P (G i) = 0) →
      (Pairwise fun i j ↦ ∀ α β : k,
        2 ≤ (C α * G i + C β * G j).orderAt P → α = 0 ∧ β = 0) →
      (∀ i, (m : ℕ∞) < intersectionNumber P F (G i)) → IsOrdinaryMultiplePoint F P) ∧
    (∀ _ : IsLocalRing (localRing k P ⧸ span {algebraMap _ (localRing k P) F}),
      IsOrdinaryMultiplePoint F P ↔ 2 ≤ m ∧
        ∃ g : Fin m → localRing k P ⧸ span {algebraMap _ (localRing k P) F},
          (∀ i, g i ∈ maximalIdeal _) ∧
          (Pairwise fun i j ↦ ∀ a b, a * g i + b * g j ∈ maximalIdeal _ ^ 2 →
            a ∈ maximalIdeal _ ∧ b ∈ maximalIdeal _) ∧
          ∀ i, (m : ℕ∞) < Ring.ord _ (g i)) ∧
    (eval P F = 0 → ∀ (G : MvPolynomial (Fin 2) k) (Q : Fin 2 → k), eval Q G = 0 →
      Nonempty ((localRing k P ⧸ span {algebraMap _ (localRing k P) F}) ≃+*
        (localRing k Q ⧸ span {algebraMap _ (localRing k Q) G})) →
      (IsOrdinaryMultiplePoint F P ↔ IsOrdinaryMultiplePoint G Q)) :=
  ⟨fun h ↦ h.exists_isTangentAt hm,
    fun h2 _ hG hind hI ↦ isOrdinaryMultiplePoint_of_lt_intersectionNumber hm h2 hG hind hI,
    fun _ ↦ isOrdinaryMultiplePoint_iff_exists_ord hm,
    fun hF _ _ hG ⟨e⟩ ↦ isOrdinaryMultiplePoint_iff_of_ringEquiv hF hG e⟩

end IsAlgClosed

end Affine

end PlaneCurves

end
