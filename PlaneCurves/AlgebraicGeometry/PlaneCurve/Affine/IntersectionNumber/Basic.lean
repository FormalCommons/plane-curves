/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.LocalRing.Length
public import TauCeti.RingTheory.Intersection
public import TauCeti.RingTheory.KrullDimension.Regular
public import TauCeti.RingTheory.Length
public import PlaneCurves.AlgebraicGeometry.AffineSpace.LocalRing
public import PlaneCurves.AlgebraicGeometry.AffineSpace.PlaneZeroLocus
public import PlaneCurves.RingTheory.MvPolynomial.Factorization
public import PlaneCurves.RingTheory.UniqueFactorizationDomain.Radical

/-!
# The local intersection number of two affine plane curves

For `F, G ∈ k[X, Y]` and a point `P ∈ k²`, the intersection number `I(P, F ∩ G)` is the length
of `𝒪_P(𝔸²) ⧸ (F, G)` over the local ring `𝒪_P(𝔸²)`, which is its dimension over `k`. This file
defines it, with the notion of two curves intersecting properly at `P`, and proves Fulton's
properties (1)–(4) and (7) over any field.

## Main definitions

* `PlaneCurves.Affine.IntersectProperlyAt F G P`: no irreducible common factor of `F` and `G`
  vanishes at `P`; that is, `F` and `G` have no common component through `P`.
* `PlaneCurves.Affine.intersectionNumber P F G`: the intersection number `I(P, F ∩ G) : ℕ∞`.

## Main results

* `PlaneCurves.Affine.intersectionNumber_eq_length_restrictScalars`: `I(P, F ∩ G)` is the
  dimension of `𝒪_P(𝔸²) ⧸ (F, G)` over `k`.
* `PlaneCurves.Affine.intersectionNumber_ne_top_iff`: property (1), `I(P, F ∩ G) < ∞` iff `F`
  and `G` intersect properly at `P`.
* `PlaneCurves.Affine.intersectionNumber_eq_zero_iff`,
  `PlaneCurves.Affine.intersectionNumber_mul_left_of_eval_ne_zero`: property (2).
* `PlaneCurves.Affine.intersectionNumber_algEquiv`, `PlaneCurves.Affine.intersectionNumber_taylor`,
  `PlaneCurves.Affine.intersectionNumber_linearSubst`: property (3), invariance under changes of
  coordinates.
* `PlaneCurves.Affine.intersectionNumber_comm`: property (4).
* `PlaneCurves.Affine.intersectionNumber_add_mul`: property (7).
* `PlaneCurves.Affine.IntersectProperlyAt.radical_span_eq_maximalIdeal`: for a proper
  intersection through `P`, the ideal `(F, G) 𝒪_P(𝔸²)` has radical the maximal ideal.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §3.3
-/

public section

open MvPolynomial IsLocalRing Ideal

namespace PlaneCurves.Affine

variable {k : Type*} [Field k]

/-! ### Proper intersection -/

/-- Two plane curves `F` and `G` intersect properly at `P` if no irreducible common factor of `F`
and `G` vanishes at `P`, that is, if they have no common component through `P`. Over an
algebraically closed field this is Fulton's condition that `gcd(F, G)` does not vanish at `P`. -/
def IntersectProperlyAt (F G : MvPolynomial (Fin 2) k) (P : Fin 2 → k) : Prop :=
  ∀ H : MvPolynomial (Fin 2) k, Irreducible H → H ∣ F → H ∣ G → eval P H ≠ 0

variable {F G A U : MvPolynomial (Fin 2) k} {P : Fin 2 → k}

theorem intersectProperlyAt_def : IntersectProperlyAt F G P ↔
    ∀ H : MvPolynomial (Fin 2) k, Irreducible H → H ∣ F → H ∣ G → eval P H ≠ 0 :=
  Iff.rfl

theorem IntersectProperlyAt.symm (h : IntersectProperlyAt F G P) : IntersectProperlyAt G F P :=
  fun H hH hG hF => h H hH hF hG

theorem intersectProperlyAt_comm : IntersectProperlyAt F G P ↔ IntersectProperlyAt G F P :=
  ⟨.symm, .symm⟩

/-- Relatively prime curves intersect properly everywhere. -/
theorem _root_.IsRelPrime.intersectProperlyAt (h : IsRelPrime F G) : IntersectProperlyAt F G P :=
  fun _ hH hF hG => (hH.not_isUnit (h hF hG)).elim

/-- A curve not passing through `P` intersects every curve properly at `P`. -/
theorem intersectProperlyAt_of_eval_ne_zero_left (hF : eval P F ≠ 0) :
    IntersectProperlyAt F G P := by
  rintro H - ⟨c, rfl⟩ - hH
  simp [hH] at hF

/-- A curve not passing through `P` intersects every curve properly at `P`. -/
theorem intersectProperlyAt_of_eval_ne_zero_right (hG : eval P G ≠ 0) :
    IntersectProperlyAt F G P :=
  (intersectProperlyAt_of_eval_ne_zero_left hG).symm

theorem intersectProperlyAt_mul_left_iff :
    IntersectProperlyAt (F * G) A P ↔ IntersectProperlyAt F A P ∧ IntersectProperlyAt G A P := by
  refine ⟨fun h => ⟨fun H hH hF hA => h H hH (hF.mul_right G) hA,
    fun H hH hG hA => h H hH (hG.mul_left F) hA⟩, fun ⟨hF, hG⟩ H hH hFG hA => ?_⟩
  rcases hH.prime.dvd_or_dvd hFG with h | h
  exacts [hF H hH h hA, hG H hH h hA]

theorem intersectProperlyAt_mul_right_iff :
    IntersectProperlyAt A (F * G) P ↔ IntersectProperlyAt A F P ∧ IntersectProperlyAt A G P := by
  simp only [intersectProperlyAt_comm (F := A), intersectProperlyAt_mul_left_iff]

/-- Proper intersection depends only on the ideal `(F, G)`: `G` may be replaced by `G + A F`. -/
@[simp]
theorem intersectProperlyAt_add_mul_iff :
    IntersectProperlyAt F (G + A * F) P ↔ IntersectProperlyAt F G P :=
  forall_congr' fun _ => imp_congr_right fun _ => imp_congr_right fun hF =>
    imp_congr_left (dvd_add_left (hF.mul_left A))

/-- If `F` and `G` intersect properly at `P` and `G` vanishes at `P`, then `F ≠ 0`. -/
theorem IntersectProperlyAt.ne_zero_left (h : IntersectProperlyAt F G P) (hG : eval P G = 0) :
    F ≠ 0 := by
  rintro rfl
  by_cases hG0 : G = 0
  · subst hG0
    have hL : (X 0 - C (P 0) : MvPolynomial (Fin 2) k) ≠ 0 := fun hL => by
      simpa using congr(eval (Function.update P 0 (P 0 + 1)) $hL)
    obtain ⟨H, hH, -, hHP⟩ :=
      (RingHom.ker_isPrime (eval P)).exists_irreducible_dvd_mem hL (RingHom.mem_ker.2 (by simp))
    exact h H hH (dvd_zero H) (dvd_zero H) hHP
  · obtain ⟨H, hH, hHG, hHP⟩ :=
      (RingHom.ker_isPrime (eval P)).exists_irreducible_dvd_mem hG0 (RingHom.mem_ker.2 hG)
    exact h H hH (dvd_zero H) hHG hHP

/-- If `F` and `G` intersect properly at `P` and `F` vanishes at `P`, then `G ≠ 0`. -/
theorem IntersectProperlyAt.ne_zero_right (h : IntersectProperlyAt F G P) (hF : eval P F = 0) :
    G ≠ 0 :=
  h.symm.ne_zero_left hF

/-! ### The intersection number -/

/-- The intersection number `I(P, F ∩ G)` of two affine plane curves at a point `P ∈ k²`: the
length of `𝒪_P(𝔸²) ⧸ (F, G)` over the local ring `𝒪_P(𝔸²)`. It is `⊤` exactly when `F` and `G`
do not intersect properly at `P` (`intersectionNumber_ne_top_iff`). -/
noncomputable def intersectionNumber (P : Fin 2 → k) (F G : MvPolynomial (Fin 2) k) : ℕ∞ :=
  Module.length (AffineSpace.localRing k P) (AffineSpace.localRing k P ⧸
    Ideal.span {algebraMap _ (AffineSpace.localRing k P) F, algebraMap _ _ G})

theorem intersectionNumber_def (P : Fin 2 → k) (F G : MvPolynomial (Fin 2) k) :
    intersectionNumber P F G = Module.length (AffineSpace.localRing k P)
      (AffineSpace.localRing k P ⧸
        Ideal.span {algebraMap _ (AffineSpace.localRing k P) F, algebraMap _ _ G}) :=
  (rfl)

/-- The intersection number is the dimension over `k` of `𝒪_P(𝔸²) ⧸ (F, G)`, Fulton's
definition. -/
theorem intersectionNumber_eq_length_restrictScalars (P : Fin 2 → k)
    (F G : MvPolynomial (Fin 2) k) :
    intersectionNumber P F G = Module.length k (AffineSpace.localRing k P ⧸
      Ideal.span {algebraMap _ (AffineSpace.localRing k P) F, algebraMap _ _ G}) := by
  rw [IsLocalRing.length_restrictScalars k (AffineSpace.localRing k P),
    ← Module.length_eq_of_surjective (R := IsLocalRing.ResidueField k)
      (M := IsLocalRing.ResidueField _)
      residue_surjective,
    (AffineSpace.localRing.residueFieldAlgEquiv k P).toLinearEquiv.length_eq,
    Module.length_eq_finrank, Module.finrank_self, Nat.cast_one, mul_one, intersectionNumber_def]

/-- The intersection number is `(dim_k 𝒪_P(𝔸²) ⧸ (F, G))`, as an element of `ℕ∞`. -/
theorem intersectionNumber_eq_rank (P : Fin 2 → k) (F G : MvPolynomial (Fin 2) k) :
    intersectionNumber P F G = (Module.rank k (AffineSpace.localRing k P ⧸
      Ideal.span {algebraMap _ (AffineSpace.localRing k P) F, algebraMap _ _ G})).toENat := by
  rw [intersectionNumber_eq_length_restrictScalars, Module.length_eq_rank]

/-- The intersection number depends only on the ideal `(F, G)` of `k[X, Y]`. -/
theorem intersectionNumber_congr {F' G' : MvPolynomial (Fin 2) k}
    (h : Ideal.span {F, G} = Ideal.span {F', G'}) :
    intersectionNumber P F G = intersectionNumber P F' G' := by
  have h' := congr(Ideal.map (algebraMap _ (AffineSpace.localRing k P)) $h)
  simp only [Ideal.map_span, Set.image_pair] at h'
  rw [intersectionNumber_def, intersectionNumber_def, h']

/-- **Property (4)**: the intersection number is symmetric. -/
theorem intersectionNumber_comm (P : Fin 2 → k) (F G : MvPolynomial (Fin 2) k) :
    intersectionNumber P F G = intersectionNumber P G F :=
  TauCeti.length_quotient_span_pair_comm _ _

/-- **Property (7)**: `I(P, F ∩ (G + A F)) = I(P, F ∩ G)`. -/
@[simp]
theorem intersectionNumber_add_mul (P : Fin 2 → k) (F G A : MvPolynomial (Fin 2) k) :
    intersectionNumber P F (G + A * F) = intersectionNumber P F G :=
  intersectionNumber_congr (Ideal.span_pair_add_mul_left _ _ _)

/-- **Property (2)**, first part: `I(P, F ∩ G) = 0` iff `P` lies on only one of the curves. -/
theorem intersectionNumber_eq_zero_iff :
    intersectionNumber P F G = 0 ↔ eval P F ≠ 0 ∨ eval P G ≠ 0 := by
  rw [intersectionNumber_def, TauCeti.length_quotient_span_pair_eq_zero_iff,
    ← AffineSpace.localRing.isUnit_algebraMap_iff, ← AffineSpace.localRing.isUnit_algebraMap_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra! hu
    refine (maximalIdeal.isMaximal (AffineSpace.localRing k P)).ne_top (eq_top_iff.2 ?_)
    rw [← h, Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hu.1, hu.2⟩
  · rcases h with h | h
    · exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) h
    · exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) h

/-- A curve not through `P` meets every curve with intersection number zero at `P`. -/
theorem intersectionNumber_eq_zero_of_eval_ne_zero_left (hF : eval P F ≠ 0) :
    intersectionNumber P F G = 0 :=
  intersectionNumber_eq_zero_iff.2 (.inl hF)

/-- A curve not through `P` meets every curve with intersection number zero at `P`. -/
theorem intersectionNumber_eq_zero_of_eval_ne_zero_right (hG : eval P G ≠ 0) :
    intersectionNumber P F G = 0 :=
  intersectionNumber_eq_zero_iff.2 (.inr hG)

/-- **Property (2)**, second part: `I(P, F U ∩ G) = I(P, F ∩ G)` when `U(P) ≠ 0`. -/
theorem intersectionNumber_mul_left_of_eval_ne_zero (hU : eval P U ≠ 0) :
    intersectionNumber P (F * U) G = intersectionNumber P F G := by
  rw [intersectionNumber_def, intersectionNumber_def, map_mul, Ideal.span_insert,
    Ideal.span_singleton_mul_right_unit (AffineSpace.localRing.isUnit_algebraMap_iff.2 hU),
    ← Ideal.span_insert]

/-- `I(P, F ∩ G U) = I(P, F ∩ G)` when `U(P) ≠ 0`. -/
theorem intersectionNumber_mul_right_of_eval_ne_zero (hU : eval P U ≠ 0) :
    intersectionNumber P F (G * U) = intersectionNumber P F G := by
  rw [intersectionNumber_comm, intersectionNumber_mul_left_of_eval_ne_zero hU,
    intersectionNumber_comm]

/-! #### Changes of coordinates -/

/-- An isomorphism of local rings carrying `F, G` to `F', G'` preserves intersection numbers. -/
private theorem intersectionNumber_eq_of_ringEquiv {Q : Fin 2 → k}
    (e : AffineSpace.localRing k P ≃+* AffineSpace.localRing k Q)
    {F' G' : MvPolynomial (Fin 2) k} (hF : e (algebraMap _ _ F) = algebraMap _ _ F')
    (hG : e (algebraMap _ _ G) = algebraMap _ _ G') :
    intersectionNumber Q F' G' = intersectionNumber P F G := by
  have h := Ideal.length_quotient_map_of_surjective
    (Ideal.span {algebraMap _ (AffineSpace.localRing k P) F, algebraMap _ _ G}) e.surjective
  rw [Ideal.map_span, Set.image_pair, hF, hG,
    (RingHom.injective_iff_ker_eq_bot _).1 e.injective, sup_bot_eq] at h
  rw [intersectionNumber_def, intersectionNumber_def, h]

/-- **Property (3)**: intersection numbers are invariant under polynomial changes of coordinates.
If `ψ` is a `k`-algebra automorphism of `k[X, Y]`, the substitution of a polynomial
automorphism `T` of `𝔸²` with `T(Q) = P`, so that `(ψ g)(Q) = g(P)`, then
`I(Q, ψ F ∩ ψ G) = I(P, F ∩ G)`. -/
theorem intersectionNumber_algEquiv {Q : Fin 2 → k}
    (ψ : MvPolynomial (Fin 2) k ≃ₐ[k] MvPolynomial (Fin 2) k) (h : ∀ g, eval Q (ψ g) = eval P g)
    (F G : MvPolynomial (Fin 2) k) :
    intersectionNumber Q (ψ F) (ψ G) = intersectionNumber P F G :=
  intersectionNumber_eq_of_ringEquiv (AffineSpace.localRing.mapEquiv ψ h).toRingEquiv
    (AffineSpace.localRing.mapEquiv_algebraMap ψ h F)
    (AffineSpace.localRing.mapEquiv_algebraMap ψ h G)

/-- Translating `P` to the origin preserves intersection numbers:
`I(0, F(X + P) ∩ G(X + P)) = I(P, F ∩ G)`. -/
@[simp]
theorem intersectionNumber_taylor (P : Fin 2 → k) (F G : MvPolynomial (Fin 2) k) :
    intersectionNumber 0 (taylor P F) (taylor P G) = intersectionNumber P F G :=
  intersectionNumber_eq_of_ringEquiv (AffineSpace.localRing.taylorEquiv P).toRingEquiv
    (AffineSpace.localRing.taylorEquiv_algebraMap F)
    (AffineSpace.localRing.taylorEquiv_algebraMap G)

/-- An invertible linear substitution `f ↦ f(M X)` preserves intersection numbers:
`I(P, F(M X) ∩ G(M X)) = I(M P, F ∩ G)`. -/
@[simp]
theorem intersectionNumber_linearSubst (M : Matrix.GeneralLinearGroup (Fin 2) k)
    (P : Fin 2 → k) (F G : MvPolynomial (Fin 2) k) :
    intersectionNumber P (linearSubst M.1 F) (linearSubst M.1 G) =
      intersectionNumber (M.1.mulVec P) F G :=
  intersectionNumber_eq_of_ringEquiv
    (AffineSpace.localRing.linearSubstEquiv (P := P) M).toRingEquiv
    (AffineSpace.localRing.linearSubstEquiv_algebraMap M F)
    (AffineSpace.localRing.linearSubstEquiv_algebraMap M G)

/-! #### Finiteness -/

/-- If `k[X, Y] ⧸ (F, G)` is finite-dimensional, then `I(P, F ∩ G)` is finite at every `P`. -/
theorem intersectionNumber_ne_top_of_finite
    [Module.Finite k (MvPolynomial (Fin 2) k ⧸ Ideal.span {F, G})] :
    intersectionNumber P F G ≠ ⊤ := by
  by_cases hP : eval P F ≠ 0 ∨ eval P G ≠ 0
  · simp [intersectionNumber_eq_zero_iff.2 hP]
  push Not at hP
  set J := Ideal.span {F, G}
  have hJ : J ≤ vanishingIdeal k {P} := by
    rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨(mem_vanishingIdeal_singleton_iff P F).2 hP.1,
      (mem_vanishingIdeal_singleton_iff P G).2 hP.2⟩
  have := isPrime_map_quotientMk_of_isPrime hJ
  have : IsArtinianRing (MvPolynomial (Fin 2) k ⧸ J) := .of_finite k _
  have hs := IsArtinianRing.localization_surjective
    ((vanishingIdeal k {P}).map (Ideal.Quotient.mk J)).primeCompl
    (Localization.AtPrime ((vanishingIdeal k {P}).map (Ideal.Quotient.mk J)))
  have := Module.Finite.of_surjective
    (IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k ⧸ J) _).toLinearMap hs
  have := Module.Finite.equiv (Localization.AtPrime.quotientAlgEquiv k hJ).toLinearEquiv
  rw [intersectionNumber_eq_length_restrictScalars, ← Set.image_pair, ← Ideal.map_span,
    Module.length_eq_finrank]
  exact ENat.natCast_ne_top _

/-- **Property (1)**: `I(P, F ∩ G)` is finite iff `F` and `G` intersect properly at `P`. -/
theorem intersectionNumber_ne_top_iff :
    intersectionNumber P F G ≠ ⊤ ↔ IntersectProperlyAt F G P := by
  refine ⟨fun h H hH hF hG hHP => h ?_, fun h => ?_⟩
  · -- `𝒪 ⧸ (F, G)` maps onto `𝒪 ⧸ (H)`, of dimension one, hence of infinite length
    set 𝒪 := AffineSpace.localRing k P
    have hH𝒪 : algebraMap _ 𝒪 H ∈ maximalIdeal 𝒪 := by
      rw [← AffineSpace.localRing.evalAt_eq_zero_iff, AffineSpace.localRing.evalAt_algebraMap, hHP]
    have hHnz : algebraMap _ 𝒪 H ∈ nonZeroDivisors 𝒪 :=
      mem_nonZeroDivisors_of_ne_zero fun h0 => hH.ne_zero <|
        IsLocalization.injective 𝒪 (vanishingIdeal k {P}).primeCompl_le_nonZeroDivisors
          (h0.trans (map_zero _).symm)
    have hd : ringKrullDim 𝒪 = 2 := by
      rw [AffineSpace.localRing.ringKrullDim_eq, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have hle : Ideal.span {algebraMap _ 𝒪 F, algebraMap _ 𝒪 G} ≤ Ideal.span {algebraMap _ 𝒪 H} := by
      rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨Ideal.mem_span_singleton.2 (map_dvd _ hF), Ideal.mem_span_singleton.2 (map_dvd _ hG)⟩
    refine top_le_iff.1 ((top_le_iff.2 ?_).trans (TauCeti.length_quotient_anti hle))
    rw [Module.length_eq_of_surjective (R := 𝒪 ⧸ Ideal.span {algebraMap _ 𝒪 H})
      Ideal.Quotient.mk_surjective]
    exact TauCeti.length_self_eq_top_of_ringKrullDim_pos
      (by rw [TauCeti.ringKrullDim_quotient_span_singleton_eq_one hd hH𝒪 hHnz]; exact one_pos)
  · -- remove the factors not vanishing at `P`; what remains is relatively prime
    by_cases hP : eval P F ≠ 0 ∨ eval P G ≠ 0
    · simp [intersectionNumber_eq_zero_iff.2 hP]
    push Not at hP
    obtain ⟨F', U, rfl, hU, hF'⟩ := exists_eq_mul_eval_ne_zero P (h.ne_zero_left hP.2)
    obtain ⟨G', V, rfl, hV, -⟩ := exists_eq_mul_eval_ne_zero P (h.ne_zero_right hP.1)
    have hrel : IsRelPrime F' G' :=
      WfDvdMonoid.isRelPrime_of_no_irreducible_factors
        (fun h0 => left_ne_zero_of_mul (h.ne_zero_left hP.2) h0.1)
        fun H hH h1 h2 => h H hH (h1.mul_right U) (h2.mul_right V) (hF' H hH h1)
    have := finite_quotient_span_pair_of_isRelPrime hrel
    rw [intersectionNumber_mul_left_of_eval_ne_zero hU,
      intersectionNumber_mul_right_of_eval_ne_zero hV]
    exact intersectionNumber_ne_top_of_finite

/-- `I(P, F ∩ G) = ⊤` iff `F` and `G` do not intersect properly at `P`. -/
theorem intersectionNumber_eq_top_iff :
    intersectionNumber P F G = ⊤ ↔ ¬IntersectProperlyAt F G P := by
  rw [← intersectionNumber_ne_top_iff, not_not]

/-- `I(P, 0 ∩ G) = ⊤` iff `G(P) = 0`. -/
theorem intersectionNumber_zero_left_eq_top_iff :
    intersectionNumber P 0 G = ⊤ ↔ eval P G = 0 := by
  refine ⟨fun h => ?_, fun h => intersectionNumber_eq_top_iff.2 fun h' => h'.ne_zero_left h rfl⟩
  by_contra hG
  simp [intersectionNumber_eq_zero_of_eval_ne_zero_right hG] at h

/-- For a proper intersection at a common point `P`, the ideal `(F, G)` of `𝒪_P(𝔸²)` has radical
the maximal ideal: it is `𝔪`-primary. -/
theorem IntersectProperlyAt.radical_span_eq_maximalIdeal (h : IntersectProperlyAt F G P)
    (hF : eval P F = 0) (hG : eval P G = 0) :
    (Ideal.span {algebraMap _ (AffineSpace.localRing k P) F, algebraMap _ _ G}).radical =
      maximalIdeal (AffineSpace.localRing k P) := by
  set 𝒪 := AffineSpace.localRing k P
  set I := Ideal.span {algebraMap _ 𝒪 F, algebraMap _ 𝒪 G}
  have hI : I ≠ ⊤ := fun hI => by
    simpa [hF, hG] using intersectionNumber_eq_zero_iff.1
      ((TauCeti.length_quotient_span_pair_eq_zero_iff _ _).2 hI)
  have hfin := Module.length_ne_top_iff.1 (intersectionNumber_ne_top_iff.2 h)
  have : IsArtinianRing (𝒪 ⧸ I) :=
    isArtinian_of_tower 𝒪 (isFiniteLength_iff_isNoetherian_isArtinian.1 hfin).2
  rw [Ideal.radical_eq_sInf]
  refine le_antisymm (sInf_le ⟨le_maximalIdeal hI, inferInstance⟩)
    (le_sInf fun J ⟨hIJ, hJ⟩ => ?_)
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ J := by rwa [Ideal.mk_ker]
  have := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have : (J.map (Ideal.Quotient.mk I)).IsMaximal :=
    IsArtinianRing.isMaximal_of_isPrime (R := 𝒪 ⧸ I) (J.map (Ideal.Quotient.mk I))
  have hmax := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective (K := J.map (Ideal.Quotient.mk I))
  rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.2 hker] at hmax
  exact (IsLocalRing.eq_maximalIdeal hmax).ge

/-- **Finiteness and vanishing of the local intersection number** (Fulton, §3.3, properties
(1)–(4) and (7)). Over any field `k`, for `F, G ∈ k[X, Y]` and `P ∈ k²`:
1. `I(P, F ∩ G)` is finite iff `F` and `G` intersect properly at `P`;
2. `I(P, F ∩ G) = 0` iff `F(P) ≠ 0` or `G(P) ≠ 0`, and `I(P, F U ∩ G) = I(P, F ∩ G)` when
   `U(P) ≠ 0`;
3. `I(Q, ψ F ∩ ψ G) = I(P, F ∩ G)` for every change of coordinates, that is, every `k`-algebra
   automorphism `ψ` of `k[X, Y]` with `(ψ g)(Q) = g(P)` for all `g`; the substitution of an
   affine change of coordinates `T` with `T(Q) = P` is one;
4. `I(P, F ∩ G) = I(P, G ∩ F)`;
7. `I(P, F ∩ (G + A F)) = I(P, F ∩ G)`.

Milestone: *Finiteness and vanishing of the local intersection number*. -/
theorem intersectionNumber_ne_top_iff_and_eq_zero_iff (P : Fin 2 → k)
    (F G : MvPolynomial (Fin 2) k) :
    (intersectionNumber P F G ≠ ⊤ ↔ IntersectProperlyAt F G P) ∧
    (intersectionNumber P F G = 0 ↔ eval P F ≠ 0 ∨ eval P G ≠ 0) ∧
    (∀ U, eval P U ≠ 0 → intersectionNumber P (F * U) G = intersectionNumber P F G) ∧
    (∀ (Q : Fin 2 → k) (ψ : MvPolynomial (Fin 2) k ≃ₐ[k] MvPolynomial (Fin 2) k),
      (∀ g, eval Q (ψ g) = eval P g) →
        intersectionNumber Q (ψ F) (ψ G) = intersectionNumber P F G) ∧
    intersectionNumber P F G = intersectionNumber P G F ∧
    ∀ A, intersectionNumber P F (G + A * F) = intersectionNumber P F G :=
  ⟨intersectionNumber_ne_top_iff, intersectionNumber_eq_zero_iff,
    fun _ hU => intersectionNumber_mul_left_of_eval_ne_zero hU,
    fun _ ψ h => intersectionNumber_algEquiv ψ h F G, intersectionNumber_comm P F G,
    intersectionNumber_add_mul P F G⟩

end PlaneCurves.Affine

end
