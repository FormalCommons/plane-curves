/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Affine.IntersectionNumber.Sum
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Finiteness
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.IntersectionNumber.Basic
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.ChangeOfCoordinates
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import PlaneCurves.AlgebraicGeometry.ProjectiveSpace.LinearSubvariety
public import PlaneCurves.RingTheory.MvPolynomial.Irreducible
public import PlaneCurves.RingTheory.MvPolynomial.QuotientSpanPair

/-!
# Bézout's theorem

Let `k` be algebraically closed and `F`, `G` forms of degrees `m` and `n` in `k[X, Y, Z]` with
no common component. **Bézout's theorem** says that `∑_P I(P, F ∩ G) = mn`, the sum over the
finitely many points of `ℙ²` where both curves pass.

The proof is Fulton's (§5.3). The common zeros are finite (Problem 5.7), so a line misses them
all, and a projective change of coordinates makes it the line `Z = 0`; intersection numbers do
not change (property (3)). Then `F(X, Y, 0)` and `G(X, Y, 0)` are coprime, and Steps 1–3 of
`PlaneCurves.RingTheory.MvPolynomial.QuotientSpanPair` give `dim_k k[X, Y]/(F_*, G_*) = mn`. All
intersection points lie in the chart `Z ≠ 0`, where the intersection numbers are the affine
ones, which add up to `dim_k k[X, Y]/(F_*, G_*)` (property (9)).

## Main results

* `PlaneCurves.Projective.isRelPrime_bind₁_update_X_zero`: if no common zero of `F` and `G`
  lies on `X i = 0`, then `F` and `G` stay coprime when `X i` is set to zero.
* `PlaneCurves.Projective.finite_support_intersectionNumber`: relatively prime forms have
  nonzero intersection numbers at finitely many points.
* `PlaneCurves.Projective.finsum_intersectionNumber_eq_mul_of_forall_mem_affineOpen`: Bézout's
  theorem when all common zeros lie in a standard chart.
* `PlaneCurves.Projective.finsum_intersectionNumber_eq_mul`: Bézout's theorem,
  `∑ᶠ P, I(P, F ∩ G) = mn`, and `sum_intersectionNumber_eq_mul` for a sum over a `Finset`
  containing the common zeros.
* `PlaneCurves.Projective.finsum_intersectionNumber_eq_of_isHomogeneous_one`: a line `L` that
  is not a component of `F` meets it in `deg F` points, counted with multiplicity (Problem 5.12).
* `PlaneCurves.Projective.finsum_intersectionNumber_spec`: the milestone, both statements.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.3, and §5.1, Problem 5.12
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] {F G : MvPolynomial (Fin 3) k} {m n : ℕ}

/-- Points of `ℙ²` with a nonzero intersection number of `F` and `G` are common zeros. -/
theorem eval_rep_eq_zero_of_intersectionNumber_ne_zero (hF : F.IsHomogeneous m)
    (hG : G.IsHomogeneous n) {P : ℙ k (Fin 3 → k)} (h : intersectionNumber P F G ≠ 0) :
    eval P.rep F = 0 ∧ eval P.rep G = 0 := by
  simpa [intersectionNumber_eq_zero_iff hF hG] using h

/-- Relatively prime forms have a nonzero intersection number at only finitely many points. -/
theorem finite_support_intersectionNumber (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hFG : IsRelPrime F G) : (Function.support fun P ↦ intersectionNumber P F G).Finite := by
  refine (finite_zeroLocus_pair_of_isRelPrime hF hG hFG).subset fun P hP ↦ ?_
  have h := eval_rep_eq_zero_of_intersectionNumber_ne_zero hF hG hP
  rw [mem_zeroLocus_iff_eval_rep (by rintro f (rfl | rfl); exacts [⟨m, hF⟩, ⟨n, hG⟩])]
  rintro f (rfl | rfl)
  exacts [h.1, h.2]

/-- **The hypothesis of Step 2 of Bézout's proof.** Let `k` be algebraically closed and `F`, `G`
forms in `k[X, Y, Z]` without common zero on the line `X i = 0`. Then `F` and `G` stay coprime
when `X i` is set to zero: a common factor of positive degree would vanish at a point of that
line. -/
theorem isRelPrime_bind₁_update_X_zero [IsAlgClosed k] (hF : F.IsHomogeneous m)
    (hG : G.IsHomogeneous n) {i : Fin 3}
    (h : ∀ P : ℙ k (Fin 3 → k), eval P.rep F = 0 → eval P.rep G = 0 → P ∈ affineOpen i) :
    IsRelPrime (bind₁ (Function.update X i 0) F) (bind₁ (Function.update X i 0) G) := by
  classical
  set φ : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 3) k := bind₁ (Function.update X i 0)
  have hg (j : Fin 3) : (Function.update X i (0 : MvPolynomial (Fin 3) k) j).IsHomogeneous 1 := by
    rcases eq_or_ne j i with rfl | hj
    · simpa using isHomogeneous_zero (Fin 3) k 1
    · simpa [hj] using isHomogeneous_X k j
  have hφ {p : MvPolynomial (Fin 3) k} {d : ℕ} (hp : p.IsHomogeneous d) :
      (φ p).IsHomogeneous d := by
    simpa using hp.aeval _ hg
  by_contra hφFG
  obtain ⟨H', e, he, hH', hH'F, hH'G⟩ :=
    (hφ hF).exists_isHomogeneous_dvd_of_not_isRelPrime (hφ hG) hφFG
  obtain ⟨P, hP⟩ := zeroLocus_nonempty_of_card_le (s := {H', X i}) Finset.card_le_two (by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro f (rfl | rfl)
    exacts [⟨e, he, hH'⟩, ⟨1, one_ne_zero, isHomogeneous_X k i⟩])
  rw [Finset.coe_insert, Finset.coe_singleton, mem_zeroLocus_iff_eval_rep (by
    rintro f (rfl | rfl); exacts [⟨e, hH'⟩, ⟨1, isHomogeneous_X k i⟩])] at hP
  have hPH : eval P.rep H' = 0 := hP H' (by simp)
  have hPi : P.rep i = 0 := by simpa using hP (X i) (by simp)
  have hPφ {K : MvPolynomial (Fin 3) k} (hK : H' ∣ φ K) : eval P.rep K = 0 := by
    obtain ⟨c, hc⟩ := hK
    have := congrArg (eval P.rep) hc
    rwa [eval_bind₁_update_X_zero, ← hPi, Function.update_eq_self, eval_mul, hPH,
      zero_mul] at this
  exact (mem_affineOpen_iff i P).1 (h P (hPφ hH'F) (hPφ hH'G)) hPi

variable [IsAlgClosed k]

/-- **Bézout's theorem in good coordinates.** Let `k` be algebraically closed and `F`, `G`
relatively prime forms of degrees `m` and `n` in `k[X, Y, Z]` whose common zeros all lie in the
chart `X i ≠ 0`. Then `∑ᶠ P, I(P, F ∩ G) = mn`. -/
theorem finsum_intersectionNumber_eq_mul_of_forall_mem_affineOpen (hF : F.IsHomogeneous m)
    (hG : G.IsHomogeneous n) (hFG : IsRelPrime F G) {i : Fin 3}
    (h : ∀ P : ℙ k (Fin 3 → k), eval P.rep F = 0 → eval P.rep G = 0 → P ∈ affineOpen i) :
    ∑ᶠ P, intersectionNumber P F G = ↑(m * n) := by
  classical
  obtain ⟨hV, -, hsum⟩ := Affine.sum_intersectionNumber_eq_finrank_of_isRelPrime
    (isRelPrime_dehomogenize (i := i) hF hG hFG)
  rw [finrank_quotient_span_pair_dehomogenize hF hG hFG
    (isRelPrime_bind₁_update_X_zero hF hG h)] at hsum
  have hinj : Set.InjOn (affineChart (K := k) i).symm (hV.toFinset : Set (Fin 2 → k)) :=
    fun x _ y _ hxy ↦ by
      simpa [(affineChart i).right_inv] using congrArg (affineChart i) hxy
  rw [finsum_eq_sum_of_support_subset (s := hV.toFinset.image (affineChart i).symm), ← hsum,
    Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    have hx : (affineChart i).symm x ∈ affineOpen i := by
      simp
    rw [intersectionNumber_eq_affine hF hG hx,
      (affineChart i).right_inv (by simp)]
  · intro P hP
    obtain ⟨hPF, hPG⟩ := eval_rep_eq_zero_of_intersectionNumber_ne_zero hF hG hP
    have hPi := h P hPF hPG
    simp only [Finset.coe_image, Set.Finite.coe_toFinset, Set.mem_image]
    refine ⟨affineChart i P, ?_, (affineChart i).left_inv (by simpa using hPi)⟩
    rw [MvPolynomial.mem_zeroLocus_iff]
    intro p hp
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hp
    simp [(eval_affineChart_dehomogenize_eq_zero_iff hPi hF).2 hPF,
      (eval_affineChart_dehomogenize_eq_zero_iff hPi hG).2 hPG]

/-- **Bézout's theorem.** Let `k` be algebraically closed and `F`, `G` forms of degrees `m` and
`n` in `k[X, Y, Z]` with no common component. Then `∑ᶠ P, I(P, F ∩ G) = mn`, a sum with finitely
many nonzero terms (`finite_support_intersectionNumber`). -/
theorem finsum_intersectionNumber_eq_mul (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hFG : IsRelPrime F G) : ∑ᶠ P, intersectionNumber P F G = ↑(m * n) := by
  classical
  -- a change of coordinates moving the finitely many common zeros into the chart `Z ≠ 0`
  obtain ⟨N, hN⟩ :=
    exists_linearSubst_forall_mem_affineOpen_last (finite_zeroLocus_pair_of_isRelPrime hF hG hFG)
  set T := map N.1.mulVecLin (Matrix.mulVec_injective_of_isUnit N.isUnit)
  have hrel : IsRelPrime (linearSubst N.1 F) (linearSubst N.1 G) :=
    IsRelPrime.of_map (linearSubstAlgEquiv N).symm (by
      rwa [← linearSubstAlgEquiv_apply, ← linearSubstAlgEquiv_apply, AlgEquiv.symm_apply_apply,
        AlgEquiv.symm_apply_apply])
  have key := finsum_intersectionNumber_eq_mul_of_forall_mem_affineOpen (i := Fin.last 2)
    (hF.linearSubst N.1) (hG.linearSubst N.1) hrel fun Q hQF hQG ↦ hN Q (by
      rw [mem_zeroLocus_iff_eval_rep (by rintro f (rfl | rfl); exacts [⟨m, hF⟩, ⟨n, hG⟩])]
      rintro f (rfl | rfl)
      exacts [(eval_rep_linearSubst_eq_zero_iff N hF Q).1 hQF,
        (eval_rep_linearSubst_eq_zero_iff N hG Q).1 hQG])
  simp_rw [intersectionNumber_linearSubst hF hG N] at key
  rw [← finsum_comp_equiv (Equiv.ofBijective T (bijective_map_mulVecLin N))]
  exact key

/-- **Bézout's theorem**, as a sum over a `Finset` containing the common zeros of `F` and `G`. -/
theorem sum_intersectionNumber_eq_mul (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous n)
    (hFG : IsRelPrime F G) {s : Finset (ℙ k (Fin 3 → k))}
    (hs : ∀ P : ℙ k (Fin 3 → k), eval P.rep F = 0 → eval P.rep G = 0 → P ∈ s) :
    ∑ P ∈ s, intersectionNumber P F G = ↑(m * n) := by
  rw [← finsum_intersectionNumber_eq_mul hF hG hFG,
    finsum_eq_sum_of_support_subset _ fun P hP ↦ ?_]
  obtain ⟨hPF, hPG⟩ := eval_rep_eq_zero_of_intersectionNumber_ne_zero hF hG hP
  exact hs P hPF hPG

/-- **Problem 5.12.** Let `k` be algebraically closed, `F` a form of degree `m` and `L` a line,
that is, a nonzero form of degree one, that is not a component of `F`. Then
`∑ᶠ P, I(P, F ∩ L) = m`. -/
theorem finsum_intersectionNumber_eq_of_isHomogeneous_one {L : MvPolynomial (Fin 3) k}
    (hF : F.IsHomogeneous m) (hL : L.IsHomogeneous 1) (hL0 : L ≠ 0) (hLF : ¬ L ∣ F) :
    ∑ᶠ P, intersectionNumber P F L = m := by
  simpa using finsum_intersectionNumber_eq_mul hF hL
    ((irreducible_of_isHomogeneous_one hL hL0).isRelPrime_iff_not_dvd.2 hLF).symm

/-- **Bézout's theorem for projective plane curves** (Fulton, §5.3, and Problem 5.12). Let `k` be
algebraically closed and `F` a form of degree `m` in `k[X, Y, Z]`.

1. For a form `G` of degree `n` with no common component with `F`, the intersection number
   `I(P, F ∩ G)` is nonzero at only finitely many points `P` of `ℙ²`, and
   `∑ᶠ P, I(P, F ∩ G) = mn`.
2. For a line `L`, a nonzero form of degree one, that is not a component of `F`,
   `∑ᶠ P, I(P, F ∩ L) = m`.

Neither statement needs `m` or `n` to be positive.

Milestone: *Bézout's theorem for projective plane curves*. -/
theorem finsum_intersectionNumber_spec (hF : F.IsHomogeneous m) :
    (∀ {G : MvPolynomial (Fin 3) k} {n : ℕ}, G.IsHomogeneous n → IsRelPrime F G →
      (Function.support fun P ↦ intersectionNumber P F G).Finite ∧
        ∑ᶠ P, intersectionNumber P F G = ↑(m * n)) ∧
    (∀ {L : MvPolynomial (Fin 3) k}, L.IsHomogeneous 1 → L ≠ 0 → ¬ L ∣ F →
      ∑ᶠ P, intersectionNumber P F L = m) :=
  ⟨fun hG hFG ↦ ⟨finite_support_intersectionNumber hF hG hFG,
    finsum_intersectionNumber_eq_mul hF hG hFG⟩,
    finsum_intersectionNumber_eq_of_isHomogeneous_one hF⟩

end PlaneCurves.Projective

end
