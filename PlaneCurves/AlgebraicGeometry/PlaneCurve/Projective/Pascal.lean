/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Cubic.Residual
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Bezout.Corollaries

/-!
# Pascal's and Pappus's theorems

Two corollaries of the residual intersection theorem for a conic on a cubic (Fulton, §5.6,
Proposition 2). A hexagon has vertices `P₀, …, P₅` and sides `Lᵢ`, the lines through `Pᵢ` and
`Pᵢ₊₁` (indices mod 6); the opposite sides are `Lᵢ` and `Lᵢ₊₃`.

Both theorems follow from one statement about a hexagon inscribed in a conic `G`, possibly
reducible: if no side passes through a third vertex and no side is a component of `G`, then the
three points where opposite sides meet are collinear. The proof is Fulton's: with the cubics
`F = L₀ L₂ L₄` and `H = L₁ L₃ L₅`, the cycle `G • F` is the six vertices, each a simple point of
`F`, and it lies below `H • F`; Proposition 2 cuts out the residual cycle `H • F - G • F`, which
contains the three points, by a line.

## Main results

* `exists_isHomogeneous_one_of_hexagon`: the statement for a hexagon inscribed in any conic.
* `pascal`: **Pascal's theorem** for a hexagon inscribed in an irreducible conic.
* `pappus`: **Pappus's theorem**.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.6, Corollaries 1 and 2
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] [IsAlgClosed k]

/-- **The opposite sides of a hexagon inscribed in a conic meet in collinear points.** Let `k`
be algebraically closed, `G` a conic (a form of degree 2, possibly reducible), `P₀, …, P₅` points
of `G`, and `Lᵢ` a line through `Pᵢ` and `Pᵢ₊₁` (indices mod 6) that is not a component of `G`
and passes through no other `Pⱼ`. If `Rᵢ` lies on the opposite sides `Lᵢ` and `Lᵢ₊₃`, for
`i = 0, 1, 2`, then `R₀`, `R₁` and `R₂` lie on a line. The hypotheses force the `Pᵢ` to be
distinct. -/
theorem exists_isHomogeneous_one_of_hexagon {G : MvPolynomial (Fin 3) k}
    (hG : G.IsHomogeneous 2) {P : Fin 6 → ℙ k (Fin 3 → k)} (hPG : ∀ i, eval (P i).rep G = 0)
    {L : Fin 6 → MvPolynomial (Fin 3) k} (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : ∀ i, L i ≠ 0)
    (hLG : ∀ i, ¬L i ∣ G)
    (hLP : ∀ i, eval (P i).rep (L i) = 0 ∧ eval (P (i + 1)).rep (L i) = 0)
    (hLP' : ∀ i j, j ≠ i → j ≠ i + 1 → eval (P j).rep (L i) ≠ 0) {R : Fin 3 → ℙ k (Fin 3 → k)}
    (hR : ∀ i, eval (R i).rep (L (Fin.castAdd 3 i)) = 0 ∧
      eval (R i).rep (L (Fin.natAdd 3 i)) = 0) :
    ∃ M : MvPolynomial (Fin 3) k, M.IsHomogeneous 1 ∧ M ≠ 0 ∧ ∀ i, eval (R i).rep M = 0 := by
  classical
  have hirr i : Irreducible (L i) := irreducible_of_isHomogeneous_one (hL i) (hL0 i)
  have hinj : Function.Injective P := by
    intro i j hij
    by_contra hne
    by_cases hj : j = i + 1
    · subst hj
      refine hLP' (i + 1) i (by grind) (by grind) ?_
      rw [hij]
      exact (hLP _).1
    · exact hLP' i j (Ne.symm hne) hj (hij ▸ (hLP i).1)
  -- a side meets `G` only in its two vertices
  have hside i S (hS : eval S.rep (L i) = 0) (hSG : eval S.rep G = 0) :
      S = P i ∨ S = P (i + 1) := by
    have hne : P i ≠ P (i + 1) := hinj.ne (by grind)
    exact eq_or_eq_of_isHomogeneous_one_of_not_dvd (hL i) (hL0 i) hG (hLG i) hne
      ⟨(hLP i).1, hPG i⟩ ⟨(hLP i).2, hPG _⟩ ⟨hS, hSG⟩
  have hLL i j (hij : i ≠ j) : IsRelPrime (L i) (L j) := by
    refine (hirr i).isRelPrime_iff_not_dvd.2 fun hd ↦ ?_
    have key : (i ≠ j ∧ i ≠ j + 1) ∨ (i + 1 ≠ j ∧ i + 1 ≠ j + 1) := by grind
    rcases key with h | h
    · exact hLP' j i h.1 h.2 (zero_dvd_iff.1 ((hLP i).1 ▸ map_dvd (eval (P i).rep) hd))
    · exact hLP' j (i + 1) h.1 h.2 (zero_dvd_iff.1 ((hLP i).2 ▸ map_dvd (eval (P (i + 1)).rep) hd))
  set F := L 0 * L 2 * L 4 with hFdef
  set H := L 1 * L 3 * L 5 with hHdef
  have hF : F.IsHomogeneous 3 := ((hL 0).mul (hL 2)).mul (hL 4)
  have hH : H.IsHomogeneous 3 := ((hL 1).mul (hL 3)).mul (hL 5)
  have hLG' i : IsRelPrime (L i) G := (hirr i).isRelPrime_iff_not_dvd.2 (hLG i)
  have hFG : IsRelPrime F G := ((hLG' 0).mul_left (hLG' 2)).mul_left (hLG' 4)
  have hFH : IsRelPrime F H := by
    have h a (ha : a = 0 ∨ a = 2 ∨ a = 4) : IsRelPrime (L a) H :=
      (((hLL a 1 (by grind)).mul_right (hLL a 3 (by grind))).mul_right (hLL a 5 (by grind)))
    exact ((h 0 (by simp)).mul_left (h 2 (by simp))).mul_left (h 4 (by simp))
  -- the common zeros of `F` and `G` are the six vertices
  set s : Finset (ℙ k (Fin 3 → k)) := Finset.univ.image P
  have hs S : S ∈ s ↔ eval S.rep F = 0 ∧ eval S.rep G = 0 := by
    constructor
    · rintro hS
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hS
      refine ⟨?_, hPG i⟩
      have := hLP 0; have := hLP 1; have := hLP 2; have := hLP 3; have := hLP 4; have := hLP 5
      fin_cases i <;> simp_all
    · rintro ⟨hSF, hSG⟩
      simp only [hFdef, eval_mul, mul_eq_zero] at hSF
      have h a (ha : eval S.rep (L a) = 0) : S ∈ s := by
        rcases hside a S ha hSG with rfl | rfl <;> exact Finset.mem_image_of_mem _ (by simp)
      rcases hSF with (h0 | h2) | h4
      exacts [h 0 h0, h 2 h2, h 4 h4]
  have hcard : s.card = 3 * 2 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hsH S (hS : S ∈ s) : eval S.rep H = 0 := by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hS
    have := hLP 0; have := hLP 1; have := hLP 2; have := hLP 3; have := hLP 4; have := hLP 5
    fin_cases i <;> simp_all
  -- `G • F ≤ H • F`
  have hle : intersectionCycle G F ≤ intersectionCycle H F := by
    intro S
    by_cases hS : S ∈ s
    · have hI := (isSimplePoint_of_card_eq_mul hF hG hs hcard hS).2.2.1
      have h1 : intersectionCycle G F S = 1 := by
        have := intersectionCycle_apply hG hF hFG.symm S
        rw [intersectionNumber_comm, hI] at this
        exact_mod_cast this
      rw [h1, Nat.one_le_iff_ne_zero, ← Finsupp.mem_support_iff,
        mem_support_intersectionCycle_iff hH hF hFH.symm]
      exact ⟨hsH S hS, ((hs S).1 hS).1⟩
    · have : S ∉ (intersectionCycle G F).support := by
        rw [mem_support_intersectionCycle_iff hG hF hFG.symm, and_comm, ← hs]
        exact hS
      rw [Finsupp.notMem_support_iff.1 this]
      exact Nat.zero_le _
  obtain ⟨M, hM, hM0, hFM, hMF⟩ := exists_isHomogeneous_one_intersectionCycle_eq hF hG hH hFG hFH
    (add_tsub_cancel_of_le hle).symm fun S hS ↦ by
      rw [mem_support_intersectionCycle_iff hG hF hFG.symm, and_comm, ← hs] at hS
      exact (isSimplePoint_of_card_eq_mul hF hG hs hcard hS).1
  refine ⟨M, hM, hM0, fun i ↦ ?_⟩
  -- `Rᵢ` is not a vertex, and lies on `F` and on `H`
  have hRs : R i ∉ s := by
    intro hRs
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hRs
    have h1 := hR i
    rw [← hj] at h1
    have key : ∀ i : Fin 3, ∀ j : Fin 6, (j ≠ Fin.castAdd 3 i ∧ j ≠ Fin.castAdd 3 i + 1) ∨
        (j ≠ Fin.natAdd 3 i ∧ j ≠ Fin.natAdd 3 i + 1) := by decide
    rcases key i j with h | h
    · exact hLP' _ j h.1 h.2 h1.1
    · exact hLP' _ j h.1 h.2 h1.2
  have hRFH : eval (R i).rep F = 0 ∧ eval (R i).rep H = 0 := by
    have := hR i
    fin_cases i <;> simp_all
  have hRE : R i ∈ (intersectionCycle M F).support := by
    rw [hMF, Finsupp.mem_support_iff, Finsupp.tsub_apply]
    have hG0 : intersectionCycle G F (R i) = 0 := by
      rw [← Finsupp.notMem_support_iff, mem_support_intersectionCycle_iff hG hF hFG.symm,
        and_comm, ← hs]
      exact hRs
    have hH0 : intersectionCycle H F (R i) ≠ 0 := by
      rw [← Finsupp.mem_support_iff, mem_support_intersectionCycle_iff hH hF hFH.symm]
      exact hRFH.symm
    omega
  exact ((mem_support_intersectionCycle_iff hM hF hFM.symm).1 hRE).1

/-- **Pascal's theorem** (Fulton, §5.6, Corollary 1). Let `k` be algebraically closed, `G` an
irreducible conic, `P₀, …, P₅` distinct points of `G`, and `Lᵢ` a line through `Pᵢ` and `Pᵢ₊₁`
(indices mod 6). If `Rᵢ` lies on the opposite sides `Lᵢ` and `Lᵢ₊₃`, for `i = 0, 1, 2`, then
`R₀`, `R₁` and `R₂` lie on a line. Opposite sides are distinct lines, since an irreducible conic
contains no three collinear points, so each `Rᵢ` is the point where they meet.

Milestone: *Pascal's theorem for a hexagon inscribed in an irreducible conic*. -/
theorem pascal {G : MvPolynomial (Fin 3) k} (hG : G.IsHomogeneous 2) (hirr : Irreducible G)
    {P : Fin 6 → ℙ k (Fin 3 → k)} (hP : Function.Injective P) (hPG : ∀ i, eval (P i).rep G = 0)
    {L : Fin 6 → MvPolynomial (Fin 3) k} (hL : ∀ i, (L i).IsHomogeneous 1) (hL0 : ∀ i, L i ≠ 0)
    (hLP : ∀ i, eval (P i).rep (L i) = 0 ∧ eval (P (i + 1)).rep (L i) = 0)
    {R : Fin 3 → ℙ k (Fin 3 → k)}
    (hR : ∀ i, eval (R i).rep (L (Fin.castAdd 3 i)) = 0 ∧
      eval (R i).rep (L (Fin.natAdd 3 i)) = 0) :
    ∃ M : MvPolynomial (Fin 3) k, M.IsHomogeneous 1 ∧ M ≠ 0 ∧ ∀ i, eval (R i).rep M = 0 := by
  classical
  have hirrL i : Irreducible (L i) := irreducible_of_isHomogeneous_one (hL i) (hL0 i)
  have hLG i : ¬L i ∣ G := fun h ↦ by
    have := totalDegree_le_of_dvd_of_isDomain
      (((hirrL i).dvd_irreducible_iff_associated hirr).1 h).symm.dvd (hL0 i)
    rw [hG.totalDegree hirr.ne_zero, (hL i).totalDegree (hL0 i)] at this
    omega
  refine exists_isHomogeneous_one_of_hexagon hG hPG hL hL0 hLG hLP (fun i j hji hji' hj ↦ ?_) hR
  -- otherwise `Lᵢ` meets `G` in three points
  rcases eq_or_eq_of_isHomogeneous_one_of_not_dvd (hL i) (hL0 i) hG (hLG i) (hP.ne (by grind))
      ⟨(hLP i).1, hPG i⟩ ⟨(hLP i).2, hPG _⟩ ⟨hj, hPG j⟩ with h | h
  exacts [hji (hP h), hji' (hP h)]

/-- **Pappus's theorem** (Fulton, §5.6, Corollary 2). Let `k` be algebraically closed, `A` and
`B` lines, `P₀, P₁, P₂` distinct points of `A` not on `B`, and `Q₀, Q₁, Q₂` distinct points of `B`
not on `A`. Let `Lᵢⱼ` be a line through `Pᵢ` and `Qⱼ`. If `Rₗ` lies on `Lᵢⱼ` and on `Lⱼᵢ`
whenever `{i, j, l} = {0, 1, 2}`, then `R₀`, `R₁` and `R₂` lie on a line. The lines `Lᵢⱼ` and
`Lⱼᵢ` are distinct for `i ≠ j`, so each `Rₗ` is the point where they meet.

Milestone: *Pappus's theorem*. -/
theorem pappus {A B : MvPolynomial (Fin 3) k} (hA : A.IsHomogeneous 1) (hB : B.IsHomogeneous 1)
    {P Q : Fin 3 → ℙ k (Fin 3 → k)} (hP : Function.Injective P) (hQ : Function.Injective Q)
    (hPA : ∀ i, eval (P i).rep A = 0) (hPB : ∀ i, eval (P i).rep B ≠ 0)
    (hQB : ∀ j, eval (Q j).rep B = 0) (hQA : ∀ j, eval (Q j).rep A ≠ 0)
    {L : Fin 3 → Fin 3 → MvPolynomial (Fin 3) k} (hL : ∀ i j, (L i j).IsHomogeneous 1)
    (hL0 : ∀ i j, L i j ≠ 0)
    (hLP : ∀ i j, eval (P i).rep (L i j) = 0 ∧ eval (Q j).rep (L i j) = 0)
    {R : Fin 3 → ℙ k (Fin 3 → k)}
    (hR : ∀ i j l, i ≠ j → j ≠ l → i ≠ l → eval (R l).rep (L i j) = 0) :
    ∃ M : MvPolynomial (Fin 3) k, M.IsHomogeneous 1 ∧ M ≠ 0 ∧ ∀ i, eval (R i).rep M = 0 := by
  have hA0 : A ≠ 0 := fun h ↦ hQA 0 (by simp [h])
  have hB0 : B ≠ 0 := fun h ↦ hPB 0 (by simp [h])
  -- `Lᵢⱼ` passes through no other `Pᵢ'` or `Qⱼ'`, and is neither `A` nor `B`
  have hP' i j i' (h : i' ≠ i) : eval (P i').rep (L i j) ≠ 0 := fun h0 ↦
    hQA j (zero_dvd_iff.1 ((hLP i j).2 ▸ map_dvd (eval _)
      (associated_of_eval_rep_eq_zero_of_ne (hL i j) (hL0 i j) hA hA0
        (hP.ne h.symm) (hLP i j).1 h0 (hPA i) (hPA i')).dvd))
  have hQ' i j j' (h : j' ≠ j) : eval (Q j').rep (L i j) ≠ 0 := fun h0 ↦
    hPB i (zero_dvd_iff.1 ((hLP i j).1 ▸ map_dvd (eval _)
      (associated_of_eval_rep_eq_zero_of_ne (hL i j) (hL0 i j) hB hB0
        (hQ.ne h.symm) (hLP i j).2 h0 (hQB j) (hQB j')).dvd))
  have hLG i j : ¬L i j ∣ A * B := fun h ↦
    ((irreducible_of_isHomogeneous_one (hL i j) (hL0 i j)).prime.dvd_or_dvd h).elim
      (fun h ↦ hQA j (zero_dvd_iff.1 ((hLP i j).2 ▸ map_dvd (eval _) h)))
      (fun h ↦ hPB i (zero_dvd_iff.1 ((hLP i j).1 ▸ map_dvd (eval _) h)))
  -- the hexagon `P₀ Q₁ P₂ Q₀ P₁ Q₂`, with sides `L₀₁, L₂₁, L₂₀, L₁₀, L₁₂, L₀₂`
  set V : Fin 6 → ℙ k (Fin 3 → k) := ![P 0, Q 1, P 2, Q 0, P 1, Q 2]
  set ip : Fin 6 → Fin 3 := ![0, 2, 2, 1, 1, 0]
  set jq : Fin 6 → Fin 3 := ![1, 1, 0, 0, 2, 2]
  have hVb b : (V b = P (![0, 0, 2, 2, 1, 1] b) ∧
        ∀ a, b ≠ a → b ≠ a + 1 → ![0, 0, 2, 2, 1, 1] b ≠ ip a) ∨
      (V b = Q (![1, 1, 0, 0, 2, 2] b) ∧
        ∀ a, b ≠ a → b ≠ a + 1 → ![1, 1, 0, 0, 2, 2] b ≠ jq a) := by
    fin_cases b
    exacts [Or.inl ⟨rfl, by decide⟩, Or.inr ⟨rfl, by decide⟩, Or.inl ⟨rfl, by decide⟩,
      Or.inr ⟨rfl, by decide⟩, Or.inl ⟨rfl, by decide⟩, Or.inr ⟨rfl, by decide⟩]
  obtain ⟨M, hM, hM0, hMR⟩ := exists_isHomogeneous_one_of_hexagon (G := A * B) (P := V)
    (L := fun a ↦ L (ip a) (jq a)) (R := ![R 2, R 0, R 1]) (by simpa using hA.mul hB)
    (fun a ↦ by fin_cases a <;> simp [V, hPA, hQB]) (fun a ↦ hL _ _) (fun a ↦ hL0 _ _)
    (fun a ↦ hLG _ _) (fun a ↦ by fin_cases a <;> simp [V, ip, jq, hLP])
    (fun a b h1 h2 ↦ by
      rcases hVb b with ⟨hb, hd⟩ | ⟨hb, hd⟩ <;> rw [hb]
      exacts [hP' _ _ _ (hd a h1 h2), hQ' _ _ _ (hd a h1 h2)])
    (fun i ↦ by
      fin_cases i <;>
        exact ⟨hR _ _ _ (by decide) (by decide) (by decide),
          hR _ _ _ (by decide) (by decide) (by decide)⟩)
  refine ⟨M, hM, hM0, fun i ↦ ?_⟩
  fin_cases i
  exacts [hMR 1, hMR 2, hMR 0]

end PlaneCurves.Projective

end
