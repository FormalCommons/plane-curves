/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Bezout.Corollaries
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Finiteness
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.LinearSystem.Independence
public import PlaneCurves.AlgebraicGeometry.PlaneCurve.Projective.Tangent
public import PlaneCurves.RingTheory.MvPolynomial.Factorization

/-!
# Bounds on the multiple points of a plane curve

Let `k` be algebraically closed and `F` a form of degree `n` in `k[X, Y, Z]`, irreducible except
in Problem 5.25.

* **The polar bound** (Fulton, Problem 5.22): `∑_P m_P(F) (m_P(F) - 1) ≤ n(n - 1)`, so `F` has
  at most `n(n - 1)/2` multiple points. Some partial derivative `F_{Xᵢ}` is nonzero, of degree
  `n - 1` and prime to `F`; Corollary 1 of Bézout's theorem for `F` and `F_{Xᵢ}`, with
  `m_P(F_{Xᵢ}) ≥ m_P(F) - 1` (Problem 5.6), gives the bound.
* **Theorem 2 of §5.4**: `∑_P m_P(F) (m_P(F) - 1)/2 ≤ (n - 1)(n - 2)/2`. With
  `r = (n - 1)(n + 2)/2 - ∑_P m_P(m_P - 1)/2`, which the polar bound makes nonnegative, pick `r`
  simple points `Qⱼ` of `F`; a curve `G ≠ 0` of degree `n - 1` with `m_P(G) ≥ m_P(F) - 1` at the
  points `P` and through the `Qⱼ` exists (§5.2, Theorem 1), and Corollary 1 of Bézout's theorem
  for `F` and `G` gives `n(n - 1) ≥ ∑_P m_P(m_P - 1) + r`.
* Its consequences: lines and irreducible conics are nonsingular, an irreducible cubic has at
  most one multiple point, a double point, and an irreducible quartic has either only double
  points, at most three, or one triple point and no other multiple point.
* **Problem 5.25**: for a form `F` of degree `n` with no multiple components and `c`
  irreducible factors, `∑_P m_P(F) (m_P(F) - 1)/2 ≤ (n - 1)(n - 2)/2 + c - 1 ≤ n(n - 1)/2`. With
  `F = GH`, `G` irreducible of degree `a` and prime to `H` of degree `b`, `m_P(F) = m_P(G) +
  m_P(H)`, and Corollary 1 of Bézout's theorem bounds `∑_P m_P(G) m_P(H)` by `ab`; induction on
  the factors of `F` gives the bound from Theorem 2.

The multiplicities are those of `PlaneCurves.Projective.mult`, with values in `ℕ∞`; the sums are
over any finite set of points, or `finsum`s over all of `ℙ²`, whose terms vanish outside the
finitely many multiple points.

## Main results

* `PlaneCurves.Projective.finsum_mult_mul_mult_sub_one_le_mul_sub_one`: the polar bound.
* `PlaneCurves.Projective.ncard_setOf_isMultiplePoint_le`: at most `n(n - 1)/2` multiple points.
* `PlaneCurves.Projective.finsum_mult_mul_mult_sub_one_le_sub_one_mul_sub_two`: Theorem 2,
  `∑_P m_P(m_P - 1) ≤ (n - 1)(n - 2)`, and
  `PlaneCurves.Projective.finsum_toNat_mult_mul_sub_one_div_two_le`, its form with halves.
* `PlaneCurves.Projective.not_isMultiplePoint_of_le_two`,
  `PlaneCurves.Projective.eq_of_isMultiplePoint_of_degree_three`,
  `PlaneCurves.Projective.mult_eq_two_of_degree_three`: lines, conics and cubics.
* `PlaneCurves.Projective.multiple_points_of_degree_four`: quartics.
* `PlaneCurves.Projective.ncard_setOf_isMultiplePoint_le_sub_one_mul_sub_two`: at most
  `(n - 1)(n - 2)/2` multiple points.
* `PlaneCurves.Projective.finsum_mult_mul_mult_sub_one_le_mul_sub_one_spec` and
  `PlaneCurves.Projective.finsum_toNat_mult_mul_sub_one_div_two_le_spec`: the two bounds with
  their consequences, as Fulton states them.
* `PlaneCurves.Projective.finsum_mult_mul_mult_sub_one_add_le` and
  `PlaneCurves.Projective.finsum_toNat_mult_mul_sub_one_div_two_le_of_squarefree`: Problem 5.25.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §5.3, Problem 5.22; §5.4, Theorem 2, Problem 5.25
-/

public section

namespace PlaneCurves.Projective

open MvPolynomial Projectivization TauCeti PlaneCurves.ProjectiveSpace
open scoped LinearAlgebra.Projectivization

variable {k : Type*} [Field k] [IsAlgClosed k] {F : MvPolynomial (Fin 3) k} {n : ℕ}

/-- A `finsum` of `ℕ∞`-valued terms is bounded by any bound of its finite partial sums. -/
private theorem finsum_le_of_forall_sum_le {α : Type*} {f : α → ℕ∞} {c : ℕ∞}
    (h : ∀ s : Finset α, ∑ a ∈ s, f a ≤ c) : ∑ᶠ a, f a ≤ c := by
  by_cases hf : (Function.support f).Finite
  · rw [finsum_eq_sum f hf]
    exact h _
  · rw [finsum_of_infinite_support hf]
    exact zero_le

/-- `(m - 1)((m - 1) + 1) = m(m - 1)` for every natural number `m`. -/
private theorem sub_one_mul_sub_one_add_one (m : ℕ) : (m - 1) * (m - 1 + 1) = m * (m - 1) := by
  rcases m with _ | m
  · rfl
  · simp [mul_comm]

omit [IsAlgClosed k] in
/-- For `F ≠ 0`, the sum of the `m_P(F) (m_P(F) - 1)` in `ℕ∞` is the cast of the sum in `ℕ`. -/
private theorem natCast_sum_toNat_mult (hF0 : F ≠ 0) (s : Finset (ℙ k (Fin 3 → k))) :
    ((∑ P ∈ s, (mult F P).toNat * ((mult F P).toNat - 1) : ℕ) : ℕ∞) =
      ∑ P ∈ s, mult F P * (mult F P - 1) := by
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  rw [Nat.cast_mul, ENat.natCast_sub, ENat.natCast_toNat (mult_eq_top_iff.not.2 hF0),
    Nat.cast_one]

omit [IsAlgClosed k] in
/-- For `F ≠ 0`, `P` is a multiple point of `F` exactly when the natural number `m_P(F)` is at
least `2`. -/
private theorem isMultiplePoint_iff_two_le_toNat (hF0 : F ≠ 0) {P : ℙ k (Fin 3 → k)} :
    IsMultiplePoint F P ↔ 2 ≤ (mult F P).toNat := by
  rw [isMultiplePoint_def, ← ENat.natCast_toNat (mult_eq_top_iff.not.2 hF0)]
  exact_mod_cast Iff.rfl

omit [IsAlgClosed k] in
/-- For `F ≠ 0`, the number of multiple points of `F` in a set `s` of multiple points is at most
half the sum of the `m_P(F) (m_P(F) - 1)`. -/
private theorem two_mul_card_le_sum_toNat_mult (hF0 : F ≠ 0) {s : Finset (ℙ k (Fin 3 → k))}
    (hs : ∀ P ∈ s, IsMultiplePoint F P) :
    2 * s.card ≤ ∑ P ∈ s, (mult F P).toNat * ((mult F P).toNat - 1) := by
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun P hP ↦ ?_
  have := (isMultiplePoint_iff_two_le_toNat hF0).1 (hs P hP)
  nlinarith [Nat.sub_add_cancel (one_le_two.trans this)]

/-! ### The polar bound -/

/-- **The polar bound**, over a finite set of points. Let `k` be algebraically closed and `F`
an irreducible form of degree `n`. Then `∑_{P ∈ s} m_P(F) (m_P(F) - 1) ≤ n(n - 1)`. -/
theorem sum_mult_mul_mult_sub_one_le_mul_sub_one (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) (s : Finset (ℙ k (Fin 3 → k))) :
    ∑ P ∈ s, mult F P * (mult F P - 1) ≤ ↑(n * (n - 1)) := by
  obtain ⟨i, hi⟩ := hirr.exists_pderiv_ne_zero
  have hrel : IsRelPrime F (pderiv i F) :=
    hirr.isRelPrime_iff_not_dvd.2 fun hd ↦ hi (pderiv_eq_zero_of_dvd hd)
  refine (Finset.sum_le_sum fun P _ ↦ ?_).trans
    (sum_mult_mul_mult_le hF hF.pderiv hrel s)
  exact mul_le_mul_right (mult_sub_one_le_mult_pderiv F P i) _

/-- **The polar bound.** Let `k` be algebraically closed and `F` an irreducible form of degree
`n`. Then `∑_P m_P(F) (m_P(F) - 1) ≤ n(n - 1)`. -/
theorem finsum_mult_mul_mult_sub_one_le_mul_sub_one (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) : ∑ᶠ P, mult F P * (mult F P - 1) ≤ ↑(n * (n - 1)) :=
  finsum_le_of_forall_sum_le (sum_mult_mul_mult_sub_one_le_mul_sub_one hF hirr)

/-- An irreducible form `F` of degree `n`, over an algebraically closed field, has at most
`n(n - 1)/2` multiple points. -/
theorem ncard_setOf_isMultiplePoint_le (hF : F.IsHomogeneous n) (hirr : Irreducible F) :
    {P | IsMultiplePoint F P}.ncard ≤ n * (n - 1) / 2 := by
  have hfin := finite_setOf_isMultiplePoint_of_irreducible hF hirr
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have h := sum_mult_mul_mult_sub_one_le_mul_sub_one hF hirr hfin.toFinset
  rw [← natCast_sum_toNat_mult hirr.ne_zero] at h
  have h' : ∑ P ∈ hfin.toFinset, (mult F P).toNat * ((mult F P).toNat - 1) ≤ n * (n - 1) := by
    exact_mod_cast h
  have := two_mul_card_le_sum_toNat_mult hirr.ne_zero (s := hfin.toFinset) (by simp)
  omega

/-- **Polar bound on the multiple points of an irreducible plane curve** (Fulton, Problem 5.22).
Let `k` be algebraically closed and `F` an irreducible form of degree `n` in `k[X, Y, Z]`. Then
`∑_P m_P(F) (m_P(F) - 1) ≤ n(n - 1)`, and `F` has finitely many multiple points, at most
`n(n - 1)/2` of them. No hypothesis `F_X ≠ 0` is needed: some partial derivative of `F` is
nonzero. Every characteristic.

Milestone: *Polar bound on the multiple points of an irreducible plane curve*. -/
theorem finsum_mult_mul_mult_sub_one_le_mul_sub_one_spec (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) :
    ∑ᶠ P, mult F P * (mult F P - 1) ≤ ↑(n * (n - 1)) ∧ {P | IsMultiplePoint F P}.Finite ∧
      {P | IsMultiplePoint F P}.ncard ≤ n * (n - 1) / 2 :=
  ⟨finsum_mult_mul_mult_sub_one_le_mul_sub_one hF hirr,
    finite_setOf_isMultiplePoint_of_irreducible hF hirr, ncard_setOf_isMultiplePoint_le hF hirr⟩

/-! ### Theorem 2 -/

omit [IsAlgClosed k] in
/-- A curve of degree `d` with multiplicity at least `e P` at the points `P` of `s` and through
the points of a disjoint set `T`, when these impose at most `d(d + 3)/2` conditions. -/
private theorem exists_ne_zero_le_mult {d : ℕ} {s T : Finset (ℙ k (Fin 3 → k))}
    (hTs : Disjoint s T) (e : ℙ k (Fin 3 → k) → ℕ)
    (he : ∑ P ∈ s, e P * (e P + 1) / 2 + T.card ≤ d * (d + 3) / 2) :
    ∃ G : MvPolynomial (Fin 3) k, G ≠ 0 ∧ G.IsHomogeneous d ∧
      (∀ P ∈ s, (e P : ℕ∞) ≤ mult G P) ∧ ∀ Q ∈ T, 1 ≤ mult G Q := by
  classical
  let f : ℙ k (Fin 3 → k) → ℕ := fun P ↦ if P ∈ s then e P else if P ∈ T then 1 else 0
  have hf (P) (hP : f P ≠ 0) : P ∈ s ∪ T := by
    simp only [f] at hP
    split_ifs at hP with h1 h2 <;> simp_all
  have hρ : (Finsupp.onFinset (s ∪ T) f hf).sum (fun _ e ↦ e * (e + 1) / 2) ≤
      d * (d + 3) / 2 := by
    rw [Finsupp.onFinset_sum _ fun _ ↦ rfl, Finset.sum_union hTs]
    refine le_of_eq_of_le ?_ he
    congr 1
    · exact Finset.sum_congr rfl fun P hP ↦ by simp [f, hP]
    · rw [Finset.card_eq_sum_ones]
      exact Finset.sum_congr rfl fun P hP ↦ by simp [f, Finset.disjoint_right.1 hTs hP, hP]
  obtain ⟨G, hGmem, hG0⟩ := exists_ne_zero_mem_linearSystem hρ
  obtain ⟨hG, hGmult⟩ := mem_linearSystem.1 hGmem
  refine ⟨G, hG0, hG, fun P hP ↦ ?_, fun Q hQ ↦ ?_⟩
  · simpa [f, hP] using hGmult P
  · simpa [f, Finset.disjoint_right.1 hTs hQ, hQ] using hGmult Q

/-- Theorem 2 in natural numbers, over a finite set of points. -/
private theorem sum_toNat_mult_mul_sub_one_le (hF : F.IsHomogeneous n) (hirr : Irreducible F)
    (s : Finset (ℙ k (Fin 3 → k))) :
    ∑ P ∈ s, (mult F P).toNat * ((mult F P).toNat - 1) ≤ (n - 1) * (n - 2) := by
  classical
  set m : ℙ k (Fin 3 → k) → ℕ := fun P ↦ (mult F P).toNat with hm
  have hmF (P) : mult F P = m P := by
    rw [hm, ENat.natCast_toNat (mult_eq_top_iff.not.2 hirr.ne_zero)]
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := Nat.exists_eq_add_one.2 (Nat.pos_of_ne_zero
    (hF.degree_ne_zero_of_irreducible hirr))
  -- the polar bound, and the halves `δ` of the terms
  set D := ∑ P ∈ s, m P * (m P - 1) with hD
  have hpolar : D ≤ (d + 1) * d := by
    have := sum_mult_mul_mult_sub_one_le_mul_sub_one hF hirr s
    rw [← natCast_sum_toNat_mult hirr.ne_zero, Nat.add_sub_cancel] at this
    exact_mod_cast this
  set δ := ∑ P ∈ s, m P * (m P - 1) / 2 with hδ
  have hDδ : D = 2 * δ := by
    rw [hD, hδ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun P _ ↦
      (Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd).symm
  have e1 : (d + 1) * d = d * d + d := by ring
  have e2 : d * (d + 3) = d * d + 3 * d := by ring
  have e3 : d * (d + 1 - 2) = d * d - d := by rw [show d + 1 - 2 = d - 1 by omega, Nat.mul_sub_one]
  have hev : (d * d + d) % 2 = 0 := by
    rw [← e1, mul_comm]; exact Nat.even_iff.1 (Nat.even_mul_succ_self d)
  have hdd : d ≤ d * d := Nat.le_mul_self d
  -- `r` simple points of `F` off `s`
  set r := d * (d + 3) / 2 - δ
  obtain ⟨T, hTs, hTcard, hTsimple⟩ := exists_finset_isSimplePoint_of_irreducible hF hirr s r
  -- a curve `G` of degree `d` with `m_P(G) ≥ m_P(F) - 1` on `s` through the points of `T`
  obtain ⟨G, hG0, hG, hGs, hGT⟩ := exists_ne_zero_le_mult (d := d) hTs (fun P ↦ m P - 1) (by
    rw [Finset.sum_congr rfl fun P _ ↦ by rw [sub_one_mul_sub_one_add_one], ← hδ, hTcard]
    omega)
  -- Corollary 1 of Bézout's theorem for `F` and `G`
  have hbez := sum_mult_mul_mult_le hF hG (hF.isRelPrime_of_irreducible hirr hG hG0 (by omega))
    (s ∪ T)
  rw [Finset.sum_union hTs] at hbez
  have hs : (D : ℕ∞) ≤ ∑ P ∈ s, mult F P * mult G P := by
    rw [hD, Nat.cast_sum]
    refine Finset.sum_le_sum fun P hP ↦ ?_
    rw [Nat.cast_mul, hmF]
    exact mul_le_mul_right ((ENat.natCast_sub _ _).trans_le (hGs P hP)) _
  have hT : (r : ℕ∞) ≤ ∑ P ∈ T, mult F P * mult G P := by
    rw [← hTcard, Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun Q hQ ↦ ?_
    rw [isSimplePoint_def.1 (hTsimple Q hQ), one_mul]
    exact_mod_cast hGT Q hQ
  have : D + r ≤ (d + 1) * d := by exact_mod_cast (add_le_add hs hT).trans hbez
  change D ≤ d * (d + 1 - 2)
  omega

/-- **Theorem 2 of §5.4**, over a finite set of points. Let `k` be algebraically closed and `F`
an irreducible form of degree `n`. Then `∑_{P ∈ s} m_P(F) (m_P(F) - 1) ≤ (n - 1)(n - 2)`. -/
theorem sum_mult_mul_mult_sub_one_le_sub_one_mul_sub_two (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) (s : Finset (ℙ k (Fin 3 → k))) :
    ∑ P ∈ s, mult F P * (mult F P - 1) ≤ ↑((n - 1) * (n - 2)) := by
  rw [← natCast_sum_toNat_mult hirr.ne_zero]
  exact_mod_cast sum_toNat_mult_mul_sub_one_le hF hirr s

/-- **Theorem 2 of §5.4.** Let `k` be algebraically closed and `F` an irreducible form of degree
`n`. Then `∑_P m_P(F) (m_P(F) - 1) ≤ (n - 1)(n - 2)`. -/
theorem finsum_mult_mul_mult_sub_one_le_sub_one_mul_sub_two (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) : ∑ᶠ P, mult F P * (mult F P - 1) ≤ ↑((n - 1) * (n - 2)) :=
  finsum_le_of_forall_sum_le (sum_mult_mul_mult_sub_one_le_sub_one_mul_sub_two hF hirr)

/-- **Theorem 2 of §5.4**, with halves, in natural numbers. Let `k` be algebraically closed and
`F` an irreducible form of degree `n`. Then `∑_P m_P(F) (m_P(F) - 1)/2 ≤ (n - 1)(n - 2)/2`; the
multiplicities are finite since `F ≠ 0`. -/
theorem finsum_toNat_mult_mul_sub_one_div_two_le (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) :
    ∑ᶠ P, (mult F P).toNat * ((mult F P).toNat - 1) / 2 ≤ (n - 1) * (n - 2) / 2 := by
  set g : ℙ k (Fin 3 → k) → ℕ := fun P ↦ (mult F P).toNat * ((mult F P).toNat - 1)
  by_cases hfin : (Function.support fun P ↦ g P / 2).Finite
  · rw [finsum_eq_sum _ hfin]
    have h := sum_toNat_mult_mul_sub_one_le hF hirr hfin.toFinset
    have h2 : 2 * ∑ P ∈ hfin.toFinset, g P / 2 = ∑ P ∈ hfin.toFinset, g P := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun P _ ↦ Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd
    change ∑ P ∈ hfin.toFinset, g P ≤ _ at h
    change ∑ P ∈ hfin.toFinset, g P / 2 ≤ _
    omega
  · rw [finsum_of_infinite_support hfin]
    exact Nat.zero_le _

/-- An irreducible form `F` of degree `n`, over an algebraically closed field, has at most
`(n - 1)(n - 2)/2` multiple points. -/
theorem ncard_setOf_isMultiplePoint_le_sub_one_mul_sub_two (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) : {P | IsMultiplePoint F P}.ncard ≤ (n - 1) * (n - 2) / 2 := by
  have hfin := finite_setOf_isMultiplePoint_of_irreducible hF hirr
  rw [Set.ncard_eq_toFinset_card _ hfin]
  have h := sum_toNat_mult_mul_sub_one_le hF hirr hfin.toFinset
  have := two_mul_card_le_sum_toNat_mult hirr.ne_zero (s := hfin.toFinset) (by simp)
  omega

/-! ### Curves of low degree -/

/-- Lines and irreducible conics are nonsingular: an irreducible form of degree at most `2` has
no multiple points. -/
theorem not_isMultiplePoint_of_le_two (hF : F.IsHomogeneous n) (hirr : Irreducible F)
    (hn : n ≤ 2) (P : ℙ k (Fin 3 → k)) : ¬IsMultiplePoint F P := by
  intro hP
  have h := sum_toNat_mult_mul_sub_one_le hF hirr {P}
  have h2 := (isMultiplePoint_iff_two_le_toNat hirr.ne_zero).1 hP
  rw [Finset.sum_singleton, show (n - 1) * (n - 2) = 0 by
    rcases Nat.lt_or_ge n 2 with h | h
    · rw [show n - 2 = 0 by omega, mul_zero]
    · rw [show n = 2 by omega]] at h
  nlinarith [Nat.sub_add_cancel (one_le_two.trans h2)]

/-- An irreducible cubic has at most one multiple point. -/
theorem eq_of_isMultiplePoint_of_degree_three (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    {P Q : ℙ k (Fin 3 → k)} (hP : IsMultiplePoint F P) (hQ : IsMultiplePoint F Q) : P = Q := by
  classical
  by_contra hPQ
  have h := sum_toNat_mult_mul_sub_one_le hF hirr {P, Q}
  rw [Finset.sum_pair hPQ] at h
  have hP2 := (isMultiplePoint_iff_two_le_toNat hirr.ne_zero).1 hP
  have hQ2 := (isMultiplePoint_iff_two_le_toNat hirr.ne_zero).1 hQ
  nlinarith [Nat.sub_add_cancel (one_le_two.trans hP2), Nat.sub_add_cancel (one_le_two.trans hQ2)]

/-- A multiple point of an irreducible cubic is a double point. -/
theorem mult_eq_two_of_degree_three (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    {P : ℙ k (Fin 3 → k)} (hP : IsMultiplePoint F P) : mult F P = 2 := by
  have h := sum_toNat_mult_mul_sub_one_le hF hirr {P}
  have h2 := (isMultiplePoint_iff_two_le_toNat hirr.ne_zero).1 hP
  rw [Finset.sum_singleton] at h
  have : (mult F P).toNat = 2 := by
    nlinarith [Nat.sub_add_cancel (one_le_two.trans h2)]
  rw [← ENat.natCast_toNat (mult_eq_top_iff.not.2 hirr.ne_zero), this, Nat.cast_ofNat]

/-- The multiple points of an irreducible quartic are either all double points, at most three
of them, or a single triple point. -/
theorem multiple_points_of_degree_four (hF : F.IsHomogeneous 4) (hirr : Irreducible F) :
    ((∀ P, IsMultiplePoint F P → mult F P = 2) ∧ {P | IsMultiplePoint F P}.ncard ≤ 3) ∨
      ∃ P, mult F P = 3 ∧ ∀ Q ≠ P, ¬IsMultiplePoint F Q := by
  classical
  have hF0 := hirr.ne_zero
  have hm (P) : mult F P = (mult F P).toNat :=
    (ENat.natCast_toNat (mult_eq_top_iff.not.2 hF0)).symm
  by_cases h : ∃ P, IsMultiplePoint F P ∧ (mult F P).toNat ≠ 2
  · obtain ⟨P, hP, hP2⟩ := h
    have h2 := (isMultiplePoint_iff_two_le_toNat hF0).1 hP
    have h1 := sum_toNat_mult_mul_sub_one_le hF hirr {P}
    rw [Finset.sum_singleton] at h1
    have h3 : (mult F P).toNat = 3 := by
      have : 3 ≤ (mult F P).toNat := by omega
      nlinarith [Nat.sub_add_cancel (one_le_two.trans h2)]
    refine Or.inr ⟨P, by rw [hm, h3, Nat.cast_ofNat], fun Q hQP hQ ↦ ?_⟩
    have hQ2 := (isMultiplePoint_iff_two_le_toNat hF0).1 hQ
    have h := sum_toNat_mult_mul_sub_one_le hF hirr {P, Q}
    rw [Finset.sum_pair (Ne.symm hQP), h3] at h
    nlinarith [Nat.sub_add_cancel (one_le_two.trans hQ2)]
  · push Not at h
    refine Or.inl ⟨fun P hP ↦ by rw [hm, h P hP, Nat.cast_ofNat], ?_⟩
    exact ncard_setOf_isMultiplePoint_le_sub_one_mul_sub_two hF hirr

/-- **Bound on the multiple points of an irreducible plane curve** (Fulton, §5.4, Theorem 2 and
the remarks after it). Let `k` be algebraically closed and `F` an irreducible form of degree `n`
in `k[X, Y, Z]`. Then `∑_P m_P(F) (m_P(F) - 1)/2 ≤ (n - 1)(n - 2)/2`, the sum running over the
finitely many multiple points. Consequently

1. lines and irreducible conics are nonsingular;
2. an irreducible cubic has at most one multiple point, and it is a double point;
3. an irreducible quartic has either only double points, at most three of them, or one triple
   point and no other multiple point.

Every characteristic.

For a curve with no multiple components and `c` components, the bound becomes
`(n - 1)(n - 2)/2 + c - 1`: see `finsum_toNat_mult_mul_sub_one_div_two_le_of_squarefree`.

Milestone: *Bound on the multiple points of an irreducible plane curve*. -/
theorem finsum_toNat_mult_mul_sub_one_div_two_le_spec (hF : F.IsHomogeneous n)
    (hirr : Irreducible F) :
    ∑ᶠ P, (mult F P).toNat * ((mult F P).toNat - 1) / 2 ≤ (n - 1) * (n - 2) / 2 ∧
    (n ≤ 2 → ∀ P, ¬IsMultiplePoint F P) ∧
    (n = 3 → (∀ P Q, IsMultiplePoint F P → IsMultiplePoint F Q → P = Q) ∧
      ∀ P, IsMultiplePoint F P → mult F P = 2) ∧
    (n = 4 → ((∀ P, IsMultiplePoint F P → mult F P = 2) ∧ {P | IsMultiplePoint F P}.ncard ≤ 3) ∨
      ∃ P, mult F P = 3 ∧ ∀ Q ≠ P, ¬IsMultiplePoint F Q) := by
  refine ⟨finsum_toNat_mult_mul_sub_one_div_two_le hF hirr,
    fun hn ↦ not_isMultiplePoint_of_le_two hF hirr hn, ?_, ?_⟩
  · rintro rfl
    exact ⟨fun _ _ ↦ eq_of_isMultiplePoint_of_degree_three hF hirr,
      fun _ ↦ mult_eq_two_of_degree_three hF hirr⟩
  · rintro rfl
    exact multiple_points_of_degree_four hF hirr

/-! ### Curves with several components -/

/-- `(g + h)(g + h - 1) = g(g - 1) + h(h - 1) + 2gh` in natural numbers. -/
private theorem add_mul_add_sub_one (g h : ℕ) :
    (g + h) * (g + h - 1) = g * (g - 1) + h * (h - 1) + 2 * (g * h) := by
  rcases g with _ | g
  · simp
  rcases h with _ | h
  · simp
  rw [show g + 1 + (h + 1) - 1 = g + h + 1 by omega, Nat.add_sub_cancel, Nat.add_sub_cancel]
  ring

/-- `(d - 1)(d - 2) + 3d = d² + 2` for `d ≥ 1`, in natural numbers. -/
private theorem sub_one_mul_sub_two_add {d : ℕ} (hd : d ≠ 0) :
    (d - 1) * (d - 2) + 3 * d = d * d + 2 := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_one.2 (Nat.pos_of_ne_zero hd)
  rcases e with _ | e
  · rfl
  rw [show e + 1 + 1 - 1 = e + 1 by omega, show e + 1 + 1 - 2 = e by omega]
  ring

/-- Corollary 1 of Bézout's theorem in natural numbers: for relatively prime nonzero forms `G`
and `H` of degrees `a` and `b`, `∑_{P ∈ s} m_P(G) m_P(H) ≤ ab`. -/
private theorem sum_toNat_mult_mul_toNat_mult_le {G H : MvPolynomial (Fin 3) k} {a b : ℕ}
    (hG : G.IsHomogeneous a) (hH : H.IsHomogeneous b) (hG0 : G ≠ 0) (hH0 : H ≠ 0)
    (hGH : IsRelPrime G H) (s : Finset (ℙ k (Fin 3 → k))) :
    ∑ P ∈ s, (mult G P).toNat * (mult H P).toNat ≤ a * b := by
  have h := sum_mult_mul_mult_le hG hH hGH s
  have hc : ((∑ P ∈ s, (mult G P).toNat * (mult H P).toNat : ℕ) : ℕ∞) =
      ∑ P ∈ s, mult G P * mult H P := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun P _ ↦ ?_
    rw [Nat.cast_mul, ENat.natCast_toNat (mult_eq_top_iff.not.2 hG0),
      ENat.natCast_toNat (mult_eq_top_iff.not.2 hH0)]
  rw [← hc] at h
  exact_mod_cast h

/-- Problem 5.25 in natural numbers, over a finite set of points, in the form
`∑_P m_P(m_P - 1) + 3n ≤ n² + 2c`, by induction on the factors of `F`. -/
private theorem sum_toNat_mult_mul_sub_one_add_le (hF : F.IsHomogeneous n) (hsq : Squarefree F)
    (s : Finset (ℙ k (Fin 3 → k))) :
    ∑ P ∈ s, (mult F P).toNat * ((mult F P).toNat - 1) + 3 * n ≤
      n * n + 2 * (UniqueFactorizationMonoid.factors F).card := by
  induction F using WfDvdMonoid.induction_on_irreducible generalizing n with
  | zero => exact absurd hsq not_squarefree_zero
  | unit u hu =>
    obtain ⟨v, hv⟩ := hu.exists_right_inv
    have hdeg := totalDegree_mul_of_isDomain hu.ne_zero (right_ne_zero_of_mul_eq_one hv)
    rw [hv, totalDegree_one, hF.totalDegree hu.ne_zero] at hdeg
    have hn : n = 0 := by omega
    subst hn
    have hm (P : ℙ k (Fin 3 → k)) : (mult u P).toNat = 0 := by
      have := mult_le_degree hF hu.ne_zero P
      rw [Nat.cast_zero, nonpos_iff_eq_zero] at this
      rw [this, ENat.toNat_zero]
    simp [hm]
  | mul a p ha hp ih =>
    have hp0 := hp.ne_zero
    have hpH : p.IsHomogeneous p.totalDegree := hF.of_mul_left ha
    have haH : a.IsHomogeneous a.totalDegree := hF.of_mul_right hp0
    have hn : n = p.totalDegree + a.totalDegree := (hF.inj_right (hpH.mul haH) (mul_ne_zero hp0 ha))
    have hrel : IsRelPrime p a :=
      hp.isRelPrime_iff_not_dvd.2 fun h ↦ hp.not_isUnit (hsq p (mul_dvd_mul_left p h))
    have h1 := sum_toNat_mult_mul_sub_one_le hpH hp s
    have h2 := ih haH hsq.of_mul_right
    have h3 := sum_toNat_mult_mul_toNat_mult_le hpH haH hp0 ha hrel s
    have h4 := sub_one_mul_sub_two_add (hpH.degree_ne_zero_of_irreducible hp)
    have hm (P : ℙ k (Fin 3 → k)) :
        (mult (p * a) P).toNat = (mult p P).toNat + (mult a P).toNat := by
      rw [mult_mul, ENat.toNat_add (mult_eq_top_iff.not.2 hp0) (mult_eq_top_iff.not.2 ha)]
    rw [Finset.sum_congr rfl fun P _ ↦ by rw [hm, add_mul_add_sub_one],
      Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      Multiset.card_eq_card_of_rel (UniqueFactorizationMonoid.factors_mul hp0 ha),
      Multiset.card_add, UniqueFactorizationMonoid.card_factors_of_irreducible hp]
    have hnn : n * n = p.totalDegree * p.totalDegree + 2 * (p.totalDegree * a.totalDegree) +
        a.totalDegree * a.totalDegree := by
      rw [hn]; ring
    linarith

omit [IsAlgClosed k] in
/-- `∑_P m_P(F)(m_P(F) - 1)` in natural numbers is twice the `finsum` of the halves of its
terms, a sum over some finite set of points. -/
private theorem exists_finset_two_mul_finsum_eq (F : MvPolynomial (Fin 3) k) :
    ∃ s : Finset (ℙ k (Fin 3 → k)),
      2 * ∑ᶠ P, (mult F P).toNat * ((mult F P).toNat - 1) / 2 =
        ∑ P ∈ s, (mult F P).toNat * ((mult F P).toNat - 1) := by
  by_cases hfin : (Function.support fun P ↦ (mult F P).toNat * ((mult F P).toNat - 1) / 2).Finite
  · refine ⟨hfin.toFinset, ?_⟩
    rw [finsum_eq_sum _ hfin, Finset.mul_sum]
    exact Finset.sum_congr rfl fun P _ ↦ Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd
  · exact ⟨∅, by rw [finsum_of_infinite_support hfin]; simp⟩

/-- **Fulton, Problem 5.25**, over a finite set of points. Let `k` be algebraically closed and
`F` a form of degree `n` with no multiple components, and `c` the number of its irreducible
factors. Then `∑_{P ∈ s} m_P(F) (m_P(F) - 1) + 3n ≤ n² + 2c`, that is,
`∑_{P ∈ s} m_P(F) (m_P(F) - 1) ≤ (n - 1)(n - 2) + 2(c - 1)`. -/
theorem sum_mult_mul_mult_sub_one_add_le (hF : F.IsHomogeneous n) (hsq : Squarefree F)
    (s : Finset (ℙ k (Fin 3 → k))) :
    ∑ P ∈ s, mult F P * (mult F P - 1) + ↑(3 * n) ≤
      ↑(n * n + 2 * (UniqueFactorizationMonoid.factors F).card) := by
  rw [← natCast_sum_toNat_mult hsq.ne_zero, ← Nat.cast_add]
  exact_mod_cast sum_toNat_mult_mul_sub_one_add_le hF hsq s

/-- **Fulton, Problem 5.25.** Let `k` be algebraically closed and `F` a form of degree `n` with
no multiple components, and `c` the number of its irreducible factors. Then
`∑_P m_P(F) (m_P(F) - 1) + 3n ≤ n² + 2c`, that is,
`∑_P m_P(F) (m_P(F) - 1) ≤ (n - 1)(n - 2) + 2(c - 1)`. -/
theorem finsum_mult_mul_mult_sub_one_add_le (hF : F.IsHomogeneous n) (hsq : Squarefree F) :
    ∑ᶠ P, mult F P * (mult F P - 1) + ↑(3 * n) ≤
      ↑(n * n + 2 * (UniqueFactorizationMonoid.factors F).card) := by
  by_cases hfin : (Function.support fun P ↦ mult F P * (mult F P - 1)).Finite
  · rw [finsum_eq_sum _ hfin]
    exact sum_mult_mul_mult_sub_one_add_le hF hsq _
  · rw [finsum_of_infinite_support hfin]
    simpa using sum_mult_mul_mult_sub_one_add_le hF hsq ∅

/-- **Bound on the multiple points of a plane curve with `c` components** (Fulton,
Problem 5.25). Let `k` be algebraically closed and `F` a form of degree `n` in `k[X, Y, Z]`
with no multiple components (`Squarefree F`), and `c` the number of its irreducible factors.
Then, in `ℤ`,
`∑_P m_P(F) (m_P(F) - 1)/2 ≤ (n - 1)(n - 2)/2 + c - 1 ≤ n(n - 1)/2`,
the sum running over the finitely many multiple points; the halves are exact. -/
theorem finsum_toNat_mult_mul_sub_one_div_two_le_of_squarefree (hF : F.IsHomogeneous n)
    (hsq : Squarefree F) :
    ((∑ᶠ P, (mult F P).toNat * ((mult F P).toNat - 1) / 2 : ℕ) : ℤ) ≤
        ((n : ℤ) - 1) * (n - 2) / 2 + (UniqueFactorizationMonoid.factors F).card - 1 ∧
      ((n : ℤ) - 1) * (n - 2) / 2 + (UniqueFactorizationMonoid.factors F).card - 1 ≤
        n * (n - 1) / 2 := by
  set S := ∑ᶠ P, (mult F P).toNat * ((mult F P).toNat - 1) / 2
  set c := (UniqueFactorizationMonoid.factors F).card
  obtain ⟨s, hs⟩ := exists_finset_two_mul_finsum_eq F
  have h := sum_toNat_mult_mul_sub_one_add_le hF hsq s
  rw [← hs] at h
  have hc : c ≤ n := hF.totalDegree hsq.ne_zero ▸ card_factors_le_totalDegree hsq.ne_zero
  obtain ⟨q, hq⟩ : 2 ∣ ((n : ℤ) - 1) * (n - 2) := by
    rw [show ((n : ℤ) - 1) * (n - 2) = (n - 2) * (n - 2 + 1) by ring]
    exact (Int.even_mul_succ_self _).two_dvd
  obtain ⟨q', hq'⟩ : 2 ∣ (n : ℤ) * (n - 1) := by
    rw [show (n : ℤ) * (n - 1) = (n - 1) * (n - 1 + 1) by ring]
    exact (Int.even_mul_succ_self _).two_dvd
  rw [hq, hq', Int.mul_ediv_cancel_left _ two_ne_zero, Int.mul_ediv_cancel_left _ two_ne_zero]
  constructor <;> nlinarith

end PlaneCurves.Projective

end
