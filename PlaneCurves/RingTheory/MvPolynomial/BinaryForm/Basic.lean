/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import TauCeti.Algebra.Polynomial.Homogenize

/-!
# Binary forms split into linear forms

A binary form is a homogeneous `F : MvPolynomial (Fin 2) R`; we write `X = X 0` and `Y = X 1`.
Its dehomogenization is `F(X, 1) = aeval ![Polynomial.X, 1] F`.

## Main results

* `MvPolynomial.IsHomogeneous.eq_C_mul_X_pow_mul_prod`: over a domain, if `F(X, 1)` has as many
  roots as its degree, then a binary form `F` of degree `d` is
  `F = c Y ^ (d - deg F(X, 1)) ∏ⱼ (X - λⱼ Y)`, where `c` is the leading coefficient of `F(X, 1)`
  and the `λⱼ` are its roots, with multiplicity.
* `MvPolynomial.IsHomogeneous.exists_eq_C_mul_prod_of_splits`: hence a nonzero binary form of
  degree `d` whose dehomogenization splits is `ε ∏ᵢ (aᵢ X + bᵢ Y)` for some `ε ≠ 0` and `d` nonzero
  linear forms.
* `MvPolynomial.IsHomogeneous.splits_iff_exists_eq_C_mul_prod`: over a field, a nonzero binary
  form is a product of linear forms if and only if its dehomogenization splits.
* `MvPolynomial.IsHomogeneous.exists_eq_C_mul_prod`: over an algebraically closed field, every
  nonzero binary form of degree `d` is a product of `d` linear forms.
* `MvPolynomial.irreducible_of_isHomogeneous_one`: over a field, nonzero linear forms in any
  number of variables are irreducible.
* `MvPolynomial.irreducible_C_mul_X_add_C_mul_X`, `MvPolynomial.rel_associated_of_C_mul_prod_eq`:
  over a field, nonzero linear forms are irreducible, so the linear factors of a binary form are
  unique up to order and nonzero scalars.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §2.6, Corollary (p. 24)
-/

public section

namespace MvPolynomial

section Domain

variable {R : Type*} [CommRing R] [IsDomain R] {F : MvPolynomial (Fin 2) R} {d : ℕ}

/-- Over a domain, if the dehomogenization `g = F(X, 1)` of a binary form `F` of degree `d` has as
many roots as its degree, then `F = c Y ^ (d - deg g) ∏_{λ ∈ roots g} (X - λ Y)`, where `c` is the
leading coefficient of `g`. -/
theorem IsHomogeneous.eq_C_mul_X_pow_mul_prod (hF : F.IsHomogeneous d)
    (hroots : Multiset.card (MvPolynomial.aeval ![Polynomial.X, 1] F : Polynomial R).roots =
      (MvPolynomial.aeval ![Polynomial.X, 1] F : Polynomial R).natDegree) :
    F = C (MvPolynomial.aeval ![Polynomial.X, 1] F : Polynomial R).leadingCoeff *
      X 1 ^ (d - (MvPolynomial.aeval ![Polynomial.X, 1] F : Polynomial R).natDegree) *
      ((MvPolynomial.aeval ![Polynomial.X, 1] F : Polynomial R).roots.map
        fun a ↦ X 0 - C a * X 1).prod := by
  have hgd : (MvPolynomial.aeval ![Polynomial.X, 1] F : Polynomial R).natDegree ≤ d :=
    hF.natDegree_aeval_le fun i ↦ by fin_cases i <;> simp
  conv_lhs => rw [← Polynomial.homogenize_eq_of_isHomogeneous hF rfl]
  exact Polynomial.homogenize_eq_C_mul_X_pow_mul_prod hgd hroots

/-- Over a domain, a nonzero binary form `F` of degree `d` whose dehomogenization `F(X, 1)` splits
is `F = ε ∏ᵢ (aᵢ X + bᵢ Y)` for some `ε ≠ 0` and `d` linear forms with `(aᵢ, bᵢ) ≠ (0, 0)`.
The linear forms are `X - λ Y` for the roots `λ` of `F(X, 1)`, with multiplicity, and `Y`. -/
theorem IsHomogeneous.exists_eq_C_mul_prod_of_splits (hF : F.IsHomogeneous d) (hF₀ : F ≠ 0)
    (hs : (MvPolynomial.aeval ![Polynomial.X, 1] F : Polynomial R).Splits) :
    ∃ ε : R, ε ≠ 0 ∧ ∃ s : Multiset (R × R), Multiset.card s = d ∧ (∀ ℓ ∈ s, ℓ ≠ (0, 0)) ∧
      F = C ε * (s.map fun ℓ ↦ C ℓ.1 * X 0 + C ℓ.2 * X 1).prod := by
  set g : Polynomial R := MvPolynomial.aeval ![Polynomial.X, 1] F
  have hgd : g.natDegree ≤ d := hF.natDegree_aeval_le fun i ↦ by fin_cases i <;> simp
  have hg₀ : g ≠ 0 := fun hg ↦ hF₀ (by
    rw [← Polynomial.homogenize_eq_of_isHomogeneous hF rfl]
    exact (congrArg (Polynomial.homogenize · d) hg).trans (Polynomial.homogenize_zero d))
  have hfac := hF.eq_C_mul_X_pow_mul_prod (Polynomial.splits_iff_card_roots.1 hs)
  refine ⟨g.leadingCoeff, Polynomial.leadingCoeff_ne_zero.2 hg₀,
    g.roots.map (fun a ↦ ((1 : R), -a)) + Multiset.replicate (d - g.natDegree) (0, 1), ?_, ?_, ?_⟩
  · simp [Polynomial.splits_iff_card_roots.1 hs, hgd]
  · intro ℓ hℓ
    rcases Multiset.mem_add.1 hℓ with h | h
    · obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 h
      simp
    · simp [Multiset.eq_of_mem_replicate h]
  · conv_lhs => rw [hfac]
    simp only [Multiset.map_add, Multiset.prod_add, Multiset.map_map, Multiset.map_replicate,
      Multiset.prod_replicate, Function.comp_def, map_one, one_mul, map_zero, zero_mul, zero_add,
      map_neg, neg_mul, ← sub_eq_add_neg]
    ring

end Domain

section Field

variable {K : Type*} [Field K] {F : MvPolynomial (Fin 2) K} {d : ℕ}

/-- Over a field, a nonzero linear form, in any number of variables, is irreducible. -/
theorem irreducible_of_isHomogeneous_one {σ : Type*} {L : MvPolynomial σ K}
    (hL : L.IsHomogeneous 1) (hL₀ : L ≠ 0) : Irreducible L := by
  refine irreducible_of_totalDegree_eq_one (hL.totalDegree hL₀) fun x hx ↦ ?_
  obtain ⟨d, hd⟩ := ne_zero_iff.1 hL₀
  exact isUnit_iff_ne_zero.2 fun hx0 ↦ hd (zero_dvd_iff.1 (hx0 ▸ hx d))

/-- Over a field, a nonzero linear binary form `a X + b Y` is irreducible. -/
theorem irreducible_C_mul_X_add_C_mul_X {a b : K} (h : (a, b) ≠ (0, 0)) :
    Irreducible (C a * X 0 + C b * X 1 : MvPolynomial (Fin 2) K) := by
  have ha : (C a * X 0 + C b * X 1 : MvPolynomial (Fin 2) K).coeff (Finsupp.single 0 1) = a := by
    simp [coeff_X, Finsupp.single_eq_single_iff]
  have hb : (C a * X 0 + C b * X 1 : MvPolynomial (Fin 2) K).coeff (Finsupp.single 1 1) = b := by
    simp [coeff_X, Finsupp.single_eq_single_iff]
  have hne : (C a * X 0 + C b * X 1 : MvPolynomial (Fin 2) K) ≠ 0 := fun h0 ↦
    h (by simp only [h0] at ha hb; simp [← ha, ← hb])
  refine irreducible_of_totalDegree_eq_one ?_ fun x hx ↦ ?_
  · exact (((isHomogeneous_C _ a).mul (isHomogeneous_X K 0)).add
      ((isHomogeneous_C _ b).mul (isHomogeneous_X K 1))).totalDegree hne
  · refine isUnit_iff_ne_zero.2 fun hx0 ↦ h ?_
    have h0 := hx (Finsupp.single 0 1)
    have h1 := hx (Finsupp.single 1 1)
    rw [ha, hx0, zero_dvd_iff] at h0
    rw [hb, hx0, zero_dvd_iff] at h1
    rw [h0, h1]

/-- Over a field, the linear factors of a binary form are unique up to order and nonzero scalars:
if `ε ∏ᵢ (aᵢ X + bᵢ Y) = ε' ∏ⱼ (a'ⱼ X + b'ⱼ Y)` with `ε, ε' ≠ 0` and all linear forms nonzero, the
two families of linear forms agree up to a permutation and nonzero scalars. -/
theorem rel_associated_of_C_mul_prod_eq {ε ε' : K} (hε : ε ≠ 0) (hε' : ε' ≠ 0)
    {s t : Multiset (K × K)} (hs : ∀ ℓ ∈ s, ℓ ≠ (0, 0)) (ht : ∀ ℓ ∈ t, ℓ ≠ (0, 0))
    (h : (C ε * (s.map fun ℓ ↦ C ℓ.1 * X 0 + C ℓ.2 * X 1).prod : MvPolynomial (Fin 2) K) =
      C ε' * (t.map fun ℓ ↦ C ℓ.1 * X 0 + C ℓ.2 * X 1).prod) :
    Multiset.Rel Associated (s.map fun ℓ ↦ (C ℓ.1 * X 0 + C ℓ.2 * X 1 : MvPolynomial (Fin 2) K))
      (t.map fun ℓ ↦ C ℓ.1 * X 0 + C ℓ.2 * X 1) := by
  have hirr {u : Multiset (K × K)} (hu : ∀ ℓ ∈ u, ℓ ≠ (0, 0)) :
      ∀ x ∈ u.map (fun ℓ ↦ (C ℓ.1 * X 0 + C ℓ.2 * X 1 : MvPolynomial (Fin 2) K)),
        Irreducible x := by
    intro x hx
    obtain ⟨ℓ, hℓ, rfl⟩ := Multiset.mem_map.1 hx
    exact irreducible_C_mul_X_add_C_mul_X (hu ℓ hℓ)
  refine UniqueFactorizationMonoid.factors_unique (hirr hs) (hirr ht) ?_
  refine (associated_unit_mul_left _ _ ((Ne.isUnit hε).map C)).symm.trans ?_
  rw [h]
  exact associated_unit_mul_left _ _ ((Ne.isUnit hε').map C)

/-- Over a field, the dehomogenization `F(X, 1)` of a product `F = ε ∏ᵢ (aᵢ X + bᵢ Y)` of linear
forms splits. -/
theorem splits_aeval_of_eq_C_mul_prod {ε : K} {s : Multiset (K × K)}
    (hF : F = C ε * (s.map fun ℓ ↦ C ℓ.1 * X 0 + C ℓ.2 * X 1).prod) :
    (MvPolynomial.aeval ![Polynomial.X, 1] F : Polynomial K).Splits := by
  subst hF
  simp only [map_mul, map_multiset_prod, Multiset.map_map, Function.comp_def, map_add, aeval_C,
    aeval_X]
  refine (Polynomial.Splits.multisetProd fun f hf ↦ ?_).C_mul _
  obtain ⟨ℓ, -, rfl⟩ := Multiset.mem_map.1 hf
  refine Polynomial.Splits.of_natDegree_le_one ?_
  simp only [Polynomial.algebraMap_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, mul_one]
  compute_degree!

/-- Over a field, a nonzero binary form `F` of degree `d` is `ε ∏ᵢ (aᵢ X + bᵢ Y)` for some `ε ≠ 0`
and `d` linear forms with `(aᵢ, bᵢ) ≠ (0, 0)` if and only if its dehomogenization `F(X, 1)`
splits. -/
theorem IsHomogeneous.splits_iff_exists_eq_C_mul_prod (hF : F.IsHomogeneous d) (hF₀ : F ≠ 0) :
    (MvPolynomial.aeval ![Polynomial.X, 1] F : Polynomial K).Splits ↔
      ∃ ε : K, ε ≠ 0 ∧ ∃ s : Multiset (K × K), Multiset.card s = d ∧ (∀ ℓ ∈ s, ℓ ≠ (0, 0)) ∧
        F = C ε * (s.map fun ℓ ↦ C ℓ.1 * X 0 + C ℓ.2 * X 1).prod :=
  ⟨hF.exists_eq_C_mul_prod_of_splits hF₀, fun ⟨_, _, _, _, _, h⟩ ↦ splits_aeval_of_eq_C_mul_prod h⟩

/-- **Binary forms split into linear forms.** Over an algebraically closed field `K`, a nonzero
binary form `F` of degree `d` is `F = ε ∏ᵢ (aᵢ X + bᵢ Y)` for some `ε ≠ 0` and `d` linear forms
with `(aᵢ, bᵢ) ≠ (0, 0)`. Explicitly (`IsHomogeneous.eq_C_mul_X_pow_mul_prod`),
`F = ε Y ^ r ∏ⱼ (X - λⱼ Y)` with `r = d - deg F(X, 1)`, where the `λⱼ` are the roots of `F(X, 1)`
with multiplicity. The factors are unique up to order and nonzero scalars
(`rel_associated_of_C_mul_prod_eq`).

Milestone: *Binary forms over an algebraically closed field split into linear forms*. -/
theorem IsHomogeneous.exists_eq_C_mul_prod [IsAlgClosed K] (hF : F.IsHomogeneous d)
    (hF₀ : F ≠ 0) :
    ∃ ε : K, ε ≠ 0 ∧ ∃ s : Multiset (K × K), Multiset.card s = d ∧ (∀ ℓ ∈ s, ℓ ≠ (0, 0)) ∧
      F = C ε * (s.map fun ℓ ↦ C ℓ.1 * X 0 + C ℓ.2 * X 1).prod :=
  hF.exists_eq_C_mul_prod_of_splits hF₀ (IsAlgClosed.splits _)

end Field

end MvPolynomial

end
