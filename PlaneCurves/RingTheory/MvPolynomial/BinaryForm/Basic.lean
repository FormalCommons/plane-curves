/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import TauCeti.Algebra.Polynomial.Homogenize
public import PlaneCurves.RingTheory.MvPolynomial.Irreducible

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
* `MvPolynomial.irreducible_C_mul_X_add_C_mul_X`, `MvPolynomial.rel_associated_of_C_mul_prod_eq`:
  over a field, a nonzero linear binary form `a X + b Y` is irreducible, so the linear factors of
  a binary form are unique up to order and nonzero scalars.
* `MvPolynomial.IsHomogeneous.multiplicity_X_zero_sub_C_mul_X_one`,
  `MvPolynomial.IsHomogeneous.multiplicity_X_one_sub_C_mul_X_zero`: over a domain, the
  multiplicity of `X - a Y` in a nonzero binary form `F` is that of the root `a` of `F(X, 1)`, and
  the multiplicity of `Y - a X` is that of the root `a` of `F(1, Y)`.
* `MvPolynomial.associated_X_one_sub_C_mul_X_zero_iff`: the linear forms `Y - α X` are pairwise
  non-associated.

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

/-- Over a domain, the multiplicity of the linear factor `X - a Y` in a nonzero binary form `F`
is the multiplicity of `a` as a root of its dehomogenization `F(X, 1)`. -/
theorem IsHomogeneous.multiplicity_X_zero_sub_C_mul_X_one (hF : F.IsHomogeneous d)
    (hF₀ : F ≠ 0) (a : R) :
    multiplicity (X 0 - C a * X 1) F =
      (MvPolynomial.aeval ![Polynomial.X, 1] F : Polynomial R).rootMultiplicity a := by
  set g : Polynomial R := MvPolynomial.aeval ![Polynomial.X, 1] F
  have hgd : g.natDegree ≤ d := hF.natDegree_aeval_le fun i ↦ by fin_cases i <;> simp
  have hFg : g.homogenize d = F := Polynomial.homogenize_eq_of_isHomogeneous hF rfl
  have hg : g ≠ 0 := by
    rintro h
    exact hF₀ (by rw [← hFg, h, Polynomial.homogenize_zero])
  -- `g = (X - a) ^ m q` with `q(a) ≠ 0`, so `F = (X - a Y) ^ m Q` with `Q(a, 1) = q(a) ≠ 0`.
  obtain ⟨q, hq, hqa⟩ := g.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hg a
  set m := g.rootMultiplicity a
  have hq₀ : q ≠ 0 := by rintro rfl; exact hg (by rw [hq, mul_zero])
  have hdeg : g.natDegree = m + q.natDegree := by
    rw [hq, Polynomial.natDegree_mul (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a)) hq₀,
      Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have hqd : q.natDegree ≤ d - m := by omega
  have hL : ((Polynomial.X - Polynomial.C a) ^ m).homogenize m = (X 0 - C a * X 1) ^ m := by
    simpa using Polynomial.homogenize_multiset_prod_X_sub_C (Multiset.replicate m a)
  have h1 : ((Polynomial.X - Polynomial.C a) ^ m).natDegree ≤ m := by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have hF' : F = (X 0 - C a * X 1) ^ m * q.homogenize (d - m) := by
    rw [← hL, ← Polynomial.homogenize_mul _ _ h1 hqd, ← hq, Nat.add_sub_cancel' (by omega), hFg]
  have hev : MvPolynomial.aeval ![Polynomial.X, 1] (X 0 - C a * X 1 : MvPolynomial (Fin 2) R) =
      Polynomial.X - Polynomial.C a := by
    simp only [map_sub, map_mul, aeval_X, aeval_C, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, mul_one, Polynomial.algebraMap_eq]
  have hL₀ : (X 0 - C a * X 1 : MvPolynomial (Fin 2) R) ≠ 0 := fun h ↦
    Polynomial.X_sub_C_ne_zero a (by rw [← hev, h, map_zero])
  refine multiplicity_eq_of_dvd_of_not_dvd ⟨_, hF'⟩ fun h ↦ hqa ?_
  rw [hF', pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ hL₀)] at h
  have := map_dvd (MvPolynomial.aeval ![Polynomial.X, (1 : Polynomial R)]) h
  rwa [hev, Polynomial.aeval_homogenize_X_one _ hqd] at this

/-- Over a domain, the multiplicity of the linear factor `Y - a X` in a nonzero binary form `F`
is the multiplicity of `a` as a root of its dehomogenization `F(1, Y)`. -/
theorem IsHomogeneous.multiplicity_X_one_sub_C_mul_X_zero (hF : F.IsHomogeneous d)
    (hF₀ : F ≠ 0) (a : R) :
    multiplicity (X 1 - C a * X 0) F =
      (MvPolynomial.aeval ![1, Polynomial.X] F : Polynomial R).rootMultiplicity a := by
  have h := IsHomogeneous.multiplicity_X_zero_sub_C_mul_X_one
    (hF.rename_isHomogeneous (f := Equiv.swap (0 : Fin 2) 1))
    ((map_ne_zero_iff _ (rename_injective _ (Equiv.injective _))).2 hF₀) a
  have he : rename (Equiv.swap (0 : Fin 2) 1) (X 1 - C a * X 0 : MvPolynomial (Fin 2) R) =
      X 0 - C a * X 1 := by simp
  have hg : MvPolynomial.aeval ![Polynomial.X, 1] (rename (Equiv.swap (0 : Fin 2) 1) F) =
      (MvPolynomial.aeval ![1, Polynomial.X] F : Polynomial R) := by
    rw [aeval_rename]
    congr 1
    ext i : 1
    fin_cases i <;> simp
  rw [← he, hg] at h
  rw [← h]
  exact (multiplicity_map_eq (renameEquiv R (Equiv.swap (0 : Fin 2) 1))).symm
end Domain

section Field

variable {K : Type*} [Field K] {F : MvPolynomial (Fin 2) K} {d : ℕ}

/-- Over a field, a nonzero linear binary form `a X + b Y` is irreducible. -/
theorem irreducible_C_mul_X_add_C_mul_X {a b : K} (h : (a, b) ≠ (0, 0)) :
    Irreducible (C a * X 0 + C b * X 1 : MvPolynomial (Fin 2) K) := by
  have ha : (C a * X 0 + C b * X 1 : MvPolynomial (Fin 2) K).coeff (Finsupp.single 0 1) = a := by
    simp [coeff_X, Finsupp.single_eq_single_iff]
  have hb : (C a * X 0 + C b * X 1 : MvPolynomial (Fin 2) K).coeff (Finsupp.single 1 1) = b := by
    simp [coeff_X, Finsupp.single_eq_single_iff]
  have hne : (C a * X 0 + C b * X 1 : MvPolynomial (Fin 2) K) ≠ 0 := fun h0 ↦
    h (by simp only [h0] at ha hb; simp [← ha, ← hb])
  exact irreducible_of_isHomogeneous_one
    ((isHomogeneous_C_mul_X a 0).add (isHomogeneous_C_mul_X b 1)) hne

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

/-- The linear form `Y - α X` is a form of degree one. -/
theorem isHomogeneous_X_one_sub_C_mul_X_zero (α : K) :
    (X 1 - C α * X 0 : MvPolynomial (Fin 2) K).IsHomogeneous 1 :=
  (isHomogeneous_X K 1).sub (isHomogeneous_C_mul_X α 0)

/-- The linear form `Y - α X` is nonzero. -/
theorem X_one_sub_C_mul_X_zero_ne_zero (α : K) : (X 1 - C α * X 0 : MvPolynomial (Fin 2) K) ≠ 0 :=
  fun h ↦ by simpa using congr(eval ![0, 1] $h)

/-- Distinct `α` give distinct linear forms `Y - α X`. -/
theorem X_one_sub_C_mul_X_zero_injective :
    Function.Injective fun α : K ↦ (X 1 - C α * X 0 : MvPolynomial (Fin 2) K) :=
  fun α β h ↦ by simpa using congr(eval ![1, 0] $h)

/-- The linear forms `Y - α X` and `Y - β X` are associated only when they are equal. -/
theorem associated_X_one_sub_C_mul_X_zero_iff {α β : K} :
    Associated (X 1 - C α * X 0 : MvPolynomial (Fin 2) K) (X 1 - C β * X 0) ↔ α = β := by
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun h ↦ h ▸ Associated.refl _⟩
  obtain ⟨c, -, hc⟩ := isUnit_iff_eq_C_of_isReduced.1 u.isUnit
  rw [hc] at hu
  have h1 : c = 1 := by simpa using congr(eval ![0, 1] $hu)
  subst h1
  exact X_one_sub_C_mul_X_zero_injective (by simpa using hu)

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
