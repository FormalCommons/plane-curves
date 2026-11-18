/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.BlockHomogenize
public import TauCeti.RingTheory.MvPolynomial.Dehomogenization

/-!
# Homogenization in any variable to a degree

For a polynomial `f` in `n` variables, a coordinate `i : Fin (n + 1)` and a degree `N`, the
homogenization `MvPolynomial.homogenize i N f` is the polynomial in `n + 1` variables obtained by
renaming the variables of `f` along `i.succAbove` and multiplying the homogeneous component of
degree `j ≤ N` by `X i ^ (N - j)`; components of degree more than `N` are discarded. It is
homogeneous of degree `N`, and Tau Ceti's dehomogenization `TauCeti.dehomogenize i` inverts it on
polynomials of total degree at most `N`. Fulton's `f*` is `homogenize i f.totalDegree f`.

## Main definitions

* `MvPolynomial.homogenize i N`: homogenization in the variable `i` to the degree `N`, as a linear
  map.

## Main results

* `MvPolynomial.isHomogeneous_homogenize`: the homogenization is homogeneous of degree `N`.
* `MvPolynomial.dehomogenize_homogenize`, `MvPolynomial.homogenize_dehomogenize`: homogenization
  and dehomogenization are inverse to each other on polynomials of total degree at most `N` and
  forms of degree `N`.
* `MvPolynomial.homogenize_mul`, `MvPolynomial.homogenize_succ`: homogenization is multiplicative,
  and raising the degree multiplies by `X i`.
* `MvPolynomial.rename_blockHomogenize`, `MvPolynomial.homogenize_uniqueAlgEquiv_symm`: comparison
  with Tau Ceti's `MvPolynomial.blockHomogenize` and Mathlib's `Polynomial.homogenize`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §2.6
-/

public section

namespace MvPolynomial

open TauCeti

variable {R : Type*} [CommSemiring R] {n : ℕ}

/-- The homogenization of a polynomial `f` in `n` variables in the variable `i` to the degree
`N`: the polynomial `∑_{j ≤ N} f_j X_i ^ (N - j)` in `n + 1` variables, where `f_j` is the
homogeneous component of degree `j` of `f`, its variables renamed along `i.succAbove`.
It is homogeneous of degree `N`, and for `f.totalDegree ≤ N` setting `X i` to one recovers `f`.
Fulton's `f*` is `homogenize i f.totalDegree f`. -/
noncomputable def homogenize (i : Fin (n + 1)) (N : ℕ) :
    MvPolynomial (Fin n) R →ₗ[R] MvPolynomial (Fin (n + 1)) R :=
  ∑ j ∈ Finset.range (N + 1), LinearMap.mulRight R (X i ^ (N - j)) ∘ₗ
    homogeneousComponent j ∘ₗ (rename i.succAbove).toLinearMap

theorem homogenize_def (i : Fin (n + 1)) (N : ℕ) (f : MvPolynomial (Fin n) R) :
    homogenize i N f = ∑ j ∈ Finset.range (N + 1),
      homogeneousComponent j (rename i.succAbove f) * X i ^ (N - j) := by
  simp [homogenize]

variable (i : Fin (n + 1)) (N : ℕ)

/-- The homogenization is homogeneous of the degree it is taken to. -/
theorem isHomogeneous_homogenize (f : MvPolynomial (Fin n) R) :
    (homogenize i N f).IsHomogeneous N := by
  rw [homogenize_def]
  refine IsHomogeneous.sum _ _ _ fun j hj ↦ ?_
  have := (homogeneousComponent_isHomogeneous j (rename i.succAbove f)).mul
    (isHomogeneous_X_pow i (N - j))
  rwa [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))] at this

/-- The homogenization of a monomial of degree at most `N` multiplies it by a power of `X i`;
monomials of larger degree are discarded. -/
theorem homogenize_monomial (e : Fin n →₀ ℕ) (c : R) :
    homogenize i N (monomial e c) =
      if e.degree ≤ N then monomial (e.mapDomain i.succAbove) c * X i ^ (N - e.degree)
      else 0 := by
  rw [homogenize_def, rename_monomial]
  simp_rw [homogeneousComponent_of_mem
    (isHomogeneous_monomial c (Finsupp.degree_mapDomain i.succAbove e)), ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

@[simp]
theorem homogenize_C (c : R) : homogenize i N (C c : MvPolynomial (Fin n) R) = C c * X i ^ N := by
  simp [← monomial_zero', homogenize_monomial]

@[simp]
theorem homogenize_one : homogenize i N (1 : MvPolynomial (Fin n) R) = X i ^ N := by
  simpa using homogenize_C i N (1 : R)

theorem homogenize_X {N : ℕ} (hN : N ≠ 0) (j : Fin n) :
    homogenize i N (X j : MvPolynomial (Fin n) R) = X (i.succAbove j) * X i ^ (N - 1) := by
  rw [X, homogenize_monomial, ite_eq_left (by simpa [Nat.one_le_iff_ne_zero] using hN)]
  simp [X]

variable {i N}

/-- Setting `X i` to one in the homogenization of a polynomial of total degree at most `N`
recovers the polynomial. -/
@[simp]
theorem dehomogenize_homogenize {f : MvPolynomial (Fin n) R} (hf : f.totalDegree ≤ N) :
    dehomogenize i (homogenize i N f) = f := by
  have hf' : (rename i.succAbove f).totalDegree ≤ N := (totalDegree_rename_le _ _).trans hf
  simp only [homogenize_def, map_sum, map_mul, map_pow, dehomogenize_X, Fin.insertNth_apply_same,
    one_pow, mul_one]
  rw [← map_sum, ← Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hf')),
    sum_homogeneousComponent, dehomogenize_rename_succAbove]
  intro j _ hj
  exact homogeneousComponent_eq_zero _ _ (by simpa [Nat.lt_succ_iff] using hj)

/-- A form of degree `N` is the homogenization to degree `N` of its dehomogenization. -/
theorem eq_homogenize_of_isHomogeneous {F : MvPolynomial (Fin (n + 1)) R}
    {f : MvPolynomial (Fin n) R}
    (hF : F.IsHomogeneous N) (hf : f.totalDegree ≤ N) (h : dehomogenize i F = f) :
    F = homogenize i N f :=
  dehomogenize_injOn i N hF (isHomogeneous_homogenize i N f) (by simp [h, hf])

/-- A form of degree `N` is the homogenization to degree `N` of its dehomogenization. -/
@[simp]
theorem homogenize_dehomogenize {F : MvPolynomial (Fin (n + 1)) R} (hF : F.IsHomogeneous N) :
    homogenize i N (dehomogenize i F) = F :=
  (eq_homogenize_of_isHomogeneous hF
    ((totalDegree_dehomogenize_le i F).trans hF.totalDegree_le) rfl).symm

theorem homogenize_eq_zero_iff {f : MvPolynomial (Fin n) R} (hf : f.totalDegree ≤ N) :
    homogenize i N f = 0 ↔ f = 0 :=
  ⟨fun h ↦ by rw [← dehomogenize_homogenize hf, h, map_zero], fun h ↦ by rw [h, map_zero]⟩

/-- Homogenization is multiplicative, the degrees adding up. -/
theorem homogenize_mul {M : ℕ} {f g : MvPolynomial (Fin n) R} (hf : f.totalDegree ≤ M)
    (hg : g.totalDegree ≤ N) :
    homogenize i (M + N) (f * g) = homogenize i M f * homogenize i N g :=
  (eq_homogenize_of_isHomogeneous ((isHomogeneous_homogenize i M f).mul
    (isHomogeneous_homogenize i N g)) ((totalDegree_mul f g).trans (add_le_add hf hg))
    (by simp [dehomogenize_homogenize hf, dehomogenize_homogenize hg])).symm

/-- Homogenizing to a degree `M` larger than the total degree bound `N` multiplies the
homogenization to degree `N` by `X i ^ (M - N)`. -/
theorem homogenize_of_le {M : ℕ} {f : MvPolynomial (Fin n) R} (hf : f.totalDegree ≤ N)
    (hNM : N ≤ M) : homogenize i M f = X i ^ (M - N) * homogenize i N f := by
  refine (eq_homogenize_of_isHomogeneous ?_ (hf.trans hNM) (by simp [dehomogenize_homogenize hf]))
    |>.symm
  simpa [Nat.sub_add_cancel hNM] using (isHomogeneous_X_pow i (M - N)).mul
    (isHomogeneous_homogenize i N f)

/-- Homogenizing to one more than a total degree bound multiplies the homogenization by `X i`. -/
theorem homogenize_succ {f : MvPolynomial (Fin n) R} (hf : f.totalDegree ≤ N) :
    homogenize i (N + 1) f = X i * homogenize i N f := by
  simpa using homogenize_of_le hf N.le_succ

variable (i N)

/-- Block homogenization with a single block, its homogenizing variable sent to `i` and the
affine variables along `i.succAbove`, is homogenization in the variable `i`. -/
theorem rename_blockHomogenize {B : Type*} [Unique B] (b : Fin n → B) (d : B → ℕ)
    (f : MvPolynomial (Fin n) R) :
    rename (Sum.elim (fun _ ↦ i) i.succAbove) (blockHomogenize b d f) =
      homogenize i (d default) f := by
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => rw [blockHomogenize_add, map_add, map_add, hf, hg]
  | monomial e c =>
    have hmap (h : B) : e.mapDomain b h = e.degree := by
      rw [← Finsupp.degree_mapDomain b e, Finsupp.degree_eq_sum, Fintype.sum_unique,
        Unique.eq_default h]
    simp only [blockHomogenize_monomial, homogenize_monomial, hmap, Unique.forall_iff]
    split_ifs with h
    · have hinj : Function.Injective (Sum.elim (fun _ : B ↦ i) i.succAbove) := by
        rintro (x | x) (y | y) hxy
        · simp [Unique.eq_default x, Unique.eq_default y]
        · exact (Fin.succAbove_ne i y hxy.symm).elim
        · exact (Fin.succAbove_ne i x hxy).elim
        · simpa using Fin.succAbove_right_injective hxy
      rw [rename_monomial, X_pow_eq_monomial, monomial_mul_monomial, mul_one]
      refine congrArg (monomial · c) (Finsupp.ext fun x ↦ ?_)
      refine Fin.succAboveCases i ?_ (fun j ↦ ?_) x
      · have h₁ := Finsupp.mapDomain_apply_of_injective hinj (blockHomogenizeExponent b d e)
          (.inl default)
        simp only [Sum.elim_inl] at h₁
        simp [h₁, Finsupp.mapDomain_of_notMem_range _ _ (fun ⟨j, hj⟩ ↦ Fin.succAbove_ne i j hj),
          hmap]
      · have h₁ := Finsupp.mapDomain_apply_of_injective hinj (blockHomogenizeExponent b d e)
          (.inr j)
        simp only [Sum.elim_inr] at h₁
        simp [h₁, Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective,
          Fin.succAbove_ne]
    · rw [map_zero]

/-- For one affine variable, homogenization in the variable `1` is Mathlib's
`Polynomial.homogenize`. -/
theorem homogenize_uniqueAlgEquiv_symm (p : Polynomial R) :
    homogenize 1 N ((uniqueAlgEquiv R (Fin 1)).symm p) = p.homogenize N := by
  rw [← rename_blockHomogenize 1 (fun _ ↦ ()) (fun _ ↦ N),
    ← rename_blockHomogenize_unique (fun _ : Fin 1 ↦ ()) (fun _ ↦ N) p]
  congr 2
  funext x
  rcases x with x | x
  · rfl
  · rw [Subsingleton.elim x 0]
    rfl

end MvPolynomial

end
