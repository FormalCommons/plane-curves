/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import PlaneCurves.RingTheory.MvPolynomial.Homogenize.Basic
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import TauCeti.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Homogenization to the total degree and factorization of forms

Fulton's homogenization `f*` of a polynomial `f` in `n` variables is
`MvPolynomial.homogenize i f.totalDegree f`, homogenization in the variable `i` to the total degree
of `f`, and his dehomogenization `F_*` of a form `F` in `n + 1` variables is Tau Ceti's
`TauCeti.dehomogenize i F`. This file proves Proposition 5 of §2.6 of Fulton's book for them, over
a commutative semiring without zero divisors, and its corollary, over a commutative ring without
zero divisors: up to powers of `X i`, factorizations of a form correspond to factorizations of its
dehomogenization.

## Main results

* `MvPolynomial.homogenize_totalDegree_mul`: `(f * g)* = f* * g*`.
* `MvPolynomial.dehomogenize_homogenize_totalDegree`: `(f*)_* = f`.
* `MvPolynomial.X_pow_mul_homogenize_dehomogenize`: a form `F` of degree `d` is
  `X i ^ (d - deg F_*) * (F_*)*`.
* `MvPolynomial.X_pow_mul_homogenize_dehomogenize_of_dvd`: if `X i ^ r` is the largest power of
  `X i` dividing a nonzero form `F`, then `X i ^ r * (F_*)* = F`.
* `MvPolynomial.totalDegree_dehomogenize_of_not_X_dvd`: a form of degree `d` not divisible by
  `X i` has a dehomogenization of total degree `d`.
* `MvPolynomial.X_pow_mul_homogenize_add`: `X i ^ t * (f + g)* = X i ^ r * f* + X i ^ s * g*`
  for `s = deg f`, `r = deg g` and `t = r + s - deg (f + g)`.
* `MvPolynomial.irreducible_dehomogenize_iff`: a form not divisible by `X i` is irreducible if and
  only if its dehomogenization is; `MvPolynomial.irreducible_homogenize_totalDegree`: `f*` is
  irreducible for irreducible `f`.
* `MvPolynomial.homogenize_totalDegree_dvd_of_dvd_dehomogenize`: a factor `f` of `F_*` gives the
  factor `f*` of `F`.
* `MvPolynomial.isRelPrime_dehomogenize`: the dehomogenizations of relatively prime forms are
  relatively prime.
* `MvPolynomial.associated_dehomogenize_iff`: forms of the same degree are associated iff their
  dehomogenizations are.
* `MvPolynomial.homogenize_totalDegree_spec`: all of these together, with Tau Ceti's
  `MvPolynomial.IsHomogeneous.of_mul_left`, that the factors of a form are forms.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §2.6, Proposition 5 and its corollary
-/

public section

namespace MvPolynomial

open TauCeti

section CommSemiring

variable {R : Type*} [CommSemiring R] {n : ℕ} {i : Fin (n + 1)}

/-- Fulton's `(f*)_* = f`: dehomogenizing the homogenization of `f` to its total degree recovers
`f`. -/
@[simp]
theorem dehomogenize_homogenize_totalDegree (f : MvPolynomial (Fin n) R) :
    dehomogenize i (homogenize i f.totalDegree f) = f :=
  dehomogenize_homogenize le_rfl

/-- A form `F` of degree `d` is `X i ^ (d - deg F_*)` times the homogenization of its
dehomogenization `F_*` to the total degree of `F_*`. -/
theorem X_pow_mul_homogenize_dehomogenize {F : MvPolynomial (Fin (n + 1)) R} {d : ℕ}
    (hF : F.IsHomogeneous d) :
    X i ^ (d - (dehomogenize i F).totalDegree) *
      homogenize i (dehomogenize i F).totalDegree (dehomogenize i F) = F := by
  rw [← homogenize_of_le le_rfl
    ((totalDegree_dehomogenize_le i F).trans hF.totalDegree_le), homogenize_dehomogenize hF]

/-- Fulton's `X i ^ t * (f + g)* = X i ^ r * f* + X i ^ s * g*`, for `s = deg f`, `r = deg g` and
`t = r + s - deg (f + g)`, where `f*` is the homogenization of `f` to its total degree. -/
theorem X_pow_mul_homogenize_add (f g : MvPolynomial (Fin n) R) :
    X i ^ (g.totalDegree + f.totalDegree - (f + g).totalDegree) *
        homogenize i (f + g).totalDegree (f + g) =
      X i ^ g.totalDegree * homogenize i f.totalDegree f +
        X i ^ f.totalDegree * homogenize i g.totalDegree g := by
  have hfg : (f + g).totalDegree ≤ g.totalDegree + f.totalDegree :=
    (totalDegree_add f g).trans (max_le (Nat.le_add_left _ _) (Nat.le_add_right _ _))
  rw [← homogenize_of_le le_rfl hfg, map_add, homogenize_of_le le_rfl (Nat.le_add_left _ _),
    homogenize_of_le le_rfl (Nat.le_add_right _ _)]
  simp

variable [NoZeroDivisors R]

/-- Fulton's `(f * g)* = f* * g*`: homogenization to the total degree is multiplicative over a
semiring without zero divisors. -/
theorem homogenize_totalDegree_mul (f g : MvPolynomial (Fin n) R) :
    homogenize i (f * g).totalDegree (f * g) =
      homogenize i f.totalDegree f * homogenize i g.totalDegree g := by
  obtain rfl | hf := eq_or_ne f 0
  · simp
  obtain rfl | hg := eq_or_ne g 0
  · simp
  rw [totalDegree_mul_of_isDomain hf hg, homogenize_mul le_rfl le_rfl]

/-- Over a semiring without zero divisors, `X i` does not divide the homogenization `f*` of a
nonzero polynomial `f` to its total degree. -/
theorem not_X_dvd_homogenize_totalDegree {f : MvPolynomial (Fin n) R} (hf : f ≠ 0) :
    ¬ X i ∣ homogenize i f.totalDegree f := by
  rintro ⟨G, hG⟩
  have hG0 : G ≠ 0 := by
    rintro rfl
    exact hf ((homogenize_eq_zero_iff le_rfl).mp (by simpa using hG))
  have : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact (hf (Subsingleton.elim _ _)).elim
    · exact hR
  have hdeg := (isHomogeneous_homogenize i f.totalDegree f).totalDegree
    (by rwa [Ne, homogenize_eq_zero_iff le_rfl])
  rw [hG, totalDegree_mul_of_isDomain (X_ne_zero i) hG0, totalDegree_X] at hdeg
  have hfG : f = dehomogenize i G := by
    simpa using congrArg (dehomogenize i) hG
  have := hfG ▸ totalDegree_dehomogenize_le i G
  omega

/-- Fulton's `X i ^ r * (F_*)* = F`: if `X i ^ r` is the largest power of `X i` dividing a nonzero
form `F`, then `F` is `X i ^ r` times the homogenization of its dehomogenization `F_*` to the
total degree of `F_*`. -/
theorem X_pow_mul_homogenize_dehomogenize_of_dvd {F : MvPolynomial (Fin (n + 1)) R} {d r : ℕ}
    (hF : F.IsHomogeneous d) (hF0 : F ≠ 0) (hr : X i ^ r ∣ F) (hr' : ¬ X i ^ (r + 1) ∣ F) :
    X i ^ r * homogenize i (dehomogenize i F).totalDegree (dehomogenize i F) = F := by
  set G := homogenize i (dehomogenize i F).totalDegree (dehomogenize i F)
  have hFG := X_pow_mul_homogenize_dehomogenize (i := i) hF
  have h0 : dehomogenize i F ≠ 0 := dehomogenize_ne_zero_of_isHomogeneous i hF hF0
  have hG : ¬ X i ∣ G := not_X_dvd_homogenize_totalDegree h0
  set e := d - (dehomogenize i F).totalDegree
  suffices r = e by rw [this, hFG]
  refine le_antisymm (not_lt.mp fun h ↦ hG ?_) (not_lt.mp fun h ↦ hr' ?_)
  · rw [← hFG] at hr
    obtain ⟨H, hH⟩ := (pow_dvd_pow (X i) h).trans hr
    rw [pow_succ] at hH
    exact ⟨H, (isRegular_X_pow (n := i) e).left (by simpa [mul_assoc] using hH)⟩
  · exact (pow_dvd_pow (X i) h).trans (hFG ▸ dvd_mul_right _ _)

/-- A form not divisible by `X i` is the homogenization of its dehomogenization `F_*` to the total
degree of `F_*`. -/
theorem homogenize_dehomogenize_of_not_X_dvd {F : MvPolynomial (Fin (n + 1)) R} {d : ℕ}
    (hF : F.IsHomogeneous d) (hX : ¬ X i ∣ F) :
    homogenize i (dehomogenize i F).totalDegree (dehomogenize i F) = F := by
  obtain rfl | hF0 := eq_or_ne F 0
  · simp
  simpa using X_pow_mul_homogenize_dehomogenize_of_dvd hF hF0 (r := 0) (by simp) (by simpa)

/-- The dehomogenization `F_*` of a form `F` of degree `d` not divisible by `X i` has total degree
`d`. -/
theorem totalDegree_dehomogenize_of_not_X_dvd {F : MvPolynomial (Fin (n + 1)) R} {d : ℕ}
    (hF : F.IsHomogeneous d) (hX : ¬ X i ∣ F) : (dehomogenize i F).totalDegree = d := by
  have h := isHomogeneous_homogenize (i := i) (N := (dehomogenize i F).totalDegree)
    (dehomogenize i F)
  rw [homogenize_dehomogenize_of_not_X_dvd hF hX] at h
  exact h.inj_right hF fun h0 ↦ hX (h0 ▸ dvd_zero _)

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {n : ℕ} {i : Fin (n + 1)}

/-- Fulton's corollary to Proposition 5 of §2.6: over a ring without zero divisors, a form
not divisible by `X i` is irreducible if and only if its dehomogenization is. -/
theorem irreducible_dehomogenize_iff {F : MvPolynomial (Fin (n + 1)) R} {d : ℕ}
    (hF : F.IsHomogeneous d) (hX : ¬ X i ∣ F) :
    Irreducible (dehomogenize i F) ↔ Irreducible F := by
  have hFF := homogenize_dehomogenize_of_not_X_dvd hF hX
  constructor
  · intro h
    refine ⟨fun hu ↦ h.not_isUnit (hu.map _), fun G H hGH ↦ ?_⟩
    have hF0 : F ≠ 0 := by rintro rfl; simp at h
    have hG0 : G ≠ 0 := by rintro rfl; simp [hF0] at hGH
    have hH0 : H ≠ 0 := by rintro rfl; simp [hF0] at hGH
    -- The factors of a form are forms, so a factor whose dehomogenization is a unit is a unit.
    have key {G H : MvPolynomial (Fin (n + 1)) R} (hGH : F = G * H) (hH0 : H ≠ 0)
        (hu : IsUnit (dehomogenize i G)) : IsUnit G := by
      have h1 := X_pow_mul_homogenize_dehomogenize (i := i) ((hGH ▸ hF).of_mul_left hH0)
      obtain ⟨c, hc, hcG⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
      rw [hcG, totalDegree_C, Nat.sub_zero, homogenize_C, pow_zero, mul_one] at h1
      rcases Nat.eq_zero_or_pos G.totalDegree with h0 | h0
      · rw [← h1, h0, pow_zero, one_mul]
        exact hc.map C
      · exact (hX (hGH ▸ h1 ▸ ((dvd_pow_self _ h0.ne').mul_right _).mul_right H)).elim
    rcases h.isUnit_or_isUnit (by rw [hGH, map_mul]) with hu | hu
    · exact .inl (key hGH hH0 hu)
    · exact .inr (key (hGH.trans (mul_comm G H)) hG0 hu)
  · intro h
    refine ⟨fun hu ↦ h.not_isUnit ?_, fun g k hgk ↦ ?_⟩
    · obtain ⟨c, hc, hcF⟩ := isUnit_iff_eq_C_of_isReduced.mp hu
      rw [← hFF, hcF, totalDegree_C, homogenize_C, pow_zero, mul_one]
      exact hc.map C
    · rw [← hFF, hgk, homogenize_totalDegree_mul] at h
      exact (h.isUnit_or_isUnit rfl).imp (fun hu ↦ by simpa using hu.map (dehomogenize i))
        (fun hu ↦ by simpa using hu.map (dehomogenize i))

/-- Over a ring without zero divisors, the homogenization `f* = homogenize i f.totalDegree f` of
an irreducible polynomial is an irreducible form. -/
theorem irreducible_homogenize_totalDegree {f : MvPolynomial (Fin n) R} (hf : Irreducible f) :
    Irreducible (homogenize i f.totalDegree f) :=
  (irreducible_dehomogenize_iff (isHomogeneous_homogenize i _ f)
    (not_X_dvd_homogenize_totalDegree hf.ne_zero)).1
    (by rwa [dehomogenize_homogenize_totalDegree])

/-- Over a ring without zero divisors, a factor `f` of the dehomogenization `F_*` of a form `F`
gives the factor `f* = homogenize i f.totalDegree f` of `F`. -/
theorem homogenize_totalDegree_dvd_of_dvd_dehomogenize {F : MvPolynomial (Fin (n + 1)) R} {d : ℕ}
    (hF : F.IsHomogeneous d) {f : MvPolynomial (Fin n) R} (hf : f ∣ dehomogenize i F) :
    homogenize i f.totalDegree f ∣ F := by
  obtain ⟨g, hg⟩ := hf
  rw [← X_pow_mul_homogenize_dehomogenize (i := i) hF, hg, homogenize_totalDegree_mul]
  exact (dvd_mul_right _ _).mul_left _

/-- Over a ring without zero divisors, the dehomogenizations of relatively prime forms are
relatively prime: a common factor `h` of `F_*` and `G_*` gives the common factor `h*` of `F`
and `G`. -/
theorem isRelPrime_dehomogenize {F G : MvPolynomial (Fin (n + 1)) R} {m d : ℕ}
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous d) (h : IsRelPrime F G) :
    IsRelPrime (dehomogenize i F) (dehomogenize i G) := by
  intro f hfF hfG
  simpa using (h (homogenize_totalDegree_dvd_of_dvd_dehomogenize hF hfF)
    (homogenize_totalDegree_dvd_of_dvd_dehomogenize hG hfG)).map (dehomogenize i)

/-- Over a ring without zero divisors, forms of the same degree are associated exactly when their
dehomogenizations are: the units of the polynomial ring are the constant units. -/
theorem associated_dehomogenize_iff {F G : MvPolynomial (Fin (n + 1)) R} {m : ℕ}
    (hF : F.IsHomogeneous m) (hG : G.IsHomogeneous m) :
    Associated (dehomogenize i F) (dehomogenize i G) ↔ Associated F G := by
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun h ↦ h.map (dehomogenize i)⟩
  obtain ⟨c, hc, hcu⟩ := (isUnit_iff_eq_C_of_isReduced (R := R)).1 u.isUnit
  refine ⟨(hc.map C).unit, dehomogenize_injOn i m
    (by simpa using hF.mul (isHomogeneous_C _ c)) hG ?_⟩
  simpa [hcu] using hu

/-- Proposition 5 of §2.6 of Fulton's book and its corollary, for Fulton's homogenization
`f* = homogenize i f.totalDegree f` and dehomogenization `F_* = dehomogenize i F` in any variable
`i`, over a ring without zero divisors:
1. `(F * G)_* = F_* * G_*` and `(f * g)* = f* * g*`;
2. if `X i ^ r` is the largest power of `X i` dividing a nonzero form `F`, then
   `X i ^ r * (F_*)* = F`; and `(f*)_* = f`;
3. `(F + G)_* = F_* + G_*`; and `X i ^ t * (f + g)* = X i ^ r * f* + X i ^ s * g*` for
   `s = deg f`, `r = deg g` and `t = r + s - deg (f + g)`;
4. a form not divisible by `X i` is irreducible if and only if its dehomogenization is, and the
   factors of a form are forms.

Milestone: *Homogenization and dehomogenization of polynomials*. -/
theorem homogenize_totalDegree_spec :
    (∀ F G : MvPolynomial (Fin (n + 1)) R,
        dehomogenize i (F * G) = dehomogenize i F * dehomogenize i G) ∧
      (∀ f g : MvPolynomial (Fin n) R, homogenize i (f * g).totalDegree (f * g) =
        homogenize i f.totalDegree f * homogenize i g.totalDegree g) ∧
      (∀ (F : MvPolynomial (Fin (n + 1)) R) (d r : ℕ), F.IsHomogeneous d → F ≠ 0 →
        X i ^ r ∣ F → ¬ X i ^ (r + 1) ∣ F →
          X i ^ r * homogenize i (dehomogenize i F).totalDegree (dehomogenize i F) = F) ∧
      (∀ f : MvPolynomial (Fin n) R, dehomogenize i (homogenize i f.totalDegree f) = f) ∧
      (∀ F G : MvPolynomial (Fin (n + 1)) R,
        dehomogenize i (F + G) = dehomogenize i F + dehomogenize i G) ∧
      (∀ f g : MvPolynomial (Fin n) R,
        X i ^ (g.totalDegree + f.totalDegree - (f + g).totalDegree) *
            homogenize i (f + g).totalDegree (f + g) =
          X i ^ g.totalDegree * homogenize i f.totalDegree f +
            X i ^ f.totalDegree * homogenize i g.totalDegree g) ∧
      (∀ (F : MvPolynomial (Fin (n + 1)) R) (d : ℕ), F.IsHomogeneous d → ¬ X i ∣ F →
        (Irreducible (dehomogenize i F) ↔ Irreducible F)) ∧
      (∀ (F G : MvPolynomial (Fin (n + 1)) R) (d : ℕ), (F * G).IsHomogeneous d → G ≠ 0 →
        F.IsHomogeneous F.totalDegree) :=
  ⟨fun _ _ ↦ map_mul _ _ _, homogenize_totalDegree_mul,
    fun _ _ _ hF hF0 hr hr' ↦ X_pow_mul_homogenize_dehomogenize_of_dvd hF hF0 hr hr',
    dehomogenize_homogenize_totalDegree, fun _ _ ↦ map_add _ _ _, X_pow_mul_homogenize_add,
    fun _ _ hF hX ↦ irreducible_dehomogenize_iff hF hX, fun _ _ _ h hG ↦ h.of_mul_left hG⟩

end CommRing

end MvPolynomial

end
