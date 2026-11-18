/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Homogeneous localization of a graded domain

For a graded ring `A` with grading `𝒜`, Mathlib's `HomogeneousLocalization 𝒜 P` is the ring of
fractions `f / g` with `f, g` homogeneous of the same degree and `g ∈ P`, and
`HomogeneousLocalization.mapId 𝒜 h` is the map induced by an inclusion `h : P ≤ Q` of
submonoids. This file adds:

* `HomogeneousLocalization.mem_range_mapId_iff`: the image of `mapId 𝒜 h` consists of the
  fractions whose denominator lies in `P`.
* `HomogeneousLocalization.mapId_injective`: `mapId 𝒜 h` is injective when `Q` consists of
  non-zero-divisors. In particular, for a graded domain and a prime `𝔭`, the map from
  `AtPrime 𝒜 𝔭` to `AtPrime 𝒜 ⊥` is injective (`mapId_atPrime_bot_injective`).
* `HomogeneousLocalization.instFieldAtPrimeBot`: for a graded domain, `AtPrime 𝒜 ⊥`, the
  ring of fractions `f / g` of homogeneous elements of equal degree with `g ≠ 0`, is a field.
  The inverse of `f / g` is `g / f` (`HomogeneousLocalization.mk_inv`).
  For the homogeneous coordinate ring of a projective variety it is the function field.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008]
-/

public section

noncomputable section

namespace HomogeneousLocalization

variable {ι A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [AddCommMonoid ι] [DecidableEq ι] (𝒜 : ι → σ) [GradedRing 𝒜]

section mapId

variable {P Q : Submonoid A} (h : P ≤ Q)

/-- An element of the homogeneous localization at `Q` lies in the image of the homogeneous
localization at a smaller submonoid `P` iff it is a fraction `f / g` of homogeneous elements of
the same degree with `g ∈ P`. -/
theorem mem_range_mapId_iff (x : HomogeneousLocalization 𝒜 Q) :
    x ∈ (mapId 𝒜 h).range ↔
      ∃ (i : ι) (f g : 𝒜 i) (hg : (g : A) ∈ P), mk ⟨i, f, g, h hg⟩ = x := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨c, rfl⟩ := mk_surjective y
    exact ⟨c.deg, c.num, c.den, c.den_mem, rfl⟩
  · rintro ⟨i, f, g, hg, rfl⟩
    exact ⟨mk ⟨i, f, g, hg⟩, rfl⟩

/-- The map `mapId 𝒜 h` between homogeneous localizations at submonoids `P ≤ Q` is injective
when `Q` consists of non-zero-divisors. -/
theorem mapId_injective (hQ : Q ≤ nonZeroDivisors A) : Function.Injective (mapId 𝒜 h) := by
  intro x y e
  obtain ⟨x, rfl⟩ := mk_surjective x
  obtain ⟨y, rfl⟩ := mk_surjective y
  rw [ext_iff_val] at e ⊢
  change Localization.mk (x.num : A) ⟨x.den, h x.den_mem⟩ =
    Localization.mk (y.num : A) ⟨y.den, h y.den_mem⟩ at e
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at e
  rw [val_mk, val_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  obtain ⟨c, hc⟩ := e
  exact ⟨1, by simpa using (mul_cancel_left_mem_nonZeroDivisors (hQ c.2)).1 hc⟩

end mapId

section domain

variable [IsDomain A]

/-- For a graded domain, the map from a homogeneous localization at `P` (for instance at
`𝔭.primeCompl` for a prime `𝔭`, where `h` is
`𝔭.primeCompl_le_nonZeroDivisors.trans Ideal.primeCompl_bot.ge`) to the homogeneous
localization at `⊥` is injective. -/
theorem mapId_atPrime_bot_injective {P : Submonoid A} (h : P ≤ (⊥ : Ideal A).primeCompl) :
    Function.Injective (mapId 𝒜 h) :=
  mapId_injective 𝒜 h Ideal.primeCompl_bot.le

example (𝔭 : Ideal A) [𝔭.IsPrime] : Function.Injective
    (mapId 𝒜 (𝔭.primeCompl_le_nonZeroDivisors.trans (Ideal.primeCompl_bot (α := A)).ge)) :=
  mapId_atPrime_bot_injective 𝒜 _

variable {𝒜}

/-- In the homogeneous localization of a graded domain at `⊥`, the fraction `f / g` with
`f ≠ 0` has inverse `g / f`. -/
theorem mk_mul_mk_swap {i : ι} (f g : 𝒜 i) (hf : (f : A) ∈ (⊥ : Ideal A).primeCompl)
    (hg : (g : A) ∈ (⊥ : Ideal A).primeCompl) :
    (mk ⟨i, f, g, hg⟩ : AtPrime 𝒜 ⊥) * mk ⟨i, g, f, hf⟩ = 1 := by
  rw [← mk_mul, ext_iff_val, val_mk, val_one]
  simp only [NumDenSameDeg.num_mul, NumDenSameDeg.den_mul]
  rw [mul_comm (f : A), Localization.mk_self (⟨_, _⟩ : (⊥ : Ideal A).primeCompl)]

variable (𝒜)

/-- For a graded domain, the homogeneous localization at `⊥` is a field. -/
theorem isField_atPrime_bot : IsField (AtPrime 𝒜 ⊥) where
  exists_pair_ne := exists_pair_ne _
  mul_comm := mul_comm
  mul_inv_cancel {x} hx := by
    obtain ⟨⟨i, f, g, hg⟩, rfl⟩ := mk_surjective x
    have hf : (f : A) ∈ (⊥ : Ideal A).primeCompl := fun h0 ↦
      hx (mk_eq_zero_of_num _ (by simpa using h0))
    exact ⟨_, mk_mul_mk_swap f g hf hg⟩

/-- For a graded domain `A`, the homogeneous localization at `⊥`, the ring of fractions `f / g`
of homogeneous elements of the same degree with `g ≠ 0`, is a field. -/
instance instFieldAtPrimeBot : Field (AtPrime 𝒜 ⊥) := (isField_atPrime_bot 𝒜).toField

variable {𝒜}

/-- In the homogeneous localization of a graded domain at `⊥`, the inverse of `f / g` with
`f ≠ 0` is `g / f`. -/
@[simp]
theorem mk_inv {i : ι} (f g : 𝒜 i) (hf : (f : A) ∈ (⊥ : Ideal A).primeCompl)
    (hg : (g : A) ∈ (⊥ : Ideal A).primeCompl) :
    (mk ⟨i, f, g, hg⟩ : AtPrime 𝒜 ⊥)⁻¹ = mk ⟨i, g, f, hf⟩ :=
  inv_eq_of_mul_eq_one_right (mk_mul_mk_swap f g hf hg)

end domain

end HomogeneousLocalization

end
