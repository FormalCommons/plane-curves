/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.LocalRing.LocalSubring

/-!
# Local subrings of a field

Facts about Mathlib's `LocalSubring` of a field: units of a subring, domination in terms of
inverses, images under field homomorphisms, and the elements of `LocalSubring.ofPrime`.

## Main results

* `Subring.isUnit_mk_iff`: an element of a subring of a field is a unit there iff it is nonzero
  and its inverse lies in the subring.
* `LocalSubring.le_iff_of_field`: domination of local subrings of a field in terms of inverses.
* `LocalSubring.map_mono`, `LocalSubring.map_id`, `LocalSubring.map_map`,
  `LocalSubring.map_symm_map`: images of local
  subrings under field homomorphisms.
* `LocalSubring.mem_ofPrime_iff`: the elements of `LocalSubring.ofPrime A P` are the fractions
  `a / s` with `a, s ∈ A` and `s ∉ P`.
-/

public section

namespace Subring

variable {L : Type*} [Field L]

/-- An element of a subring of a field is a unit there iff it is nonzero and its inverse lies in
the subring. -/
theorem isUnit_mk_iff {S : Subring L} {x : L} (hx : x ∈ S) :
    IsUnit (⟨x, hx⟩ : S) ↔ x ≠ 0 ∧ x⁻¹ ∈ S := by
  refine ⟨fun ⟨u, hu⟩ ↦ ?_, fun ⟨h0, hi⟩ ↦ ?_⟩
  · have h1 : x * ((u⁻¹ : Sˣ) : L) = 1 := by
      have := congrArg Subtype.val u.mul_inv
      rwa [hu] at this
    refine ⟨left_ne_zero_of_mul_eq_one h1, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h1]
    exact (u⁻¹ : Sˣ).1.2
  · exact IsUnit.of_mul_eq_one (⟨x⁻¹, hi⟩ : S) (Subtype.ext (mul_inv_cancel₀ h0))

end Subring

namespace LocalSubring

section Field

variable {L L' : Type*} [Field L] [Field L']

/-- For local subrings `A`, `B` of a field, `B` dominates `A` iff `A ⊆ B` and every element of
`A` whose inverse lies in `B` has its inverse in `A`. -/
theorem le_iff_of_field {A B : LocalSubring L} :
    A ≤ B ↔ A.toSubring ≤ B.toSubring ∧ ∀ x ∈ A.toSubring, x⁻¹ ∈ B.toSubring →
      x⁻¹ ∈ A.toSubring := by
  refine ⟨fun ⟨h, hl⟩ ↦ ⟨h, fun x hx hxB ↦ ?_⟩, fun ⟨h, hl⟩ ↦ ⟨h, ⟨fun ⟨x, hx⟩ hu ↦ ?_⟩⟩⟩
  · rcases eq_or_ne x 0 with rfl | h0
    · simp
    · have : IsUnit (Subring.inclusion h ⟨x, hx⟩) :=
        (Subring.isUnit_mk_iff (h hx)).2 ⟨h0, hxB⟩
      exact ((Subring.isUnit_mk_iff hx).1 (hl.map_nonunit _ this)).2
  · have := (Subring.isUnit_mk_iff (h hx)).1 hu
    exact (Subring.isUnit_mk_iff hx).2 ⟨this.1, hl x hx this.2⟩

/-- The image of local subrings of a field under a field homomorphism preserves domination. -/
theorem map_mono (f : L →+* L') {A B : LocalSubring L} (h : A ≤ B) : A.map f ≤ B.map f := by
  rw [le_iff_of_field] at h ⊢
  refine ⟨fun _ ⟨x, hx, e⟩ ↦ ⟨x, h.1 hx, e⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
  rw [← map_inv₀] at hyx ⊢
  rw [f.injective hyx] at hy
  exact ⟨x⁻¹, h.2 x hx hy, rfl⟩

/-- Mapping a local subring by the identity gives it back. -/
@[simp]
theorem map_id (A : LocalSubring L) : A.map (RingHom.id L) = A :=
  LocalSubring.ext (Subring.map_id _)

/-- Mapping a local subring by two homomorphisms in turn is mapping it by their composite. -/
theorem map_map (f : L →+* L') {L'' : Type*} [Field L''] (g : L' →+* L'') (A : LocalSubring L) :
    (A.map f).map g = A.map (g.comp f) :=
  LocalSubring.ext (Subring.map_map _ _ _)

/-- Mapping a local subring by an isomorphism of algebras and then by its inverse gives it back. -/
theorem map_symm_map {k : Type*} [CommRing k] [Algebra k L] [Algebra k L'] (φ : L ≃ₐ[k] L')
    (A : LocalSubring L) : (A.map (φ : L →+* L')).map (φ.symm : L' →+* L) = A := by
  rw [map_map]
  convert map_id A
  ext x
  simp

/-- The elements of Mathlib's `LocalSubring.ofPrime A P`, the localization of a subring `A` of
a field at a prime `P`, are the fractions `a / s` with `a, s ∈ A` and `s ∉ P`. -/
theorem mem_ofPrime_iff {A : Subring L} {P : Ideal A} [P.IsPrime] {x : L} :
    x ∈ (ofPrime A P).toSubring ↔ ∃ a s : A, s ∉ P ∧ x = a * (s : L)⁻¹ := by
  have key (a s : A) (hs : s ∉ P) : (a : L) = s * (a * (s : L)⁻¹) := by
    have hs : (s : L) ≠ 0 := fun h ↦ hs (by
      rw [show s = 0 from Subtype.ext h]; exact P.zero_mem)
    rw [mul_comm (a : L), mul_inv_cancel_left₀ hs]
  rw [ofPrime, range_toSubring]
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨a, s, hs⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
    refine ⟨a, s, hs, ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    exact key a s hs
  · rintro ⟨a, s, hs, rfl⟩
    refine ⟨IsLocalization.mk' _ a (⟨s, hs⟩ : P.primeCompl), ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    exact key a s hs

end Field

end LocalSubring

end
