/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Maximal ideals of an integral extension as kernels of points

Let `k` be an algebraically closed field, `A` a local `k`-algebra with a `k`-algebra map
`e : A → k`, and `B` an `A`-algebra integral over `A`. Every maximal ideal `m` of `B` lies over
the maximal ideal of `A`, which is the kernel of `e`; so `B ⧸ m` is integral over `k`, hence equal
to `k`. Thus `m` is the kernel of a `k`-algebra map `B → k`.

## Main results

* `Ideal.IsMaximal.exists_algHom_ker_eq_of_isIntegral`: every maximal ideal of `B` is the kernel
  of a `k`-algebra map `B → k`.
-/

public section

open IsLocalRing

/-- Let `k` be an algebraically closed field, `A` a local `k`-algebra with a `k`-algebra map to
`k`, and `B` integral over `A`. Then every maximal ideal of `B` is the kernel of a `k`-algebra map
`B → k`. -/
theorem Ideal.IsMaximal.exists_algHom_ker_eq_of_isIntegral {k A B : Type*} [Field k]
    [IsAlgClosed k] [CommRing A] [IsLocalRing A] [Algebra k A] [CommRing B] [Algebra A B]
    [Algebra k B] [IsScalarTower k A B] [Algebra.IsIntegral A B] (e : A →ₐ[k] k) {m : Ideal B}
    (hm : m.IsMaximal) : ∃ φ : B →ₐ[k] k, RingHom.ker φ = m := by
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  have hker : RingHom.ker e = maximalIdeal A :=
    eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨algebraMap k A c, by simp⟩)
  have hmA : m.comap (algebraMap A B) = maximalIdeal A :=
    eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
      (algebraMap_isIntegral_iff.2 inferInstance) m)
  have hc : (algebraMap k (B ⧸ m)).comp e.toRingHom = algebraMap A (B ⧸ m) := by
    ext c
    change Ideal.Quotient.mk m (algebraMap k B (e c)) = Ideal.Quotient.mk m (algebraMap A B c)
    rw [Ideal.Quotient.eq, IsScalarTower.algebraMap_apply k A B, ← map_sub, ← Ideal.mem_comap,
      hmA, ← hker, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  have : Algebra.IsIntegral k (B ⧸ m) := by
    refine ⟨fun b ↦ ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := A) b
    refine ⟨p.map e.toRingHom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map, hc,
      ← Polynomial.aeval_def, ← Ideal.Quotient.mkₐ_eq_mk A, Polynomial.aeval_algHom_apply,
      Polynomial.aeval_def, hpb, map_zero]
  let ψ := AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ m))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨ψ.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  ext b
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

end
