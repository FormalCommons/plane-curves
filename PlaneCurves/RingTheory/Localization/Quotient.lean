/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Localization at a prime commutes with quotients

Let `A` be a commutative ring, `I ≤ J` ideals of `A` and `p ⊇ I` a prime of `A`. Write `p'` for
the image of `p` in `A ⧸ I`, a prime ideal. Localization at `p` commutes with the quotient by `I`:
`(A ⧸ I)_{p'} ≅ A_p ⧸ I A_p`, and compatibly with `J`,
`A_p ⧸ J A_p ≅ (A ⧸ I)_{p'} ⧸ J' (A ⧸ I)_{p'}`, where `J'` is the image of `J` in `A ⧸ I`.

## Main results

* `Ideal.isPrime_map_quotientMk`: the image of a prime `p ⊇ I` in `A ⧸ I` is prime.
* `Localization.AtPrime.isLocalization_quotient`: `A_p ⧸ I A_p` is a localization of `A ⧸ I`
  at the image of `p`.
* `Localization.AtPrime.quotientAlgEquiv`: `(A ⧸ I)_{p'} ≃ₐ A_p ⧸ I A_p`.
* `Localization.AtPrime.quotientMapAlgEquiv`: `A_p ⧸ J A_p ≃ₐ (A ⧸ I)_{p'} ⧸ J' (A ⧸ I)_{p'}`.

## References

* [W. Fulton, *Algebraic Curves*][Fulton2008], §2.8, Problems 2.42–2.44
-/

public section

open Ideal

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {I J p : Ideal A} [p.IsPrime]

namespace Ideal

/-- The image of a prime `p` containing `I` in `A ⧸ I` is prime. -/
theorem isPrime_map_quotientMk (hIp : I ≤ p) : (p.map (Ideal.Quotient.mk I)).IsPrime :=
  map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)

/-- For a prime `p` containing `I`, the image in `A ⧸ I` of the complement of `p` is the
complement of the image of `p`. -/
theorem algebraMapSubmonoid_primeCompl_quotient (hIp : I ≤ p)
    [(p.map (Ideal.Quotient.mk I)).IsPrime] :
    Algebra.algebraMapSubmonoid (A ⧸ I) p.primeCompl =
      (p.map (Ideal.Quotient.mk I)).primeCompl := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map, mem_primeCompl_iff,
    Quotient.algebraMap_eq]
  rw [mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
  constructor
  · rintro ⟨b, hb, hba⟩ ⟨c, hc, hca⟩
    rw [← hca, Quotient.eq] at hba
    exact hb (by simpa using p.add_mem hc (hIp hba))
  · intro h
    exact ⟨a, fun ha => h ⟨a, ha, rfl⟩, rfl⟩

end Ideal

namespace Localization.AtPrime

variable (I p) in
/-- For a prime `p` containing `I`, the quotient `A_p ⧸ I A_p` is a localization of `A ⧸ I` at
the image of `p`. -/
theorem isLocalization_quotient (hIp : I ≤ p) [(p.map (Ideal.Quotient.mk I)).IsPrime] :
    IsLocalization.AtPrime (Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p)))
      (p.map (Ideal.Quotient.mk I)) := by
  unfold IsLocalization.AtPrime
  rw [← algebraMapSubmonoid_primeCompl_quotient hIp]
  infer_instance

variable (R) in
/-- **Localization commutes with quotients.** For a prime `p` containing `I`, the localization
of `A ⧸ I` at the image of `p` is `A_p ⧸ I A_p`. -/
noncomputable def quotientAlgEquiv (hIp : I ≤ p) [(p.map (Ideal.Quotient.mk I)).IsPrime] :
    Localization.AtPrime (p.map (Ideal.Quotient.mk I)) ≃ₐ[R]
      Localization.AtPrime p ⧸ I.map (algebraMap A (Localization.AtPrime p)) :=
  haveI := isLocalization_quotient I p hIp
  AlgEquiv.ofRingEquiv
    (f := (IsLocalization.algEquiv (p.map (Ideal.Quotient.mk I)).primeCompl _ _).toRingEquiv)
    fun r => by
      rw [IsScalarTower.algebraMap_apply R (A ⧸ I)]
      exact ((IsLocalization.algEquiv _ _ _).commutes _).trans rfl

theorem quotientAlgEquiv_def (hIp : I ≤ p) [(p.map (Ideal.Quotient.mk I)).IsPrime] :
    quotientAlgEquiv R hIp =
      haveI := isLocalization_quotient I p hIp
      AlgEquiv.ofRingEquiv
        (f := (IsLocalization.algEquiv (p.map (Ideal.Quotient.mk I)).primeCompl _ _).toRingEquiv)
        fun r => by
          rw [IsScalarTower.algebraMap_apply R (A ⧸ I)]
          exact ((IsLocalization.algEquiv _ _ _).commutes _).trans rfl :=
  (rfl)

@[simp]
theorem quotientAlgEquiv_algebraMap (hIp : I ≤ p) [(p.map (Ideal.Quotient.mk I)).IsPrime]
    (x : A ⧸ I) :
    quotientAlgEquiv R hIp (algebraMap _ _ x) = algebraMap (A ⧸ I) _ x := by
  have := isLocalization_quotient I p hIp
  rw [quotientAlgEquiv_def, AlgEquiv.ofRingEquiv_apply]
  exact AlgEquiv.commutes _ x

theorem quotientAlgEquiv_algebraMap_mk (hIp : I ≤ p) [(p.map (Ideal.Quotient.mk I)).IsPrime]
    (a : A) :
    quotientAlgEquiv R hIp (algebraMap _ _ (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime p) a) :=
  (quotientAlgEquiv_algebraMap hIp _).trans rfl

theorem quotientAlgEquiv_symm_mk_algebraMap (hIp : I ≤ p)
    [(p.map (Ideal.Quotient.mk I)).IsPrime] (a : A) :
    (quotientAlgEquiv R hIp).symm
        (Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime p) a)) =
      algebraMap _ _ (Ideal.Quotient.mk I a) := by
  rw [AlgEquiv.symm_apply_eq, quotientAlgEquiv_algebraMap_mk]

variable (R) in
/-- The composite `A → A_p ⧸ I A_p ≅ (A ⧸ I)_{p'}` is the natural map. -/
theorem quotientAlgEquiv_symm_comp (hIp : I ≤ p) [(p.map (Ideal.Quotient.mk I)).IsPrime] :
    ((quotientAlgEquiv R hIp).symm.toRingEquiv.toRingHom).comp
        ((Ideal.Quotient.mk _).comp (algebraMap A (Localization.AtPrime p))) =
      (algebraMap (A ⧸ I) _).comp (Ideal.Quotient.mk I) := by
  ext a
  exact quotientAlgEquiv_symm_mk_algebraMap (R := R) hIp a

variable (R) in
/-- The image of an ideal `J` of `A` under `A_p ⧸ I A_p ≅ (A ⧸ I)_{p'}` is the ideal that the
image of `J` in `A ⧸ I` generates. -/
theorem map_quotientAlgEquiv_symm (hIp : I ≤ p) [(p.map (Ideal.Quotient.mk I)).IsPrime]
    (J : Ideal A) :
    ((J.map (algebraMap A (Localization.AtPrime p))).map
        (Ideal.Quotient.mk (I.map (algebraMap A (Localization.AtPrime p))))).map
        (quotientAlgEquiv R hIp).symm =
      (J.map (Ideal.Quotient.mk I)).map (algebraMap (A ⧸ I) _) := by
  have h := congrArg (J.map ·) (quotientAlgEquiv_symm_comp R hIp)
  simp only [← map_map] at h
  exact h

variable (R) in
/-- **Localization commutes with quotients, compatibly with a larger ideal.** For ideals
`I ≤ J` and a prime `p` containing `I`, `A_p ⧸ J A_p` is the quotient of the localization of
`A ⧸ I` at the image of `p` by the image of `J`. -/
noncomputable def quotientMapAlgEquiv (hIJ : I ≤ J) (hIp : I ≤ p)
    [(p.map (Ideal.Quotient.mk I)).IsPrime] :
    (Localization.AtPrime p ⧸ J.map (algebraMap A (Localization.AtPrime p))) ≃ₐ[R]
      Localization.AtPrime (p.map (Ideal.Quotient.mk I)) ⧸
        (J.map (Ideal.Quotient.mk I)).map
          (algebraMap (A ⧸ I) (Localization.AtPrime (p.map (Ideal.Quotient.mk I)))) :=
  (DoubleQuot.quotQuotEquivQuotOfLEₐ R (map_mono hIJ)).symm.trans <|
    quotientEquivAlg _ _ (quotientAlgEquiv R hIp).symm (map_quotientAlgEquiv_symm R hIp J).symm

theorem quotientMapAlgEquiv_def (hIJ : I ≤ J) (hIp : I ≤ p)
    [(p.map (Ideal.Quotient.mk I)).IsPrime] :
    quotientMapAlgEquiv R hIJ hIp =
      (DoubleQuot.quotQuotEquivQuotOfLEₐ R (map_mono hIJ)).symm.trans
        (quotientEquivAlg _ _ (quotientAlgEquiv R hIp).symm
          (map_quotientAlgEquiv_symm R hIp J).symm) :=
  (rfl)

@[simp]
theorem quotientMapAlgEquiv_mk_algebraMap (hIJ : I ≤ J) (hIp : I ≤ p)
    [(p.map (Ideal.Quotient.mk I)).IsPrime] (a : A) :
    quotientMapAlgEquiv R hIJ hIp
        (Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime p) a)) =
      Ideal.Quotient.mk _ (algebraMap _ _ (Ideal.Quotient.mk I a)) := by
  rw [quotientMapAlgEquiv_def, AlgEquiv.trans_apply]
  exact (quotientEquivAlg_mk _ _ _ _).trans
    (congrArg _ (quotientAlgEquiv_symm_mk_algebraMap (R := R) hIp a))

end Localization.AtPrime

end
