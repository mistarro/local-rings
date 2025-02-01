import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Subsemiring.Defs

import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Subring

/-!
# Supplementary results for rings.
-/

/- Accepted in Mathlib4 in `Mathlib.RingTheory.Spectrum.Maximal.Defs`. -/
/-- The maximal spectrum of a ring. -/
def MaximalSpectrum (R : Type*) [Semiring R] : Set (Ideal R) :=
  {I | I.IsMaximal}

/- Accepted in Mathlib4 in `Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic`. -/
/-- Maximal spectrum of a local ring is a singleton. -/
instance (R : Type*) [CommSemiring R] [IsLocalRing R] : Unique (MaximalSpectrum R) :=
  { default := ⟨IsLocalRing.maximalIdeal R, IsLocalRing.maximalIdeal.isMaximal R⟩
    uniq := fun I ↦ Subtype.coe_injective <| IsLocalRing.eq_maximalIdeal I.2 }

/- Accepted in Mathlib4 in `Mathlib.Algebra.Ring.Equiv`. -/
/-- Product of a singleton family of semirings is isomorphic to the only member of this family. -/
def RingEquiv.piUnique {ι : Type*} (R : ι → Type*) [Unique ι] [∀ i, Semiring (R i)] :
    (∀ i, R i) ≃+* R default :=
  { Equiv.piUnique R with
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl }

section

open nonZeroDivisors

/- Accepted in Mathlib4 in `Mathlib.Algebra.GroupWithZero.NonZeroDivisors`. -/
/-- If an element maps to a non-zero-divisor via injective homomorphism,
    then it is non-zero-divisor. -/
theorem mem_nonZeroDivisor_of_injective {M N F : Type*} [MonoidWithZero M] [MonoidWithZero N]
    [FunLike F M N] [MonoidWithZeroHomClass F M N] {f : F} (hf : Function.Injective f)
    {a : M} (ha : f a ∈ N⁰) : a ∈ M⁰ :=
  fun x hx ↦ hf <| map_zero f ▸ ha (f x) (map_mul f x a ▸ map_zero f ▸ congrArg f hx)

/- Accepted in Mathlib4 in `Mathlib.Algebra.GroupWithZero.NonZeroDivisors`. -/
theorem comap_nonZeroDivisor_le_of_injective {M N F : Type*} [MonoidWithZero M] [MonoidWithZero N]
    [FunLike F M N] [MonoidWithZeroHomClass F M N] {f : F} (hf : Function.Injective f) :
    N⁰.comap f ≤ M⁰ :=
  fun _ ha ↦ mem_nonZeroDivisor_of_injective hf (Submonoid.mem_comap.mp ha)

end

namespace Algebra

/- Accepted in Mathlib4 in `Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic`. -/
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] in
theorem finite_adjoin_simple_of_isIntegral {x : A} (hi : IsIntegral R x) :
    Module.Finite R (adjoin R {x}) :=
  Module.Finite.iff_fg.mpr hi.fg_adjoin_singleton

end Algebra

namespace IsArtinianRing

variable {R A : Type*}
variable [CommRing R] [IsArtinianRing R] [CommRing A] [Algebra R A]

/- Accepted in Mathlib4 in `Mathlib.RingTheory.Artinian.Ring`. -/
/-- Commutative artinian reduced local ring is a field. -/
theorem isField_of_isReduced_of_isLocalRing [IsReduced R] [IsLocalRing R] : IsField R :=
  let m := IsLocalRing.maximalIdeal R
  let e : R ≃+* _ := (IsArtinianRing.equivPi R).trans <|
    RingEquiv.piUnique fun I : MaximalSpectrum R ↦ R ⧸ I.1
  MulEquiv.isField _ (Ideal.Quotient.field m).toIsField e.toMulEquiv

open nonZeroDivisors

/- Accepted in Mathlib4 in `Mathlib.RingTheory.Artinian.Ring`. -/
/-- If an element of an artinian ring is not a zero divisor then it is a unit. -/
theorem isUnit_of_mem_nonZeroDivisors {a : R} (ha : a ∈ R⁰) : IsUnit a :=
  IsUnit.isUnit_iff_mulLeft_bijective.mpr <|
    IsArtinian.bijective_of_injective_endomorphism (LinearMap.mulLeft R a)
      fun _ _ ↦ (mul_cancel_left_mem_nonZeroDivisors ha).mp

/- Accepted in Mathlib4 in `Mathlib.RingTheory.Artinian.Algebra`. -/
/-- In an `R`-algebra over an artinian ring `R`, if an element is integral and
is not a zero divisor, then it is a unit. -/
theorem isUnit_of_isIntegral_of_nonZeroDivisor {a : A} (hi : IsIntegral R a)
    (ha : a ∈ A⁰) : IsUnit a :=
  let B := Algebra.adjoin R {a}
  let b : B := ⟨a, Algebra.self_mem_adjoin_singleton R a⟩
  haveI : Module.Finite R B := Algebra.finite_adjoin_simple_of_isIntegral hi
  haveI : IsArtinianRing B := isArtinian_of_tower R inferInstance
  have hinj : Function.Injective (B.subtype) := Subtype.val_injective
  have hb : b ∈ B⁰ := comap_nonZeroDivisor_le_of_injective hinj ha
  (isUnit_of_mem_nonZeroDivisors hb).map B.subtype

end IsArtinianRing

section Algebra

open nonZeroDivisors

/- Accepted in Mathlib4 in `Mathlib.RingTheory.LocalRing.Subring`. -/
/-- If a (semi)ring `R` in which every element is either invertible or a zero divisor
embeds in a local (semi)ring `S`, then `R` is local. -/
lemma IsLocalRing.of_injective {R S} [Semiring R] [Semiring S] [IsLocalRing S]
    {f : R →+* S} (hf : Function.Injective f) (h : ∀ a, a ∈ R⁰ → IsUnit a) : IsLocalRing R := by
  haveI : Nontrivial R := f.domain_nontrivial
  refine IsLocalRing.of_is_unit_or_is_unit_of_add_one fun {a b} hab ↦ ?_
  apply Or.imp (h _) (h _)
  apply Or.imp (mem_nonZeroDivisor_of_injective hf) (mem_nonZeroDivisor_of_injective hf)
  apply Or.imp IsUnit.mem_nonZeroDivisors IsUnit.mem_nonZeroDivisors
  exact IsLocalRing.isUnit_or_isUnit_of_add_one <| map_add f .. ▸ map_one f ▸ congrArg f hab

/- Accepted in Mathlib4 in `Mathlib.RingTheory.LocalRing.Subring`. -/
theorem Subsemiring.inclusion_injective {S} [Semiring S] {R R' : Subsemiring S} (inc : R ≤ R') :
    Function.Injective (inclusion inc) := Set.inclusion_injective inc

/- Accepted in Mathlib4 in `Mathlib.RingTheory.LocalRing.Subring`. -/
/-- If in a sub(semi)ring `R` of a local (semi)ring `R'` every element is either
invertible or a zero divisor, then `R` is local.
This version is for `R` and `R'` that are both sub(semi)rings of a (semi)ring `S`. -/
lemma IsLocalRing.of_subring' {S} [Semiring S] {R R' : Subsemiring S} [IsLocalRing R'] (inc : R ≤ R')
    (h : ∀ a, a ∈ R⁰ → IsUnit a) : IsLocalRing R :=
  IsLocalRing.of_injective (Subsemiring.inclusion_injective inc) h

end Algebra

namespace AlgHom

variable {R A B C₁ C₂ : Type*}
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable [Semiring C₁] [Semiring C₂] [Algebra R C₁] [Algebra R C₂]

/- Accepted in Mathlib4 in `Mathlib.Algebra.Algebra.Prod`. -/
lemma prod_comp (f : A →ₐ[R] B) (g₁ : B →ₐ[R] C₁) (g₂ : B →ₐ[R] C₂) :
    (g₁.prod g₂).comp f = (g₁.comp f).prod (g₂.comp f) := rfl

end AlgHom

namespace Polynomial

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/- Accepted in Mathlib4 in `Mathlib.Algebra.Polynomial.AlgebraMap`. -/
/-- Polynomial evaluation on a pair is a product of the evaluations on the components. -/
theorem aeval_prod (a : A × B) : aeval (R := R) a = (aeval a.1).prod (aeval a.2) :=
  aeval_algHom (.fst R A B) a ▸ aeval_algHom (.snd R A B) a ▸
    (aeval a).prod_comp (.fst R A B) (.snd R A B)

/- Accepted in Mathlib4 in `Mathlib.Algebra.Polynomial.AlgebraMap`. -/
/-- Polynomial evaluation on a pair is a pair of evaluations. -/
theorem aeval_prod_apply (a : A × B) (p : R[X]) : p.aeval a = (p.aeval a.1, p.aeval a.2) := by
  simp [aeval_prod]

end Polynomial

section IsIntegral

variable {R A B : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/- Accepted in Mathlib4 in `Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic`. -/
/-- A pair of elements is integral if each component is integral. -/
theorem IsIntegral.pair {a : A × B} (ha₁ : IsIntegral R a.1) (ha₂ : IsIntegral R a.2) :
    IsIntegral R a := by
  obtain ⟨μ₁, ⟨hμ₁Monic, hμ₁Eval⟩⟩ := ha₁
  obtain ⟨μ₂, ⟨hμ₂Monic, hμ₂Eval⟩⟩ := ha₂
  refine ⟨μ₁ * μ₂, ⟨hμ₁Monic.mul hμ₂Monic, ?_⟩⟩
  rw [← Polynomial.aeval_def] at *
  rw [Polynomial.aeval_prod_apply,
    Polynomial.aeval_mul, hμ₁Eval, zero_mul,
    Polynomial.aeval_mul, hμ₂Eval, mul_zero]
  rfl

/- Accepted in Mathlib4 in `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`. -/
/-- Product of two integral algebras is an integral algebra. -/
instance Algebra.IsIntegral.prod [Algebra.IsIntegral R A] [Algebra.IsIntegral R B] :
    Algebra.IsIntegral R (A × B) :=
  Algebra.isIntegral_def.mpr fun a ↦
    (Algebra.isIntegral_def.mp ‹_› a.1).pair (Algebra.isIntegral_def.mp ‹_› a.2)

/- Accepted in Mathlib4 in `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`. -/
/-- Image of an integral algebra is an integral algebra. -/
theorem Algebra.IsIntegral.of_surjective [Algebra.IsIntegral R A]
    (f : A →ₐ[R] B) (hf : Function.Surjective f) : Algebra.IsIntegral R B :=
  Algebra.isIntegral_def.mpr fun b ↦ let ⟨a, ha⟩ := hf b
    ha ▸ (Algebra.isIntegral_def.mp ‹_› a).map f

end IsIntegral
