import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Ring.Hom.Defs

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

/-- The maximal spectrum of a ring. -/
def SpecMax (R : Type*) [Semiring R] : Set (Ideal R) :=
  {I | I.IsMaximal}

/-- Maximal spectrum of a local ring is a singleton. -/
instance (R : Type*) [CommSemiring R] [IsLocalRing R] : Unique (SpecMax R) :=
  { default := ⟨IsLocalRing.maximalIdeal R, IsLocalRing.maximalIdeal.isMaximal R⟩
    uniq := fun I ↦ Subtype.coe_injective <| IsLocalRing.eq_maximalIdeal I.2 }

/-- Product of a singleton family of semirings is isomorphic to the only member of this family. -/
def RingEquiv.piUnique {ι : Type*} (R : ι → Type*) [Unique ι] [∀ i, Semiring (R i)] :
    (∀ i, R i) ≃+* R default :=
  { Equiv.piUnique R with
    map_add' := fun _ _ => rfl
    map_mul' := fun _ _ => rfl }

/-- If an element maps to a non-zero-divisor via injective homomorphism,
    then it is non-zero-divisor. -/
theorem nonZeroDivisor.map {M N F : Type*} [MonoidWithZero M] [MonoidWithZero N]
    [FunLike F M N] [MonoidWithZeroHomClass F M N] {f : F} (hf : Function.Injective f)
    {a : M} : f a ∈ nonZeroDivisors N → a ∈ nonZeroDivisors M :=
  fun h x hx ↦ hf <| map_zero f ▸ h (f x) (map_mul f x a ▸ map_zero f ▸ congrArg f hx)

section IsArtinian

variable {R : Type*} [CommRing R] [IsArtinianRing R]

/-- If an element of an artinian ring is not a zero divisor then it is a unit. -/
theorem IsUnit.of_mem_nonZeroDivisors_of_artinian {a : R} :
    a ∈ nonZeroDivisors R → IsUnit a :=
  fun ha ↦ IsUnit.isUnit_iff_mulLeft_bijective.mpr <|
      IsArtinian.bijective_of_injective_endomorphism (LinearMap.mulLeft R a)
        fun _ _ ↦ (mul_cancel_left_mem_nonZeroDivisors ha).mp

/-- In an artinian ring, an element is a unit iff it is a non-zero-divisor. -/
lemma IsUnit.iff_mem_nonZeroDivisors_of_artinian {a : R} :
    IsUnit a ↔ a ∈ nonZeroDivisors R :=
  ⟨IsUnit.mem_nonZeroDivisors, IsUnit.of_mem_nonZeroDivisors_of_artinian⟩

/-- Commutative artinian reduced local ring is a field. -/
instance isField_of_artinian_reduced_local [IsReduced R] [IsLocalRing R] : IsField R :=
  let m := IsLocalRing.maximalIdeal R
  let e : R ≃+* R ⧸ m := (IsArtinianRing.equivPi R).trans <|
    RingEquiv.piUnique fun I : SpecMax R ↦ R ⧸ I.1
  MulEquiv.isField (R ⧸ m) (Ideal.Quotient.field m).toIsField e.toMulEquiv

end IsArtinian

section Algebra

/-- Transfer `R`-algebra structure via ring homomorphism. -/
def algebra_fromRingHom {R A₁ A₂ : Type*} [CommSemiring R] [Semiring A₁] [CommSemiring A₂]
    [Algebra R A₁] (f : A₁ →+* A₂) : Algebra R A₂ :=
  (f.comp (algebraMap R A₁)).toAlgebra

variable {F A : Type*}
variable [Field F] [CommRing A] [Algebra F A]

theorem FiniteDimensional.of_integral_adjoin {a : A} (hai : IsIntegral F a) :
    FiniteDimensional F (Algebra.adjoin F {a}) :=
  FiniteDimensional.of_fintype_basis (Algebra.adjoin.powerBasisAux hai)

/-- Integral element of an `F`-algebra is either zero divisor or unit. -/
theorem IsUnit.of_nonzerodivisor_of_integral {a : A} (hi : IsIntegral F a)
    (ha : a ∈ nonZeroDivisors A) : IsUnit a :=
  let B := Algebra.adjoin F {a}
  let b : B := ⟨a, Algebra.subset_adjoin (Set.mem_singleton a)⟩
  haveI := FiniteDimensional.of_integral_adjoin hi
  haveI : IsArtinianRing B := isArtinian_of_tower F inferInstance
  have hinj : Function.Injective (B.subtype) := Subtype.val_injective
  have hb : b ∈ nonZeroDivisors B := nonZeroDivisor.map hinj ha
  (IsUnit.of_mem_nonZeroDivisors_of_artinian hb).map B.subtype

/-- Integral element of an `F`-algebra is either zero divisor or unit. -/
theorem IsUnit.iff_nonzerodivisor_of_integral {a : A} (hi : IsIntegral F a) :
    IsUnit a ↔ a ∈ nonZeroDivisors A :=
  ⟨IsUnit.mem_nonZeroDivisors, IsUnit.of_nonzerodivisor_of_integral hi⟩

/- how to make an instance? -/
theorem Subsemiring.nontrivial' {R : Type*} [Semiring R] {B C : Subsemiring R} [Nontrivial C]
    (inc : B ≤ C) : Nontrivial B :=
  nontrivial_of_ne 0 1 fun H ↦ zero_ne_one (congr_arg (Subsemiring.inclusion inc) H)

/-- Let `C` be a local `F`-algebra. If `B` is an `F`-subalgebra of `C` in which
    every element is either invertible or a zero divisor, then `B` is local.
    Version for `B` and `C` being subalgebras of an `F`-algebra `A`.
  -/
lemma IsLocalRing.of_subalgebra' {B C : Subalgebra F A} [IsLocalRing C] (inc : B ≤ C)
    (h : ∀ a, a ∈ nonZeroDivisors B → IsUnit a) : IsLocalRing B :=
  haveI : Nontrivial B := Subsemiring.nontrivial' inc
  let ι := Subalgebra.inclusion inc
  have hι := Subalgebra.inclusion_injective inc
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    fun a ↦ Or.imp (h _) (h _) <|
      Or.imp (nonZeroDivisor.map hι) (nonZeroDivisor.map hι) <|
      map_sub ι .. ▸ map_one ι ▸
        (IsLocalRing.isUnit_or_isUnit_one_sub_self (ι a)).imp
          IsUnit.mem_nonZeroDivisors IsUnit.mem_nonZeroDivisors

/-- Let `A` be a local `F`-algebra. If `B` is an `F`-subalgebra of `A` in which
    every element is either invertible or a zero divisor, then `B` is local.
  -/
lemma IsLocalRing.of_subalgebra [IsLocalRing A] {B : Subalgebra F A}
    (h : ∀ a, a ∈ nonZeroDivisors B → IsUnit a) : IsLocalRing B :=
  haveI : IsLocalRing (⊤ : Subalgebra F A) := isLocalRing_top
  IsLocalRing.of_subalgebra' (le_top : B ≤ ⊤) h

end Algebra

namespace AlgHom

/- Some missing simple lemmas regarding product of algebras. -/

variable {R A B : Type*}
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (R)

lemma fst_apply (a) : fst R A B a = a.1 := rfl
lemma snd_apply (a) : snd R A B a = a.2 := rfl

end AlgHom

section IsIntegral

variable {R A B : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- Polynomial evaluation on a pair is a pair of evaluations. -/
theorem Polynomial.aeval_prod_apply (a : A × B) (p : Polynomial R) :
    p.aeval a = (p.aeval a.1, p.aeval a.2) :=
  AlgHom.id_apply (R := R) (p.aeval a) ▸ AlgHom.fst_apply R a ▸ AlgHom.snd_apply R a ▸
    p.aeval_algHom_apply (AlgHom.fst R A B) a ▸ p.aeval_algHom_apply (AlgHom.snd R A B) a ▸
    AlgHom.prod_apply (AlgHom.fst R A B) (AlgHom.snd R A B) (p.aeval a)

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

/-- Product of two integral algebras is an integral algebra. -/
instance Algebra.IsIntegral.prod [Algebra.IsIntegral R A] [Algebra.IsIntegral R B] :
    Algebra.IsIntegral R (A × B) :=
  Algebra.isIntegral_def.mpr fun a ↦
    IsIntegral.pair (Algebra.isIntegral_def.mp ‹_› a.1) (Algebra.isIntegral_def.mp ‹_› a.2)

/-- Image of an integral algebra is an integral algebra. -/
theorem Algebra.IsIntegral.of_surjective [Algebra.IsIntegral R A]
    (f : A →ₐ[R] B) (hf : Function.Surjective f) : Algebra.IsIntegral R B :=
  Algebra.isIntegral_def.mpr fun b ↦ let ⟨a, ha⟩ := hf b
    ha ▸ IsIntegral.map f (Algebra.isIntegral_def.mp ‹_› a)

end IsIntegral
