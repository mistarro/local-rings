import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Ring.Hom.Defs

import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Artinian


/-!
# Supplementary lemmas for commutative rings.
-/

/-- If an element maps to non-zero-divisor via injective homomorphism,
    then it is non-zero-divizor. -/
theorem nonZeroDivisor.map {M N F : Type*} [MonoidWithZero M] [MonoidWithZero N]
    [FunLike F M N] [MonoidWithZeroHomClass F M N] {f : F} (hf : Function.Injective f)
    {a : M} : f a ∈ nonZeroDivisors N → a ∈ nonZeroDivisors M :=
  fun h x hx ↦ hf <| map_zero f ▸ h (f x) (map_mul f x a ▸ map_zero f ▸ congrArg f hx)

/-- Equivalent condition for a ring `R` not to be local. -/
lemma nonLocalRing_def {R : Type*} [CommRing R] [Nontrivial R] (h : ¬IsLocalRing R) :
    ∃ a : R, ¬IsUnit a ∧ ¬IsUnit (1 - a) := by
  by_contra hn
  simp [not_exists, ←not_or] at hn
  exact h (IsLocalRing.of_isUnit_or_isUnit_one_sub_self hn)

lemma nonLocalProj.{u} {R : Type u} [CommRing R] [Nontrivial R] (h : ¬IsLocalRing R) :
    ∃ (K₁ K₂ : Type u) (_ : Field K₁) (_ : Field K₂) (f : R →+* K₁ × K₂),
      Function.Surjective f := by
  /- get two different maximal ideals and project on the product of quotients -/
  obtain ⟨a, ⟨hnua, hnub⟩⟩ := nonLocalRing_def h
  rw [←mem_nonunits_iff] at hnua hnub
  obtain ⟨m₁, ⟨_, ham⟩⟩ := exists_max_ideal_of_mem_nonunits hnua
  obtain ⟨m₂, ⟨_, hbm⟩⟩ := exists_max_ideal_of_mem_nonunits hnub
  -- `R →+* R ⧸ m₁ ⊓ m₂`
  let g := Ideal.Quotient.mk (m₁ ⊓ m₂)
  -- `R ⧸ m₁ ⊓ m₂ ≃+* (R ⧸ m₁) × R ⧸ m₂`
  let e := Ideal.quotientInfEquivQuotientProd m₁ m₂ <|
    Ideal.isCoprime_iff_exists.mpr ⟨a, ham, 1 - a, hbm, add_sub_cancel a 1⟩
  let K₁ := R ⧸ m₁
  let K₂ := R ⧸ m₂
  let fK₁ : Field K₁ := Ideal.Quotient.field m₁
  let fK₂ : Field K₂ := Ideal.Quotient.field m₂
  let f := RingHom.comp (e : R ⧸ m₁ ⊓ m₂ →+* K₁ × K₂) g
  use K₁, K₂, fK₁, fK₂, f
  apply Function.Surjective.comp e.surjective Ideal.Quotient.mk_surjective

/-- Commutative artinian reduced local ring is a field. -/
theorem artinian_reduced_local_is_field (R : Type*) [CommRing R]
    [IsArtinianRing R] [IsReduced R] [IsLocalRing R] : IsField R := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  calc IsLocalRing.maximalIdeal R
    _ = (0 : Ideal R).jacobson := (IsLocalRing.jacobson_eq_maximalIdeal 0 bot_ne_top).symm
    _ = (0 : Ideal R).radical := by
      simp_rw [Ideal.radical_eq_sInf 0, IsArtinianRing.isPrime_iff_isMaximal]
      rfl
    _ = nilradical R := rfl
    _ = 0 := nilradical_eq_zero R

section Algebra

/-- Transfer `R`-algebra structure via ring homomorphism. -/
def algebra_fromRingHom {R A₁ A₂ : Type*} [CommSemiring R] [Semiring A₁] [CommSemiring A₂]
    [Algebra R A₁] (f : A₁ →+* A₂) : Algebra R A₂ :=
  (f.comp (algebraMap R A₁)).toAlgebra

variable (F : Type*)
variable {A A' : Type*}
variable [Field F] [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A']

variable {F} in
theorem FiniteDimensional.of_integral_adjoin {a : A} (hai : IsIntegral F a) :
    FiniteDimensional F (Algebra.adjoin F {a}) :=
  FiniteDimensional.of_fintype_basis (Algebra.adjoin.powerBasisAux hai)

variable {F} in
lemma IsUnit.iff_mulLeft_surjective {a : A} :
    IsUnit a ↔ Function.Surjective (LinearMap.mulLeft F a) := by
  apply Iff.intro
  · intro ha b
    obtain ⟨a', ⟨ha', -⟩⟩ := isUnit_iff_exists.mp ha
    use a' * b
    simp
    rw [← mul_assoc, ha', one_mul]
  · intro h
    obtain ⟨b, hb⟩ := h 1
    exact isUnit_of_mul_eq_one a b hb

/-- If an element of a finite-dimensional `F`-algebra is not a zero divisor then it is a unit. -/
theorem IsUnit.of_nonzerodivisor_of_finrank [FiniteDimensional F A] {a : A} :
    a ∈ nonZeroDivisors A → IsUnit a :=
  fun ha ↦
    IsUnit.iff_mulLeft_surjective.mpr <| LinearMap.surjective_of_injective <|
      (injective_iff_map_eq_zero (LinearMap.mulLeft F a)).mpr
        fun _ ↦ (mul_left_mem_nonZeroDivisors_eq_zero_iff ha).mp

/-- An element of a finite-dimensional `F`-algebra is either zero divisor or unit. -/
theorem IsUnit.iff_nonzerodivisor_of_finrank [FiniteDimensional F A] {a : A} :
    IsUnit a ↔ a ∈ nonZeroDivisors A :=
  ⟨IsUnit.mem_nonZeroDivisors, IsUnit.of_nonzerodivisor_of_finrank F⟩

/-- Integral element of an `F`-algebra is either zero divisor or unit. -/
theorem IsUnit.of_nonzerodivisor_of_integral {a : A} (hi : IsIntegral F a) :
    a ∈ nonZeroDivisors A → IsUnit a := by
  intro ha
  let B := Algebra.adjoin F {a}
  let a' : B := ⟨a, Algebra.subset_adjoin (Set.mem_singleton a)⟩
  haveI := FiniteDimensional.of_integral_adjoin hi
  have hinj : Function.Injective (B.subtype) := Subtype.val_injective
  have ha' : a' ∈ nonZeroDivisors B := nonZeroDivisor.map hinj ha
  exact
    IsUnit.map
      B.subtype
      (IsUnit.of_nonzerodivisor_of_finrank F ha')

/-- Integral element of an `F`-algebra is either zero divisor or unit. -/
theorem IsUnit.iff_nonzerodivisor_of_integral {a : A} (hi : IsIntegral F a) :
    IsUnit a ↔ a ∈ nonZeroDivisors A :=
  ⟨IsUnit.mem_nonZeroDivisors, IsUnit.of_nonzerodivisor_of_integral F hi⟩

/- how to make an instance? -/
theorem Subsemiring.nontrivial' {R : Type*} [Semiring R] {B C : Subsemiring R} [Nontrivial C]
    (inc : B ≤ C) : Nontrivial B :=
  nontrivial_of_ne 0 1 fun H ↦ zero_ne_one (congr_arg (Subsemiring.inclusion inc) H)

/-- Let `C` be a local `F`-algebra. If `B` is an `F`-subalgebra of `C` in which
    every element is either invertible or a zero divisor, then `B` is local.
    Version for `B` and `C` being subalgebras of an `F`-algebra `A`.
  -/
lemma IsLocalRing.of_subalgebra' {B C : Subalgebra F A} [IsLocalRing C] (inc : B ≤ C)
    (h : ∀ a, a ∈ nonZeroDivisors B → IsUnit a) : IsLocalRing B := by
  haveI : Nontrivial B := Subsemiring.nontrivial' inc
  let ι := Subalgebra.inclusion inc
  have hι := Subalgebra.inclusion_injective inc
  exact IsLocalRing.of_isUnit_or_isUnit_one_sub_self
    fun a ↦ Or.imp (h a) (h (1 - a)) <|
      Or.imp (nonZeroDivisor.map hι) (nonZeroDivisor.map hι) <|
      map_sub ι 1 a ▸ map_one ι ▸
        (Or.imp IsUnit.mem_nonZeroDivisors IsUnit.mem_nonZeroDivisors <|
        IsLocalRing.isUnit_or_isUnit_one_sub_self (ι a))

/-- Let `A` be a local `F`-algebra. If `B` is an `F`-subalgebra of `A` in which
    every element is either invertible or a zero divisor, then `B` is local.
  -/
lemma IsLocalRing.of_subalgebra [IsLocalRing A] {B : Subalgebra F A}
    (h : ∀ a, a ∈ nonZeroDivisors B → IsUnit a) : IsLocalRing B := by
  let e : A ≃ₐ[F] _ := Subalgebra.topEquiv.symm
  haveI : IsLocalRing (⊤ : Subalgebra F A) :=
    IsLocalRing.of_surjective' e.toAlgHom e.surjective
  exact IsLocalRing.of_subalgebra' F (le_top : B ≤ ⊤) h

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
    {f : A →ₐ[R] B} (hf : Function.Surjective f) : Algebra.IsIntegral R B :=
  Algebra.isIntegral_def.mpr fun b ↦ let ⟨a, ha⟩ := hf b
    ha ▸ IsIntegral.map f (Algebra.isIntegral_def.mp ‹_› a)

end IsIntegral
