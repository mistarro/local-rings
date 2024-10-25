import Mathlib.Algebra.Ring.Hom.Defs

import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
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


variable {R : Type u} [CommRing R]

/-- Equivalent condition for a ring `R` not to be local. -/
lemma nonLocalRing_def [Nontrivial R] (h : ¬LocalRing R) : ∃ a : R, ¬IsUnit a ∧ ¬IsUnit (1 - a) := by
  by_contra hn
  simp [not_exists, ←not_or] at hn
  exact h (LocalRing.of_isUnit_or_isUnit_one_sub_self hn)

lemma nonLocalProj [Nontrivial R] (h : ¬LocalRing R) :
    ∃ (K₁ K₂ : Type u) (fK₁ : Field K₁) (fK₂ : Field K₂) (f : R →+* K₁ × K₂), Function.Surjective f := by
  /- get two maximal ideals and project -/
  obtain ⟨a, ⟨hnua, hnub⟩⟩ := nonLocalRing_def h
  rw [←mem_nonunits_iff] at hnua hnub
  obtain ⟨m₁, ⟨_, ham⟩⟩ := exists_max_ideal_of_mem_nonunits hnua
  obtain ⟨m₂, ⟨_, hbm⟩⟩ := exists_max_ideal_of_mem_nonunits hnub
  have coprime : IsCoprime m₁ m₂ := by
    rw [Ideal.isCoprime_iff_exists]
    use a, ham, 1 - a, hbm
    ring
  -- `R →+* R ⧸ m₁ ⊓ m₂`
  let g := Ideal.Quotient.mk (m₁ ⊓ m₂)
  -- `R ⧸ m₁ ⊓ m₂ ≃+* (R ⧸ m₁) × R ⧸ m₂`
  let e := Ideal.quotientInfEquivQuotientProd m₁ m₂ coprime
  let K₁ := R ⧸ m₁
  let K₂ := R ⧸ m₂
  let fK₁ : Field K₁ := Ideal.Quotient.field m₁
  let fK₂ : Field K₂ := Ideal.Quotient.field m₂
  let f := RingHom.comp (e : R ⧸ m₁ ⊓ m₂ →+* K₁ × K₂) g
  use K₁, K₂, fK₁, fK₂, f
  apply Function.Surjective.comp e.surjective Ideal.Quotient.mk_surjective

/-- Commutative artinian reduced local ring is a field. -/
theorem artinian_reduced_local_is_field (R : Type u)
    [CommRing R] [IsArtinianRing R] [IsReduced R] [LocalRing R] : IsField R := by
  rw [LocalRing.isField_iff_maximalIdeal_eq]
  calc LocalRing.maximalIdeal R
    _ = (0 : Ideal R).jacobson := (LocalRing.jacobson_eq_maximalIdeal 0 bot_ne_top).symm
    _ = (0 : Ideal R).radical := by
      simp_rw [Ideal.radical_eq_sInf 0, IsArtinianRing.isPrime_iff_isMaximal]
      rfl
    _ = nilradical R := rfl
    _ = 0 := nilradical_eq_zero R

section Algebra

/-- Transfer `R`-algebra structure via ring homomorphism. -/
def algebra_fromRingHom {A₁ A₂ : Type*} [Semiring A₁] [CommSemiring A₂]
    [Algebra R A₁] (f : A₁ →+* A₂) : Algebra R A₂ :=
  (f.comp (algebraMap R A₁)).toAlgebra

variable (F : Type u)
variable {A A' : Type u}
variable [Field F] [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A']

/- TODO: move to Ring.lean -/
variable {F} in
theorem FiniteDimensional.of_integral_adjoin {a : A} (hai : IsIntegral F a) :
    FiniteDimensional F (Algebra.adjoin F {a}) :=
  FiniteDimensional.of_fintype_basis (Algebra.adjoin.powerBasisAux hai)

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

/-- An element of a finite-dimensional `F`-algebra is either zero divisor or unit. -/
theorem IsUnit.iff_nonzerodivisor_of_finrank [FiniteDimensional F A] {a : A} :
    IsUnit a ↔ a ∈ nonZeroDivisors A := by
  refine ⟨IsUnit.mem_nonZeroDivisors, fun ha ↦ ?_⟩
  rw [IsUnit.iff_mulLeft_surjective F]
  apply LinearMap.surjective_of_injective
  rw [injective_iff_map_eq_zero]
  intro x
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff ha).mp

/-- Integral element of an `F`-algebra is either zero divisor or unit. -/
theorem IsUnit.iff_nonzerodivisor_of_integral {a : A} (hi : IsIntegral F a) :
    IsUnit a ↔ a ∈ nonZeroDivisors A := by
  refine ⟨IsUnit.mem_nonZeroDivisors, fun ha ↦ ?_⟩
  let B := Algebra.adjoin F {a}
  let a' : B := ⟨a, Algebra.subset_adjoin (Set.mem_singleton a)⟩
  haveI := FiniteDimensional.of_integral_adjoin hi
  have hinj : Function.Injective (B.subtype) := Subtype.val_injective
  have ha' : a' ∈ nonZeroDivisors B := nonZeroDivisor.map hinj ha
  exact
    IsUnit.map
      B.subtype
      ((IsUnit.iff_nonzerodivisor_of_finrank F).mpr ha')

/- how to make an instance? -/
theorem Subsemiring.nontrivial' {R : Type*} [Semiring R] {B C : Subsemiring R} [Nontrivial C] (inc : B ≤ C) : Nontrivial B :=
    nontrivial_of_ne 0 1 fun H ↦ zero_ne_one (congr_arg (Subsemiring.inclusion inc) H)

/-- Let `C` be a local `F`-algebra. If `B` is an `F`-subalgebra of `C` in which
    every element is either invertible or a zero divisor, then `B` is local.
    Version for `B` and `C` being subalgebras of an `F`-algebra `A`.
  -/
lemma LocalRing.of_subalgebra' {B C : Subalgebra F A} [LocalRing C] (inc : B ≤ C)
    (h : ∀ a, IsUnit a ↔ a ∈ nonZeroDivisors B) : LocalRing B := by
  haveI : Nontrivial B := Subsemiring.nontrivial' inc
  apply LocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  let ι := Subalgebra.inclusion inc
  have hι := Subalgebra.inclusion_injective inc
  have hc := LocalRing.isUnit_or_isUnit_one_sub_self (ι a)
  replace hc := Or.imp IsUnit.mem_nonZeroDivisors IsUnit.mem_nonZeroDivisors hc
  rw [← map_one ι, ← map_sub] at hc
  replace hc := Or.imp (nonZeroDivisor.map hι) (nonZeroDivisor.map hι) hc
  rwa [h, h]

/-- Let `A` be a local `F`-algebra. If `B` is an `F`-subalgebra of `A` in which
    every element is either invertible or a zero divisor, then `B` is local.
  -/
lemma LocalRing.of_subalgebra [LocalRing A] {B : Subalgebra F A}
    (h : ∀ a, IsUnit a ↔ a ∈ nonZeroDivisors B) : LocalRing B := by
  let e : A ≃ₐ[F] _ := Subalgebra.topEquiv.symm
  haveI : LocalRing (⊤ : Subalgebra F A) :=
    LocalRing.of_surjective' e.toAlgHom e.surjective
  exact LocalRing.of_subalgebra' F (le_top : B ≤ ⊤) h
  /- direct proof:
  apply LocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  have hc := LocalRing.isUnit_or_isUnit_one_sub_self (B.val a)
  replace hc := Or.imp IsUnit.mem_nonZeroDivisors IsUnit.mem_nonZeroDivisors hc
  rw [← map_one B.val, ← map_sub] at hc
  have hinj : Function.Injective B.val := Subtype.coe_injective
  replace hc := Or.imp (nonZeroDivisor_map hinj) (nonZeroDivisor_map hinj) hc
  rwa [h, h]
  -/

end Algebra
