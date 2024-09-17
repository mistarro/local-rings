import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Subring.Basic

import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.Basic

variable {R : Type u} [CommRing R]

lemma isUnit_subring {S : Subring R} {a : S} (h : IsUnit a) : IsUnit (a : R) := by
  exact IsUnit.map S.subtype h

/-- Equivalent condition for a ring `R` not to be local. -/
lemma nonLocalDef [Nontrivial R] (h : ¬LocalRing R) : ∃ a : R, ¬IsUnit a ∧ ¬IsUnit (1 - a) := by
  by_contra hn
  simp [not_exists, ←not_or] at hn
  exact h (LocalRing.of_isUnit_or_isUnit_one_sub_self hn)

lemma nonLocalProj [Nontrivial R] (h : ¬LocalRing R) :
    ∃ (K₁ K₂ : Type u) (fK₁ : Field K₁) (fK₂ : Field K₂) (f : R →+* K₁ × K₂), Function.Surjective f := by
  /- get two maximal ideals and project -/
  obtain ⟨a, ⟨hnua, hnub⟩⟩ := nonLocalDef h
  have hnua1 : a ∈ nonunits R := by rwa [←mem_nonunits_iff] at hnua
  have hnub1 : 1 - a ∈ nonunits R := by rwa [←mem_nonunits_iff] at hnub
  obtain ⟨m₁, ⟨_, ham⟩⟩ := exists_max_ideal_of_mem_nonunits hnua1
  obtain ⟨m₂, ⟨_, hbm⟩⟩ := exists_max_ideal_of_mem_nonunits hnub1
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

/- If `f '' S₁ ⊆ S₂` then the image of the span of `S₁` is a submodule of the span of `S₂`. -/
lemma span_transfer {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] {S₁ : Set M₁} {S₂ : Set M₂} {f : M₁ →ₗ[R] M₂}
    (h : f '' S₁ ⊆ S₂) : (Submodule.span R S₁).map f ≤ Submodule.span R S₂ := by
  have h1 : Submodule.span R (f '' S₁) ≤ Submodule.span R S₂ := Submodule.span_mono h
  have h2 : (Submodule.span R S₁).map f ≤ Submodule.span R (f '' S₁) := by
    rw [Submodule.map_span_le]
    intro m hm
    exact (Submodule.subset_span : f '' S₁ ⊆ Submodule.span R (f '' S₁)) (Set.mem_image_of_mem f hm)
  exact Set.Subset.trans h2 h1

/-- Transfer `R`-algebra structure via ring homomorphism. -/
def algebra_fromRingHom {A₁ A₂ : Type*} [Semiring A₁] [CommSemiring A₂]
    [Algebra R A₁] (f : A₁ →+* A₂) : Algebra R A₂ :=
  (f.comp (algebraMap R A₁)).toAlgebra
