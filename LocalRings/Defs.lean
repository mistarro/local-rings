import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.QuotientOperations

import LocalRings.Utils

variable {R : Type*}
variable [CommRing R]

/-- An element `a` of a ring `R` is *local* iff
    it belongs to a local subring of `R`. -/
def isLocalElement (a : R) : Prop :=
  ∃ S : Subring R, LocalRing S ∧ a ∈ S

/-- In a local ring, all elements are local -/
theorem all_local_if_local [LocalRing R] (a : R) : isLocalElement a := by
  use ⊤
  apply And.intro
  · exact (Subsemiring.topEquiv : (⊤ : Subsemiring R) ≃+* R).symm.localRing
  · exact Subsemiring.mem_top a

/-- If all elements of a ring are local then the ring is local. -/
theorem local_if_all_local [Nontrivial R] (ha : ∀ a : R, isLocalElement a) : LocalRing R := by
  apply LocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  -- a is local so there is B : Subring R, LocalRing B ∧ a ∈ B,
  obtain ⟨B, ⟨hB, haB⟩⟩ := ha a
  -- if `a` is a unit in `B`, then it is a unit in `R`
  -- if `1 - a` is a unit in `B`, then it is a unit in `R`
  let aa : B := ⟨a, haB⟩
  exact Or.imp (isUnit_subring (a := aa)) (isUnit_subring (a := 1 - aa))
    (by apply LocalRing.isUnit_or_isUnit_one_sub_self)

/-- A homomorphism of rings maps local elements to local elements. -/
theorem isLocalElement_map {S : Type*} [Nontrivial S] [CommRing S] (f : R →+* S)
    {a : R} (ha : isLocalElement a) : isLocalElement (f a) := by
  -- B := local ring containing a
  obtain ⟨B, ⟨hB, haB⟩⟩ := ha
  -- g : ↥B →+* S
  let g := f.domRestrict B
  use g.range
  apply And.intro
  · -- goal: g.range is a local ring
    exact LocalRing.of_surjective' g.rangeRestrict (RingHom.rangeRestrict_surjective g)
  · -- goal: f a ∈ g.range
    rw [RingHom.mem_range, Subtype.exists]
    use a, haB
    rw [RingHom.restrict_apply]

variable {F A : Type u}
variable [Field F] [CommRing A] [Algebra F A]

/-- An `F`-algebra `A` is *locally generated* if the local elements of `A`
    generate `A` as a vector space over `F`. -/
def isLocallyGenerated (F A : Type*) [Field F] [CommRing A] [Algebra F A] : Prop :=
  Submodule.span F {a : A | isLocalElement a} = ⊤

/-- If `F`-algebra `A` is locally generated and `f : A → B` is a surjective `F`-algebra
    homomorphism, then `F`-algebra `B` is also locally generated. -/
lemma isLocallyGenerated_surjective {B : Type*} [CommRing B] [Nontrivial B] [Algebra F B] (f : A →ₐ[F] B)
    (hf : Function.Surjective f) (h : isLocallyGenerated F A) : isLocallyGenerated F B := by
  let lA := {a : A | isLocalElement a}
  let lB := {b : B | isLocalElement b}
  have h1 : f '' lA ⊆ lB := by
    intro y hy
    obtain ⟨x, ⟨hx, hfxy⟩⟩ := hy
    rw [Set.mem_setOf_eq, ← hfxy] at *
    exact isLocalElement_map f.toRingHom hx
  have h2 : (Submodule.span F lA).map f ≤ Submodule.span F lB :=
    span_transfer (f := f.toLinearMap) h1
  rwa [h, Submodule.map_top, LinearMap.range_eq_top.mpr hf, top_le_iff] at h2

variable {K₁ K₂ : Type u} [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂]

/-- Property of two field extenstions `K₁`, `K₂` of `F`:
    if both satisfy `Q`, then `K₁ × K₂` is not locally generated over `F`. -/
def notLocallyGeneratedKK_if (Q : Type u → Prop) (F K₁ K₂ : Type u)
    [Field F] [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂] : Prop :=
    Q K₁ → Q K₂ → ¬isLocallyGenerated F (K₁ × K₂)

/-- Generic theorem: given
      * `hPQ`: proof that `P A` implies `Q K` given a surjective `f : A →ₐ[F] B`
      * `hKK`: proof that `K₁ × K₂` is not locally generated if `Q K₁` and `Q K₂`
    an `F`-algebra `A` is local if it satisfies `P A` and is locally generated. -/
theorem isLocalRing_if_isLocallyGenerated [Nontrivial A] {P Q : Type u → Prop}
    (hPQ : ∀ {F A K : Type u} [Field F] [CommRing A] [Algebra F A] [Field K] [Algebra F K] (f : A →ₐ[F] K), Function.Surjective f → P A → Q K)
    (hKK : ∀ (F K₁ K₂ : Type u) [Field F] [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂], notLocallyGeneratedKK_if Q F K₁ K₂)
    (h : P A) (hLG : isLocallyGenerated F A) : LocalRing A := by
  by_contra hNonLocalA
  obtain ⟨K₁, K₂, fK₁, fK₂, f', hf⟩ := nonLocalProj hNonLocalA
  -- Introduce compatible `F`-algebra structures
  let algKK : Algebra F (K₁ × K₂) := algebra_fromRingHom f'
  let algK₁ : Algebra F K₁ := algebra_fromRingHom (RingHom.fst K₁ K₂)
  let algK₂ : Algebra F K₂ := algebra_fromRingHom (RingHom.snd K₁ K₂)
  -- Promote `f'` to an `F`-algebra homomorphism.
  let f : A →ₐ[F] (K₁ × K₂) := by
    apply AlgHom.mk' f'
    intro _ _
    simp_all [Algebra.smul_def]
    rfl
  /- compose `f` with projections on `K₁`... -/
  let f₁ := (AlgHom.fst F K₁ K₂).comp f
  have hf₁ : Function.Surjective f₁ := by
    simpa using Function.Surjective.comp Prod.fst_surjective hf
  /- ... and `K₂` -/
  let f₂ := (AlgHom.snd F K₁ K₂).comp f
  have hf₂ : Function.Surjective f₂ := by
    simpa using Function.Surjective.comp Prod.snd_surjective hf
  exact hKK F K₁ K₂ (hPQ f₁ hf₁ h) (hPQ f₂ hf₂ h) (isLocallyGenerated_surjective f hf hLG)

/-- For finite fields `K₁`, `K₂` extending `F`, the `F`-algebra `K₁ × K₂`
    is not locally generated. -/
theorem notLocallyGenerated_KK_if_finite (F K₁ K₂ : Type u)
    [Field F] [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂] :
    notLocallyGeneratedKK_if Finite F K₁ K₂ := by
  intro hfK₁ hfK₂ h
  sorry

/-- Finite algebras are local if they are locally generated. -/
theorem isLocalRing_if_isLocallyGenerated_finite [Nontrivial A]
    (h : Finite A) (hLG : isLocallyGenerated F A) : LocalRing A := by
  refine isLocalRing_if_isLocallyGenerated ?_ notLocallyGenerated_KK_if_finite h hLG
  intro _ _ _ _ _ _ _ _ f hf hA
  exact hA.of_surjective f hf
