import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Ring.Prod

import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Trace.Basic

import LocalRings.Utils.Module
import LocalRings.Utils.PurelyInseparable
import LocalRings.Utils.Ring
import LocalRings.Utils.Trace

/-!
# Basic results about local elements and local rings.

## Main definitions

* `isLocalElement`: an element `a` of an `F`-algebra `A` is *local* iff
    it belongs to a local `F`-subalgebra of `A`.
* `localElements`: the set of all local elements in an `F`-algebra `A`.
* `isLocallyGenerated`: an `F`-algebra `A` is *locally generated* if
    the local elements of `A` generate `A` as a vector space over `F`.
* `iRedₛₗ`: the map `iRed` as a semilinear map wrt. `iteratedFrobenius` on the scalar field.
* `iRed_frobₛₗ`: the map `iRed_frob` as a semilinear map wrt. `iteratedFrobenius`
    on the scalar field.

## Main results

* `local_if_all_local`: if all elements of an `F`-algebra are local then the algebra is local.
* `isLocalAlgebra_if_isLocallyGenerated`: generic theorem used to reduce: given
  * `hPQ`: proof that `P F A` implies `Q F K` given a surjective `f : A →ₐ[F] K`;
  * `hKK`: proof that `K₁ × K₂` cannot be locally generated if `Q F K₁` and `Q F K₂`;
  an `F`-algebra `A` is local if it satisfies `P A` and is locally generated.
-/

variable (F : Type u)
variable {A A' : Type u}
variable [Field F] [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A']

/-- An element `a` of an `F`-algebra `A` is *local* iff
    it belongs to a local `F`-subalgebra of `A`. -/
def isLocalElement (a : A) : Prop :=
  ∃ B : Subalgebra F A, LocalRing B ∧ a ∈ B

/-- In a local `F`-algebra, all elements are local -/
theorem all_local_if_local [LocalRing A] (a : A) : isLocalElement F a := by
  use ⊤
  apply And.intro
  · exact (Subsemiring.topEquiv : (⊤ : Subsemiring A) ≃+* A).symm.localRing
  · exact Subsemiring.mem_top a

/-- If all elements of an `F`-algebra are local then the algebra is local. -/
theorem local_if_all_local [Nontrivial A] (ha : ∀ a : A, isLocalElement F a) : LocalRing A := by
  apply LocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  obtain ⟨B, ⟨hB, haB⟩⟩ := ha a
  /- if `a` is a unit in `B`, then it is a unit in `R`
     if `1 - a` is a unit in `B`, then it is a unit in `R` -/
  exact Or.imp
    (IsUnit.map B.subtype)
    (IsUnit.map B.subtype)
    (by apply LocalRing.isUnit_or_isUnit_one_sub_self (⟨a, haB⟩ : B))

/-- A power of a local element is a local element. -/
theorem isLocalElement_pow {a : A} (ha : isLocalElement F a) (n : ℕ) : isLocalElement F (a ^ n) := by
  obtain ⟨B, ⟨hB, haB⟩⟩ := ha
  use B
  exact ⟨hB, Subalgebra.pow_mem B haB n⟩

/-- A homomorphism of rings maps local elements to local elements. -/
theorem isLocalElement_map [Nontrivial A'] (f : A →ₐ[F] A')
    {a : A} (ha : isLocalElement F a) : isLocalElement F (f a) := by
  obtain ⟨B, ⟨hB, haB⟩⟩ := ha
  /- g : B →ₐ[F] A' -/
  let g := f.comp (B.val)
  use g.range
  apply And.intro
  · /- goal: `g.range` is a local ring -/
    exact LocalRing.of_surjective' g.rangeRestrict (g.rangeRestrict_surjective)
  · /- goal: `f a ∈ g.range` -/
    rw [AlgHom.mem_range g]
    use ⟨a, haB⟩
    rfl

variable (A) in
/-- Set of all local elements of an `F`-algebra `A`. -/
def localElements : Set A := {a : A | isLocalElement F a}

variable (A) in
/-- An `F`-algebra `A` is *locally generated* if the local elements of `A`
    generate `A` as a vector space over `F`. -/
def isLocallyGenerated : Prop := Submodule.span F (localElements F A) = ⊤

/-- If `F`-algebra `A` is locally generated and `f : A →ₐ[F] A'` is a surjective `F`-algebra
    homomorphism, then `F`-algebra `A'` is also locally generated. -/
lemma isLocallyGenerated_surjective [Nontrivial A'] (f : A →ₐ[F] A')
    (hf : Function.Surjective f) (h : isLocallyGenerated F A) : isLocallyGenerated F A' := by
  let lA := localElements F A
  let lA' := localElements F A'
  have hsub : f '' lA ⊆ lA' := by
    intro y ⟨x, ⟨hx, hfxy⟩⟩
    rw [← hfxy]
    exact isLocalElement_map F f hx
  replace hsub : (Submodule.span F lA).map f ≤ Submodule.span F lA' :=
    span_transfer (f := f.toLinearMap) hsub
  rwa [h, Submodule.map_top, LinearMap.range_eq_top.mpr hf, top_le_iff] at hsub

variable {K₁ K₂ : Type u} [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂]

/-- Generic theorem: given
      * `hPQ`: proof that `P F A` implies `Q F K` given a surjective `f : A →ₐ[F] K`;
      * `hKK`: proof that `K₁ × K₂` cannot be locally generated if `Q F K₁` and `Q F K₂`;
    an `F`-algebra `A` is local if it satisfies `P A` and is locally generated. -/
theorem isLocalAlgebra_if_isLocallyGenerated [Nontrivial A]
    {Q : ∀ (F K : Type u) [Field F] [Field K] [Algebra F K], Prop}
    {P : ∀ (F A : Type u) [Field F] [CommRing A] [Algebra F A], Prop}
    (hPQ : ∀ {F A K : Type u} [Field F] [CommRing A] [Algebra F A] [Field K] [Algebra F K] (f : A →ₐ[F] K),
      Function.Surjective f → P F A → Q F K)
    (hKK : ∀ (F : Type u) [Field F] (K₁ K₂ : Type u) [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂],
      Q F K₁ → Q F K₂ → ¬isLocallyGenerated F (K₁ × K₂))
    (h : P F A) (hLG : isLocallyGenerated F A) : LocalRing A := by
  by_contra hNonLocalA
  obtain ⟨K₁, K₂, fK₁, fK₂, f', hf⟩ := nonLocalProj hNonLocalA
  /- introduce compatible `F`-algebra structures -/
  let algKK : Algebra F (K₁ × K₂) := algebra_fromRingHom f'
  let algK₁ : Algebra F K₁ := algebra_fromRingHom (RingHom.fst K₁ K₂)
  let algK₂ : Algebra F K₂ := algebra_fromRingHom (RingHom.snd K₁ K₂)
  /- promote `f'` to an `F`-algebra homomorphism -/
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
  exact hKK F K₁ K₂ (hPQ f₁ hf₁ h) (hPQ f₂ hf₂ h) (isLocallyGenerated_surjective F f hf hLG)
