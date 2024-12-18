import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Ring.Prod

import Mathlib.LinearAlgebra.Span

import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Trace.Basic

import LocalRings.Utils.Ring

/-!
# Basic results about local elements and local rings.

## Main definitions

* `isLocalElement`: an element `a` of an `F`-algebra `A` is *local* iff
    it belongs to a local `F`-subalgebra of `A`.
* `localElements`: the set of all local elements in an `F`-algebra `A`.
* `isLocallyGenerated`: an `F`-algebra `A` is *locally generated* if
    the local elements of `A` generate `A` as a vector space over `F`.

## Main results

* `isLocalElement_integral`: if a local element `a` of an `F`-algebra `A` is
    integral then it belongs to a finite-dimensional local `F`-subalgebra of `A`.
* `local_if_all_local`: if all elements of an `F`-algebra are local then the algebra is local.
* `isLocalAlgebra_if_isLocallyGenerated`: generic theorem used to reduce: given
  * `hPQ`: proof that `P F A` implies `Q F K` given a surjective `f : A →ₐ[F] K`;
  * `hKK`: proof that `K₁ × K₂` cannot be locally generated if `Q F K₁` and `Q F K₂`;
  an `F`-algebra `A` is local if it satisfies `P A` and is locally generated.
-/

universe u

variable (F : Type u)
variable {A A' : Type u}
variable [Field F] [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A']

/-- An element `a` of an `F`-algebra `A` is *local* iff
    it belongs to a local `F`-subalgebra of `A`. -/
def isLocalElement (a : A) : Prop :=
  ∃ B : Subalgebra F A, LocalRing B ∧ a ∈ B

/-- In a local `F`-algebra, all elements are local -/
theorem all_local_if_local [LocalRing A] (a : A) : isLocalElement F a :=
  ⟨⊤, ⟨(Subsemiring.topEquiv : (⊤ : Subsemiring A) ≃+* A).symm.localRing,
    Subsemiring.mem_top a⟩⟩

/-- If all elements of an `F`-algebra are local then the algebra is local. -/
theorem local_if_all_local [Nontrivial A] (ha : ∀ a : A, isLocalElement F a) : LocalRing A :=
  .of_isUnit_or_isUnit_one_sub_self fun a ↦ let ⟨B, ⟨_, haB⟩⟩ := ha a;
    Or.imp
      (IsUnit.map B.subtype)
      (IsUnit.map B.subtype)
      (LocalRing.isUnit_or_isUnit_one_sub_self (⟨a, haB⟩ : B))

/-- A power of a local element is a local element. -/
theorem isLocalElement_pow {a : A} (ha : isLocalElement F a) (n : ℕ) : isLocalElement F (a ^ n) :=
  let ⟨B, ⟨hB, haB⟩⟩ := ha
  ⟨B, ⟨hB, Subalgebra.pow_mem B haB n⟩⟩

/-- A homomorphism of rings maps local elements to local elements. -/
theorem isLocalElement_map [Nontrivial A'] (f : A →ₐ[F] A')
    {a : A} (ha : isLocalElement F a) : isLocalElement F (f a) :=
  let ⟨B, ⟨_, haB⟩⟩ := ha
  let g : B →ₐ[F] A' := f.comp (B.val)
  ⟨g.range, ⟨.of_surjective' g.rangeRestrict (g.rangeRestrict_surjective),
    (AlgHom.mem_range g).mpr ⟨⟨a, haB⟩, rfl⟩⟩⟩

variable {F} in
/-- If a local element `a` of an `F`-algebra `A` is integral then
    it belongs to a finite-dimensional local `F`-subalgebra of `A`. -/
theorem isLocalElement_integral {a : A} (hi : IsIntegral F a) (hl : isLocalElement F a) :
    ∃ B : Subalgebra F A, LocalRing B ∧ FiniteDimensional F B ∧ a ∈ B :=
  haveI := FiniteDimensional.of_integral_adjoin hi
  let ⟨_, ⟨_, ha⟩⟩ := hl
  ⟨Algebra.adjoin F {a}, ⟨.of_subalgebra' F (Algebra.adjoin_le (Set.singleton_subset_iff.mpr ha))
      (fun a' ↦ IsUnit.of_nonzerodivisor_of_integral F (.of_finite F a')),
    .of_integral_adjoin hi,
    Algebra.subset_adjoin (Set.mem_singleton a)⟩⟩

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
  have hsub : f '' lA ⊆ lA' := fun y ⟨x, ⟨hx, hfxy⟩⟩ ↦ hfxy ▸ isLocalElement_map F f hx
  replace hsub : (Submodule.span F lA).map f ≤ Submodule.span F lA' :=
    Set.Subset.trans
      (Submodule.image_span_subset_span f lA)
      (Submodule.span_mono hsub)
  exact top_le_iff.mp <| LinearMap.range_eq_top.mpr hf ▸ Submodule.map_top f ▸ h ▸ hsub

variable {K₁ K₂ : Type u} [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂]

/-- If `(a₁, a₂) : K₁ × K₂` is local then `minpoly F a₁ = minpoly F a₂` -/
lemma local_minpoly_eq {a₁ : K₁} {a₂ : K₂} (hi : IsIntegral F (a₁, a₂)) (hl : isLocalElement F (a₁, a₂)) :
    minpoly F a₁ = minpoly F a₂ := by
  let μ₁ := minpoly F a₁
  have ha₁ : IsIntegral F a₁ := IsIntegral.map (AlgHom.fst F K₁ K₂) hi
  obtain ⟨B, ⟨_, _, ha⟩⟩ := isLocalElement_integral hi hl
  haveI : IsArtinianRing B := isArtinian_of_tower F (inferInstance : IsArtinian F B)
  haveI : IsReduced B := isReduced_of_injective B.toSubring.subtype (by apply Subtype.coe_injective)
  letI := (artinian_reduced_local_is_field B).toField
  let a : B := ⟨(a₁, a₂), ha⟩
  let f₁ := (AlgHom.fst F K₁ K₂).comp (B.val) /- projection `R →ₐ[F] K₁` -/
  let f₂ := (AlgHom.snd F K₁ K₂).comp (B.val) /- projection `R →ₐ[F] K₂` -/
  have hf₁μ₁a := Polynomial.aeval_algHom_apply f₁ a μ₁
  rw [show f₁ a = a₁ by rfl, minpoly.aeval] at hf₁μ₁a
  /- `hf₁μ₁a : f₁ (μ₁ a) = 0` -/
  have hμ₁a0 /- `μ₁ a = 0` -/ := (map_eq_zero f₁).mp hf₁μ₁a.symm
  have hμ₁a₂0 := Polynomial.aeval_algHom_apply f₂ a μ₁
  rw [show f₂ a = a₂ by rfl, hμ₁a0, map_zero] at hμ₁a₂0
  /- `hμ₁a₂0 : μ₁ a₂ = 0` -/
  exact minpoly.eq_of_irreducible_of_monic
    (minpoly.irreducible ha₁)
    hμ₁a₂0
    (minpoly.monic ha₁)

/-- Generic theorem: given
      * `hPQ`: proof that `P F A` implies `Q F K` given a surjective `f : A →ₐ[F] K`;
      * `hKK`: proof that `K₁ × K₂` cannot be locally generated if `Q F K₁` and `Q F K₂`;
    an `F`-algebra `A` satisfying `P A` is local if it is locally generated. -/
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
  let f : A →ₐ[F] (K₁ × K₂) := AlgHom.mk' f' (by intro _ _; simp [Algebra.smul_def]; rfl)
  /- compose `f` with projections on `K₁`... -/
  let f₁ := (AlgHom.fst F K₁ K₂).comp f
  have hf₁ : Function.Surjective f₁ := by
    simpa using Function.Surjective.comp Prod.fst_surjective hf
  /- ... and `K₂` -/
  let f₂ := (AlgHom.snd F K₁ K₂).comp f
  have hf₂ : Function.Surjective f₂ := by
    simpa using Function.Surjective.comp Prod.snd_surjective hf
  exact hKK F K₁ K₂ (hPQ f₁ hf₁ h) (hPQ f₂ hf₂ h) (isLocallyGenerated_surjective F f hf hLG)
