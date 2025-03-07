import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Ring.Prod
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.Subring
import Mathlib.RingTheory.Trace.Basic

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

variable (F : Type*)
variable {A A' : Type*}
variable [Field F] [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A']

/-- An element `a` of an `F`-algebra `A` is *local* iff
    it belongs to a local `F`-subalgebra of `A`. -/
def isLocalElement (a : A) : Prop :=
  ∃ B : Subalgebra F A, IsLocalRing B ∧ a ∈ B

/-- In a local `F`-algebra, all elements are local -/
theorem all_local_if_local [IsLocalRing A] (a : A) : isLocalElement F a :=
  ⟨⊤, ⟨Subsemiring.topEquiv.symm.isLocalRing, Subsemiring.mem_top a⟩⟩

/-- If all elements of an `F`-algebra are local then the algebra is local. -/
theorem local_if_all_local [Nontrivial A] (ha : ∀ a : A, isLocalElement F a) : IsLocalRing A :=
  .of_isUnit_or_isUnit_one_sub_self fun a ↦ let ⟨B, ⟨_, haB⟩⟩ := ha a;
    Or.imp
      (IsUnit.map B.subtype)
      (IsUnit.map B.subtype)
      (IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨a, haB⟩ : B))

variable {F}

/-- A power of a local element is a local element. -/
theorem isLocalElement_pow {a : A} (ha : isLocalElement F a) (n : ℕ) : isLocalElement F (a ^ n) :=
  let ⟨B, ⟨hB, haB⟩⟩ := ha
  ⟨B, ⟨hB, B.pow_mem haB n⟩⟩

/-- A homomorphism of algebras maps local elements to local elements. -/
theorem isLocalElement_map [Nontrivial A'] (f : A →ₐ[F] A')
    {a : A} (ha : isLocalElement F a) : isLocalElement F (f a) :=
  let ⟨B, ⟨_, haB⟩⟩ := ha
  let g : B →ₐ[F] A' := f.comp (B.val)
  ⟨g.range, ⟨.of_surjective' (R := B) g.rangeRestrict (g.rangeRestrict_surjective),
    g.mem_range.mpr ⟨⟨a, haB⟩, rfl⟩⟩⟩

/-- If a local element `a` of an `F`-algebra `A` is integral then
    it belongs to a finite-dimensional local `F`-subalgebra of `A`. -/
theorem isLocalElement_integral {a : A} (hi : IsIntegral F a) (hl : isLocalElement F a) :
    ∃ B : Subalgebra F A, IsLocalRing B ∧ FiniteDimensional F B ∧ a ∈ B :=
  let B := Algebra.adjoin F {a}
  haveI hfd := Algebra.finite_adjoin_simple_of_isIntegral hi
  have hu (b : B) := IsArtinianRing.isUnit_of_isIntegral_of_nonZeroDivisor (IsIntegral.of_finite F b)
  let ⟨_, ⟨_, ha⟩⟩ := hl
  ⟨B, ⟨.of_subring' (Algebra.adjoin_le (Set.singleton_subset_iff.mpr ha)) fun b ↦ hu b,
    hfd, Algebra.self_mem_adjoin_singleton F a⟩⟩

variable (F A) in
/-- Set of all local elements of an `F`-algebra `A`. -/
def localElements : Set A := {a : A | isLocalElement F a}

variable (F A) in
/-- An `F`-algebra `A` is *locally generated* if the local elements of `A`
    generate `A` as a vector space over `F`. -/
def isLocallyGenerated : Prop := Submodule.span F (localElements F A) = ⊤

/-- If `F`-algebra `A` is locally generated and `f : A →ₐ[F] A'` is a surjective `F`-algebra
    homomorphism, then `F`-algebra `A'` is also locally generated. -/
lemma isLocallyGenerated_surjective [Nontrivial A'] {f : A →ₐ[F] A'}
    (hf : Function.Surjective f) (h : isLocallyGenerated F A) : isLocallyGenerated F A' := by
  let lA := localElements F A
  let lA' := localElements F A'
  have hsub : f '' lA ⊆ lA' := fun y ⟨x, ⟨hx, hfxy⟩⟩ ↦ hfxy ▸ isLocalElement_map f hx
  replace hsub : (Submodule.span F lA).map f ≤ Submodule.span F lA' :=
    Set.Subset.trans
      (Submodule.image_span_subset_span f lA)
      (Submodule.span_mono hsub)
  exact top_le_iff.mp <| LinearMap.range_eq_top.mpr hf ▸ Submodule.map_top f ▸ h ▸ hsub

/-- If `(a₁, a₂) : K₁ × K₂` is local then `minpoly F a₁ = minpoly F a₂`. -/
lemma local_minpoly_eq {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂]
    {a : K₁ × K₂} (hi : IsIntegral F a) (hl : isLocalElement F a) :
    minpoly F a.1 = minpoly F a.2 := by
  let μ₁ := minpoly F a.1
  obtain ⟨B, ⟨_, _, ha⟩⟩ := isLocalElement_integral hi hl
  haveI : IsArtinianRing B := isArtinian_of_tower F inferInstance
  haveI : IsReduced B := isReduced_of_injective B.toSubring.subtype (by apply Subtype.coe_injective)
  letI : Field B := IsArtinianRing.isField_of_isReduced_of_isLocalRing B |>.toField
  let a' : B := ⟨a, ha⟩
  let f₁ := (AlgHom.fst F K₁ K₂).comp (B.val) /- projection `B →ₐ[F] K₁` -/
  let f₂ := (AlgHom.snd F K₁ K₂).comp (B.val) /- projection `B →ₐ[F] K₂` -/
  have := μ₁.aeval_algHom_apply f₁ a'
  have : f₁ (μ₁.aeval a') = 0 := (minpoly.aeval F a.1 ▸ μ₁.aeval_algHom_apply f₁ a').symm
  have : μ₁.aeval a' = 0 := (map_eq_zero f₁).mp this
  have : μ₁.aeval a.2 = 0 := map_zero f₂ ▸ this ▸ μ₁.aeval_algHom_apply f₂ a'
  have ha1int : IsIntegral F a.1 := hi.map (AlgHom.fst F K₁ K₂)
  exact minpoly.eq_of_irreducible_of_monic
    (minpoly.irreducible ha1int)
    this
    (minpoly.monic ha1int)

universe u v

/-- For a non-local ring, there exists a surjection onto product of two fields. -/
lemma nonLocalProj {R : Type u} [CommRing R] [Nontrivial R] (h : ¬IsLocalRing R) :
    ∃ (K₁ K₂ : Type u) (_ : Field K₁) (_ : Field K₂) (f : R →+* K₁ × K₂),
      Function.Surjective f := by
  /- get two different maximal ideals and project on the product of quotients -/
  obtain ⟨a, ⟨hnua, hnub⟩⟩ :=
    (exists_congr fun x : R ↦ not_or).mp <|
      not_forall.mp (h ∘ .of_isUnit_or_isUnit_one_sub_self)
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

/-- Generic theorem: given
      * `hPQ`: proof that `P F A` implies `Q F K` for a surjective `f : A →ₐ[F] K`;
      * `hKK`: proof that `K₁ × K₂` cannot be locally generated if `Q F K₁` and `Q F K₂`;
    an `F`-algebra `A` satisfying `P F A` is local if it is locally generated. -/
theorem isLocalAlgebra_if_isLocallyGenerated {F : Type u} {A : Type v}
    [Field F] [CommRing A] [Nontrivial A] [Algebra F A]
    {Q : ∀ (F) (K : Type v) [Field F] [Field K] [Algebra F K], Prop}
    {P : ∀ (F A) [Field F] [CommRing A] [Algebra F A], Prop}
    (hPQ : ∀ {F A K} [Field F] [CommRing A] [Algebra F A] [Field K] [Algebra F K]
      (f : A →ₐ[F] K), Function.Surjective f → P F A → Q F K)
    (hKK : ∀ (F) {K₁ K₂} [Field F] [Field K₁] [Field K₂]
      [Algebra F K₁] [Algebra F K₂], Q F K₁ → Q F K₂ → ¬isLocallyGenerated F (K₁ × K₂))
    (h : P F A) (hLG : isLocallyGenerated F A) : IsLocalRing A := by
  by_contra hNonLocalA
  let ⟨K₁, K₂, fK₁, fK₂, f', hf'⟩ := nonLocalProj hNonLocalA
  /- introduce compatible `F`-algebra structures -/
  let algK₁ : Algebra F K₁ := RingHom.fst K₁ K₂ |>.comp f' |>.comp (algebraMap F A) |>.toAlgebra
  let algK₂ : Algebra F K₂ := RingHom.snd K₁ K₂ |>.comp f' |>.comp (algebraMap F A) |>.toAlgebra
  /- promote `f'` to an `F`-algebra homomorphism -/
  let f : A →ₐ[F] (K₁ × K₂) := ⟨f', fun _ ↦ rfl⟩
  have hf : Function.Surjective f := hf'
  /- compose `f` with projections on `K₁`... -/
  let f₁ := (AlgHom.fst F K₁ K₂).comp f
  have hf₁ : Function.Surjective f₁ :=
    (AlgHom.fst F K₁ K₂).coe_comp f ▸ Function.Surjective.comp Prod.fst_surjective hf
  /- ... and `K₂` -/
  let f₂ := (AlgHom.snd F K₁ K₂).comp f
  have hf₂ : Function.Surjective f₂ :=
    (AlgHom.snd F K₁ K₂).coe_comp f ▸ Function.Surjective.comp Prod.snd_surjective hf
  exact hKK F (hPQ f₁ hf₁ h) (hPQ f₂ hf₂ h) (isLocallyGenerated_surjective hf hLG)
