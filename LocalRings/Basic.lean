import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Artinian.Algebra
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalRing.NonLocalRing
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.Subring

/-!
# Basic results about local elements and local rings.

## Main definitions

* `isLocalElement`: an element `a` of an `F`-algebra `A` is *local* iff
    it belongs to a local `F`-subalgebra of `A`.
* `localElements`: the set of all local elements in an `F`-algebra `A`.
* `isLocallyGenerated`: an `F`-algebra `A` is *locally generated* if
    the local elements of `A` generate `A` as a vector space over `F`.

## Main results

* `isLocalElement.integral`: if a local element `a` of an `F`-algebra `A` is
    integral then it belongs to a finite-dimensional local `F`-subalgebra of `A`.
* `isLocalRing_of_all_isLocalElement`: if all elements of an `F`-algebra are local then the algebra is local.
* `IsLocalRing.of_isLocallyGenerated`: generic theorem used to reduce: given
  * `P`, `Q`: properties of field extensions and commutative algebras, respectively;
  * `hPQ`: proof that `P F A` implies `Q F K` given a surjective `f : A →ₐ[F] K`;
  * `hKK`: proof that `K₁ × K₂` is not locally generated if `Q F K₁` and `Q F K₂`;
  an `F`-algebra `A` is local if it satisfies `P F A` and is locally generated.
-/

variable (F : Type*)
variable {A A' : Type*}
variable [Field F] [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A']

/-- An element `a` of an `F`-algebra `A` is *local* iff
    it belongs to a local `F`-subalgebra of `A`. -/
def isLocalElement (a : A) : Prop :=
  ∃ B : Subalgebra F A, IsLocalRing B ∧ a ∈ B

/-- In a local `F`-algebra, all elements are local -/
theorem isLocalElement.of_isLocalRing [IsLocalRing A] (a : A) : isLocalElement F a :=
  ⟨⊤, ⟨Subsemiring.topEquiv.symm.isLocalRing, Subsemiring.mem_top a⟩⟩

/-- If all elements of an `F`-algebra are local then the algebra is local. -/
theorem isLocalRing_of_all_isLocalElement [Nontrivial A] (ha : ∀ a : A, isLocalElement F a) : IsLocalRing A :=
  .of_isUnit_or_isUnit_one_sub_self
    fun a ↦ let ⟨B, ⟨_, haB⟩⟩ := ha a; (IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨a, haB⟩ : B)).imp
      (.map B.subtype) (.map B.subtype)

variable {F}

/-- A power of a local element is a local element. -/
theorem isLocalElement.pow {a : A} (ha : isLocalElement F a) (n : ℕ) : isLocalElement F (a ^ n) :=
  let ⟨B, ⟨hB, haB⟩⟩ := ha
  ⟨B, ⟨hB, B.pow_mem haB n⟩⟩

/-- A homomorphism of algebras maps local elements to local elements. -/
theorem isLocalElement.map [Nontrivial A'] (f : A →ₐ[F] A')
    {a : A} (ha : isLocalElement F a) : isLocalElement F (f a) :=
  let ⟨B, ⟨_, haB⟩⟩ := ha
  let g : B →ₐ[F] A' := f.comp (B.val)
  ⟨g.range, ⟨.of_surjective' (R := B) g.rangeRestrict (g.rangeRestrict_surjective),
    g.mem_range.mpr ⟨⟨a, haB⟩, rfl⟩⟩⟩

/-- If a local element `a` of an `F`-algebra `A` is integral then
    it belongs to a finite-dimensional local `F`-subalgebra of `A`. -/
theorem isLocalElement.integral {a : A} (hi : IsIntegral F a) (hl : isLocalElement F a) :
    ∃ B : Subalgebra F A, IsLocalRing B ∧ FiniteDimensional F B ∧ a ∈ B :=
  let B := Algebra.adjoin F {a}
  have hfd := Algebra.finite_adjoin_simple_of_isIntegral hi
  have hu (b : B) := IsArtinianRing.isUnit_of_isIntegral_of_nonZeroDivisor (.of_finite F b)
  let ⟨_, _, ha⟩ := hl
  ⟨B, .of_subring' (Algebra.adjoin_singleton_le ha) hu, hfd, Algebra.self_mem_adjoin_singleton F a⟩

/-- If `(a₁, a₂) : K₁ × K₂` is local then `minpoly F a₁ = minpoly F a₂`. -/
lemma isLocalElement.minpoly_eq_minpoly {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂]
    {a : K₁ × K₂} (hi : IsIntegral F a) (hl : isLocalElement F a) :
    minpoly F a.1 = minpoly F a.2 := by
  obtain ⟨B, ⟨_, _, ha⟩⟩ := hl.integral hi
  have : IsArtinianRing B := isArtinian_of_tower F inferInstance
  have : IsReduced B := isReduced_of_injective B.toSubring.subtype (by apply Subtype.coe_injective)
  let _ : Field B := IsArtinianRing.isField_of_isReduced_of_isLocalRing B |>.toField
  let a' : B := ⟨a, ha⟩
  let f₁ : B →ₐ[F] K₁ := (AlgHom.fst F K₁ K₂).comp (B.val)
  let f₂ : B →ₐ[F] K₂ := (AlgHom.snd F K₁ K₂).comp (B.val)
  simpa using (minpoly.algHom_eq f₁ f₁.injective a').trans (minpoly.algHom_eq f₂ f₂.injective a').symm

variable (F A) in
/-- Set of all local elements of an `F`-algebra `A`. -/
def localElements : Set A := {a : A | isLocalElement F a}

variable (F A) in
/-- An `F`-algebra `A` is *locally generated* if the local elements of `A`
    generate `A` as a vector space over `F`. -/
def isLocallyGenerated : Prop := Submodule.span F (localElements F A) = ⊤

/-- If `F`-algebra `A` is locally generated and `f : A →ₐ[F] A'` is a surjective `F`-algebra
    homomorphism, then `F`-algebra `A'` is also locally generated. -/
lemma isLocallyGenerated.map_surjective [Nontrivial A'] {f : A →ₐ[F] A'}
    (hf : Function.Surjective f) (h : isLocallyGenerated F A) : isLocallyGenerated F A' := by
  let lA := localElements F A
  let lA' := localElements F A'
  have hsub : f '' lA ⊆ lA' := fun y ⟨x, hx, hfxy⟩ ↦ hfxy ▸ hx.map f
  have htop := LinearMap.range_eq_top_of_surjective f hf ▸ Submodule.map_top f ▸ h ▸ Submodule.map_span f lA
  exact top_le_iff.mp <| htop ▸ Submodule.span_mono hsub

/-- Generic theorem: given
      * `P`, `Q`: properties of field extensions and commutative algebras, respectively;
      * `hPQ`: proof that `P F A` implies `Q F K` for a surjective `f : A →ₐ[F] K`;
      * `hKK`: proof that `K₁ × K₂` cannot be locally generated if `Q F K₁` and `Q F K₂`;
    an `F`-algebra `A` satisfying `P F A` is local if it is locally generated. -/
theorem IsLocalRing.of_isLocallyGenerated.{u} {F : Type*} {A : Type u}
    [Field F] [CommRing A] [Nontrivial A] [Algebra F A]
    {Q : ∀ (F) (K : Type u) [Field F] [Field K] [Algebra F K], Prop}
    {P : ∀ (F A) [Field F] [CommRing A] [Algebra F A], Prop}
    (hPQ : ∀ {F A K} [Field F] [CommRing A] [Algebra F A] [Field K] [Algebra F K]
      (f : A →ₐ[F] K), Function.Surjective f → P F A → Q F K)
    (hKK : ∀ (F) {K₁ K₂} [Field F] [Field K₁] [Field K₂]
      [Algebra F K₁] [Algebra F K₂], Q F K₁ → Q F K₂ → ¬isLocallyGenerated F (K₁ × K₂))
    (h : P F A) (hLG : isLocallyGenerated F A) : IsLocalRing A := by
  by_contra hNonLocalA
  let ⟨K₁, K₂, _, _, f', hf'⟩ := IsLocalRing.exists_surjective_of_not_isLocalRing hNonLocalA
  /- introduce compatible `F`-algebra structures -/
  let _ : Algebra F K₁ := RingHom.fst K₁ K₂ |>.comp f' |>.comp (algebraMap F A) |>.toAlgebra
  let _ : Algebra F K₂ := RingHom.snd K₁ K₂ |>.comp f' |>.comp (algebraMap F A) |>.toAlgebra
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
  exact hKK F (hPQ f₁ hf₁ h) (hPQ f₂ hf₂ h) (hLG.map_surjective hf)
