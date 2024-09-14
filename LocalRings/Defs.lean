import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.QuotientOperations

variable {R : Type*}
variable [CommRing R]

/-- Product of two non-trivial rings is not a local ring. -/
theorem nonLocalRing_if_prod_of_2 (R S : Type u) [CommRing R] [CommRing S] [Nontrivial R] [Nontrivial S] :
    ¬LocalRing (R × S) := by
  let a : R × S := ⟨1, 0⟩
  have hnua : ¬IsUnit a := by
    intro hua
    simpa using IsUnit.map (RingHom.snd R S) hua
  have hnub : ¬IsUnit (1 - a) := by
    intro hub
    simpa using IsUnit.map (RingHom.fst R S) hub
  intro hLocalRS
  simpa using Or.imp hnua hnub (LocalRing.isUnit_or_isUnit_one_sub_self a)

lemma nonLocalDef [Nontrivial R] (h : ¬LocalRing R) : ∃ a : R, ¬IsUnit a ∧ ¬IsUnit (1 - a) := by
  by_contra hn
  simp [not_exists, ←not_or] at hn
  exact h (LocalRing.of_isUnit_or_isUnit_one_sub_self hn)

lemma nonLocalProj {R : Type u} [CommRing R] [Nontrivial R] (h : ¬LocalRing R) :
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

/-- A ring `R` is local iff all ring homomorphism from `R` to a product of two fields
    are not surjective. -/
theorem nonLocalRing_iff_image_prod_of_2_fields {R : Type u} [CommRing R] [Nontrivial R] :
    (∀ (K₁ K₂ : Type u) [Field K₁] [Field K₂] (f : R →+* K₁ × K₂), ¬Function.Surjective f) ↔ LocalRing R := by
  apply Iff.intro
  · intro h
    by_contra hNonLocalR
    obtain ⟨K₁, K₂, fK₁, fK₂, f, hf⟩ := nonLocalProj hNonLocalR
    exact @h K₁ K₂ fK₁ fK₂ f hf
  · intro hlocalR
    by_contra h
    push_neg at h
    obtain ⟨K₁, K₂, _, _, f, hfs⟩ := h
    exact nonLocalRing_if_prod_of_2 K₁ K₂ (LocalRing.of_surjective' f hfs)

/-- An element `a` of a ring `R` is *local* iff
    it belongs to a local subring of `R`. -/
def isLocalElement (a : R) : Prop :=
  ∃ S : Subring R, LocalRing S ∧ a ∈ S

/-- In a local ring, all elements are local -/
theorem all_local_in_local [LocalRing R] (a : R) : isLocalElement a := by
  use ⊤
  apply And.intro
  · exact (Subsemiring.topEquiv : (⊤ : Subsemiring R) ≃+* R).symm.localRing
  · exact Subsemiring.mem_top a

lemma subring_rep {S : Subring R} {a : R} (ha : a ∈ S) : ∃ x : S, x = a := by
  rw [Subtype.exists]
  use a, ha

lemma unit_sub_coe {S : Subring R} (a : S) : IsUnit a → IsUnit (a : R) := by
  intro ha
  exact IsUnit.map S.subtype ha

lemma unit_sub {S : Subring R} {x : S} {a : R} (hax : x = a) : IsUnit x → IsUnit a := by
  intro hux
  have h : IsUnit (x : R) := unit_sub_coe x hux
  rw [hax] at h
  assumption

/-- If all elements of a ring are local then the ring is local. -/
theorem local_if_all_local [Nontrivial R] (ha : ∀ a : R, isLocalElement a) : LocalRing R := by
  apply LocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  -- a is local so there is B : Subring R, LocalRing B ∧ a ∈ B,
  obtain ⟨B, ⟨hB, haB⟩⟩ := ha a
  -- if `a` is a unit in `B`, then it is a unit in `R`
  -- if `1 - a` is a unit in `B`, then it is a unit in `R`
  obtain ⟨aa, haa⟩ := subring_rep haB
  have hbb : (1 - aa : B) = 1 - a := by simp [haa]
  exact Or.imp (unit_sub haa) (unit_sub hbb) (by apply LocalRing.isUnit_or_isUnit_one_sub_self)

/-- A homomorphism of rings maps local elements to local elements. -/
theorem isLocal_of_map_local {S : Type*} [Nontrivial S] [CommRing S] (f : R →+* S)
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

/-- All scalars in an `F`-algebra are local. -/
theorem scalar_is_local {a : A} [Nontrivial A] (ha : a ∈ (⊥ : Subalgebra F A)) : isLocalElement a := by
  use (⊥ : Subalgebra F A).toSubring
  apply And.intro
  · exact (Algebra.botEquivOfInjective (algebraMap F A).injective).toRingEquiv.symm.localRing
  · assumption

/-- An `F`-algebra `A` is *locally generated* if the local elements of `A`
    generate `A` as a vector space over `F`. -/
def isLocallyGenerated (F A : Type*) [Field F] [CommRing A] [Algebra F A] : Prop :=
  Submodule.span F {a : A | isLocalElement a} = ⊤

/- Auxilliary. TODO: move to `Utils.lean`? -/
lemma span_transfer {R M₁ M₂ : Type*} [CommRing R] [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] {S₁ : Set M₁} {S₂ : Set M₂} {f : M₁ →ₗ[R] M₂}
    (h : f '' S₁ ⊆ S₂) : (Submodule.span R S₁).map f ≤ Submodule.span R S₂ := by
  have h1 : Submodule.span R (f '' S₁) ≤ Submodule.span R S₂ := Submodule.span_mono h
  have h2 : (Submodule.span R S₁).map f ≤ Submodule.span R (f '' S₁) := by
    rw [Submodule.map_span_le]
    intro m hm
    exact (Submodule.subset_span : f '' S₁ ⊆ Submodule.span R (f '' S₁)) (Set.mem_image_of_mem f hm)
  exact Set.Subset.trans h2 h1

/-- If `F`-algebra `A` is locally generated and `f : A → B` is a surjective `F`-algebra
    homomorphism, then `F`-algebra `B` is also locally generated. -/
lemma locallyGenerated_surjective {B : Type*} [CommRing B] [Nontrivial B] [Algebra F B] (f : A →ₐ[F] B)
    (hf : Function.Surjective f) (h : isLocallyGenerated F A) : isLocallyGenerated F B := by
  let lA := {a : A | isLocalElement a}
  let lB := {b : B | isLocalElement b}
  have h1 : f '' lA ⊆ lB := by
    intro y hy
    obtain ⟨x, ⟨hx, hfxy⟩⟩ := hy
    rw [Set.mem_setOf_eq, ← hfxy] at *
    exact isLocal_of_map_local f.toRingHom hx
  have h2 : (Submodule.span F lA).map f ≤ Submodule.span F lB :=
    span_transfer (f := f.toLinearMap) h1
  rwa [h, Submodule.map_top, LinearMap.range_eq_top.mpr hf, top_le_iff] at h2

/-- Transfer `R`-algebra structure via ring homomorphism. -/
def algebra_fromRingHom {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [Algebra R A] (f : A →+* B) : Algebra R B :=
  (f.comp (algebraMap R A)).toAlgebra

variable {K₁ K₂ : Type u} [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂]

/-- Property of two field extenstions `K₁`, `K₂` of `F`:
    if both satisfy `Q`, then `K₁ × K₂` is not locally generated over `F`. -/
def notLocallyGeneratedKK_if (Q : Type u → Prop) (F K₁ K₂ : Type u)
    [Field F] [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂] : Prop :=
    Q K₁ → Q K₂ → ¬isLocallyGenerated F (K₁ × K₂)

/-- Generic form: given
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
  exact hKK F K₁ K₂ (hPQ f₁ hf₁ h) (hPQ f₂ hf₂ h) (locallyGenerated_surjective f hf hLG)

/-- For finite fields `K₁`, `K₂` extending `F`, the `F`-algebra `K₁ × K₂`
    is not locally generated. -/
theorem notLocallyGenerated_KK_ifFinite (F K₁ K₂ : Type u)
    [Field F] [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂] :
    notLocallyGeneratedKK_if Finite F K₁ K₂ := by
  intro hfK₁ hfK₂ h
  sorry

theorem isLocalRing_if_isLocallyGenerated_finite [Nontrivial A]
    (h : Finite A) (hLG : isLocallyGenerated F A) : LocalRing A := by
  refine isLocalRing_if_isLocallyGenerated ?_ notLocallyGenerated_KK_ifFinite h hLG
  intro _ _ _ _ _ _ _ _ f hf hA
  exact hA.of_surjective f hf
