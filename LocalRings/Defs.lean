import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Ideal.QuotientOperations

import Mathlib.Tactic

variable {R : Type*}
variable [CommRing R]

/-- Product of two non-trivial rings is not a local ring. -/
theorem nonLocalRing_if_prod_of_2 {S : Type*} [CommRing S] [Nontrivial R] [Nontrivial S] :
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

/-- A ring `R` is local iff all ring homomorphism from `R` to a product of two fields
    are not surjective. -/
theorem nonLocalRing_iff_image_prod_of_2_fields {R : Type u} [CommRing R] [Nontrivial R] :
    (∀ {K₁ K₂ : Type u} [Field K₁] [Field K₂] (f : R →+* K₁ × K₂), ¬Function.Surjective f) ↔ LocalRing R := by
  apply Iff.intro
  · /- get two maximal ideals and project -/
    intro h
    by_contra hNonLocalR
    obtain ⟨a, ⟨hnua, hnub⟩⟩ := nonLocalDef hNonLocalR
    have hnua1 : a ∈ nonunits R := by rwa [←mem_nonunits_iff] at hnua
    have hnub1 : 1 - a ∈ nonunits R := by rwa [←mem_nonunits_iff] at hnub
    obtain ⟨m₁, ⟨hm1max, ham⟩⟩ := exists_max_ideal_of_mem_nonunits hnua1
    obtain ⟨m₂, ⟨hm2max, hbm⟩⟩ := exists_max_ideal_of_mem_nonunits hnub1
    have coprime : IsCoprime m₁ m₂ := by
      rw [Ideal.isCoprime_iff_exists]
      use a, ham, 1 - a, hbm
      ring
    let e := Ideal.quotientInfEquivQuotientProd m₁ m₂ coprime
    have he := e.surjective
    let g := Ideal.Quotient.mk (m₁ ⊓ m₂)
    have hg : Function.Surjective g := Ideal.Quotient.mk_surjective
    -- let K₁ := R / m₁ -- does not work?
    let K₁ := @HasQuotient.Quotient R (Ideal R) Ideal.instHasQuotient m₁
    let K₂ := @HasQuotient.Quotient R (Ideal R) Ideal.instHasQuotient m₂
    let fK₁ : Field K₁ := Ideal.Quotient.field m₁
    let fK₂ : Field K₂ := Ideal.Quotient.field m₂
    let f := RingHom.comp (e : R ⧸ m₁ ⊓ m₂ →+* K₁ × K₂) g
    have hf := Function.Surjective.comp he hg -- f is surjective
    have contra_hf := @h K₁ K₂ fK₁ fK₂ f -- f is not surjective
    rw [RingHom.coe_comp, RingHom.coe_coe] at contra_hf
    exact contra_hf hf
  · intro hlocalR
    by_contra h
    push_neg at h
    obtain ⟨f, hfs⟩ := h
    exact nonLocalRing_if_prod_of_2 (LocalRing.of_surjective' f hfs)

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
  --apply LocalRing.isUnit_or_isUnit_one_sub_self
  obtain ⟨aa, haa⟩ := subring_rep haB
  have hbb : (1 - aa : B) = 1 - a := by simp [haa]
  exact Or.imp (unit_sub haa) (unit_sub hbb) (by apply LocalRing.isUnit_or_isUnit_one_sub_self)

/-- A homomorphism of rings maps local elements to local elements. -/
theorem isLocal_of_map_local {S : Type*} [Nontrivial S] [CommRing S]
    {a : R} (ha : isLocalElement a) (f : R →+* S) : isLocalElement (f a) := by
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

variable {F A : Type*}
variable [Field F] [CommRing A] [Algebra F A]

/-- All scalars in an `F`-algebra are local. -/
theorem scalar_is_local {a : A} [Nontrivial A] (ha : a ∈ (⊥ : Subalgebra F A)) : isLocalElement a := by
  use (⊥ : Subalgebra F A).toSubring
  apply And.intro
  · exact (Algebra.botEquivOfInjective (algebraMap F A).injective).toRingEquiv.symm.localRing
  · assumption
