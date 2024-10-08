import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Ring.Hom.Defs

import Mathlib.LinearAlgebra.Prod

import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Trace.Basic

import LocalRings.Utils.Module
import LocalRings.Utils.PurelyInseparable
import LocalRings.Utils.Ring

variable (F : Type u)
variable {A A' : Type u}
variable [Field F] [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A']

/-- An element `a` of an `F`-algebra `A` is *local* iff
    it belongs to a local `F`-subalgebra of `A`. -/
def isLocalElement (a : A) : Prop :=
  ∃ B : Subalgebra F A, LocalRing B ∧ a ∈ B

/-- In a local ring, all elements are local -/
theorem all_local_if_local [LocalRing A] (a : A) : isLocalElement F a := by
  use ⊤
  apply And.intro
  · exact (Subsemiring.topEquiv : (⊤ : Subsemiring A) ≃+* A).symm.localRing
  · exact Subsemiring.mem_top a

/-- If all elements of a ring are local then the ring is local. -/
theorem local_if_all_local [Nontrivial A] (ha : ∀ a : A, isLocalElement F a) : LocalRing A := by
  apply LocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  -- a is local so there is B : Subring R, LocalRing B ∧ a ∈ B,
  obtain ⟨B, ⟨hB, haB⟩⟩ := ha a
  -- if `a` is a unit in `B`, then it is a unit in `R`
  -- if `1 - a` is a unit in `B`, then it is a unit in `R`
  let aa : B := ⟨a, haB⟩
  let bb : B := 1 - aa
  exact Or.imp
    (isUnit_subring (S := B.toSubring) (a := aa))
    (isUnit_subring (S := B.toSubring) (a := bb))
    (by apply LocalRing.isUnit_or_isUnit_one_sub_self aa)

/-- A homomorphism of rings maps local elements to local elements. -/
theorem isLocalElement_map [Nontrivial A'] (f : A →ₐ[F] A')
    {a : A} (ha : isLocalElement F a) : isLocalElement F (f a) := by
  -- B := local subalgebra containing a
  obtain ⟨B, ⟨hB, haB⟩⟩ := ha
  -- g : ↥B →+* A'
  let g := f.comp (B.val)
  use g.range
  apply And.intro
  · -- goal: `g.range` is a local ring
    exact LocalRing.of_surjective' g.rangeRestrict (g.rangeRestrict_surjective)
  · -- goal: `f a ∈ g.range`
    rw [AlgHom.mem_range, Subtype.exists]
    use a, haB
    rfl

/-- An `F`-algebra `A` is *locally generated* if the local elements of `A`
    generate `A` as a vector space over `F`. -/
def isLocallyGenerated (A : Type u) [CommRing A] [Algebra F A] : Prop :=
  Submodule.span F {a : A | isLocalElement F a} = ⊤

/-- If `F`-algebra `A` is locally generated and `f : A → A'` is a surjective `F`-algebra
    homomorphism, then `F`-algebra `B` is also locally generated. -/
lemma isLocallyGenerated_surjective [Nontrivial A'] (f : A →ₐ[F] A')
    (hf : Function.Surjective f) (h : isLocallyGenerated F A) : isLocallyGenerated F A' := by
  let lA := {a : A | isLocalElement F a}
  let lA' := {a' : A' | isLocalElement F a'}
  have h1 : f '' lA ⊆ lA' := by
    intro y hy
    obtain ⟨x, ⟨hx, hfxy⟩⟩ := hy
    rw [Set.mem_setOf_eq, ← hfxy] at *
    exact isLocalElement_map F f hx
  have h2 : (Submodule.span F lA).map f ≤ Submodule.span F lA' :=
    span_transfer (f := f.toLinearMap) h1
  rwa [h, Submodule.map_top, LinearMap.range_eq_top.mpr hf, top_le_iff] at h2

variable {K₁ K₂ : Type u} [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂]

/-- Generic theorem: given
      * `hPQ`: proof that `P F A` implies `Q F K` given a surjective `f : A →ₐ[F] K`
      * `hKK`: proof that `K₁ × K₂` is not locally generated if `Q F K₁` and `Q F K₂`
    an `F`-algebra `A` is local if it satisfies `P A` and is locally generated. -/
theorem isLocalRing_if_isLocallyGenerated [Nontrivial A]
    {Q : ∀ (F K : Type u) [Field F] [Field K] [Algebra F K], Prop}
    {P : ∀ (F A : Type u) [Field F] [CommRing A] [Algebra F A], Prop}
    (hPQ : ∀ {F A K : Type u} [Field F] [CommRing A] [Algebra F A] [Field K] [Algebra F K] (f : A →ₐ[F] K),
      Function.Surjective f → P F A → Q F K)
    (hKK : ∀ (F : Type u) [Field F] (K₁ K₂ : Type u) [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂],
      Q F K₁ → Q F K₂ → ¬isLocallyGenerated F (K₁ × K₂))
    (h : P F A) (hLG : isLocallyGenerated F A) : LocalRing A := by
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
  exact hKK F K₁ K₂ (hPQ f₁ hf₁ h) (hPQ f₂ hf₂ h) (isLocallyGenerated_surjective F f hf hLG)

section FiniteDimensional

variable [FiniteDimensional F K₁] [FiniteDimensional F K₂]

/-- If `(a₁, a₂) : K₁ × K₂` is local then `minpoly F a₁ = minpoly F a₂` -/
lemma local_minpoly_eq (a₁ : K₁) (a₂ : K₂) (h1 : isLocalElement F (a₁, a₂)) :
    minpoly F a₁ = minpoly F a₂ := by
  let μ₁ := minpoly F a₁
  have int_a₁ : IsIntegral F a₁ := IsIntegral.of_finite F a₁
  obtain ⟨R, ⟨_, ha⟩⟩ := h1
  haveI : IsArtinianRing R := isArtinian_of_tower F (inferInstance : IsArtinian F R)
  haveI : IsReduced R := isReduced_of_injective R.toSubring.subtype (by apply Subtype.coe_injective)
  letI := (artinian_reduced_local_is_field R).toField
  let a : R := ⟨(a₁, a₂), ha⟩
  let f₁ := (AlgHom.fst F K₁ K₂).comp (R.val) /- projection `R →ₐ[F] K₁` -/
  let f₂ := (AlgHom.snd F K₁ K₂).comp (R.val) /- projection `R →ₐ[F] K₂` -/
  have hf₁a : f₁ a = a₁ := by rfl
  have hf₂a : f₂ a = a₂ := by rfl
  have hf₁μ₁a := Polynomial.aeval_algHom_apply f₁ a μ₁
  rw [hf₁a, minpoly.aeval] at hf₁μ₁a
  /- `hf₁μ₁a : f₁ (μ₁ a) = 0` -/
  have hμ₁a0 /- `μ₁ a = 0` -/ := (map_eq_zero f₁).mp hf₁μ₁a.symm
  have hμ₁a₂0 := Polynomial.aeval_algHom_apply f₂ a μ₁
  rw [hf₂a, hμ₁a0, map_zero] at hμ₁a₂0
  /- `hμ₁a₂0 : μ₁ a₂ = 0` -/
  exact minpoly.eq_of_irreducible_of_monic
    (minpoly.irreducible int_a₁)
    hμ₁a₂0
    (minpoly.monic int_a₁)

def UFiniteDimensional (F A : Type u) [Field F] [CommRing A] [Algebra F A] : Prop := FiniteDimensional F A

/-- For finite extensions `K₁`, `K₂` of `F`, the `F`-algebra `K₁ × K₂`
    is not locally generated. -/
theorem notLocallyGenerated_KK_if_findim (K₁ K₂ : Type u)
    [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂] :
    UFiniteDimensional F K₁ → UFiniteDimensional F K₂ → ¬isLocallyGenerated F (K₁ × K₂) := by
  intro fdK₁ fdK₂ h
  haveI : FiniteDimensional F K₁ := fdK₁
  haveI : FiniteDimensional F K₂ := fdK₂
  let E₁ := separableClosure F K₁
  let E₂ := separableClosure F K₂
  haveI : IsPurelyInseparable E₁ K₁ := separableClosure.isPurelyInseparable F K₁
  haveI : IsPurelyInseparable E₂ K₂ := separableClosure.isPurelyInseparable F K₂
  letI p := ringExpChar F
  haveI : ExpChar F p := inferInstance
  let r₁ : ℕ := finInsepLogRank E₁ K₁ p
  let r₂ : ℕ := finInsepLogRank E₂ K₂ p
  let r := max r₁ r₂
  let s₁ : ℕ := r - r₁
  let s₂ : ℕ := r - r₂
  have hrs₁ : r₁ + s₁ = r := by simp only [s₁, add_tsub_cancel_of_le (le_max_left r₁ r₂)]
  have hrs₂ : r₂ + s₂ = r := by simp only [s₂, add_tsub_cancel_of_le (le_max_right r₁ r₂)]
  let b₁ := FiniteDimensional.finrank F E₁
  let b₂ := FiniteDimensional.finrank F E₂
  let d : ℕ := Nat.gcd b₁ b₂
  have hd : 0 < d := by
    apply Nat.gcd_pos_of_pos_left
    apply FiniteDimensional.finrank_pos
  let a₁' := b₁ / d
  let a₂' := b₂ / d
  have a_coprime : Nat.gcd a₁' a₂' = 1 := by
    have := Nat.gcd_div (Nat.gcd_dvd_left b₁ b₂) (Nat.gcd_dvd_right b₁ b₂)
    rw [Nat.div_self hd] at this
    exact this
  let a₁ := (a₁' : F)
  let a₂ := (a₂' : F)
  have a_nonzero : a₁ ≠ 0 ∨ a₂ ≠ 0 := by
    by_contra h1
    push_neg at h1
    /- The following is simpler but requires `p : ℕ` and `ExpChar F p` as parameters:
    rcases ‹ExpChar F p› with _ | ⟨hprime⟩
    · simp [Nat.cast_eq_zero] at h1
      simp [h1.1, h1.2] at a_coprime
    · simp only [CharP.cast_eq_zero_iff F p] at h1
      rw [← Nat.dvd_gcd_iff, a_coprime, Nat.dvd_one] at h1
      rw [h1] at hprime
      contradiction
    --/
    by_cases h : p = 1
    · haveI := ExpChar.congr F p h
      haveI := charZero_of_expChar_one' F
      simp [a₁, a₂, Nat.cast_eq_zero] at h1
      simp [h1.1, h1.2] at a_coprime
    · haveI := charP_of_expChar_prime' (R := F) h
      simp only [CharP.cast_eq_zero_iff F p] at h1
      rw [← Nat.dvd_gcd_iff, a_coprime, Nat.dvd_one] at h1
      exact h h1

  let σ := iterateFrobenius F p r
  let T₁ : K₁ × K₂ →ₛₗ[σ] F := by
    simp [σ]
    rw [← hrs₁]
    exact ((Algebra.trace F E₁).comp (iRed_frobₛₗ F E₁ K₁ p s₁)).comp (LinearMap.fst F K₁ K₂)
  -- will try to reduce this duplication
  let T₂ : K₁ × K₂ →ₛₗ[σ] F := by
    simp [σ]
    rw [← hrs₂]
    exact ((Algebra.trace F E₂).comp (iRed_frobₛₗ F E₂ K₂ p s₂)).comp (LinearMap.snd F K₁ K₂)
  let T : K₁ × K₂ →ₛₗ[σ] F := a₁ • T₁ - a₂ • T₂
  let U : Subspace F (K₁ × K₂) := LinearMap.ker T
  /-
    Things to show:
      1. `T ≠ 0`
      2. `T` vanishes on local elements (so all local elements are in `U`)
   -/
  sorry

/-- Finite algebras are local if they are locally generated. -/
theorem isLocalRing_if_isLocallyGenerated_findim [Nontrivial A]
    (h : UFiniteDimensional F A) (hLG : isLocallyGenerated F A) : LocalRing A := by
  refine isLocalRing_if_isLocallyGenerated F ?_ notLocallyGenerated_KK_if_findim h hLG
  intro _ _ _ _ _ _ _ _ f hf hA
  exact hA.of_surjective f hf

end FiniteDimensional
