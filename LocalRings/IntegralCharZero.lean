import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Ring.Hom.Defs

import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.SeparableClosure

import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Prod

import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Nilpotent.Defs

import LocalRings.Basic
import LocalRings.Utils.PurelyInseparable
import LocalRings.Utils.Trace

/-!
# Results for integral (algebraic) algebras

## Main definitions

* `absoluteTrace`: a non-trivial linear map `algebraicClosure F →ₗ[F] F`
  in characteristic `0`.

## Main results

* `isLocalRing_if_isLocallyGenerated_integral`: an integral (equivalently algebraic)
    algebra is local if it is locally generated.
-/

universe u

section Integral

variable (F A : Type u) [Field F] [CommRing A] [Algebra F A]
variable {K₁ K₂ : Type u} [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂]

open scoped IntermediateField /- `F⟮a⟯` notation for simple field adjoin -/

section Trace

variable (F K : Type u) [Field F] [Field K] [Algebra F K]

/-- Absolute trace function from an algebraic extension `K` to the base field `F`. -/
noncomputable def absoluteTrace' : K → F :=
    fun a ↦ (Module.finrank F F⟮a⟯ : F)⁻¹ *
      Algebra.trace F F⟮a⟯ (IntermediateField.AdjoinSimple.gen F a)

section FiniteDimensional

/-- The absolute trace from a finite-dimensional extension `E` of `F` to `F`
    is the trace map scaled by `[E : F]`.
    This version accepts an argument from `E`. -/
lemma absoluteTrace_eq_findim [CharZero F] {E : Type u} [Field E] [Algebra F E] [FiniteDimensional F E] (a : E) :
    absoluteTrace' F E a =
      (Module.finrank F E : F)⁻¹ * Algebra.trace F E a := by
  rw [trace_eq_trace_adjoin F a, ← Module.finrank_mul_finrank F F⟮a⟯ E]
  simp [absoluteTrace']
  rw [mul_comm (Module.finrank F⟮a⟯ E : F)⁻¹, mul_assoc,
    inv_mul_cancel_left₀ <| Nat.cast_ne_zero.mpr <| Nat.ne_zero_iff_zero_lt.mpr <|
      Module.finrank_pos (R := F⟮a⟯) (M := E)]

/-- The absolute trace from a finite-dimensional extension `E` of `F` to `F`
    is the trace map scaled by `[E : F]`. -/
lemma absoluteTrace_eq_findim' [CharZero F] {E : Type u} [Field E] [Algebra F E] [FiniteDimensional F E] :
    absoluteTrace' F E = (Module.finrank F E : F)⁻¹ • (Algebra.trace F E) :=
  funext (absoluteTrace_eq_findim F)

end FiniteDimensional

/-- The absolute trace transfers via (injective) maps. -/
lemma absoluteTrace_map_eq {E : Type u} [Field E] [Algebra F E] (f : E →ₐ[F] K) (a : E) :
    absoluteTrace' F K (f a) = absoluteTrace' F E a := by
  have he := Set.image_singleton ▸ IntermediateField.adjoin_map F {a} f
  let e := (F⟮a⟯.equivMap f).trans (IntermediateField.equivOfEq he)
  simp [absoluteTrace']
  rw [← LinearEquiv.finrank_eq e.toLinearEquiv]
  apply congrArg
  exact Algebra.trace_eq_of_algEquiv e (IntermediateField.AdjoinSimple.gen F a)

/-- The absolute trace transfers via restriction to a subextension. -/
lemma absoluteTrace_map_eq' {E : IntermediateField F K} (a : E) :
    absoluteTrace' F K a = absoluteTrace' F E a :=
  absoluteTrace_map_eq F K E.val a

variable {F} in
/-- The absolute trace map `absoluteTrace' F F` is identity. -/
theorem absoluteTrace_scalar (a : F) : absoluteTrace' F F a = a := by
  simp [absoluteTrace']
  have hbot : F⟮a⟯ = ⊥ := IntermediateField.adjoin_simple_eq_bot_iff.mpr <|
      Subalgebra.algebraMap_mem (⊥ : Subalgebra F F) a
  have hrank1 : Module.finrank F F⟮a⟯ = 1 := hbot ▸ IntermediateField.finrank_bot
  have hrank1' := one_mul (Module.finrank F⟮a⟯ F) ▸
    hrank1 ▸ Module.finrank_self F ▸ Module.finrank_mul_finrank F F⟮a⟯ F
  simp [hrank1]
  have htr := hrank1' ▸ trace_eq_trace_adjoin F a
  simp at htr
  exact htr.symm.trans (trace_self a)

/-- The absolute trace map is a left inverse of the algebra map. -/
theorem absoluteTrace_algebraMap (a : F) : absoluteTrace' F K (algebraMap F K a) = a :=
  (Algebra.ofId_apply K a ▸
    absoluteTrace_map_eq F K (Algebra.ofId F K) a).trans (absoluteTrace_scalar a)


variable [CharZero F] [Algebra.IsIntegral F K]

/-- The absolute trace is additive. -/
theorem absoluteTrace_add (a b : K) :
    absoluteTrace' F K (a + b) = absoluteTrace' F K a + absoluteTrace' F K b := by
  let E := F⟮a⟯ ⊔ F⟮b⟯ /- `let E := F⟮a, b⟯` causes more problems -/
  haveI : FiniteDimensional F F⟮a⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  haveI : FiniteDimensional F F⟮b⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral b)
  haveI : FiniteDimensional F E :=
    IntermediateField.finiteDimensional_sup F⟮a⟯ F⟮b⟯
  have ha : a ∈ E := (le_sup_left : F⟮a⟯ ≤ E) <|
    IntermediateField.subset_adjoin F {a} (Set.mem_singleton a)
  have hb : b ∈ E := (le_sup_right : F⟮b⟯ ≤ E) <|
    IntermediateField.subset_adjoin F {b} (Set.mem_singleton b)
  have hab : a + b ∈ E := IntermediateField.add_mem E ha hb
  let a' : E := ⟨a, ha⟩
  let b' : E := ⟨b, hb⟩
  let ab' : E := ⟨a + b, hab⟩
  rw [absoluteTrace_map_eq' F K a',
    absoluteTrace_map_eq' F K b',
    absoluteTrace_map_eq' F K ab',
    absoluteTrace_eq_findim F a',
    absoluteTrace_eq_findim F b',
    absoluteTrace_eq_findim F ab',
    ← Distrib.left_distrib, ← map_add]
  rfl

/-- The absolute trace commutes with scalar multiplication. -/
theorem absoluteTrace_smul (m : F) (a : K) :
    absoluteTrace' F K (m • a) = m • absoluteTrace' F K a := by
  let E := F⟮a⟯
  haveI : FiniteDimensional F F⟮a⟯ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  have ha : a ∈ E := IntermediateField.subset_adjoin F {a}
    (Set.mem_singleton a)
  have hma := IntermediateField.smul_mem E ha (x := m)
  let a' : E := ⟨a, ha⟩
  let ma' : E := ⟨m • a, hma⟩
  rw [absoluteTrace_map_eq' F K a',
    absoluteTrace_map_eq' F K ma',
    absoluteTrace_eq_findim F a',
    absoluteTrace_eq_findim F ma',
    ← mul_smul_comm, ← map_smul]
  rfl

/-- Absolute trace function from an algebraic extension `K` to the base field `F`,
    as an `F`-linear map. -/
noncomputable def absoluteTrace : K →ₗ[F] F where
  toFun := absoluteTrace' F K
  map_add' := absoluteTrace_add F K
  map_smul' := absoluteTrace_smul F K

/-- Absolute trace map is non-trivial. -/
theorem nontrivial_absoluteTrace : absoluteTrace F K ≠ 0 := by
  simp [DFunLike.ne_iff, absoluteTrace]
  use 1
  exact (map_one (algebraMap F K) ▸ absoluteTrace_algebraMap F K 1) ▸ one_ne_zero

end Trace

/-- Uniform definition of *algebraic and of characteristic zero* to be used in
    the generic theorem.
  -/
def UIntegralCharZero : Prop := Algebra.IsIntegral F A ∧ CharZero F

/-- For finite-dimensional extensions `K₁`, `K₂` of `F`, the `F`-algebra `K₁ × K₂`
    is not locally generated. -/
theorem notLocallyGenerated_KK_if_integral (K₁ K₂ : Type u)
    [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂] :
    UIntegralCharZero F K₁ → UIntegralCharZero F K₂ → ¬isLocallyGenerated F (K₁ × K₂) := by
  intro intK₁ intK₂ h
  haveI : Algebra.IsIntegral F K₁ := intK₁.1
  haveI : Algebra.IsIntegral F K₂ := intK₂.1
  haveI : CharZero F := intK₁.2

  let T : K₁ × K₂ →ₗ[F] F :=
    absoluteTrace F K₁ ∘ₗ LinearMap.fst F K₁ K₂ -
    absoluteTrace F K₂ ∘ₗ LinearMap.snd F K₁ K₂

  let U : Subspace F (K₁ × K₂) := LinearMap.ker T

  /- Show `T ≠ 0` (equivalent to `U ≠ K₁ × K₂`). -/
  have hU_ne_top : U ≠ ⊤ := by
    apply (not_congr <| LinearMap.ker_eq_top).mpr
    have h := nontrivial_absoluteTrace F K₁
    simp [DFunLike.ne_iff] at h ⊢
    obtain ⟨x, hx⟩ := h
    use x, 0
    simpa [T]

  /- Show that `T` vanishes on local elements. -/
  have hT2 : localElements F (K₁ × K₂) ⊆ U := by
    intro ⟨α₁, α₂⟩ hα_loc
    have hα₁_int : IsIntegral F α₁ := Algebra.isIntegral_def.mp ‹_› α₁
    have hα₂_int : IsIntegral F α₂ := Algebra.isIntegral_def.mp ‹_› α₂
    have hα_int := IsIntegral_pair hα₁_int hα₂_int
    have hα_minpoly := local_minpoly_eq F hα_int hα_loc
    simp [U, T, sub_eq_zero, absoluteTrace, absoluteTrace']
    exact congrArg₂ (fun (x : ℕ) (y : F) ↦ (x : F)⁻¹ * y)
      /- finrank = finrank -/
      (IntermediateField.adjoin.finrank hα₂_int ▸
        hα_minpoly ▸
        IntermediateField.adjoin.finrank hα₁_int)
      /- trace = trace -/
      (trace_minpoly' F hα₂_int ▸ hα_minpoly ▸ trace_minpoly' F hα₁_int)

  /- Subspace generated by local elements is proper. -/
  have h_contra : Submodule.span F (localElements F (K₁ × K₂)) < ⊤ :=
    lt_of_le_of_lt
      (Submodule.span_le.mpr hT2) /- local span ≤ U -/
      (lt_top_iff_ne_top.mpr hU_ne_top) /- U < ⊤ -/
  exact (lt_top_iff_ne_top.mp h_contra) h

variable {F A} in
/-- Integral (equivalently algebraic) algebras are local if they are locally generated. -/
theorem isLocalRing_if_isLocallyGenerated_integral [Nontrivial A]
    [Algebra.IsIntegral F A] [CharZero F]
    (hLG : isLocallyGenerated F A) : LocalRing A := by
  have h : UIntegralCharZero F A := ⟨‹_›, ‹_›⟩
  refine isLocalAlgebra_if_isLocallyGenerated F ?_ notLocallyGenerated_KK_if_integral h hLG
  intro F A K _ _ _ _ _ f hf ⟨_, hChar⟩
  exact ⟨Algebra.IsIntegral_of_surjective hf, hChar⟩

end Integral
