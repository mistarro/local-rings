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

import Mathlib.RingTheory.Artinian.Ring
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

section Integral

/- Accepted in Mathlib4 in `Mathlib.FieldTheory.NormalizedTrace`. -/
section Trace

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

open scoped IntermediateField /- `F⟮a⟯` notation for simple field adjoin -/

/-- Absolute trace function from an algebraic extension `K` to the base field `F`. -/
noncomputable def absoluteTrace' : K → F :=
  fun a ↦ Algebra.trace F F⟮a⟯ (IntermediateField.AdjoinSimple.gen F a) /
    Module.finrank F F⟮a⟯

variable {E : Type*} [Field E] [Algebra F E]

section FiniteDimensional

variable [CharZero F] [FiniteDimensional F E]

/-- The absolute trace from a finite-dimensional extension `E` of `F` to `F`
    is the trace map scaled by `[E : F]`.
    This version accepts an argument from `E`. -/
lemma absoluteTrace_eq_findim (a : E) :
    absoluteTrace' F E a = Algebra.trace F E a / Module.finrank F E := by
  have h := (Nat.cast_ne_zero (R := F)).mpr <|
    Nat.pos_iff_ne_zero.mp <| Module.finrank_pos (R := F⟮a⟯) (M := E)
  rw [trace_eq_trace_adjoin F a, ← Module.finrank_mul_finrank F F⟮a⟯ E,
    nsmul_eq_mul, Nat.cast_mul,
    mul_comm, mul_div_mul_right _ _ h]
  rfl

end FiniteDimensional

/-- The absolute trace transfers via (injective) maps. -/
lemma absoluteTrace_map_eq (f : E →ₐ[F] K) (a : E) :
    absoluteTrace' F K (f a) = absoluteTrace' F E a := by
  have he := Set.image_singleton ▸ IntermediateField.adjoin_map F {a} f
  let e := (F⟮a⟯.equivMap f).trans (IntermediateField.equivOfEq he)
  rw [absoluteTrace', absoluteTrace',
    ← LinearEquiv.finrank_eq e.toLinearEquiv,
    div_eq_mul_inv, div_eq_mul_inv]
  exact congrArg (fun x : F ↦ x * _) <|
    Algebra.trace_eq_of_algEquiv e (IntermediateField.AdjoinSimple.gen F a)

/-- The absolute trace transfers via restriction to a subextension. -/
lemma absoluteTrace_map_eq' {E : IntermediateField F K} (a : E) :
    absoluteTrace' F K a = absoluteTrace' F E a :=
  absoluteTrace_map_eq F K E.val a

variable [CharZero F]

variable {F} in
/-- The absolute trace map `absoluteTrace' F F` is identity. -/
theorem absoluteTrace_scalar (a : F) : absoluteTrace' F F a = a := by
  rw [absoluteTrace_eq_findim F a, Module.finrank_self F,
    Nat.cast_one, div_one, Algebra.trace_self_apply]

/-- The absolute trace map is a left inverse of the algebra map. -/
theorem absoluteTrace_algebraMap (a : F) :
    absoluteTrace' F K (algebraMap F K a) = a :=
  (Algebra.ofId_apply K a ▸
    absoluteTrace_map_eq F K (Algebra.ofId F K) a).trans (absoluteTrace_scalar a)


variable [Algebra.IsIntegral F K]

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
    ← add_div, ← map_add]
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
    ← smul_div_assoc, ← map_smul]
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
  exact ⟨1, (map_one (algebraMap F K) ▸ absoluteTrace_algebraMap F K 1) ▸ one_ne_zero⟩

end Trace

variable (F A K₁ K₂ : Type*)
variable [Field F] [CommRing A] [Algebra F A]
variable [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂]

/-- Uniform definition of *algebraic and of characteristic zero* to be used in
    the generic theorem.
  -/
def UIntegralCharZero : Prop := Algebra.IsIntegral F A ∧ CharZero F

/-- For finite-dimensional extensions `K₁`, `K₂` of `F`, the `F`-algebra `K₁ × K₂`
    is not locally generated. -/
theorem notLocallyGenerated_KK_if_integral :
    UIntegralCharZero F K₁ → UIntegralCharZero F K₂ → ¬isLocallyGenerated F (K₁ × K₂) := by
  intro intK₁ intK₂ h
  haveI : Algebra.IsIntegral F K₁ := intK₁.1
  haveI : Algebra.IsIntegral F K₂ := intK₂.1
  haveI : CharZero F := intK₁.2
  let T : K₁ × K₂ →ₗ[F] F :=
    absoluteTrace F K₁ ∘ₗ LinearMap.fst F K₁ K₂ - absoluteTrace F K₂ ∘ₗ LinearMap.snd F K₁ K₂
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
    intro α hα_loc
    have hα₁_int := Algebra.isIntegral_def.mp ‹_› α.1
    have hα₂_int := Algebra.isIntegral_def.mp ‹_› α.2
    have hα_minpoly := local_minpoly_eq (hα₁_int.pair hα₂_int) hα_loc
    simp [U, T, sub_eq_zero, absoluteTrace, absoluteTrace']
    exact congrArg₂ (fun (x : ℕ) (y : F) ↦ y / x)
      /- finrank = finrank -/
      (IntermediateField.adjoin.finrank hα₂_int ▸
        hα_minpoly ▸
        IntermediateField.adjoin.finrank hα₁_int)
      /- trace = trace -/
      (trace_adjoinSimpleGen hα₂_int ▸
        hα_minpoly ▸
        trace_adjoinSimpleGen hα₁_int)
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
    (hLG : isLocallyGenerated F A) : IsLocalRing A :=
  haveI h : UIntegralCharZero F A := ⟨‹_›, ‹_›⟩
  isLocalAlgebra_if_isLocallyGenerated
    (fun f hf ⟨_, hChar⟩ ↦ ⟨Algebra.IsIntegral.of_surjective f hf, hChar⟩)
    notLocallyGenerated_KK_if_integral h hLG

end Integral
