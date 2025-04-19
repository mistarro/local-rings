import Mathlib.FieldTheory.NormalizedTrace

import LocalRings.Basic

/-!
# Results for integral (algebraic) algebras in characteristic 0

## Main results

* `IsLocalRing.of_isLocallyGenerated_of_isIntegral_of_charZero`: an integral (equivalently algebraic)
  algebra over a field of characteristic 0 is local if it is locally generated.
-/

variable (F A K₁ K₂ : Type*)
variable [Field F] [CommRing A] [Algebra F A]
variable [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂]

/-- Uniform definition of *algebraic and of characteristic zero* to be used in
    the generic theorem. -/
def UIntegralCharZero : Prop := Algebra.IsIntegral F A ∧ CharZero F

/-- For finite-dimensional extensions `K₁`, `K₂` of `F`, the `F`-algebra `K₁ × K₂`
    is not locally generated. -/
theorem not_isLocallyGenerated_of_isIntegral_of_charZero (intK₁ : UIntegralCharZero F K₁)
    (intK₂ : UIntegralCharZero F K₂) : ¬isLocallyGenerated F (K₁ × K₂) := by
  have : Algebra.IsIntegral F K₁ := intK₁.1
  have : Algebra.IsIntegral F K₂ := intK₂.1
  have : CharZero F := intK₁.2
  let T : K₁ × K₂ →ₗ[F] F :=
    Algebra.normalizedTrace F K₁ ∘ₗ LinearMap.fst F K₁ K₂ -
      Algebra.normalizedTrace F K₂ ∘ₗ LinearMap.snd F K₁ K₂
  let U : Subspace F (K₁ × K₂) := LinearMap.ker T
  /- Reduce the goal to show that `U` is a proper subspace and that local elements are in `U`. -/
  refine lt_top_iff_ne_top.mp <| lt_of_le_of_lt (b := U) (Submodule.span_le.mpr ?_) (lt_top_iff_ne_top.mpr ?_)
  /- Show that `T` vanishes on local elements. -/
  · intro α hαl
    have hα₁i := Algebra.isIntegral_def.mp ‹_› α.1
    have hα₂i := Algebra.isIntegral_def.mp ‹_› α.2
    have hα := hαl.minpoly_eq_minpoly (hα₁i.pair hα₂i)
    simp [U, T, sub_eq_zero, Algebra.normalizedTrace_def]
    exact congrArg₂ (fun (x : ℕ) (y : F) ↦ (x : F)⁻¹ * y)
      /- finrank = finrank -/
      (IntermediateField.adjoin.finrank hα₂i ▸ hα ▸ IntermediateField.adjoin.finrank hα₁i)
      /- trace = trace -/
      (trace_adjoinSimpleGen hα₂i ▸ hα ▸ trace_adjoinSimpleGen hα₁i)
  /- Show `T ≠ 0` (equivalent to `U ≠ K₁ × K₂`). -/
  · apply (not_congr <| LinearMap.ker_eq_top).mpr
    obtain ⟨x, _⟩ := DFunLike.ne_iff.mp <| Algebra.normalizedTrace_ne_zero F K₁
    exact DFunLike.ne_iff.mpr ⟨(x, 0), by simpa [T]⟩

variable {F A} in
/-- Integral (equivalently algebraic) algebras of characteristic 0 are local if they are locally generated. -/
theorem IsLocalRing.of_isLocallyGenerated_of_isIntegral_of_charZero [Nontrivial A]
    [Algebra.IsIntegral F A] [CharZero F] (hLG : isLocallyGenerated F A) : IsLocalRing A :=
  have h : UIntegralCharZero F A := ⟨‹_›, ‹_›⟩
  .of_isLocallyGenerated (fun f hf ⟨_, hChar⟩ ↦ ⟨Algebra.IsIntegral.of_surjective f hf, hChar⟩)
    not_isLocallyGenerated_of_isIntegral_of_charZero h hLG
