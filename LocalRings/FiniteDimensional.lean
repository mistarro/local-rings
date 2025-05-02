import Mathlib.FieldTheory.PurelyInseparable.Exponent
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.RingTheory.Trace.Basic

import LocalRings.Basic

/-!
# Results for finite-dimensional algebras

## Main results

* `IsLocalRing.of_isLocallyGenerated_of_finiteDimensional`: a finite-dimensional algebra is local
  if it is locally generated.
-/

variable (F : Type*) {E K : Type*} [Field F] [Field E] [Field K]
variable [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
variable [FiniteDimensional F E] [FiniteDimensional E K]
variable [Algebra.IsSeparable F E] [IsPurelyInseparable E K]
variable (p : ℕ) [ExpChar F p] [ExpChar E p]

/-- In exponential characteristic `p`, the composition of the trace map for separable part and
    iterated Frobenius for purely inseparable one is non-trivial. -/
lemma nontrivial_trace_iteratedFrobenius {s : ℕ} (hs : IsPurelyInseparable.exponent E K ≤ s) :
    (Algebra.trace F E).comp (IsPurelyInseparable.iterateFrobeniusₛₗ F E K p hs) ≠ 0 := by
  have : ExpChar E p := expChar_of_injective_ringHom (algebraMap F E).injective p
  simp [DFunLike.ne_iff]
  /- Trace is surjective, so there is `a : E` with `Algebra.trace F E a = 1` -/
  obtain ⟨a, ha⟩ := Algebra.trace_surjective F E 1
  refine ⟨algebraMap E K a, IsPurelyInseparable.iterateFrobeniusₛₗ_algebraMap F E K p hs a ▸ ?_⟩
  have hsep : IsSeparable F a := Algebra.IsSeparable.isSeparable F a
  let ⟨hn, hc⟩ := mul_ne_zero_iff.mp (trace_eq_finrank_mul_minpoly_nextCoeff F a ▸ ha ▸ one_ne_zero)
  rw [← ne_eq, trace_eq_finrank_mul_minpoly_nextCoeff, mul_ne_zero_iff]
  constructor
  · rwa [← IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable F E hsep p s]
  · rw [← iterateFrobenius_def, minpoly.iterateFrobenius_of_isSeparable p s hsep,
      Polynomial.nextCoeff_map (iterateFrobenius F p s).injective, iterateFrobenius_def, neg_ne_zero]
    exact pow_ne_zero _ <| neg_ne_zero.mp hc

section FiniteDimensional

variable {F A K₁ K₂ : Type*}
variable [Field F] [CommRing A] [Algebra F A]
variable [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂]

open IntermediateField in
/-- For finite-dimensional extensions `K₁`, `K₂` of `F`, the `F`-algebra `K₁ × K₂`
    is not locally generated. -/
theorem not_isLocallyGenerated_of_findim [FiniteDimensional F K₁] [FiniteDimensional F K₂]
    (p : ℕ) [ExpChar F p] : ¬isLocallyGenerated F (K₁ × K₂) := by
  let E₁ := separableClosure F K₁
  let E₂ := separableClosure F K₂
  have : IsPurelyInseparable E₁ K₁ := separableClosure.isPurelyInseparable F K₁
  have : IsPurelyInseparable E₂ K₂ := separableClosure.isPurelyInseparable F K₂
  have : ExpChar E₁ p := expChar_of_injective_ringHom (algebraMap F E₁).injective p
  have : ExpChar E₂ p := expChar_of_injective_ringHom (algebraMap F E₂).injective p
  /- Purely inseparable part. -/
  let r₁ : ℕ := IsPurelyInseparable.exponent E₁ K₁
  let r₂ : ℕ := IsPurelyInseparable.exponent E₂ K₂
  let r := max r₁ r₂
  have hr₁ := le_max_left r₁ r₂
  have hr₂ := le_max_right r₁ r₂
  /- Separable part. -/
  let b₁ := Module.finrank F E₁
  let b₂ := Module.finrank F E₂
  let d : ℕ := Nat.gcd b₁ b₂
  have hb₁d : d ∣ b₁ := Nat.gcd_dvd_left b₁ b₂
  have hb₂d : d ∣ b₂ := Nat.gcd_dvd_right b₁ b₂
  let a₁' := b₁ / d
  let a₂' := b₂ / d
  let a₁ : F := a₁'
  let a₂ : F := a₂'
  /- Define the semilinear map `T : K₁ × K₂ →ₛₗ[σ] F`. -/
  let T₁ := Algebra.trace F E₁ ∘ₛₗ IsPurelyInseparable.iterateFrobeniusₛₗ F E₁ K₁ p hr₁ ∘ₛₗ LinearMap.fst F K₁ K₂
  let T₂ := Algebra.trace F E₂ ∘ₛₗ IsPurelyInseparable.iterateFrobeniusₛₗ F E₂ K₂ p hr₂ ∘ₛₗ LinearMap.snd F K₁ K₂
  let T : K₁ × K₂ →ₛₗ[_] F := a₂ • T₁ - a₁ • T₂
  let U : Subspace F (K₁ × K₂) := LinearMap.ker T
  /- Reduce the goal to show that `U` is a proper subspace and that local elements are in `U`. -/
  refine lt_top_iff_ne_top.mp <| lt_of_le_of_lt (b := U) (Submodule.span_le.mpr ?_) (lt_top_iff_ne_top.mpr ?_)
  /- Show that `T` vanishes on local elements. -/
  · intro ⟨α₁, α₂⟩ hα
    replace hα := hα.pow _ |>.minpoly_eq_minpoly (.of_finite F (α₁ ^ p ^ r, α₂ ^ p ^ r))
    rw [← IsPurelyInseparable.algebraMap_iterateFrobeniusₛₗ F E₁ K₁ p hr₁ α₁,
      ← IsPurelyInseparable.algebraMap_iterateFrobeniusₛₗ F E₂ K₂ p hr₂ α₂,
      minpoly.algebraMap_eq (algebraMap E₁ K₁).injective,
      minpoly.algebraMap_eq (algebraMap E₂ K₂).injective] at hα
    simp [U, T, T₁, T₂, a₁, a₂, sub_eq_zero]
    set β₁ : E₁ := IsPurelyInseparable.iterateFrobeniusₛₗ F E₁ K₁ p hr₁ α₁
    set β₂ : E₂ := IsPurelyInseparable.iterateFrobeniusₛₗ F E₂ K₂ p hr₂ α₂
    rw [trace_eq_finrank_mul_minpoly_nextCoeff, trace_eq_finrank_mul_minpoly_nextCoeff,
      ← mul_assoc, ← mul_assoc, hα, ← Nat.cast_mul, ← Nat.cast_mul]
    apply congrArg fun x : ℕ ↦ (x : F) * _
    rw [Nat.div_mul_right_comm hb₁d, Nat.div_mul_right_comm hb₂d]
    apply congrArg fun x ↦ x / d
    dsimp only [b₁, b₂]
    rw [← Module.finrank_mul_finrank F F⟮β₁⟯ E₁, ← Module.finrank_mul_finrank F F⟮β₂⟯ E₂,
      IntermediateField.adjoin.finrank (.of_finite F β₂),
      IntermediateField.adjoin.finrank (.of_finite F β₁), hα]
    ring
  /- Show `T ≠ 0` (equivalent to `U ≠ K₁ × K₂`). -/
  · apply (not_congr <| LinearMap.ker_eq_top).mpr
    by_cases ha : a₁ = 0 ∧ a₂ = 0
    · exfalso
      have a_coprime : Nat.Coprime a₁' a₂' := Nat.coprime_div_gcd_div_gcd <|
        Nat.gcd_pos_of_pos_left b₂ (Module.finrank_pos (R := F) (M := E₁))
      rcases ‹ExpChar F p› with _ | ⟨hp⟩
      · simp [a₁, a₂] at ha
        simp [ha] at a_coprime
      · simp [a₁, a₂, CharP.cast_eq_zero_iff F p, ← Nat.dvd_gcd_iff, a_coprime, hp.not_dvd_one] at ha
    · rcases not_and_or.mp ha with ha₁ | ha₂
      · obtain ⟨x, _⟩ := DFunLike.ne_iff.mp <| nontrivial_trace_iteratedFrobenius F p hr₂
        exact DFunLike.ne_iff.mpr ⟨(0, x), by simpa [T, T₁, ha₁]⟩
      · obtain ⟨x, _⟩ := DFunLike.ne_iff.mp <| nontrivial_trace_iteratedFrobenius F p hr₁
        exact DFunLike.ne_iff.mpr ⟨(x, 0), by simpa [T, T₂, ha₂]⟩

variable (F A) in
/-- Uniform definition of `FiniteDimensional` to be used in the generic theorem.
    Original definition is:
      FiniteDimensional (K : Type u_1) (V : Type u_2) [DivisionRing K] [AddCommGroup V] [Module K V] : Prop
  -/
def UFiniteDimensional : Prop := FiniteDimensional F A

variable (F) in
/-- For finite-dimensional extensions `K₁`, `K₂` of `F`, the `F`-algebra `K₁ × K₂`
    is not locally generated.
    Version to be used with generic theorem. -/
theorem not_isLocallyGenerated_of_findim' (fdK₁ : UFiniteDimensional F K₁) (fdK₂ : UFiniteDimensional F K₂) :
    ¬isLocallyGenerated F (K₁ × K₂) :=
  have : FiniteDimensional F K₁ := fdK₁
  have : FiniteDimensional F K₂ := fdK₂
  let p := ringExpChar F
  have : ExpChar F p := inferInstance
  not_isLocallyGenerated_of_findim p

/-- Finite-dimensional algebras are local if they are locally generated. -/
theorem IsLocalRing.of_isLocallyGenerated_of_finiteDimensional [Nontrivial A] [FiniteDimensional F A]
    (hLG : isLocallyGenerated F A) : IsLocalRing A :=
  have h : UFiniteDimensional F A := ‹_›
  .of_isLocallyGenerated (fun f hf hA ↦ hA.of_surjective f hf) not_isLocallyGenerated_of_findim' h hLG

end FiniteDimensional
