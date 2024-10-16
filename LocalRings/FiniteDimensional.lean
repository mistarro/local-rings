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
import LocalRings.Utils.Module
import LocalRings.Utils.PurelyInseparable
import LocalRings.Utils.Trace


/-!
# Results for finite-dimensional algebras

## Main results

* `isLocalRing_if_isLocallyGenerated_findim`: a finite-dimensional algebra is local
    if it is locally generated.
-/

section FiniteDimensional

variable (F A : Type u) [Field F] [CommRing A] [Algebra F A]
variable {K₁ K₂ : Type u} [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂]

open scoped IntermediateField /- `F⟮a⟯` notation for simple field adjoin -/

/- Auxiliary lemma to workaround problems with typeclass search. -/
lemma finrank_equality_aux
    {E₁ : IntermediateField F K₁} {E₂ : IntermediateField F K₂}
    (h : FiniteDimensional.finrank F E₁ = FiniteDimensional.finrank F E₂) :
    FiniteDimensional.finrank F K₂ * FiniteDimensional.finrank E₁ K₁ =
    FiniteDimensional.finrank F K₁ * FiniteDimensional.finrank E₂ K₂ := by
  have h₁ := FiniteDimensional.finrank_mul_finrank F E₁ K₁
  have h₂ := FiniteDimensional.finrank_mul_finrank F E₂ K₂
  rw [← h₁, ← h₂, mul_comm, ← mul_assoc]
  apply congrArg (fun (x : ℕ) => x * FiniteDimensional.finrank E₂ K₂)
  rw [mul_comm]
  apply congrArg (fun (x : ℕ) => x * FiniteDimensional.finrank E₁ K₁)
  exact h.symm

variable [FiniteDimensional F K₁] [FiniteDimensional F K₂]

/-- If `(a₁, a₂) : K₁ × K₂` is local then `minpoly F a₁ = minpoly F a₂` -/
lemma local_minpoly_eq {a₁ : K₁} {a₂ : K₂} (h1 : isLocalElement F (a₁, a₂)) :
    minpoly F a₁ = minpoly F a₂ := by
  let μ₁ := minpoly F a₁
  have int_a₁ : IsIntegral F a₁ := IsIntegral.of_finite F a₁
  obtain ⟨B, ⟨_, ha⟩⟩ := h1
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
    (minpoly.irreducible int_a₁)
    hμ₁a₂0
    (minpoly.monic int_a₁)

/-- Uniform definition of `FiniteDimensional` to be used in the generic theorem.
    Original definition is:
      FiniteDimensional (K : Type u_1) (V : Type u_2) [DivisionRing K] [AddCommGroup V] [Module K V] : Prop
  -/
def UFiniteDimensional : Prop := FiniteDimensional F A

/-- For finite-dimensional extensions `K₁`, `K₂` of `F`, the `F`-algebra `K₁ × K₂`
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
  have hb₁d : d ∣ b₁ := Nat.gcd_dvd_left b₁ b₂
  have hb₂d : d ∣ b₂ := Nat.gcd_dvd_right b₁ b₂
  let a₁' := b₁ / d
  let a₂' := b₂ / d
  have a_coprime : Nat.gcd a₁' a₂' = 1 := by rw [Nat.gcd_div hb₁d hb₂d, Nat.div_self hd]
  let a₁ := (a₁' : F)
  let a₂ := (a₂' : F)
  have a_nonzero : a₁ ≠ 0 ∨ a₂ ≠ 0 := by
    by_contra hc
    push_neg at hc
    /- The following is simpler but requires `p : ℕ` and `ExpChar F p` as parameters:
    rcases ‹ExpChar F p› with _ | ⟨hprime⟩
    · simp [Nat.cast_eq_zero] at hc
      simp [hc.1, hc.2] at a_coprime
    · simp only [CharP.cast_eq_zero_iff F p] at hc
      rw [← Nat.dvd_gcd_iff, a_coprime, Nat.dvd_one] at hc
      rw [hc] at hprime
      contradiction
    --/
    by_cases h : p = 1
    · haveI := ExpChar.congr F p h
      haveI := charZero_of_expChar_one' F
      simp [a₁, a₂, Nat.cast_eq_zero] at hc
      simp [hc.1, hc.2] at a_coprime
    · haveI := charP_of_expChar_prime' (R := F) h
      simp only [CharP.cast_eq_zero_iff F p] at hc
      rw [← Nat.dvd_gcd_iff, a_coprime, Nat.dvd_one] at hc
      exact h hc

  let σ := iterateFrobenius F p r
  haveI := RingHomCompTriple.iterateFrobenius F p hrs₁
  haveI := RingHomCompTriple.iterateFrobenius F p hrs₂
  let T₁ := ((Algebra.trace F E₁).comp (iRed_frobₛₗ F E₁ K₁ p s₁ σ)).comp (LinearMap.fst F K₁ K₂)
  let T₂ := ((Algebra.trace F E₂).comp (iRed_frobₛₗ F E₂ K₂ p s₂ σ)).comp (LinearMap.snd F K₁ K₂)
  let T : K₁ × K₂ →ₛₗ[σ] F := a₂ • T₁ - a₁ • T₂
  let U : Subspace F (K₁ × K₂) := LinearMap.ker T
  /- Show `T ≠ 0` (equivalent to `U ≠ K₁ × K₂`) -/
  have hU_ne_top : U ≠ ⊤ := by
    intro h
    suffices T ≠ 0 by exact this <| LinearMap.ker_eq_top.mp h
    simp [DFunLike.ne_iff]
    cases a_nonzero with
    | inl ha₁ =>
        have h := nontrivial_trace_iRed_frob F E₂ K₂ p s₂ σ
        simp [T₂, DFunLike.ne_iff] at h ⊢
        obtain ⟨x, hx⟩ := h
        use 0, x
        simp [T, T₁, T₂]
        exact ⟨ha₁, hx⟩
    | inr ha₂ =>
        have h := nontrivial_trace_iRed_frob F E₁ K₁ p s₁ σ
        simp [T₁, DFunLike.ne_iff] at h ⊢
        obtain ⟨x, hx⟩ := h
        use x, 0
        simp [T, T₁, T₂]
        exact ⟨ha₂, hx⟩
  /- Show that `T` vanishes on local elements -/
  have hT2 : localElements F (K₁ × K₂) ⊆ U := by
    intro α hα
    simp [localElements, Set.mem_setOf_eq] at hα
    simp [U]
    obtain ⟨α₁, α₂⟩ := α

    simp [T, T₁, T₂]
    rw [sub_eq_zero]

    let β₁ : E₁ := iRed_frobₛₗ F E₁ K₁ p s₁ σ α₁
    let β₂ : E₂ := iRed_frobₛₗ F E₂ K₂ p s₂ σ α₂

    /- goal is now `a₂ * (Algebra.trace F E₁ β₁) = a₁ * (Algebra.trace F E₂ β₂)` -/

    have hβ₁α₁ : algebraMap E₁ K₁ β₁ = α₁ ^ p ^ r := by
      rw [← hrs₁]
      exact iRed_frobₛₗ_algebraMap' F E₁ K₁ p s₁ α₁ σ
    have hβ₂α₂ : algebraMap E₂ K₂ β₂ = α₂ ^ p ^ r := by
      rw [← hrs₂]
      exact iRed_frobₛₗ_algebraMap' F E₂ K₂ p s₂ α₂ σ

    /- if `α` is local then so is `α ^ p ^ r` -/
    replace hα := isLocalElement_pow F hα (p ^ r)
    simp at hα
    replace hα := local_minpoly_eq F hα
    rw [← hβ₁α₁, ← hβ₂α₂,
      minpoly.algebraMap_eq (algebraMap E₁ K₁).injective,
      minpoly.algebraMap_eq (algebraMap E₂ K₂).injective] at hα

    have hβ₁i : IsIntegral F β₁ := IsIntegral.of_finite F β₁
    have hβ₂i : IsIntegral F β₂ := IsIntegral.of_finite F β₂

    have h_finrank := IntermediateField.adjoin.finrank hβ₁i
    rw [hα, ← IntermediateField.adjoin.finrank hβ₂i] at h_finrank
    have h_nextCoeff := congrArg Polynomial.nextCoeff hα

    rw [trace_minpoly F β₁, trace_minpoly F β₂,
      show a₁ = (a₁' : F) by rfl,
      show a₂ = (a₂' : F) by rfl,
      ← mul_assoc, ← mul_assoc,
      h_nextCoeff]

    norm_cast

    apply congrArg (fun (x : F) => x * -(minpoly F β₂).nextCoeff)
    apply congrArg Nat.cast

    simp [a₁', a₂']
    rw [mul_comm, mul_comm (b₁ / d) _]
    apply Nat.eq_of_mul_eq_mul_right hd
    rw [mul_assoc, Nat.div_mul_cancel hb₂d, mul_assoc, Nat.div_mul_cancel hb₁d]
    rw [mul_comm, mul_comm _ b₁]
    simp [b₁, b₂]

    exact finrank_equality_aux F h_finrank

  have h_contra : Submodule.span F (localElements F (K₁ × K₂)) < ⊤ :=
    lt_of_le_of_lt
      (Submodule.span_le.mpr hT2) /- local span ≤ U -/
      (lt_top_iff_ne_top.mpr hU_ne_top) /- U < ⊤ -/
  exact (lt_top_iff_ne_top.mp h_contra) h

variable {F A} in
/-- Finite-dimensional algebras are local if they are locally generated. -/
theorem isLocalRing_if_isLocallyGenerated_findim [Nontrivial A]
    (h : UFiniteDimensional F A) (hLG : isLocallyGenerated F A) : LocalRing A := by
  refine isLocalAlgebra_if_isLocallyGenerated F ?_ notLocallyGenerated_KK_if_findim h hLG
  intro _ _ _ _ _ _ _ _ f hf hA
  exact hA.of_surjective f hf

end FiniteDimensional
