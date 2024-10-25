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
    FiniteDimensional.finrank E₁ K₁ * FiniteDimensional.finrank F K₂ =
    FiniteDimensional.finrank E₂ K₂ * FiniteDimensional.finrank F K₁:= by
  rw [← FiniteDimensional.finrank_mul_finrank F E₁ K₁,
    ← FiniteDimensional.finrank_mul_finrank F E₂ K₂,
    mul_comm, ← mul_assoc]
  apply congrArg (fun (x : ℕ) ↦ x * FiniteDimensional.finrank E₁ K₁)
  rw [mul_comm]
  apply congrArg (fun (x : ℕ) ↦ FiniteDimensional.finrank E₂ K₂ * x)
  exact h.symm

variable [FiniteDimensional F K₁] [FiniteDimensional F K₂]

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

  /- Purely inseparable (logarithmic) degrees. -/
  let r₁ : ℕ := finInsepLogRank E₁ K₁ p
  let r₂ : ℕ := finInsepLogRank E₂ K₂ p
  let r := max r₁ r₂
  let s₁ : ℕ := r - r₁
  let s₂ : ℕ := r - r₂
  have hrs₁ : r₁ + s₁ = r := by simp only [s₁, add_tsub_cancel_of_le (le_max_left r₁ r₂)]
  have hrs₂ : r₂ + s₂ = r := by simp only [s₂, add_tsub_cancel_of_le (le_max_right r₁ r₂)]

  /- Separable degrees. -/
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
  let a₁ : F := a₁'
  let a₂ : F := a₂'
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
    · haveI := ExpChar.congr F p h /- ExpChar F 1 -/
      haveI := charZero_of_expChar_one' F /- CharZero F -/
      simp [a₁, a₂, Nat.cast_eq_zero] at hc
      simp [hc.1, hc.2] at a_coprime
    · haveI := charP_of_expChar_prime' (R := F) h /- CharP F p -/
      simp only [CharP.cast_eq_zero_iff F p] at hc
      rw [← Nat.dvd_gcd_iff, a_coprime, Nat.dvd_one] at hc
      exact h hc

  /- Define the semilinear map `T : K₁ × K₂ →ₛₗ[σ] F`. -/
  let σ := iterateFrobenius F p r
  haveI := RingHomCompTriple.iterateFrobenius F p hrs₁
  haveI := RingHomCompTriple.iterateFrobenius F p hrs₂
  let T₁ := ((Algebra.trace F E₁).comp (iRed_frobₛₗ F E₁ K₁ p s₁ σ)).comp (LinearMap.fst F K₁ K₂)
  let T₂ := ((Algebra.trace F E₂).comp (iRed_frobₛₗ F E₂ K₂ p s₂ σ)).comp (LinearMap.snd F K₁ K₂)
  let T : K₁ × K₂ →ₛₗ[σ] F := a₂ • T₁ - a₁ • T₂
  let U : Subspace F (K₁ × K₂) := LinearMap.ker T

  /- Show `T ≠ 0` (equivalent to `U ≠ K₁ × K₂`). -/
  have hU_ne_top : U ≠ ⊤ := by
    apply (not_congr <| LinearMap.ker_eq_top).mpr
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

  /- Show that `T` vanishes on local elements. -/
  have hT2 : localElements F (K₁ × K₂) ⊆ U := by
    intro ⟨α₁, α₂⟩ hα
    simp [U, T, T₁, T₂, sub_eq_zero]
    set β₁ : E₁ := iRed_frobₛₗ F E₁ K₁ p s₁ σ α₁
    set β₂ : E₂ := iRed_frobₛₗ F E₂ K₂ p s₂ σ α₂

    /- Goal is now `a₂ * (Algebra.trace F E₁ β₁) = a₁ * (Algebra.trace F E₂ β₂)`. -/

    /- If `α` is local then so is `α ^ p ^ r`. -/
    replace hα := isLocalElement_pow F hα (p ^ r)
    simp at hα
    /- Components of `α ^ p ^ r` have the same minimal polynomial. -/
    replace hα := local_minpoly_eq F (IsIntegral.of_finite F (α₁ ^ p ^ r, α₂ ^ p ^ r)) hα
    /- Simplify using known facts: `β₁` and `β₂` have the same minimal polynomial. -/
    rw [
      show α₁ ^ p ^ r = algebraMap E₁ K₁ β₁ by
        rw [← hrs₁]
        exact (iRed_frobₛₗ_algebraMap_top F E₁ K₁ p s₁ α₁ σ).symm,
      show α₂ ^ p ^ r = algebraMap E₂ K₂ β₂ by
        rw [← hrs₂]
        exact (iRed_frobₛₗ_algebraMap_top F E₂ K₂ p s₂ α₂ σ).symm,
      minpoly.algebraMap_eq (algebraMap E₁ K₁).injective,
      minpoly.algebraMap_eq (algebraMap E₂ K₂).injective] at hα

    /- Extensions `F⟮β₁⟯` and `F⟮β₂⟯` have equal degrees over `F`.  -/
    have h_finrank_eq :=
      IntermediateField.adjoin.finrank (IsIntegral.of_finite F β₂) ▸
      hα ▸
      IntermediateField.adjoin.finrank (IsIntegral.of_finite F β₁)

    rw [trace_minpoly F β₁, trace_minpoly F β₂,
      show a₁ = (a₁' : F) by rfl,
      show a₂ = (a₂' : F) by rfl,
      ← mul_assoc, ← mul_assoc,
      congrArg Polynomial.nextCoeff hα,
      ← Nat.cast_mul, ← Nat.cast_mul]

    apply congrArg (fun x : ℕ => x * -(minpoly F β₂).nextCoeff)

    rw [mul_comm, mul_comm (b₁ / d) _, ← Nat.mul_div_assoc, ← Nat.mul_div_assoc]
    apply congrArg (fun x => x / d)
    exact finrank_equality_aux F h_finrank_eq
    /- for some reason we have extra goals: `d ∣ b₁` and `d ∣ b₂` but those are assumptions -/
    assumption
    assumption

  /- Subspace generated by local elements is proper. -/
  have h_contra : Submodule.span F (localElements F (K₁ × K₂)) < ⊤ :=
    lt_of_le_of_lt
      (Submodule.span_le.mpr hT2) /- local span ≤ U -/
      (lt_top_iff_ne_top.mpr hU_ne_top) /- U < ⊤ -/
  exact (lt_top_iff_ne_top.mp h_contra) h

variable {F A} in
/-- Finite-dimensional algebras are local if they are locally generated. -/
theorem isLocalRing_if_isLocallyGenerated_findim [Nontrivial A] [FiniteDimensional F A]
    (hLG : isLocallyGenerated F A) : LocalRing A := by
  have h : UFiniteDimensional F A := ‹FiniteDimensional F A›
  refine isLocalAlgebra_if_isLocallyGenerated F ?_ notLocallyGenerated_KK_if_findim h hLG
  intro _ _ _ _ _ _ _ _ f hf hA
  exact hA.of_surjective f hf

end FiniteDimensional
