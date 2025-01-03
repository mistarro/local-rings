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

import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

import LocalRings.Basic
import LocalRings.Utils.IntermediateField
import LocalRings.Utils.PurelyInseparable
import LocalRings.Utils.Trace


/-!
# Results for finite-dimensional algebras

## Main results

* `isLocalRing_if_isLocallyGenerated_findim`: a finite-dimensional algebra is local
    if it is locally generated.
-/

namespace LinearMap

@[inherit_doc] infixr:90 " ∘ₛₗ "  => comp

end LinearMap

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E]
variable (p : ℕ) [ExpChar F p]

lemma interateFrobenius_algebraMap_comm [ExpChar E p] (s : ℕ) :
    (algebraMap F E).comp (iterateFrobenius F p s) =
      (iterateFrobenius E p s).comp (algebraMap F E) :=
  RingHom.ext (fun x ↦
    ((algebraMap F E).comp_apply (iterateFrobenius F p s) x).trans <|
    (congrArg (algebraMap F E) (iterateFrobenius_def p s x)).trans <|
    ((algebraMap F E).map_pow x (p ^ s)).trans <|
    (iterateFrobenius_def p s (algebraMap F E x)).symm.trans <|
    ((iterateFrobenius E p s).comp_apply (algebraMap F E) x).symm)

variable [Algebra.IsSeparable F E]

open scoped IntermediateField

/-- For a separable extension `F ⊆ E` of characteristic `p > 0`,
    adjoining `a` to `F` is same as adjoining `a ^ p ^ s`. -/
lemma adjoin_a_pow_p_eq (s : ℕ) (a : E) : F⟮a ^ p ^ s⟯ = F⟮a⟯ := by
  have ha : a ∈ F⟮a⟯ := IntermediateField.mem_adjoin_simple_self F a
  have hap : a ^ p ^ s ∈ F⟮a⟯ := pow_mem ha (p ^ s)
  let L := F⟮a ^ p ^ s⟯
  /- The extension `L = F⟮a ^ p ^ s⟯ ⊆ F⟮a⟯ ≅ L⟮a⟯` is purely inseparable (and separable)
    so `L⟮a⟯ = L`. -/
  haveI : IsPurelyInseparable L L⟮a⟯ :=
    (IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem L E p).mpr
      ⟨s, (algebraMap L E).coe_range ▸
        IntermediateField.algebraMap_range_mem_iff.mpr <|
        IntermediateField.mem_adjoin_simple_self F (a ^ p ^ s)⟩
  have haL : a ∈ L :=
    IntermediateField.algebraMap_range_mem_iff.mp <|
      IntermediateField.mem_bot.mp <|
      IntermediateField.adjoin_simple_eq_bot_iff.mp <|
      L⟮a⟯.eq_bot_of_isPurelyInseparable_of_isSeparable
  exact LE.le.antisymm
    (IntermediateField.adjoin_simple_le_iff.mpr hap)
    (IntermediateField.adjoin_simple_le_iff.mpr haL)

variable [ExpChar E p]

/-- For a separable extension `F ⊆ E` of characteristic `p > 0`,
    the minimal polynomial of `a ^ p ^ s` is the minimal polynomial of `a` mapped via `(⬝ ^ p ^ s)`. -/
lemma minpoly_map_frobenius (s : ℕ) (a : E) :
    minpoly F (iterateFrobenius E p s a) = (minpoly F a).map (iterateFrobenius F p s) := by
  let μ := minpoly F a
  let μ₁ := minpoly F (a ^ p ^ s)
  let μ₂ := μ.map (iterateFrobenius F p s)
  /- goal: `μ₁ = μ₂` -/
  have hμ₂aeval : 0 = μ₂.aeval (a ^ p ^ s) :=
    iterateFrobenius_def p s a ▸
    (iterateFrobenius E p s).map_zero ▸
    minpoly.aeval F a ▸
    μ.map_aeval_eq_aeval_map (interateFrobenius_algebraMap_comm F p s) a
  have hai : IsIntegral F a := (Algebra.IsSeparable.isSeparable F a).isIntegral
  have hapi : IsIntegral F (a ^ p ^ s) := hai.pow (p ^ s)
  /- both are monic -/
  have hμ₁monic : μ₁.Monic := minpoly.monic hapi
  have hμ₂monic : μ₂.Monic := (minpoly.monic hai).map (iterateFrobenius F p s)
  /- both have same degree -/
  have hdeg : μ₂.natDegree = μ₁.natDegree := by
    calc μ₂.natDegree
      _ = μ.natDegree := μ.natDegree_map_eq_of_injective (iterateFrobenius F p s).injective
      _ = Module.finrank F F⟮a⟯ := (IntermediateField.adjoin.finrank hai).symm
      _ = Module.finrank F F⟮a ^ p ^ s⟯ := by rw [adjoin_a_pow_p_eq F p s a]
      _ = μ₁.natDegree := IntermediateField.adjoin.finrank hapi
  /- one divides the other -/
  have hdvd : μ₁ ∣ μ₂ := minpoly.dvd F (a ^ p ^ s) hμ₂aeval.symm
  symm
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hμ₁monic hμ₂monic hdvd (le_of_eq hdeg)

variable [FiniteDimensional F E]

/-- If trace of `a` is non-zero then trace of `a ^ p ^ s` is non-zero
    in a separable extension of characteristic `p`. -/
lemma trace_frob_zero (s : ℕ) (a : E) :
    Algebra.trace F E a ≠ 0 → Algebra.trace F E (a ^ p ^ s) ≠ 0 :=
  fun h ↦
    let ⟨hn, hc⟩ := mul_ne_zero_iff.mp (trace_minpoly F a ▸ h)
    trace_minpoly F (a ^ p ^ s) ▸ adjoin_a_pow_p_eq F p s a ▸
      mul_ne_zero_iff.mpr ⟨hn, neg_ne_zero.mpr <|
        iterateFrobenius_def (R := E) p .. ▸
        minpoly_map_frobenius F p s a ▸
        Polynomial.nextCoeff_map (iterateFrobenius F p s).injective (minpoly F a) ▸
        iterateFrobenius_def (R := F) p .. ▸ pow_ne_zero (p ^ s) (neg_ne_zero.mp hc)⟩

variable (K : Type*) [Field K] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
  [FiniteDimensional E K] [IsPurelyInseparable E K]

variable (E) in
/-- In characteristic `p > 0`, composition of the trace map for separable part and
    `iRed` for purely inseparable one is non-trivial. -/
lemma nontrivial_iRed_frob_trace (s : ℕ) (σ : F →+* F)
    [RingHomCompTriple (iterateFrobenius F p (PurelyInseparable.exponent E K p)) (iterateFrobenius F p s) σ] :
    (Algebra.trace F E).comp (PurelyInseparable.iRed_frobₛₗ F E K p s σ) ≠ 0 := by
  simp [DFunLike.ne_iff]
  let r := PurelyInseparable.exponent E K p + s
  /- Trace is surjective, so there is `a : E` with `Algebra.trace F E a = 1` -/
  obtain ⟨a, ha⟩ := Algebra.trace_surjective F E 1
  replace ha : Algebra.trace F E (a ^ p ^ r) ≠ 0 :=
    trace_frob_zero F p r a (ha ▸ one_ne_zero)
  exact ⟨algebraMap E K a, PurelyInseparable.iRed_frobₛₗ_algebraMap_mid F E K p s a σ ▸ ha⟩

section FiniteDimensional

variable (F A K₁ K₂ : Type*)
variable [Field F] [CommRing A] [Algebra F A]
variable [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂]

variable {K₁ K₂} in
/- Auxiliary lemma to workaround problems with typeclass search. -/
lemma finrank_equality_aux
    {E₁ : IntermediateField F K₁} {E₂ : IntermediateField F K₂}
    (h : Module.finrank F E₁ = Module.finrank F E₂) :
    Module.finrank E₁ K₁ * Module.finrank F K₂ =
    Module.finrank E₂ K₂ * Module.finrank F K₁:= by
  rw [← Module.finrank_mul_finrank F E₁ K₁,
    ← Module.finrank_mul_finrank F E₂ K₂,
    mul_comm, ← mul_assoc]
  apply congrArg (fun (x : ℕ) ↦ x * Module.finrank E₁ K₁)
  rw [mul_comm]
  apply congrArg (fun (x : ℕ) ↦ Module.finrank E₂ K₂ * x)
  exact h.symm

/-- For finite-dimensional extensions `K₁`, `K₂` of `F`, the `F`-algebra `K₁ × K₂`
    is not locally generated. -/
theorem notLocallyGenerated_KK_if_findim [FiniteDimensional F K₁] [FiniteDimensional F K₂]
    (p : ℕ) [ExpChar F p] : ¬isLocallyGenerated F (K₁ × K₂) := by
  intro h
  let E₁ := separableClosure F K₁
  let E₂ := separableClosure F K₂
  haveI : IsPurelyInseparable E₁ K₁ := separableClosure.isPurelyInseparable F K₁
  haveI : IsPurelyInseparable E₂ K₂ := separableClosure.isPurelyInseparable F K₂
  /- Purely inseparable part. -/
  let r₁ : ℕ := PurelyInseparable.exponent E₁ K₁ p
  let r₂ : ℕ := PurelyInseparable.exponent E₂ K₂ p
  let r := max r₁ r₂
  let s₁ : ℕ := r - r₁
  let s₂ : ℕ := r - r₂
  have hrs₁ : r₁ + s₁ = r := by simp only [s₁, Nat.add_sub_cancel' (le_max_left r₁ r₂)]
  have hrs₂ : r₂ + s₂ = r := by simp only [s₂, Nat.add_sub_cancel' (le_max_right r₁ r₂)]
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
  have a_nonzero : a₁ ≠ 0 ∨ a₂ ≠ 0 := by
    by_contra hc
    push_neg at hc
    have hd : 0 < d := Nat.gcd_pos_of_pos_left b₂ (Module.finrank_pos (R := F) (M := E₁))
    have a_coprime : Nat.Coprime a₁' a₂' := Nat.coprime_div_gcd_div_gcd hd
    rcases ‹ExpChar F p› with _ | ⟨hprime⟩
    · simp [a₁, a₂, Nat.cast_eq_zero] at hc
      simp [hc.1, hc.2] at a_coprime
    · simp only [CharP.cast_eq_zero_iff F p] at hc
      rw [← Nat.dvd_gcd_iff, a_coprime, Nat.dvd_one] at hc
      rw [hc] at hprime
      contradiction
  /- Define the semilinear map `T : K₁ × K₂ →ₛₗ[σ] F`. -/
  let σ := iterateFrobenius F p r
  haveI := RingHomCompTriple.iterateFrobenius F p hrs₁
  haveI := RingHomCompTriple.iterateFrobenius F p hrs₂
  let T₁ := Algebra.trace F E₁ ∘ₛₗ PurelyInseparable.iRed_frobₛₗ F E₁ K₁ p s₁ σ ∘ₛₗ LinearMap.fst F K₁ K₂
  let T₂ := Algebra.trace F E₂ ∘ₛₗ PurelyInseparable.iRed_frobₛₗ F E₂ K₂ p s₂ σ ∘ₛₗ LinearMap.snd F K₁ K₂
  -- without `∘ₛₗ` notation:
  -- let T₁ := ((Algebra.trace F E₁).comp (PurelyInseparable.iRed_frobₛₗ F E₁ K₁ p s₁ σ)).comp (LinearMap.fst F K₁ K₂)
  -- let T₂ := ((Algebra.trace F E₂).comp (PurelyInseparable.iRed_frobₛₗ F E₂ K₂ p s₂ σ)).comp (LinearMap.snd F K₁ K₂)
  let T : K₁ × K₂ →ₛₗ[σ] F := a₂ • T₁ - a₁ • T₂
  let U : Subspace F (K₁ × K₂) := LinearMap.ker T
  /- Show `T ≠ 0` (equivalent to `U ≠ K₁ × K₂`). -/
  have hU_ne_top : U ≠ ⊤ := by
    apply (not_congr <| LinearMap.ker_eq_top).mpr
    cases a_nonzero with
    | inl ha₁ =>
        have h := nontrivial_iRed_frob_trace F E₂ p K₂ s₂ σ
        simp [T₂, DFunLike.ne_iff] at h ⊢
        obtain ⟨x, hx⟩ := h
        use 0, x
        simp [T, T₁, T₂]
        exact ⟨ha₁, hx⟩
    | inr ha₂ =>
        have h := nontrivial_iRed_frob_trace F E₁ p K₁ s₁ σ
        simp [T₁, DFunLike.ne_iff] at h ⊢
        obtain ⟨x, hx⟩ := h
        use x, 0
        simp [T, T₁, T₂]
        exact ⟨ha₂, hx⟩
  /- Show that `T` vanishes on local elements. -/
  have hT2 : localElements F (K₁ × K₂) ⊆ U := by
    intro ⟨α₁, α₂⟩ hα
    simp [U, T, T₁, T₂, sub_eq_zero]
    set β₁ : E₁ := PurelyInseparable.iRed_frobₛₗ F E₁ K₁ p s₁ σ α₁
    set β₂ : E₂ := PurelyInseparable.iRed_frobₛₗ F E₂ K₂ p s₂ σ α₂
    /- Goal is now `a₂ * (Algebra.trace F E₁ β₁) = a₁ * (Algebra.trace F E₂ β₂)`. -/
    /- If `α` is local then so is `α ^ p ^ r`. -/
    replace hα := isLocalElement_pow F hα (p ^ r)
    simp at hα
    /- Components of `α ^ p ^ r` have the same minimal polynomial. -/
    replace hα := local_minpoly_eq F (IsIntegral.of_finite F (α₁ ^ p ^ r, α₂ ^ p ^ r)) hα
    /- Rewrite using the fact that `β₁` and `β₂` have the same minimal polynomial. -/
    rw [
      show α₁ ^ p ^ r = algebraMap E₁ K₁ β₁ by
        rw [← hrs₁]
        exact (PurelyInseparable.iRed_frobₛₗ_algebraMap_top F E₁ K₁ p s₁ α₁ σ).symm,
      show α₂ ^ p ^ r = algebraMap E₂ K₂ β₂ by
        rw [← hrs₂]
        exact (PurelyInseparable.iRed_frobₛₗ_algebraMap_top F E₂ K₂ p s₂ α₂ σ).symm,
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
    apply congrArg (fun x : ℕ ↦ x * -(minpoly F β₂).nextCoeff)
    rw [mul_comm, mul_comm a₁' _, ← Nat.mul_div_assoc _ hb₁d, ← Nat.mul_div_assoc _ hb₂d]
    apply congrArg (fun x ↦ x / d)
    exact finrank_equality_aux F h_finrank_eq
  /- Subspace generated by local elements is proper. -/
  have h_contra : Submodule.span F (localElements F (K₁ × K₂)) < ⊤ :=
    lt_of_le_of_lt
      (Submodule.span_le.mpr hT2) /- local span ≤ U -/
      (lt_top_iff_ne_top.mpr hU_ne_top) /- U < ⊤ -/
  exact (lt_top_iff_ne_top.mp h_contra) h

/-- Uniform definition of `FiniteDimensional` to be used in the generic theorem.
    Original definition is:
      FiniteDimensional (K : Type u_1) (V : Type u_2) [DivisionRing K] [AddCommGroup V] [Module K V] : Prop
  -/
def UFiniteDimensional : Prop := FiniteDimensional F A

/-- For finite-dimensional extensions `K₁`, `K₂` of `F`, the `F`-algebra `K₁ × K₂`
    is not locally generated.
    Version to be used with generic theorem. -/
theorem notLocallyGenerated_KK_if_findim' :
    UFiniteDimensional F K₁ → UFiniteDimensional F K₂ → ¬isLocallyGenerated F (K₁ × K₂) := by
  intro fdK₁ fdK₂
  haveI : FiniteDimensional F K₁ := fdK₁
  haveI : FiniteDimensional F K₂ := fdK₂
  letI p := ringExpChar F
  haveI : ExpChar F p := inferInstance
  exact notLocallyGenerated_KK_if_findim F K₁ K₂ p

variable {F A} in
/-- Finite-dimensional algebras are local if they are locally generated. -/
theorem isLocalRing_if_isLocallyGenerated_findim [Nontrivial A] [FiniteDimensional F A]
    (hLG : isLocallyGenerated F A) : IsLocalRing A := by
  have h : UFiniteDimensional F A := ‹FiniteDimensional F A›
  refine isLocalAlgebra_if_isLocallyGenerated F ?_ notLocallyGenerated_KK_if_findim' h hLG
  intro _ _ _ _ _ _ _ _ f hf hA
  exact hA.of_surjective f hf

end FiniteDimensional
