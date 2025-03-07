import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import LocalRings.Basic
import LocalRings.Utils.PurelyInseparable

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

lemma interateFrobenius_algebraMap_comm (p : ℕ) [ExpChar F p] [ExpChar E p] (s : ℕ) :
    (algebraMap F E).comp (iterateFrobenius F p s) =
    (iterateFrobenius E p s).comp (algebraMap F E) :=
  RingHom.ext (fun x ↦
    ((algebraMap F E).comp_apply (iterateFrobenius F p s) x).trans <|
    (congrArg (algebraMap F E) (iterateFrobenius_def p s x)).trans <|
    ((algebraMap F E).map_pow x (p ^ s)).trans <|
    (iterateFrobenius_def p s (algebraMap F E x)).symm.trans <|
    ((iterateFrobenius E p s).comp_apply (algebraMap F E) x).symm)

variable [Algebra.IsSeparable F E] [ExpChar E p]

open scoped IntermediateField

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
      _ = Module.finrank F F⟮a ^ p ^ s⟯ := by
        rw [IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable' F E a p s]
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
    let ⟨hn, hc⟩ := mul_ne_zero_iff.mp (trace_eq_finrank_mul_minpoly_nextCoeff F a ▸ h)
    trace_eq_finrank_mul_minpoly_nextCoeff F (a ^ p ^ s) ▸
      IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable' F E a p s ▸
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
lemma nontrivial_iteratedFrobenius_frob_trace {s : ℕ} (hs : IsPurelyInseparable.exponent E K ≤ s) :
    (Algebra.trace F E).comp (IsPurelyInseparable.iterateFrobeniusₛₗ F E K p hs) ≠ 0 := by
  haveI : ExpChar E p := expChar_of_injective_ringHom (algebraMap F E).injective p
  simp [DFunLike.ne_iff]
  /- Trace is surjective, so there is `a : E` with `Algebra.trace F E a = 1` -/
  obtain ⟨a, ha⟩ := Algebra.trace_surjective F E 1
  replace ha : Algebra.trace F E (a ^ p ^ s) ≠ 0 := trace_frob_zero F p s a (ha ▸ one_ne_zero)
  exact ⟨algebraMap E K a, IsPurelyInseparable.iterateFrobeniusₛₗ_algebraMap_bot F E K p hs a ▸ ha⟩

section FiniteDimensional

variable {F A K₁ K₂ : Type*}
variable [Field F] [CommRing A] [Algebra F A]
variable [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂]

/- Auxiliary lemma to workaround problems with typeclass search. -/
lemma finrank_equality_aux {E₁ : IntermediateField F K₁} {E₂ : IntermediateField F K₂}
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
  haveI : ExpChar E₁ p := expChar_of_injective_ringHom (algebraMap F E₁).injective p
  haveI : ExpChar E₂ p := expChar_of_injective_ringHom (algebraMap F E₂).injective p
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
  have a_nonzero : a₁ ≠ 0 ∨ a₂ ≠ 0 := by
    by_contra hc
    push_neg at hc
    have hd : 0 < d := Nat.gcd_pos_of_pos_left b₂ (Module.finrank_pos (R := F) (M := E₁))
    have a_coprime : Nat.Coprime a₁' a₂' := Nat.coprime_div_gcd_div_gcd hd
    rcases ‹ExpChar F p› with _ | ⟨hprime⟩
    · simp [a₁, a₂, Nat.cast_eq_zero] at hc
      simp [hc.1, hc.2] at a_coprime
    · simp only [a₁, a₂, CharP.cast_eq_zero_iff F p] at hc
      rw [← Nat.dvd_gcd_iff, a_coprime, Nat.dvd_one] at hc
      rw [hc] at hprime
      contradiction
  /- Define the semilinear map `T : K₁ × K₂ →ₛₗ[σ] F`. -/
  let T₁ := Algebra.trace F E₁ ∘ₛₗ IsPurelyInseparable.iterateFrobeniusₛₗ F E₁ K₁ p hr₁ ∘ₛₗ LinearMap.fst F K₁ K₂
  let T₂ := Algebra.trace F E₂ ∘ₛₗ IsPurelyInseparable.iterateFrobeniusₛₗ F E₂ K₂ p hr₂ ∘ₛₗ LinearMap.snd F K₁ K₂
  let T : K₁ × K₂ →ₛₗ[_] F := a₂ • T₁ - a₁ • T₂
  let U : Subspace F (K₁ × K₂) := LinearMap.ker T
  /- Show `T ≠ 0` (equivalent to `U ≠ K₁ × K₂`). -/
  have hU_ne_top : U ≠ ⊤ := by
    apply (not_congr <| LinearMap.ker_eq_top).mpr
    cases a_nonzero with
    | inl ha₁ =>
        have h := nontrivial_iteratedFrobenius_frob_trace F E₂ p K₂ hr₂
        simp [T₂, DFunLike.ne_iff] at h ⊢
        obtain ⟨x, hx⟩ := h
        use 0, x
        simp [T, T₁, T₂]
        exact ⟨ha₁, hx⟩
    | inr ha₂ =>
        have h := nontrivial_iteratedFrobenius_frob_trace F E₁ p K₁ hr₁
        simp [T₁, DFunLike.ne_iff] at h ⊢
        obtain ⟨x, hx⟩ := h
        use x, 0
        simp [T, T₁, T₂]
        exact ⟨ha₂, hx⟩
  /- Show that `T` vanishes on local elements. -/
  have hT2 : localElements F (K₁ × K₂) ⊆ U := by
    intro ⟨α₁, α₂⟩ hα
    simp [U, T, T₁, T₂, sub_eq_zero]
    have hβ₁ := IsPurelyInseparable.iterateFrobeniusₛₗ_algebraMap_top F E₁ K₁ p hr₁ α₁
    have hβ₂ := IsPurelyInseparable.iterateFrobeniusₛₗ_algebraMap_top F E₂ K₂ p hr₂ α₂
    set β₁ : E₁ := IsPurelyInseparable.iterateFrobeniusₛₗ F E₁ K₁ p hr₁ α₁
    set β₂ : E₂ := IsPurelyInseparable.iterateFrobeniusₛₗ F E₂ K₂ p hr₂ α₂
    /- Goal is now `a₂ * (Algebra.trace F E₁ β₁) = a₁ * (Algebra.trace F E₂ β₂)`. -/
    /- If `α` is local then so is `α ^ p ^ r`. -/
    replace hα := isLocalElement_pow hα (p ^ r)
    /- Components of `α ^ p ^ r` have the same minimal polynomial. -/
    replace hα := local_minpoly_eq (IsIntegral.of_finite F (α₁ ^ p ^ r, α₂ ^ p ^ r)) hα
    /- Rewrite using the fact that `β₁` and `β₂` have the same minimal polynomial. -/
    rw [← hβ₁, ← hβ₂,
      minpoly.algebraMap_eq (algebraMap E₁ K₁).injective,
      minpoly.algebraMap_eq (algebraMap E₂ K₂).injective] at hα
    /- Extensions `F⟮β₁⟯` and `F⟮β₂⟯` have equal degrees over `F`. -/
    have h_finrank_eq :=
      IntermediateField.adjoin.finrank (IsIntegral.of_finite F β₂) ▸
      hα ▸
      IntermediateField.adjoin.finrank (IsIntegral.of_finite F β₁)
    rw [trace_eq_finrank_mul_minpoly_nextCoeff F β₁, trace_eq_finrank_mul_minpoly_nextCoeff F β₂,
      show a₁ = (a₁' : F) by rfl,
      show a₂ = (a₂' : F) by rfl,
      ← mul_assoc, ← mul_assoc,
      congrArg Polynomial.nextCoeff hα,
      ← Nat.cast_mul, ← Nat.cast_mul]
    apply congrArg (fun x : ℕ ↦ x * -(minpoly F β₂).nextCoeff)
    rw [mul_comm, mul_comm a₁' _, ← Nat.mul_div_assoc _ hb₁d, ← Nat.mul_div_assoc _ hb₂d]
    apply congrArg (fun x ↦ x / d)
    exact finrank_equality_aux h_finrank_eq
  /- Subspace generated by local elements is proper. -/
  have h_contra : Submodule.span F (localElements F (K₁ × K₂)) < ⊤ :=
    lt_of_le_of_lt
      (Submodule.span_le.mpr hT2) /- local span ≤ U -/
      (lt_top_iff_ne_top.mpr hU_ne_top) /- U < ⊤ -/
  exact (lt_top_iff_ne_top.mp h_contra) h

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
theorem notLocallyGenerated_KK_if_findim' :
    UFiniteDimensional F K₁ → UFiniteDimensional F K₂ → ¬isLocallyGenerated F (K₁ × K₂) :=
  fun fdK₁ fdK₂ ↦
    haveI : FiniteDimensional F K₁ := fdK₁
    haveI : FiniteDimensional F K₂ := fdK₂
    letI p := ringExpChar F
    haveI : ExpChar F p := inferInstance
    notLocallyGenerated_KK_if_findim p

/-- Finite-dimensional algebras are local if they are locally generated. -/
theorem isLocalRing_if_isLocallyGenerated_findim [Nontrivial A] [FiniteDimensional F A]
    (hLG : isLocallyGenerated F A) : IsLocalRing A :=
  haveI h : UFiniteDimensional F A := ‹FiniteDimensional F A›
  isLocalAlgebra_if_isLocallyGenerated
    (fun f hf hA ↦ hA.of_surjective f hf)
    notLocallyGenerated_KK_if_findim' h hLG

end FiniteDimensional
