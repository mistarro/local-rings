import Mathlib.FieldTheory.Adjoin
import Mathlib.FieldTheory.PurelyInseparable
import Mathlib.RingTheory.Trace.Basic

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Monic

import LocalRings.Utils.Basic
import LocalRings.Utils.PurelyInseparable

/-!
# Results for trace from separable closure.
-/

open scoped IntermediateField

variable (F : Type u) [Field F] {E : Type u} [Field E] [Algebra F E]

/-- Classical result about trace map and minimal polynomial coefficient. -/
lemma trace_minpoly [FiniteDimensional F E] (a : E) :
    Algebra.trace F E a = FiniteDimensional.finrank F⟮a⟯ E * -(minpoly F a).nextCoeff := by
  let a' := IntermediateField.AdjoinSimple.gen F a
  let n := FiniteDimensional.finrank F⟮a⟯ E
  let pb := IntermediateField.adjoin.powerBasis (IsIntegral.of_finite F a)
  calc Algebra.trace F E a
    _ = n • Algebra.trace F F⟮a⟯ a' := trace_eq_trace_adjoin F a
    _ = n • Algebra.trace F F⟮a⟯ pb.gen := rfl
    _ = n • -(minpoly F pb.gen).nextCoeff := by
      rw [PowerBasis.trace_gen_eq_nextCoeff_minpoly pb]
    _ = n • -(minpoly F (algebraMap F⟮a⟯ E pb.gen)).nextCoeff := by
      rw [← minpoly.algebraMap_eq (algebraMap F⟮a⟯ E).injective pb.gen]
    _ = n • -(minpoly F (algebraMap F⟮a⟯ E a')).nextCoeff := rfl
    _ = n • -(minpoly F a).nextCoeff := by
      rw [IntermediateField.AdjoinSimple.algebraMap_gen F a]
    _ = n * -(minpoly F a).nextCoeff := by rw [Algebra.smul_def]; rfl

variable [Algebra.IsSeparable F E]
variable (p : ℕ) [ExpChar F p]

/-- For a separable extension `F ⊆ E` of characteristic `p > 0`,
    adjoining `a` to `F` is same as adjoining `a ^ p ^ s`. -/
lemma adjoin_a_pow_p_eq (s : ℕ) (a : E) : F⟮a ^ p ^ s⟯ = F⟮a⟯ := by
  have ha : a ∈ F⟮a⟯ := IntermediateField.mem_adjoin_simple_self F a
  have hap : a ^ p ^ s ∈ F⟮a⟯ := pow_mem ha (p ^ s)
  let L := F⟮a ^ p ^ s⟯
  let L' := L⟮a⟯
  by_cases h : a ∈ L
  · exact LE.le.antisymm
      (IntermediateField.adjoin_simple_le_iff.mpr hap)
      (IntermediateField.adjoin_simple_le_iff.mpr h)
  · exfalso
    /- `a ∉ F⟮a ^ p ^ s⟯` so `F⟮a ^ p ^ s⟯ < F⟮a⟯` is purely inseparable (and separable). -/
    suffices IsPurelyInseparable L L' by
      haveI : Algebra.IsSeparable L E := Algebra.isSeparable_tower_top_of_isSeparable F L E
      haveI : Algebra.IsSeparable L L' := Algebra.isSeparable_tower_bot_of_isSeparable L L' E
      have :=
        IntermediateField.mem_bot.mp <|
        IntermediateField.adjoin_simple_eq_bot_iff.mp <|
        IntermediateField.eq_bot_of_isPurelyInseparable_of_isSeparable L'
      simp at this
      exact h this
    simp_rw [IntermediateField.isPurelyInseparable_adjoin_simple_iff_pow_mem L E p]
    use s
    simp
    exact IntermediateField.mem_adjoin_simple_self F (a ^ p ^ s)

variable [ExpChar E p] in
/-- For a separable extension `F ⊆ E` of characteristic `p > 0`,
    the minimal polynomial of `a ^ p ^ s` is the minimal polynomial of `a` mapped via `(⬝ ^ p ^ s)`. -/
lemma minpoly_map_frobenius (s : ℕ) (a : E) :
    minpoly F (iterateFrobenius E p s a) = (minpoly F a).map (iterateFrobenius F p s) := by
  let μ := minpoly F a
  let μ₁ := minpoly F (a ^ p ^ s)
  let μ₂ := μ.map (iterateFrobenius F p s)
  /- goal: `μ₁ = μ₂` -/
  have h_aMap_Frob_comm :
      (algebraMap F E).comp (iterateFrobenius F p s) = (iterateFrobenius E p s).comp (algebraMap F E) := by
    ext x
    simpa [coe_iterateFrobenius F p s, coe_iterateFrobenius E p s]
      using RingHom.map_iterate_frobenius (algebraMap F E) p x s
  have hμ₂aeval :
    (iterateFrobenius E p s) (Polynomial.aeval a μ) = Polynomial.aeval (iterateFrobenius E p s a) μ₂ :=
      Polynomial.map_aeval_eq_aeval_map h_aMap_Frob_comm μ a
  rw [minpoly.aeval, RingHom.map_zero, iterateFrobenius_def] at hμ₂aeval
  have hai : IsIntegral F a := IsSeparable.isIntegral (Algebra.IsSeparable.isSeparable F a)
  have hapi : IsIntegral F (a ^ p ^ s) := IsSeparable.isIntegral (Algebra.IsSeparable.isSeparable F (a ^ p ^ s))
  /- both are monic -/
  have hμ₁monic : μ₁.Monic := (minpoly.monic hapi)
  have hμ₂monic : μ₂.Monic := (minpoly.monic hai).map (iterateFrobenius F p s)
  /- both have same degree -/
  have hdeg : μ₁.natDegree = μ₂.natDegree := by
    calc μ₁.natDegree
      _ = FiniteDimensional.finrank F F⟮a ^ p ^ s⟯ := (IntermediateField.adjoin.finrank hapi).symm
      _ = FiniteDimensional.finrank F F⟮a⟯ := by rw [adjoin_a_pow_p_eq F p s a]
      _ = μ.natDegree := IntermediateField.adjoin.finrank hai
      _ = μ₂.natDegree := (Polynomial.natDegree_map_eq_of_injective (iterateFrobenius F p s).injective μ).symm
  /- one divides the other -/
  have hdvd : μ₁ ∣ μ₂ := minpoly.dvd F (a ^ p ^ s) hμ₂aeval.symm
  exact Polynomial.eq_of_monic_of_eq_deg_of_dvd hμ₁monic hμ₂monic hdeg hdvd

variable [FiniteDimensional F E]

/-- Auxiliary lemma: if trace of `a` is non-zero then trace of `a ^ p ^ s` is non-zero in a separable extension. -/
lemma trace_a_frob_0 [ExpChar E p] (s : ℕ) (a : E) :
    Algebra.trace F E a ≠ 0 → Algebra.trace F E (a ^ p ^ s) ≠ 0 := by
  intro h
  obtain ⟨hn, hc⟩ := mul_ne_zero_iff.mp (trace_minpoly F a ▸ h)
  rw [trace_minpoly F (a ^ p ^ s), adjoin_a_pow_p_eq F p s a]
  apply mul_ne_zero_iff.mpr
  apply And.intro
  · assumption
  · rw [neg_ne_zero] at *
    rwa [← iterateFrobenius_def,
      minpoly_map_frobenius,
      Polynomial.nextCoeff_map (iterateFrobenius F p s).injective,
      iterateFrobenius_def,
      pow_ne_zero_iff (ne_of_lt (expChar_pow_pos F p s)).symm]

variable (K : Type u) [Field K] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
  [FiniteDimensional E K] [IsPurelyInseparable E K] (p : ℕ) [ExpChar E p] [ExpChar F p]

variable (E) in
/-- In characteristic `p > 0`, composition of the trace map for separable part and
    `iRed` for purely inseparable one is non-trivial. -/
lemma nontrivial_trace_iRed_frob (s : ℕ) (σ : F →+* F)
    [RingHomCompTriple (iterateFrobenius F p (finInsepLogRank E K p)) (iterateFrobenius F p s) σ] :
    (Algebra.trace F E).comp (iRed_frobₛₗ F E K p s σ) ≠ 0 := by
  let r := finInsepLogRank E K p + s
  /- Trace is surjective, so there is `a : E` with `Algebra.trace F E a = 1` -/
  obtain ⟨a, ha⟩ := Algebra.trace_surjective F E 1
  replace ha : Algebra.trace F E a ≠ 0 := by rw [ha]; exact one_ne_zero
  replace ha : Algebra.trace F E (a ^ p ^ r) ≠ 0 := trace_a_frob_0 F p r a ha
  have := iRed_frobₛₗ_algebraMap_mid F E K p s a σ
  simp [DFunLike.ne_iff]
  use algebraMap E K a
  rwa [this]
