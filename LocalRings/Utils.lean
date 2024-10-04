import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Subring.Basic

import Mathlib.FieldTheory.Adjoin
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.PurelyInseparable
import Mathlib.FieldTheory.Perfect

import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Artinian
import Mathlib.RingTheory.JacobsonIdeal
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic


/-- Mathlib, really? No such theorem? -/
protected theorem Nat.pow_eq_pow_iff_right {a n m : Nat} (h : 1 < a) : a ^ n = a ^ m ↔ n = m := by
  apply Iff.intro
  · intro ha
    exact LE.le.antisymm
      ((Nat.pow_le_pow_iff_right h).mp (le_of_eq ha))
      ((Nat.pow_le_pow_iff_right h).mp (le_of_eq ha.symm))
  · intro he
    rw [he]

variable {R : Type u} [CommRing R]

lemma isUnit_subring {S : Subring R} {a : S} (h : IsUnit a) : IsUnit (a : R) := by
  exact IsUnit.map S.subtype h

/-- Equivalent condition for a ring `R` not to be local. -/
lemma nonLocalDef [Nontrivial R] (h : ¬LocalRing R) : ∃ a : R, ¬IsUnit a ∧ ¬IsUnit (1 - a) := by
  by_contra hn
  simp [not_exists, ←not_or] at hn
  exact h (LocalRing.of_isUnit_or_isUnit_one_sub_self hn)

lemma nonLocalProj [Nontrivial R] (h : ¬LocalRing R) :
    ∃ (K₁ K₂ : Type u) (fK₁ : Field K₁) (fK₂ : Field K₂) (f : R →+* K₁ × K₂), Function.Surjective f := by
  /- get two maximal ideals and project -/
  obtain ⟨a, ⟨hnua, hnub⟩⟩ := nonLocalDef h
  have hnua1 : a ∈ nonunits R := by rwa [←mem_nonunits_iff] at hnua
  have hnub1 : 1 - a ∈ nonunits R := by rwa [←mem_nonunits_iff] at hnub
  obtain ⟨m₁, ⟨_, ham⟩⟩ := exists_max_ideal_of_mem_nonunits hnua1
  obtain ⟨m₂, ⟨_, hbm⟩⟩ := exists_max_ideal_of_mem_nonunits hnub1
  have coprime : IsCoprime m₁ m₂ := by
    rw [Ideal.isCoprime_iff_exists]
    use a, ham, 1 - a, hbm
    ring
  -- `R →+* R ⧸ m₁ ⊓ m₂`
  let g := Ideal.Quotient.mk (m₁ ⊓ m₂)
  -- `R ⧸ m₁ ⊓ m₂ ≃+* (R ⧸ m₁) × R ⧸ m₂`
  let e := Ideal.quotientInfEquivQuotientProd m₁ m₂ coprime
  let K₁ := R ⧸ m₁
  let K₂ := R ⧸ m₂
  let fK₁ : Field K₁ := Ideal.Quotient.field m₁
  let fK₂ : Field K₂ := Ideal.Quotient.field m₂
  let f := RingHom.comp (e : R ⧸ m₁ ⊓ m₂ →+* K₁ × K₂) g
  use K₁, K₂, fK₁, fK₂, f
  apply Function.Surjective.comp e.surjective Ideal.Quotient.mk_surjective

/- If `f '' S₁ ⊆ S₂` then the image of the span of `S₁` is a submodule of the span of `S₂`. -/
lemma span_transfer {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂] {S₁ : Set M₁} {S₂ : Set M₂} {f : M₁ →ₗ[R] M₂}
    (h : f '' S₁ ⊆ S₂) : (Submodule.span R S₁).map f ≤ Submodule.span R S₂ := by
  have h1 : Submodule.span R (f '' S₁) ≤ Submodule.span R S₂ := Submodule.span_mono h
  have h2 : (Submodule.span R S₁).map f ≤ Submodule.span R (f '' S₁) := by
    rw [Submodule.map_span_le]
    intro m hm
    exact (Submodule.subset_span : f '' S₁ ⊆ Submodule.span R (f '' S₁)) (Set.mem_image_of_mem f hm)
  exact Set.Subset.trans h2 h1

/-- Transfer `R`-algebra structure via ring homomorphism. -/
def algebra_fromRingHom {A₁ A₂ : Type*} [Semiring A₁] [CommSemiring A₂]
    [Algebra R A₁] (f : A₁ →+* A₂) : Algebra R A₂ :=
  (f.comp (algebraMap R A₁)).toAlgebra

theorem artinian_reduced_local_is_field (R : Type u) [CommRing R] [IsArtinianRing R] [IsReduced R]
    [LocalRing R] : IsField R := by
  have h : LocalRing.maximalIdeal R = 0 := by
    calc LocalRing.maximalIdeal R
      _ = (0 : Ideal R).jacobson := (LocalRing.jacobson_eq_maximalIdeal 0 bot_ne_top).symm
      _ = (0 : Ideal R).radical := by
        simp_rw [Ideal.radical_eq_sInf 0, IsArtinianRing.isPrime_iff_isMaximal]
        rfl
      _ = nilradical R := rfl
      _ = 0 := nilradical_eq_zero R
  rwa [LocalRing.isField_iff_maximalIdeal_eq]

section TensorProduct

variable {R M₁ M₂ : Type u} [CommRing R] [NoZeroDivisors R]
variable [AddCommGroup M₁] [Module R M₁] [Module.Free R M₁]
variable [AddCommGroup M₂] [Module R M₂] [Module.Free R M₂]

open scoped TensorProduct

instance nontrivial_tensor [Nontrivial R] [Nontrivial M₁] [Nontrivial M₂] :
    Nontrivial (M₁ ⊗[R] M₂) := by
  have h₁ : 0 < Module.rank R M₁ := by apply rank_pos_iff_nontrivial.mpr; assumption
  have h₂ : 0 < Module.rank R M₂ := by apply rank_pos_iff_nontrivial.mpr; assumption
  have h := CanonicallyOrderedCommSemiring.mul_pos.mpr ⟨h₁, h₂⟩
  rw [← rank_tensorProduct'] at h
  exact rank_pos_iff_nontrivial.mp h

def compositum (F K₁ K₂ : Type u) [Field F] [Field K₁] [Field K₂] [Algebra F K₁] [Algebra F K₂] :
    ∃ (L : Type u) (fL : Field L) (aFL : Algebra F L) (ι₁ : K₁ →ₐ[F] L) (ι₂ : K₂ →ₐ[F] L),
        Function.Injective ι₁ ∧ Function.Injective ι₂ ∧
        Module.rank F L ≤ (Module.rank F K₁) * (Module.rank F K₂) := by
  let A := (K₁ ⊗[F] K₂)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let L := A ⧸ m
  let fL : Field L := Ideal.Quotient.field m
  let aFL : Algebra F L := inferInstance
  let π : A →ₐ[F] L := { Ideal.Quotient.mk m with commutes' := fun _ => rfl }
  let ι₁ : K₁ →ₐ[F] L := π.comp (Algebra.TensorProduct.includeLeft)
  let ι₂ : K₂ →ₐ[F] L := π.comp (Algebra.TensorProduct.includeRight)
  use L, fL, aFL, ι₁, ι₂
  exact ⟨ι₁.injective, ι₂.injective, by
    calc Module.rank F L
      _ ≤ Module.rank F A := LinearMap.rank_le_of_surjective π.toLinearMap Ideal.Quotient.mk_surjective
      _ = (Module.rank F K₁) * (Module.rank F K₂) := rank_tensorProduct'⟩

end TensorProduct

section PurelyInseparable

theorem charP_of_expChar_prime' [ExpChar R p] (hp : p ≠ 1) : CharP R p := by
  cases ‹ExpChar R p›
  · contradiction
  · assumption

open scoped IntermediateField

theorem purelyInseparable_char0 (F K : Type u) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsPurelyInseparable F K] [CharZero F] :
    FiniteDimensional.finrank F K = 1 := by
  rw [← FiniteDimensional.rank_eq_one_iff_finrank_eq_one, ← rank_self F]
  haveI : Algebra.IsSeparable F K := ⟨by
    intro x
    exact PerfectField.separable_of_irreducible <| minpoly.irreducible <| IsIntegral.of_finite F x⟩
  exact (Algebra.rank_eq_of_equiv_equiv
    (RingEquiv.refl F)
    (RingEquiv.ofBijective
      (algebraMap F K)
      (IsPurelyInseparable.bijective_algebraMap_of_isSeparable F K))
    rfl).symm

theorem purelyInseparable_natDegree_pow (F : Type u) [Field F] {K : Type u} [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsPurelyInseparable F K] (p : ℕ) [ExpChar F p] (a : K) :
    ∃ ν : ℕ, FiniteDimensional.finrank F F⟮a⟯ = p ^ ν := by
  obtain ⟨k, _, h⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p a
  rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite F a), h,
    Polynomial.natDegree_sub_C, Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
  use k

/-- Degree of a purely inseparable field extension `F ⊆ K` is a power of the characteristic `p`
    (or `1` in case of characteristic zero, cf. `purelyInseparable_char0`) -/
theorem purelyInseparable_finrank_pow (F K : Type u) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsPurelyInseparable F K] {p : ℕ} (hp : p.Prime) [ExpChar F p] :
    ∃! ν : ℕ, FiniteDimensional.finrank F K = p ^ ν := by
  /- adjoin induction -/
  let P (L : IntermediateField F K) : Prop := ∃ k : ℕ, FiniteDimensional.finrank F L = p ^ k
  have base : P ⊥ := by use 0; exact IntermediateField.finrank_bot
  have step : ∀ (L : IntermediateField F K) (a : K), P L → P (L⟮a⟯.restrictScalars F) := by
    intro L a hFL
    obtain ⟨k, hFL⟩ := hFL
    /- `F ⊆ L ⊆ K` => `L ⊆ K` purely inseparable -/
    haveI := IsPurelyInseparable.tower_top F L K
    /- `L ⊆ L⟮a⟯ ⊆ K` => `L ⊆ L⟮a⟯` purely inseparable-/
    haveI := IsPurelyInseparable.tower_bot L L⟮a⟯ K
    obtain ⟨l, hLLx⟩ := purelyInseparable_natDegree_pow L p a
    use k + l
    calc FiniteDimensional.finrank F (L⟮a⟯.restrictScalars F)
      _ = FiniteDimensional.finrank F L⟮a⟯ := rfl
      _ = (FiniteDimensional.finrank F L) * (FiniteDimensional.finrank L L⟮a⟯) :=
        (FiniteDimensional.finrank_mul_finrank F L L⟮a⟯).symm
      _ = p ^ (k + l) := by rw [hFL, hLLx, pow_add p k l]
  have induction_result := IntermediateField.induction_on_adjoin P base step ⊤
  simp_rw [P, IntermediateField.finrank_top'] at induction_result
  obtain ⟨k, hk⟩ := induction_result
  use k
  simp
  have := Nat.Prime.one_lt hp
  apply And.intro
  · assumption
  · intro y
    rw [hk]
    intro hy
    exact (Nat.pow_eq_pow_iff_right <| Nat.Prime.one_lt <| hp).mp hy.symm

lemma expChar_prime_of_ne_one (R : Type u) [Semiring R] {p : ℕ} [ExpChar R p] (hp : p ≠ 1) : p.Prime :=
    Or.resolve_right (expChar_is_prime_or_one R p) hp

noncomputable def finInsepLogRank (F K : Type u) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsPurelyInseparable F K] (p : ℕ) [ExpChar F p] : ℕ :=
  if h : p = 1 then 0 else
    have p_prime := expChar_prime_of_ne_one F h
    Classical.choose (purelyInseparable_finrank_pow F K p_prime)

lemma finInsepLogRank_def (F K : Type u) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsPurelyInseparable F K] (p : ℕ) [ExpChar F p] :
    FiniteDimensional.finrank F K = p ^ (finInsepLogRank F K p) := by
  rw [finInsepLogRank]
  split_ifs with hp
  · haveI := ExpChar.congr F p hp
    haveI : CharZero F := charZero_of_expChar_one' F
    exact purelyInseparable_char0 F K
  · have p_prime := expChar_prime_of_ne_one F hp
    exact (Classical.choose_spec (purelyInseparable_finrank_pow F K p_prime)).1

local instance {F K : Type u} [Field F] [Field K] [Algebra F K] [IsPurelyInseparable F K]
    {E : IntermediateField F K} : IsPurelyInseparable F E :=
  IsPurelyInseparable.tower_bot F E K

local instance {F K : Type u} [Field F] [Field K] [Algebra F K] [IsPurelyInseparable F K]
    {E : IntermediateField F K} : IsPurelyInseparable E K :=
  IsPurelyInseparable.tower_top F E K

lemma finInsepLogRank_tower (F K : Type u) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsPurelyInseparable F K] (E : IntermediateField F K) (p : ℕ) [ExpChar F p] :
        finInsepLogRank F E p + finInsepLogRank E K p = finInsepLogRank F K p := by
  by_cases h : p = 1
  · simp [finInsepLogRank, h]
  · apply (Nat.pow_eq_pow_iff_right <| Nat.Prime.one_lt <| expChar_prime_of_ne_one F h).mp
    rw [pow_add,
      ← finInsepLogRank_def F E p,
      ← finInsepLogRank_def E K p,
      ← finInsepLogRank_def F K p]
    exact FiniteDimensional.finrank_mul_finrank F E K

lemma finInsepLogRank_le_tower_bot (F K : Type u) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsPurelyInseparable F K] (E : IntermediateField F K) (p : ℕ) [ExpChar F p] :
        finInsepLogRank F E p ≤ finInsepLogRank F K p := by
  calc finInsepLogRank F E p
    _ ≤ finInsepLogRank F E p + finInsepLogRank E K p := Nat.le_add_right _ _
    _ = finInsepLogRank F K p := finInsepLogRank_tower _ _ _ _

lemma IsPurelyInseparable.minpoly_natDegree (F : Type u) [Field F] {K : Type u} [Field K]
    [Algebra F K] [FiniteDimensional F K] [IsPurelyInseparable F K] (p : ℕ) [ExpChar F p]
    (a : K) : (minpoly F a).natDegree = p ^ (finInsepLogRank F F⟮a⟯ p) := by
  obtain ⟨k, b, h⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p a
  rw [finInsepLogRank]
  simp
  split_ifs with hp
  · simp [h, hp]
  · have p_prime := expChar_prime_of_ne_one F hp
    rw [← (Classical.choose_spec (purelyInseparable_finrank_pow F F⟮a⟯ p_prime)).1]
    symm
    exact IntermediateField.adjoin.finrank (IsIntegral.of_finite F a)

noncomputable def iRed_aux (F : Type u) [Field F] {K : Type u} [Field K] [Algebra F K] [FiniteDimensional F K]
    (a : K) : F :=
  - Polynomial.aeval 0 (minpoly F a) /- `= - (minpoly F a).coeff 0` -/

lemma iRed_aux_algebraMap (F : Type u) [Field F] {K : Type u} [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsPurelyInseparable F K] (p : ℕ) [ExpChar F p] (a : K) :
        algebraMap F K (iRed_aux F a) = a ^ p ^ (finInsepLogRank F F⟮a⟯ p) := by
  rw [← IsPurelyInseparable.minpoly_natDegree F p a]
  obtain ⟨k, b, h⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p a
  simp [h, iRed_aux, zero_pow <| pow_ne_zero k <| pos_iff_ne_zero.mp <| expChar_pos F p]
  have h1 := minpoly.aeval F a
  simp [h, sub_eq_zero] at h1
  exact h1.symm

noncomputable def iRed' (F K : Type u) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsPurelyInseparable F K] (p : ℕ) [ExpChar F p] : K → F :=
  fun a : K => (iRed_aux F a) ^ p ^ finInsepLogRank F⟮a⟯ K p

lemma iRed'_algebraMap (F : Type u) [Field F] {K : Type u} [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsPurelyInseparable F K] (p : ℕ) [ExpChar F p] (a : K) :
        algebraMap F K (iRed' F K p a) = a ^ p ^ finInsepLogRank F K p := by
  rw [iRed',
    RingHom.map_pow (algebraMap F K) (iRed_aux F a) (p ^ finInsepLogRank F⟮a⟯ K p),
    iRed_aux_algebraMap F p a,
    ← pow_mul, ← pow_add,
    finInsepLogRank_tower]

/-- Inseparable reduction map.
    It is a ring homomorphism, so in particular it is injective. This, together with
    `algebraMap F K` (also injective), shows that for a purely inseparable field extension
    `F ⊆ K`, `F` and `K` have the same cardinality. -/
noncomputable def iRed (F K : Type u) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    [IsPurelyInseparable F K] : K →+* F where
  toFun := iRed' F K (ringExpChar F)
  map_zero' := by
    simp [iRed', iRed_aux]
    intro hp
    exfalso
    have : 1 ≤ ringExpChar F := by simp [ringExpChar]
    linarith -- `rw [hp] at this` yields `1 ≤ 0`
  map_add' := by
    intro a b
    simp
    have inj := (algebraMap F K).injective
    apply inj
    let p := ringExpChar F
    haveI : ExpChar K p := expChar_of_injective_ringHom inj p
    rw [(algebraMap F K).map_add,
      iRed'_algebraMap F p a,
      iRed'_algebraMap F p b,
      iRed'_algebraMap F p (a + b),
      add_pow_expChar_pow K a b]
  map_one' := by
    simp [iRed', iRed_aux]
  map_mul' := by
    intro a b
    simp
    apply (algebraMap F K).injective
    let p := ringExpChar F
    rw [(algebraMap F K).map_mul,
      iRed'_algebraMap F p a,
      iRed'_algebraMap F p b,
      iRed'_algebraMap F p (a * b),
      mul_pow]

end PurelyInseparable
