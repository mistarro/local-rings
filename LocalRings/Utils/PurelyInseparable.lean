import Mathlib.FieldTheory.PurelyInseparable

import LocalRings.Utils.Basic

section PurelyInseparable

variable {R : Type u} [Semiring R]

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

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [IsPurelyInseparable F K]

local instance {E : IntermediateField F K} : IsPurelyInseparable F E :=
  IsPurelyInseparable.tower_bot F E K

local instance {E : IntermediateField F K} : IsPurelyInseparable E K :=
  IsPurelyInseparable.tower_top F E K

variable [FiniteDimensional F K] (p : ℕ) [ExpChar F p]
variable (F K)

noncomputable def finInsepLogRank : ℕ :=
  if h : p = 1 then 0 else
    have p_prime := expChar_prime_of_ne_one F h
    Classical.choose (purelyInseparable_finrank_pow F K p_prime)

lemma finInsepLogRank_def : FiniteDimensional.finrank F K = p ^ (finInsepLogRank F K p) := by
  rw [finInsepLogRank]
  split_ifs with hp
  · haveI := ExpChar.congr F p hp
    haveI : CharZero F := charZero_of_expChar_one' F
    exact purelyInseparable_char0 F K
  · have p_prime := expChar_prime_of_ne_one F hp
    exact (Classical.choose_spec (purelyInseparable_finrank_pow F K p_prime)).1

lemma finInsepLogRank_tower (E : IntermediateField F K) :
        finInsepLogRank F E p + finInsepLogRank E K p = finInsepLogRank F K p := by
  by_cases h : p = 1
  · simp [finInsepLogRank, h]
  · apply (Nat.pow_eq_pow_iff_right <| Nat.Prime.one_lt <| expChar_prime_of_ne_one F h).mp
    rw [pow_add,
      ← finInsepLogRank_def F E p,
      ← finInsepLogRank_def E K p,
      ← finInsepLogRank_def F K p]
    exact FiniteDimensional.finrank_mul_finrank F E K

lemma finInsepLogRank_le_tower_bot (E : IntermediateField F K) :
        finInsepLogRank F E p ≤ finInsepLogRank F K p := by
  calc finInsepLogRank F E p
    _ ≤ finInsepLogRank F E p + finInsepLogRank E K p := Nat.le_add_right _ _
    _ = finInsepLogRank F K p := finInsepLogRank_tower _ _ _ _

variable {K}

lemma IsPurelyInseparable.minpoly_natDegree (a : K) : (minpoly F a).natDegree = p ^ (finInsepLogRank F F⟮a⟯ p) := by
  obtain ⟨k, b, h⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p a
  rw [finInsepLogRank]
  simp
  split_ifs with hp
  · simp [h, hp]
  · have p_prime := expChar_prime_of_ne_one F hp
    rw [← (Classical.choose_spec (purelyInseparable_finrank_pow F F⟮a⟯ p_prime)).1]
    symm
    exact IntermediateField.adjoin.finrank (IsIntegral.of_finite F a)

noncomputable def iRed_aux (a : K) : F := - Polynomial.aeval 0 (minpoly F a) /- `= - (minpoly F a).coeff 0` -/

lemma iRed_aux_algebraMap (a : K) : algebraMap F K (iRed_aux F a) = a ^ p ^ (finInsepLogRank F F⟮a⟯ p) := by
  rw [← IsPurelyInseparable.minpoly_natDegree F p a]
  obtain ⟨k, b, h⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p a
  simp [h, iRed_aux, zero_pow <| pow_ne_zero k <| pos_iff_ne_zero.mp <| expChar_pos F p]
  have h1 := minpoly.aeval F a
  simp [h, sub_eq_zero] at h1
  exact h1.symm

variable (K) in
noncomputable def iRed' : K → F := fun a : K => (iRed_aux F a) ^ p ^ finInsepLogRank F⟮a⟯ K p

lemma iRed'_algebraMap (a : K) : algebraMap F K (iRed' F K p a) = a ^ p ^ finInsepLogRank F K p := by
  rw [iRed',
    RingHom.map_pow (algebraMap F K) (iRed_aux F a) (p ^ finInsepLogRank F⟮a⟯ K p),
    iRed_aux_algebraMap F p a,
    ← pow_mul, ← pow_add,
    finInsepLogRank_tower]

variable (K)

lemma iRed'_map_zero : iRed' F K p 0 = 0 := by
  simp [iRed', iRed_aux]
  intro hp
  exfalso
  have := expChar_pos F p
  linarith -- `rw [hp] at this` yields `0 < 0`

lemma iRed'_map_add (a b : K) : iRed' F K p (a + b) = iRed' F K p a + iRed' F K p b := by
  have inj := (algebraMap F K).injective
  apply inj
  haveI : ExpChar K p := expChar_of_injective_ringHom inj p
  rw [(algebraMap F K).map_add,
    iRed'_algebraMap F p a,
    iRed'_algebraMap F p b,
    iRed'_algebraMap F p (a + b),
    add_pow_expChar_pow K a b]

lemma iRed'_map_one : iRed' F K p 1 = 1 := by
  simp [iRed', iRed_aux]

lemma iRed'_map_mul (a b : K) : iRed' F K p (a * b) = iRed' F K p a * iRed' F K p b := by
  apply (algebraMap F K).injective
  rw [(algebraMap F K).map_mul,
    iRed'_algebraMap F p a,
    iRed'_algebraMap F p b,
    iRed'_algebraMap F p (a * b),
    mul_pow]

/-- Inseparable reduction map.
    It is a ring homomorphism, so in particular it is injective. This, together with
    `algebraMap F K` (also injective), shows that for a purely inseparable field extension
    `F ⊆ K`, `F` and `K` have the same cardinality. -/
noncomputable def iRed : K →+* F where
  toFun := iRed' F K p
  map_zero' := iRed'_map_zero F K p
  map_add' := iRed'_map_add F K p
  map_one' := iRed'_map_one F K p
  map_mul' := iRed'_map_mul F K p

noncomputable def iRed_frob (s : ℕ) : K →+* F := (iterateFrobenius F p s).comp (iRed F K p)

end PurelyInseparable

section SemiLinear

variable (F E K : Type u) [Field F] [Field E] [Field K] [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
variable [FiniteDimensional E K] [IsPurelyInseparable E K]
variable (p : ℕ) [ExpChar E p]

instance {m n : ℕ} [ExpChar F p] : RingHomCompTriple (iterateFrobenius F p m)
    (iterateFrobenius F p n) (iterateFrobenius F p (n + m)) :=
  { comp_eq := (iterateFrobenius_add F p n m).symm }

instance {m n : ℕ} [ExpChar F p] : RingHomCompTriple (iterateFrobenius F p m)
    (iterateFrobenius F p n) (iterateFrobenius F p (m + n)) :=
  { comp_eq := by rw [add_comm]; exact (iterateFrobenius_add F p n m).symm }

lemma iRed'_algebraMap' (a : F) : iRed' E K p (algebraMap F K a) = (algebraMap F E a) ^ p ^ finInsepLogRank E K p := by
  have := iRed'_algebraMap E p (algebraMap F K a)
  rw [← map_pow] at this
  apply (algebraMap E K).injective
  rwa [← map_pow, ← IsScalarTower.algebraMap_apply]

variable [ExpChar F p]

def iterateFrobeniusₛₗ (s : ℕ) : E →ₛₗ[iterateFrobenius F p s] E where
  toFun := (iterateFrobenius E p s).toFun
  map_add' := add_pow_expChar_pow E
  map_smul' := by
    intro a x
    simp [Algebra.smul_def, coe_iterateFrobenius]
    apply Or.inl
    symm
    exact (algebraMap F E).map_iterate_frobenius p a s

/-- Inseparable reduction map as a semilinear map over a smaller field. -/
noncomputable def iRedₛₗ : K →ₛₗ[iterateFrobenius F p (finInsepLogRank E K p)] E where
  toFun := iRed' E K p
  map_add' := iRed'_map_add E K p
  map_smul' := by
    intro a x
    simp [Algebra.smul_def]
    rw [iRed'_map_mul, iRed'_algebraMap', iterateFrobenius_def, map_pow]

/-- Inseparable reduction map composed with iterated Frobenius (semilinear map). -/
noncomputable def iRed_frobₛₗ (s : ℕ) :
  K →ₛₗ[iterateFrobenius F p (finInsepLogRank E K p + s)] E :=
  (LinearMap.iterateFrobenius F E p s).comp (iRedₛₗ F E K p)
  --(iterateFrobeniusₛₗ F E p s).comp (iRedₛₗ F E K p)

end SemiLinear
