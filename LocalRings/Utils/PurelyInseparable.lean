import Mathlib.FieldTheory.PurelyInseparable

import LocalRings.Utils.Basic

/-!
# Results for purely inseparable field extensions

## Main definitions

* `finInsepLogRank`: the *logarithmic inseparable degree*, i.e., a natural number `r`
    such that the degree of the given purely inseparable extension is `p ^ r`
    (`r = 0` in characteristic `0`, when exponential characteristic `p = 1`).
* `iRed`: For a given purely inseparable extension `F ⊆ K`, the 'reduction' ring homomorphism
    `K →+* F` with the property that `algebraMap F K (iRed F K a) = a ^ p ^ r`,
    where `r = finInsepLogRank F K`.
* `iRed_frob`: composition of `iRed` with `iteratedFrobenius` on `F`.
* `iRedₛₗ`: the map `iRed` as a semilinear map wrt. `iteratedFrobenius` on the scalar field.
* `iRed_frobₛₗ`: the map `iRed_frob` as a semilinear map wrt. `iteratedFrobenius`
    on the scalar field.

## Main results

* `purelyInseparable_char0`: purely inseparable extension in characteristic `0` is trivial.
* `purelyInseparable_finrank_pow`: degree of a purely inseparable field extension `F ⊆ K`
    is a power of the characteristic `p` (or `1` in case of characteristic zero,
    cf. `purelyInseparable_char0`).
-/

section PurelyInseparable

variable {R : Type u} [Semiring R]

lemma charP_of_expChar_prime' [ExpChar R p] (hp : p ≠ 1) : CharP R p := by
  cases ‹ExpChar R p›
  · contradiction
  · assumption

lemma expChar_prime_of_ne_one (R : Type u) [Semiring R] {p : ℕ} [ExpChar R p] (hp : p ≠ 1) : p.Prime :=
    Or.resolve_right (expChar_is_prime_or_one R p) hp

open scoped IntermediateField

/-- Purely inseparable extension in characteristic `0` is trivial. -/
theorem purelyInseparable_char0 (F K : Type u) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsPurelyInseparable F K] [CharZero F] :
    FiniteDimensional.finrank F K = 1 := by
  haveI : Algebra.IsSeparable F K := Algebra.IsSeparable.of_integral F K
  calc FiniteDimensional.finrank F K
    _ = FiniteDimensional.finrank F F :=
      (LinearEquiv.finrank_eq <|
        LinearEquiv.ofBijective
          (Algebra.linearMap F K)
          (IsPurelyInseparable.bijective_algebraMap_of_isSeparable F K)).symm
    _ = 1 := FiniteDimensional.finrank_self F

/-- Degree of a simple purely inseparable extension is a power of the characteristic `p`. -/
lemma purelyInseparable_finrank_adjoin_simple_pow (F : Type u) [Field F] {K : Type u} [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsPurelyInseparable F K] (p : ℕ) [ExpChar F p] (a : K) :
    ∃ ν : ℕ, FiniteDimensional.finrank F F⟮a⟯ = p ^ ν := by
  obtain ⟨k, _, h⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p a
  rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite F a), h,
    Polynomial.natDegree_sub_C, Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
  use k

/-- Degree of a purely inseparable field extension `F ⊆ K` is a power of the characteristic `p`
    (or `1` in case of characteristic zero, cf. `purelyInseparable_char0`). -/
theorem purelyInseparable_finrank_pow (F K : Type u) [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsPurelyInseparable F K] {p : ℕ} (hp : p.Prime) [ExpChar F p] :
    ∃! ν : ℕ, FiniteDimensional.finrank F K = p ^ ν := by
  /- adjoin induction -/
  let P (L : IntermediateField F K) : Prop := ∃ k : ℕ, FiniteDimensional.finrank F L = p ^ k
  have base : P ⊥ := by use 0; exact IntermediateField.finrank_bot
  have step (L : IntermediateField F K) (a : K) : P L → P (L⟮a⟯.restrictScalars F) := by
    intro hFL
    obtain ⟨k, hFL⟩ := hFL
    /- `F ⊆ L ⊆ K` => `L ⊆ K` purely inseparable -/
    haveI := IsPurelyInseparable.tower_top F L K
    /- `L ⊆ L⟮a⟯ ⊆ K` => `L ⊆ L⟮a⟯` purely inseparable-/
    haveI := IsPurelyInseparable.tower_bot L L⟮a⟯ K
    obtain ⟨l, hLLx⟩ := purelyInseparable_finrank_adjoin_simple_pow L p a
    use k + l
    calc FiniteDimensional.finrank F (L⟮a⟯.restrictScalars F)
      _ = FiniteDimensional.finrank F L⟮a⟯ := rfl
      _ = (FiniteDimensional.finrank F L) * (FiniteDimensional.finrank L L⟮a⟯) :=
        (FiniteDimensional.finrank_mul_finrank F L L⟮a⟯).symm
      _ = p ^ (k + l) := by rw [hFL, hLLx, pow_add p k l]
  obtain ⟨k, hk⟩ := IntermediateField.induction_on_adjoin P base step ⊤
  use k
  simp_rw [IntermediateField.finrank_top'] at hk
  simp
  apply And.intro
  · assumption
  · intro y hy
    exact (Nat.pow_eq_pow_iff_right <| Nat.Prime.one_lt hp).mp (hk ▸ hy).symm

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [IsPurelyInseparable F K]

local instance {E : IntermediateField F K} : IsPurelyInseparable F E :=
  IsPurelyInseparable.tower_bot F E K

local instance {E : IntermediateField F K} : IsPurelyInseparable E K :=
  IsPurelyInseparable.tower_top F E K

variable [FiniteDimensional F K] (p : ℕ) [ExpChar F p]
variable (F K)

/-- A *logarithmic inseparable degree*: a natural number `r` such that the degree
    of the given extension is `p ^ r` (`r = 0` in characteristic `0`). -/
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
    _ ≤ finInsepLogRank F E p + finInsepLogRank E K p := Nat.le_add_right ..
    _ = finInsepLogRank F K p := finInsepLogRank_tower ..

variable {K}

lemma IsPurelyInseparable.minpoly_natDegree (a : K) :
    (minpoly F a).natDegree = p ^ (finInsepLogRank F F⟮a⟯ p) := by
  obtain ⟨k, b, h⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p a
  rw [finInsepLogRank]
  split_ifs with hp
  · simp [h, hp]
  · have p_prime := expChar_prime_of_ne_one F hp
    rw [← (Classical.choose_spec (purelyInseparable_finrank_pow F F⟮a⟯ p_prime)).1]
    symm
    exact IntermediateField.adjoin.finrank (IsIntegral.of_finite F a)

variable (K) in
/-- Multiplictive reduction function. Defines a canonical homomorphism `K →+* F`.
    Mathematically, it acts like rising to the power of `p ^ finInsepLogRank F K p`,
    but we need a result in `F`, not in `K`, so it is defined as negated constant coefficient
    of `minpoly F a = X ^ p ^ k - c` raised to the proper complementary power of `p`. -/
noncomputable def iRed' : K → F :=
  fun a => (-Polynomial.aeval 0 (minpoly F a)) ^ p ^ finInsepLogRank F⟮a⟯ K p

/-- Action of `iRed'` on the top field. -/
lemma iRed'_algebraMap (a : K) : algebraMap F K (iRed' F K p a) = a ^ p ^ finInsepLogRank F K p := by
  let c : F := -Polynomial.aeval 0 (minpoly F a)
  have hc : algebraMap F K c = a ^ p ^ (finInsepLogRank F F⟮a⟯ p) := by
    obtain ⟨k, b, h⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p a
    rw [← IsPurelyInseparable.minpoly_natDegree F p a]
    simp [h, c, zero_pow <| pow_ne_zero k <| pos_iff_ne_zero.mp <| expChar_pos F p]
    replace h := h ▸ minpoly.aeval F a
    simp [sub_eq_zero] at h
    exact h.symm
  rw [iRed', RingHom.map_pow, hc, ← pow_mul, ← pow_add, finInsepLogRank_tower]

variable (K)

lemma iRed'_map_zero : iRed' F K p 0 = 0 := by
  simp [iRed']
  intro hp
  exfalso
  exact (pos_iff_ne_zero.mp <| expChar_pos F p) hp

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
  simp [iRed']

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

/-- Inseparable reduction map composed with iterated Frobenius (as a ring homomorphism). -/
noncomputable def iRed_frob (s : ℕ) : K →+* F := (iterateFrobenius F p s).comp (iRed F K p)

end PurelyInseparable

section SemiLinear

variable (F E K : Type u) [Field F] [Field E] [Field K] [Algebra F E] [Algebra E K] [Algebra F K]
  [IsScalarTower F E K]
variable [FiniteDimensional E K] [IsPurelyInseparable E K]
variable (p : ℕ) [ExpChar E p]

/-- Action of `iRed'` on the bottom field. -/
lemma iRed'_algebraMap_bot (a : F) :
    iRed' E K p (algebraMap F K a) = (algebraMap F E a) ^ p ^ finInsepLogRank E K p := by
  have := iRed'_algebraMap E p (algebraMap F K a)
  rw [← map_pow] at this
  apply (algebraMap E K).injective
  rwa [← map_pow, ← IsScalarTower.algebraMap_apply]

/-- Action of `iRed'` on the middle field. -/
lemma iRed'_algebraMap_mid (a : E) :
    iRed' E K p (algebraMap E K a) = a ^ p ^ finInsepLogRank E K p := by
  have := iRed'_algebraMap E p (algebraMap E K a)
  rw [← map_pow] at this
  apply (algebraMap E K).injective
  assumption

variable [ExpChar F p]

/-- Iterated Frobenius endomorphism as a semilinear map. -/
def iterateFrobeniusₛₗ (s : ℕ) : E →ₛₗ[iterateFrobenius F p s] E where
  toFun := (iterateFrobenius E p s).toFun
  map_add' := add_pow_expChar_pow E
  map_smul' := by
    intro a x
    simp [Algebra.smul_def, coe_iterateFrobenius]
    apply Or.inl
    symm
    exact (algebraMap F E).map_iterate_frobenius p a s

/-- Inseparable reduction map as a semilinear map over `F` wrt iterated Frobenius map. -/
noncomputable def iRedₛₗ : K →ₛₗ[iterateFrobenius F p (finInsepLogRank E K p)] E where
  toFun := iRed' E K p
  map_add' := iRed'_map_add E K p
  map_smul' := by
    intro a x
    simp [Algebra.smul_def]
    rw [iRed'_map_mul, iRed'_algebraMap_bot, iterateFrobenius_def, map_pow]

/-- Returns an instance of `RingHomCompTriple` for iterated Frobenius with a proper out param. -/
lemma RingHomCompTriple.iterateFrobenius {m n r : ℕ} (h : m + n = r) :
    RingHomCompTriple (iterateFrobenius F p m) (iterateFrobenius F p n) (iterateFrobenius F p r) :=
  { comp_eq := by rw [← h, add_comm]; exact (iterateFrobenius_add F p n m).symm }

/-- Inseparable reduction map composed with iterated Frobenius (as a semilinear map wrt. `σ`). -/
noncomputable def iRed_frobₛₗ (s : ℕ) (σ : F →+* F)
    [RingHomCompTriple (iterateFrobenius F p (finInsepLogRank E K p)) (iterateFrobenius F p s) σ] :
    K →ₛₗ[σ] E :=
  (LinearMap.iterateFrobenius F E p s).comp (iRedₛₗ F E K p)

/-- The map `iRed_frobₛₗ` acts on the middle field essentially raising to the power of the characteristic. -/
lemma iRed_frobₛₗ_algebraMap_mid (s : ℕ) (a : E) (σ : F →+* F)
    [RingHomCompTriple (iterateFrobenius F p (finInsepLogRank E K p)) (iterateFrobenius F p s) σ] :
    iRed_frobₛₗ F E K p s σ (algebraMap E K a) = a ^ p ^ (finInsepLogRank E K p + s) := by
  simp [iRed_frobₛₗ, iRedₛₗ, iRed'_algebraMap_mid,
    LinearMap.iterateFrobenius, iterateFrobenius_def]
  rw [← pow_mul, ← pow_add, add_comm]

/-- The map `iRed_frobₛₗ` acts on the top field essentially raising to the power of the characteristic. -/
lemma iRed_frobₛₗ_algebraMap_top (s : ℕ) (a : K) (σ : F →+* F)
  [RingHomCompTriple (iterateFrobenius F p (finInsepLogRank E K p)) (iterateFrobenius F p s) σ] :
    algebraMap E K (iRed_frobₛₗ F E K p s σ a) = a ^ p ^ (finInsepLogRank E K p + s) := by
  simp [iRed_frobₛₗ, iRedₛₗ, iRed'_algebraMap,
    LinearMap.iterateFrobenius, iterateFrobenius_def]
  rw [← pow_mul, ← pow_add, add_comm]

end SemiLinear
