import Mathlib.FieldTheory.PurelyInseparable

import LocalRings.Utils.Basic
import LocalRings.Utils.Trace

/-!
# Results for purely inseparable field extensions

## Main definitions

* `exponent`: The exponent of a purely inseparable, finite extension is the smallest
    natural number `e` such that `a ^ p ^ e ∈ F` for all `a ∈ K`.
* `elemExponent`: the *logarithmic inseparable degree*, i.e., a natural number `r`
    such that the degree of the given purely inseparable extension is `p ^ r`
    (`r = 0` in characteristic `0`, when exponential characteristic `p = 1`).
* `iRed`: For a given purely inseparable extension `F ⊆ K`, the 'reduction' ring homomorphism
    `K →+* F` with the property that `algebraMap F K (iRed F K a) = a ^ p ^ r`,
    where `r = PurelyInseparable.exponent F K`.
* `iRed_frob`: composition of `iRed` with `iteratedFrobenius` on `F`.
* `iRedₛₗ`: the map `iRed` as a semilinear map wrt. `iteratedFrobenius` on the scalar field.
* `iRed_frobₛₗ`: the map `iRed_frob` as a semilinear map wrt. `iteratedFrobenius`
    on the scalar field.
-/

namespace PurelyInseparable

open scoped IntermediateField

variable (F K : Type u) [Field F] [Field K] [Algebra F K] [IsPurelyInseparable F K]
variable (p : ℕ) [ExpChar F p]

variable {K}

/-- For each element `a : K`, there is `n : ℕ` and `y : F` such that
    `minpoly F a = X ^ p ^ n - y`. -/
lemma minpoly_eq_X_pow_sub_C' (a : K) :
    ∃ ny : ℕ × F, minpoly F a = Polynomial.X ^ p ^ ny.1 - Polynomial.C ny.2 := by
  obtain ⟨n, y, h⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C F p a
  use ⟨n, y⟩

open Classical in
/-- 'Encoding' of the minimal polynomial of an element `a : K` as the pair `⟨n, y⟩ : ℕ × F` with
    `minpoly F a = X ^ p ^ n - y`. -/
noncomputable def minpoly_encode (a : K) : ℕ × F :=
  Classical.choose (minpoly_eq_X_pow_sub_C' F p a)

/-- The exponent of an element of a purely inseparable field extension is the smallest
    natural number `e` such that `a ^ p ^ e ∈ F` for all `a ∈ K`. -/
noncomputable def elemExponent (a : K) : ℕ := (minpoly_encode F p a).1

noncomputable def elemReduct (a : K) : F := (minpoly_encode F p a).2

lemma minpoly_encode_def (a : K) :
    minpoly F a = Polynomial.X ^ p ^ (elemExponent F p a) - Polynomial.C (elemReduct F p a) := by
  exact Classical.choose_spec (minpoly_eq_X_pow_sub_C' F p a)

/-- The degree of the minimal polynomial of an element `a : K` equals `p ^ (elemExponent F p a)`. -/
lemma minpoly_encode_natDegree (a : K) :
    (minpoly F a).natDegree = p ^ (elemExponent F p a) := by
  rw [minpoly_encode_def F p a, Polynomial.natDegree_sub_C, Polynomial.natDegree_pow,
    Polynomial.natDegree_X, mul_one]

lemma minpoly_encode_algebraMap (a : K) : algebraMap F K (elemReduct F p a) = a ^ p ^ (elemExponent F p a) := by
  have := minpoly_encode_def F p a ▸ minpoly.aeval F a
  simp at this
  exact (sub_eq_zero.mp this).symm

variable (K) in
/-- A predicate class on a purely inseparable extension saying that there is a natural number
    `e` such that `a ^ p ^ e ∈ F` for all `a ∈ K`. -/
def ExponentExists [IsPurelyInseparable F K] [ExpChar F p] : Prop :=
    ∃ e : ℕ, ∀ a : K, a ^ p ^ e ∈ (algebraMap F K).range

instance exponent_exists_of_finite_dimensional [FiniteDimensional F K] :
    Fact (ExponentExists F K p) := by
  rw [fact_iff]
  rcases ‹ExpChar F p› with _ | ⟨hp⟩
  · use 0
    simp
    exact IsPurelyInseparable.surjective_algebraMap_of_isSeparable F K
  · let e := Nat.log p (Module.finrank F K)
    have h2 (a : K) : elemExponent F p a ≤ e :=
      Nat.le_log_of_pow_le (Nat.Prime.one_lt hp) (minpoly_encode_natDegree F p a ▸ minoly.natDegree_le_finrank F a)
    use e
    intro a
    simp
    use (elemReduct F p a) ^ p ^ (e - elemExponent F p a)
    rw [RingHom.map_pow,
      minpoly_encode_algebraMap,
      ← pow_mul, ← pow_add,
      Nat.add_sub_cancel' (h2 a)]

variable [Fact (ExponentExists F K p)]

open Classical in
variable (K) in
/-- The exponent of a purely inseparable, finite extension is the smallest natural number `e`
    such that `a ^ p ^ e ∈ F` for all `a ∈ K`. -/
noncomputable def exponent : ℕ :=
  Nat.find ‹Fact (ExponentExists F K p)›.out

open Classical in
lemma exponent_def (a : K) : a ^ p ^ exponent F K p ∈ (algebraMap F K).range := by
  exact Nat.find_spec ‹Fact (ExponentExists F K p)›.out a

variable {p} in
/-- An exponent of an element is less or equal than exponent of the extension. -/
lemma elemExponent_le_exponent (hp : p.Prime) (a : K) :
    elemExponent F p a ≤ exponent F K p := by
  have := exponent_def F p a
  obtain ⟨y, hy⟩ := RingHom.mem_range.mp <| exponent_def F p a
  let f := Polynomial.X ^ p ^ exponent F K p - Polynomial.C y
  have hf₁ : Polynomial.aeval a f = 0 := by
    simp [f, sub_eq_zero]
    exact hy.symm
  have hf₂ : f.Monic := Polynomial.Monic.def.mpr <|
      Polynomial.leadingCoeff_X_pow_sub_C (expChar_pow_pos F p (exponent F K p))
  have hf₃ : f.natDegree = p ^ exponent F K p := by
    rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
  have := hf₃ ▸ minpoly_encode_natDegree F p a ▸
    Polynomial.natDegree_le_natDegree (minpoly.min F a hf₂ hf₁)
  exact (Nat.pow_le_pow_iff_right <| Nat.Prime.one_lt hp).mp this

variable (K) in
/-- Multiplicative reduction function. Defines the canonical ring homomorphism `iRed : K →+* F`.
    Acts like rising to the power of `p ^ exponent F K p`, see `iRed'_algebraMap`. -/
noncomputable def iRed' : K → F :=
  fun a ↦ (elemReduct F p a) ^ p ^ (exponent F K p - elemExponent F p a)

/-- Action of `iRed'` on the top field. -/
lemma iRed'_algebraMap (a : K) : algebraMap F K (iRed' F K p a) = a ^ p ^ exponent F K p := by
  rw [iRed', RingHom.map_pow, minpoly_encode_algebraMap, ← pow_mul, ← pow_add]
  rcases ‹ExpChar F p› with _ | ⟨hp⟩
  · simp
  · rw [Nat.add_sub_cancel' (elemExponent_le_exponent F hp a)]

variable (K)

lemma iRed'_map_zero : iRed' F K p 0 = 0 := by
  apply (algebraMap F K).injective
  rw [(algebraMap F K).map_zero,
    iRed'_algebraMap F p (0 : K),
    zero_pow]
  exact Nat.pos_iff_ne_zero.mp <|
    Nat.pos_pow_of_pos (exponent F K p) (expChar_pos F p)

lemma iRed'_map_add (a b : K) : iRed' F K p (a + b) = iRed' F K p a + iRed' F K p b := by
  have inj := (algebraMap F K).injective
  apply inj
  haveI : ExpChar K p := expChar_of_injective_ringHom inj p
  rw [(algebraMap F K).map_add,
    iRed'_algebraMap F p a,
    iRed'_algebraMap F p b,
    iRed'_algebraMap F p (a + b),
    add_pow_expChar_pow a b]

lemma iRed'_map_one : iRed' F K p 1 = 1 := by
  apply (algebraMap F K).injective
  rw [(algebraMap F K).map_one,
    iRed'_algebraMap F p (1 : K),
    one_pow]

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

section SemiLinear

variable (F E K : Type u) [Field F] [Field E] [Field K]
  [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
variable [IsPurelyInseparable E K]
variable (p : ℕ) [ExpChar E p]
variable [Fact (ExponentExists E K p)]

/-- Action of `iRed'` on the bottom field. -/
lemma iRed'_algebraMap_bot (a : F) :
    iRed' E K p (algebraMap F K a) = (algebraMap F E a) ^ p ^ exponent E K p := by
  have := iRed'_algebraMap E p (algebraMap F K a)
  rw [← map_pow] at this
  apply (algebraMap E K).injective
  rwa [← map_pow, ← IsScalarTower.algebraMap_apply]

/-- Action of `iRed'` on the middle field. -/
lemma iRed'_algebraMap_mid (a : E) :
    iRed' E K p (algebraMap E K a) = a ^ p ^ exponent E K p := by
  have := iRed'_algebraMap E p (algebraMap E K a)
  rw [← map_pow] at this
  apply (algebraMap E K).injective
  assumption

variable [ExpChar F p]

/-- Iterated Frobenius endomorphism as a semilinear map. -/
def iterateFrobeniusₛₗ (s : ℕ) : E →ₛₗ[iterateFrobenius F p s] E where
  toFun := (iterateFrobenius E p s).toFun
  map_add' := by simp
  map_smul' := by
    intro a x
    simp [Algebra.smul_def, coe_iterateFrobenius]
    apply Or.inl
    symm
    exact (algebraMap F E).map_iterate_frobenius p a s

/-- Inseparable reduction map as a semilinear map over `F` wrt iterated Frobenius map. -/
noncomputable def iRedₛₗ : K →ₛₗ[iterateFrobenius F p (exponent E K p)] E where
  toFun := iRed' E K p
  map_add' := iRed'_map_add E K p
  map_smul' := by
    intro a x
    simp [Algebra.smul_def]
    rw [iRed'_map_mul, iRed'_algebraMap_bot, iterateFrobenius_def, map_pow]

/-- Returns an instance of `RingHomCompTriple` for iterated Frobenius with a proper out param. -/
lemma _root_.RingHomCompTriple.iterateFrobenius {m n r : ℕ} (h : m + n = r) :
    RingHomCompTriple (iterateFrobenius F p m) (iterateFrobenius F p n) (iterateFrobenius F p r) :=
  { comp_eq := by rw [← h, add_comm]; exact (iterateFrobenius_add F p n m).symm }

/-- Inseparable reduction map composed with iterated Frobenius (as a semilinear map wrt. `σ`). -/
noncomputable def iRed_frobₛₗ (s : ℕ) (σ : F →+* F)
    [RingHomCompTriple (iterateFrobenius F p (exponent E K p)) (iterateFrobenius F p s) σ] :
    K →ₛₗ[σ] E :=
  (LinearMap.iterateFrobenius F E p s).comp (iRedₛₗ F E K p)

/-- The map `iRed_frobₛₗ` acts on the middle field essentially raising to the power of the characteristic. -/
lemma iRed_frobₛₗ_algebraMap_mid (s : ℕ) (a : E) (σ : F →+* F)
    [RingHomCompTriple (iterateFrobenius F p (exponent E K p)) (iterateFrobenius F p s) σ] :
    iRed_frobₛₗ F E K p s σ (algebraMap E K a) = a ^ p ^ (exponent E K p + s) := by
  simp [iRed_frobₛₗ, iRedₛₗ, iRed'_algebraMap_mid,
    LinearMap.iterateFrobenius, iterateFrobenius_def]
  rw [← pow_mul, ← pow_add, add_comm]

/-- The map `iRed_frobₛₗ` acts on the top field essentially raising to the power of the characteristic. -/
lemma iRed_frobₛₗ_algebraMap_top (s : ℕ) (a : K) (σ : F →+* F)
  [RingHomCompTriple (iterateFrobenius F p (exponent E K p)) (iterateFrobenius F p s) σ] :
    algebraMap E K (iRed_frobₛₗ F E K p s σ a) = a ^ p ^ (exponent E K p + s) := by
  simp [iRed_frobₛₗ, iRedₛₗ, iRed'_algebraMap,
    LinearMap.iterateFrobenius, iterateFrobenius_def]
  rw [← pow_mul, ← pow_add, add_comm]

end SemiLinear

end PurelyInseparable
