import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.Trace.Basic

/-!
# Results for trace map and minimal polynomials.
-/

/- Accepted in Mathlib4 in `Mathlib.RingTheory.Trace.Defs`. -/
/-- The trace map `Algebra.trace R R` is identity. -/
lemma Algebra.trace_self_apply {R : Type*} [CommRing R] (a : R) :
    Algebra.trace R R a = a := by
  simpa only [Algebra.id.map_eq_self, Fintype.card_ofSubsingleton, one_smul]
    using Algebra.trace_algebraMap_of_basis (.singleton (Fin 1) R) a

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E]

open IntermediateField

/- Accepted in Mathlib4 in `Mathlib.RingTheory.Trace.Basic`. -/
variable {F} in
/-- Classical result about trace value of a generator of a simple adjoin
    and its minimal polynomial coefficient. -/
lemma trace_adjoinSimpleGen {a : E} (ha : IsIntegral F a) :
    Algebra.trace F F⟮a⟯ (AdjoinSimple.gen F a) =
      -(minpoly F a).nextCoeff := by
  simpa [minpoly_gen F a] using PowerBasis.trace_gen_eq_nextCoeff_minpoly <| adjoin.powerBasis ha

/- Accepted in Mathlib4 in `Mathlib.RingTheory.Trace.Basic`. -/
/-- Classical result about trace map, dimension and minimal polynomial coefficient. -/
lemma trace_eq_finrank_mul_minpoly_nextCoeff [FiniteDimensional F E] (a : E) :
    Algebra.trace F E a = Module.finrank F⟮a⟯ E * -(minpoly F a).nextCoeff := by
  rw [trace_eq_trace_adjoin, trace_adjoinSimpleGen (.of_finite F a), Algebra.smul_def]
  rfl
