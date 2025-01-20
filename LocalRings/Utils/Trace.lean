import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.Trace.Basic

/-!
# Results for trace map and minimal polynomials.
-/

open scoped IntermediateField

/-- The trace map `Algebra.trace R R` is identity. -/
lemma trace_self {R : Type*} [CommRing R] (a : R) :
    Algebra.trace R R a = a := by
  simpa only [Algebra.id.map_eq_self, Fintype.card_ofSubsingleton, one_smul]
    using Algebra.trace_algebraMap_of_basis (.singleton (Fin 1) R) a

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E]

variable {F} in
/-- Classical result about trace value of a generator of a simple adjoin
    and its minimal polynomial coefficient. -/
lemma trace_minpoly_adjoin_simple {a : E} (ha : IsIntegral F a) :
    Algebra.trace F F⟮a⟯ (IntermediateField.AdjoinSimple.gen F a) =
      -(minpoly F a).nextCoeff := by
  let a' := IntermediateField.AdjoinSimple.gen F a
  let pb := IntermediateField.adjoin.powerBasis ha
  calc Algebra.trace F F⟮a⟯ a'
    _ = Algebra.trace F F⟮a⟯ pb.gen := rfl
    _ = -(minpoly F pb.gen).nextCoeff := PowerBasis.trace_gen_eq_nextCoeff_minpoly pb
    _ = -(minpoly F a').nextCoeff := rfl
    _ = -(minpoly F a).nextCoeff := by rw [IntermediateField.minpoly_gen F a]

/-- Classical result about trace map, dimension and minimal polynomial coefficient. -/
lemma trace_minpoly [FiniteDimensional F E] (a : E) :
    Algebra.trace F E a = Module.finrank F⟮a⟯ E * -(minpoly F a).nextCoeff := by
  let a' := IntermediateField.AdjoinSimple.gen F a
  let n := Module.finrank F⟮a⟯ E
  calc Algebra.trace F E a
    _ = n • Algebra.trace F F⟮a⟯ a' := trace_eq_trace_adjoin F a
    _ = n * -(minpoly F a).nextCoeff := by
      rw [trace_minpoly_adjoin_simple (.of_finite F a), Algebra.smul_def]; rfl
