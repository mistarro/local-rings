import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Results for intermediate fields
-/

namespace IntermediateField

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable {E : IntermediateField F K}

lemma algebraMap_range_mem_iff {x : K} : x ∈ Set.range (algebraMap E K) ↔ x ∈ E :=
  ⟨fun ⟨⟨r, hrmem⟩, hr⟩ ↦
    ((IntermediateField.coe_val E ▸ IntermediateField.val_mk E hrmem) ▸
      IntermediateField.algebraMap_apply E ⟨r, hrmem⟩ ▸ hr) ▸ hrmem,
  fun hx ↦ Set.mem_range.mpr ⟨⟨x, hx⟩, IntermediateField.algebraMap_apply E ⟨x, hx⟩⟩⟩

/-- The range of the `algebraMap` from an intermediate field is that intermediate field. -/
lemma algebraMap_range : Set.range (algebraMap E K) = E :=
  Set.ext fun _x ↦ IntermediateField.algebraMap_range_mem_iff

end IntermediateField
