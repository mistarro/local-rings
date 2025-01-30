import Mathlib.FieldTheory.PurelyInseparable

/-!
# Results for intermediate fields
-/

namespace IntermediateField

variable (F E : Type*) [Field F] [Field E] [Algebra F E]

/- PR #21249 -/
/-- If `E / F` is a separable field extension of exponential characteristic `q`, then
`F⟮a⟯ = F⟮a ^ q ^ n⟯` for any subset `a : E` and any natural number `n`. -/
theorem adjoin_simple_eq_adjoin_pow_expChar_pow_of_isSeparable' [Algebra.IsSeparable F E] (a : E)
    (q : ℕ) [ExpChar F q] (n : ℕ) : F⟮a⟯ = F⟮a ^ q ^ n⟯ := by
  haveI := Algebra.isSeparable_tower_bot_of_isSeparable F F⟮a⟯ E
  simpa using adjoin_eq_adjoin_pow_expChar_pow_of_isSeparable F E {a} q n

end IntermediateField
