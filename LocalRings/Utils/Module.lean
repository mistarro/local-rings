import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs

import Mathlib.LinearAlgebra.Span

/-!
# Supplementary lemmas for modules.
-/

variable {R : Type u} [Semiring R]
variable {M₁ M₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂]
    [Module R M₁] [Module R M₂]

/- If `f '' S₁ ⊆ S₂` then the image of the span of `S₁` is a submodule of the span of `S₂`. -/
lemma span_transfer {S₁ : Set M₁} {S₂ : Set M₂} {f : M₁ →ₗ[R] M₂}
    (h : f '' S₁ ⊆ S₂) : (Submodule.span R S₁).map f ≤ Submodule.span R S₂ := by
  have h1 : (Submodule.span R S₁).map f ≤ Submodule.span R (f '' S₁) := by
    rw [Submodule.map_span_le]
    intro m hm
    exact (Submodule.subset_span (s := f '' S₁)) (Set.mem_image_of_mem f hm)
  have h2 : Submodule.span R (f '' S₁) ≤ Submodule.span R S₂ := Submodule.span_mono h
  exact Set.Subset.trans h1 h2
