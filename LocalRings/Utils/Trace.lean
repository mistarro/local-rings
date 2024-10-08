  /-
    Things to show:
      1. `T(x₁, x₂)` is not `0` everywhere (so `U` is proper)
      2. `T` vanishes on local elements (so local elements are in `U`)

    Ad 1.
      1.1. a : E, F(a ^ p) = F(a) := by
        F(a ^ p) ⊆ F(a)
        F(a ^ p) ≠ F(a) → purely inseparable (contra)
      1.2. if minpoly F a = ∑ᵢ aᵢ * X ^ i then
        minpoly F (a ^ p) = ∑ᵢ aᵢ ^ p * X ^ i
        ∑ᵢ aᵢ ^ p * (a ^ p) ^ i = (∑ᵢ aᵢ * a ^ i) ^ p = 0
      1.3. tr F E (a ^ p) = -[E : F(a ^ p)] * (minpoly F (a ^ p)).nextCoeff =
        = -[E : F(a)] * (minpoly F a).nextCoeff ^ p = (tr F E a) * (minpoly F a).nextCoeff ^ (p - 1)
      1.4. tr F E a ≠ 0 then tr F E (a ^ p) ≠ 0
      1.5. choose a : E₁ with tr F E₁ a ≠ 0, then T₁(a) ≠ 0
   -/
