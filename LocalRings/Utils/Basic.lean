import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Nat.Defs
import Mathlib.Order.Basic

/-!
# Some simple theorems/lemmas missing in Mathlib4
-/

/-- Mathlib, really? No such theorem? -/
protected theorem Nat.pow_eq_pow_iff_right {a n m : Nat} (h : 1 < a) : a ^ n = a ^ m ↔ n = m := by
  apply Iff.intro
  · intro ha
    exact LE.le.antisymm
      ((Nat.pow_le_pow_iff_right h).mp (le_of_eq ha))
      ((Nat.pow_le_pow_iff_right h).mp (le_of_eq ha.symm))
  · intro he
    rw [he]

/-- Two monic polynomials of the same degree are equal if one divides the other.
    Mathlib, do you have it somewhere? -/
theorem Polynomial.eq_of_monic_of_eq_deg_of_dvd {R : Type u} [CommRing R]
    {p q : Polynomial R} (hp : p.Monic) (hq : q.Monic)
    (hdeg : p.natDegree = q.natDegree) (hdvd : p ∣ q) : p = q := by
  obtain ⟨c, hc⟩ := hdvd
  have hcm : c.Monic := (Monic.of_mul_monic_left hp (hc ▸ hq))
  have := (hdeg ▸ hc ▸ Polynomial.Monic.natDegree_mul hp hcm).symm
  have hc_deg : c.natDegree = 0 := by rwa [add_right_eq_self] at this
  have hc1 : c = 1 := (Polynomial.Monic.natDegree_eq_zero_iff_eq_one hcm).mp hc_deg
  symm
  rwa [hc1, mul_one] at hc
