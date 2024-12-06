import Mathlib.Data.Nat.Defs
import Mathlib.Order.Basic

/-!
# Some simple theorems/lemmas missing in Mathlib4
-/

/-- Mathlib, really? No such theorem? -/
protected theorem Nat.pow_eq_pow_iff_right {a n m : Nat} (h : 1 < a) : a ^ n = a ^ m ↔ n = m :=
  ⟨fun ha ↦ LE.le.antisymm
    ((Nat.pow_le_pow_iff_right h).mp (le_of_eq ha))
    ((Nat.pow_le_pow_iff_right h).mp (le_of_eq ha.symm)),
  fun he ↦ congrArg (a ^ ·) he⟩
