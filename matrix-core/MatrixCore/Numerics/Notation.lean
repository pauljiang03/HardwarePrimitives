import Std
import Init.Data.Rat

/-! Notation for the mathematical number types, scoped to `MatrixCore` so that the library can be
imported together with Mathlib or with the other vendor's library. -/

namespace MatrixCore

scoped notation "ℕ" => Nat
scoped notation "ℤ" => Int
scoped notation "ℚ" => Rat

end MatrixCore
