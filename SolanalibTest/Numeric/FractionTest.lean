/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Numeric.Fraction

/-!
# Regression tests for `Solanalib.Numeric.Fraction`

Pins the spec-layer behaviour of the Q68.60 fixed-point shape:
constants, integer round-trip via the cast and `toIntFloor`, the
additive group laws, multiplication and division by `1`, ordering,
and `sub`/`add` cancellation.
-/

namespace SolanalibTest.Numeric.Fraction

open Solanalib

/-! ## Constants and conversions -/

/-- `0` and `1` are distinct. -/
example : (0 : Q68_60) ≠ 1 := fun h => by simpa using congrArg Fraction.bits h

/-- Casting a natural number and taking `toIntFloor` round-trips cleanly. -/
example (k : Nat) : (k : Q68_60).toIntFloor = k :=
  Fraction.toIntFloor_natCast k

/-- The cast of `0` is `0`. -/
example : ((0 : Nat) : Q68_60) = 0 := Nat.cast_zero

/-- The cast of `1` is `1`. -/
example : ((1 : Nat) : Q68_60) = 1 := Nat.cast_one

/-! ## Additive group and multiplicative identity -/

example : (0 : Q68_60) + 1 = 1 := zero_add 1

example : (1 : Q68_60) + 0 = 1 := add_zero 1

example (a b : Q68_60) : a + b = b + a := add_comm a b

example : Fraction.mulFloor (1 : Q68_60) 1 = 1 := Fraction.mulFloor_one 1

example (a : Q68_60) : Fraction.mulFloor 1 a = a := Fraction.one_mulFloor a

/-! ## Ordering -/

example : (0 : Q68_60) ≤ 1 := by norm_num [← Fraction.bits_le_bits]

/-- `Fraction` is signed: `-1` is below `0`. -/
example : (-1 : Q68_60) < 0 := by norm_num [← Fraction.bits_lt_bits]

example (a : Q68_60) : a ≤ a := le_refl a

example {a b c : Q68_60} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  le_trans h₁ h₂

/-! ## Subtraction -/

/-- `(a - b) + b = a`. -/
example (a b : Q68_60) : a - b + b = a := sub_add_cancel a b

/-- Concrete: `1 - 1 = 0`. -/
example : (1 : Q68_60) - 1 = 0 := sub_self 1

/-! ## Division -/

/-- Division by `1` returns the dividend unchanged. -/
example (a : Q68_60) : Fraction.divFloor a 1 = a := Fraction.divFloor_one a

/-! ## Lamports ↔ Fraction bridge -/

/-- Lamports → Fraction → integer round-trip preserves the value. -/
example (l : Lamports) : (Fraction.ofLamports l : Q68_60).toIntFloor = l.toNat :=
  Fraction.toIntFloor_ofLamports l

end SolanalibTest.Numeric.Fraction
