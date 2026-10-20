/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Solanalib.Finance.MonotoneSequence
import Solanalib.Numeric.Fraction

/-!
# CompoundInterest: discrete compounding as a `MonotoneSequence`

This module is the first downstream consumer that **composes** two
Solanalib layers we built earlier:

* `Solanalib.Numeric.Fraction` is the *rate's* type — a fixed-point
  multiplier with `d` fractional bits (1.0 = no growth, 1.01 = 1% growth per period, …).
* `Solanalib.Finance.MonotoneSequence` is the *output*'s bundled type —
  the family of unbounded monotone Nat-indexed sequences.

The definition itself is short:

```lean
def balance (principal : Nat) (multiplier : Fraction d) : Nat → Nat
  | 0     => principal
  | n + 1 => balance principal multiplier n * multiplier.bits.toNat / 2 ^ d
```

Each step multiplies by the encoded `multiplier` and divides
back out by `2 ^ d`. With `multiplier ≥ 1`
(equivalently, `multiplier.bits ≥ 2 ^ d`), this is provably monotone
non-decreasing in `n` — that's the bundled-structure proof obligation
for `MonotoneSequence`.

## Main definitions

* `Solanalib.Finance.CompoundInterest.balance` — the discrete-compounding
  function.
* `Solanalib.Finance.CompoundInterest.toMonotoneSequence` — the
  composition: a `(principal, multiplier ≥ 1)` pair becomes a
  `MonotoneSequence`, inheriting all generic theorems.

## Main statements

* `balance_zero`               — `balance p m 0 = p`.
* `balance_at_one_multiplier`  — with `multiplier = 1.0`, balance is constant.
* `balance_succ_ge`            — one-step monotonicity (given `multiplier ≥ 1`).
* `balance_monotone`           — arbitrary-step monotonicity.
* `balance_ge_principal`       — balance never drops below the principal.

The four-property pattern follows `LinearDecay`'s `value_*` discipline:
one operation, several named theorems, each catching a distinct
refactor-bug class (`balance < principal` would be a "lender loses
funds" exploit; non-monotonicity would be a "wait longer, owe less"
exploit; etc.).

The real-world step from this MVP to Kamino's
`approximate_compounded_interest` is its truncated Taylor-series
approximation of `(1 + r)^n` for large `n`. That refinement — and the
error-bound theorem relating the approximation to the exact
compounding done here — is roadmap work documented in the project
README.
-/

namespace Solanalib.Finance.CompoundInterest

open Solanalib

variable {d : ℕ}

/-- The balance after `periods` periods of compounding from `principal`
at multiplier `multiplier`. -/
def balance (principal : Nat) (multiplier : Fraction d) : Nat → Nat
  | 0       => principal
  | n + 1   => balance principal multiplier n * multiplier.bits.toNat / 2 ^ d

/-! ## Theorems -/

/-- Boundary: balance at step 0 is the principal. -/
@[simp] theorem balance_zero (principal : Nat) (multiplier : Fraction d) :
    balance principal multiplier 0 = principal := rfl

/-- With a unit multiplier (i.e. `1`, no growth), the
balance is constant across all periods. -/
theorem balance_at_one_multiplier (principal : Nat) (n : Nat) :
    balance principal (1 : Fraction d) n = principal := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show balance principal (1 : Fraction d) k * (1 : Fraction d).bits.toNat
            / 2 ^ d = principal
    have h1 : (1 : Fraction d).bits = ((2 ^ d : ℕ) : ℤ) := by simp
    rw [ih, h1, Int.toNat_natCast, Nat.mul_div_cancel _ (Nat.two_pow_pos d)]

/-- **One-step monotonicity.** With `multiplier ≥ 1`, the
balance never decreases from one period to the next. -/
theorem balance_succ_ge (principal : Nat) (multiplier : Fraction d)
    (h : 1 ≤ multiplier) (n : Nat) :
    balance principal multiplier n ≤ balance principal multiplier (n + 1) := by
  show balance principal multiplier n
        ≤ balance principal multiplier n * multiplier.bits.toNat / 2 ^ d
  -- `1 ≤ multiplier` reduces to `2 ^ d ≤ multiplier.bits`
  -- via the `LE (Fraction d)` instance and `bits_one`.
  have h_scale : 2 ^ d ≤ multiplier.bits.toNat := by
    have h1 : (1 : Fraction d).bits = ((2 ^ d : ℕ) : ℤ) := by simp
    have hh : (1 : Fraction d).bits ≤ multiplier.bits := h
    rw [h1] at hh
    omega
  have h1 : balance principal multiplier n * 2 ^ d
            ≤ balance principal multiplier n * multiplier.bits.toNat :=
    Nat.mul_le_mul_left _ h_scale
  have h2 : balance principal multiplier n * 2 ^ d / 2 ^ d
            ≤ balance principal multiplier n * multiplier.bits.toNat / 2 ^ d :=
    Nat.div_le_div_right h1
  rwa [Nat.mul_div_cancel _ (Nat.two_pow_pos d)] at h2

/-- **Multi-step monotonicity.** With `multiplier ≥ 1`, the
balance is monotone non-decreasing across any range of periods. -/
theorem balance_monotone (principal : Nat) (multiplier : Fraction d)
    (h : 1 ≤ multiplier) {n m : Nat} (hnm : n ≤ m) :
    balance principal multiplier n ≤ balance principal multiplier m := by
  induction hnm with
  | refl       => exact Nat.le_refl _
  | step _ ih  => exact Nat.le_trans ih (balance_succ_ge principal multiplier h _)

/-- The balance never drops below the principal (given `multiplier ≥ 1`). -/
theorem balance_ge_principal (principal : Nat) (multiplier : Fraction d)
    (h : 1 ≤ multiplier) (n : Nat) :
    principal ≤ balance principal multiplier n := by
  have h_mono := balance_monotone principal multiplier h (Nat.zero_le n)
  -- balance _ _ 0 = principal
  simpa using h_mono

/-! ## Composition into `MonotoneSequence`

The headline composition move: a `(principal, multiplier ≥ 1)` pair
becomes a `MonotoneSequence`, which automatically inherits the two
generic theorems proved in `Solanalib.Finance.MonotoneSequence`:

* `MonotoneSequence.apply_zero_le`  — value at any step ≥ value at step 0.
* `MonotoneSequence.apply_le_of_le` — value-at-later ≥ value-at-earlier.

Construction discharges the single `monotone` obligation via
`balance_monotone`. No new math; pure composition. -/

/-- Bundle a compounding configuration into a `MonotoneSequence`. -/
def toMonotoneSequence (principal : Nat) (multiplier : Fraction d)
    (h : 1 ≤ multiplier) : MonotoneSequence where
  apply := balance principal multiplier
  monotone := balance_monotone principal multiplier h

end Solanalib.Finance.CompoundInterest
