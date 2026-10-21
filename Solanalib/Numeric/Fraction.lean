/-
Copyright (c) 2026 Solana Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Solanalib Contributors
-/
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.WLOG
import Solanalib.Init
import Solanalib.Primitives.Lamports

/-!
# Binary fixed-point numbers

Signed binary fixed-point numbers with `n` fractional bits, modelled at the spec layer with an
unbounded `Int` as the underlying representation.
A `Fraction n` `f` represents the rational number `f.bits / 2^n`.
`Q68_60` fixes `n = 60` to match the `U68F60` type that Kamino and other Solana DeFi protocols
use on-chain.

We use `Int` rather than `u128` on purpose: we prove the mathematical properties on the
unbounded model, and the bounded on-chain representation is a separate refinement.

## Main definitions

* `Fraction n`: a binary fixed-point number with `n` fractional bits.
* `Fraction.toRat`: the rational number that a fraction represents.
* `Fraction.toIntFloor`, `Fraction.toIntCeil`, `Fraction.toIntTrunc`: rounding to an integer.
* `Fraction.ofLamports`, `Fraction.toLamports?`: conversion from and to `Lamports`.
* `Fraction.mulFloor` (`*↓`), `Fraction.mulCeil` (`*↑`), `Fraction.mulTrunc` (`*₀`):
  multiplication, one for each rounding direction.
* `Fraction.divFloor` (`/↓`), `Fraction.divCeil` (`/↑`), `Fraction.divTrunc` (`/₀`):
  division, one for each rounding direction.

## Main statements

* Algebra and order: `Fraction n` is an ordered additive commutative group
  (`AddCommGroup`, `LinearOrder`, `IsOrderedAddMonoid`).
* Conversion to integers:
  * Casting an integer or a natural number to `Fraction n` and rounding it back gives the
    original number in every rounding direction (`Fraction.toIntFloor_intCast`).
  * Converting `Lamports` to `Fraction n` with `ofLamports` and rounding it back with
    `toIntFloor` gives the original number (`Fraction.toIntFloor_ofLamports`).
  * Rounding changes a fraction by less than `1`, in the stated direction
    (`Fraction.intCast_toIntFloor_le`, `Fraction.abs_sub_intCast_toIntTrunc_lt_one`).
* Multiplication:
  * The three multiplications are commutative (`Fraction.mulFloor_comm`,
    `Fraction.mulCeil_comm`, `Fraction.mulTrunc_comm`), but not associative,
    because each one rounds.
  * Floor, truncation and ceiling are ordered (`Fraction.mulFloor_le_mulTrunc`,
    `Fraction.mulTrunc_le_mulCeil`).
* Division:
  * Floor, truncation and ceiling are ordered (`Fraction.divFloor_le_divTrunc`,
    `Fraction.divTrunc_le_divCeil`).
* Correctness with respect to `ℚ`:
  * `toRat` is a bijection between `Fraction n` and the multiples of `1 / 2^n` in `ℚ` that
    preserves `+` and `≤` (`Fraction.toRatOrderAddIso`).
  * Each multiplication differs from the exact product by less than `1 / 2^n`, in the stated
    direction (`Fraction.toRat_mulFloor_le`, `Fraction.lt_toRat_mulFloor_add`).
  * For a nonzero divisor, each division differs from the exact quotient by less than `1 / 2^n`,
    in the stated direction (`Fraction.toRat_divFloor_le`, `Fraction.lt_toRat_divFloor_add`).

## Conventions

* Every multiplication and division states its rounding direction. There is deliberately no
  `Mul` or `Div` instance, and the operators are `scoped` in `Solanalib.Fraction`.
* Division by `0` returns `0` in all three rounding directions, following the convention of
  Lean and Mathlib (`x / 0 = 0` for `ℚ` and for `Int.fdiv` and `Int.tdiv`).
* Lemmas are stated on `bits` or on `toRat`. The `bits_*` lemmas move a goal to integer
  arithmetic, the `toRat_*` lemmas to rational arithmetic.
-/

namespace Solanalib

/-- A binary fixed-point number with arbitrary width and with `n` fractional bits.

`Fraction.mk b` represents the rational number `b / 2^n`. -/
@[ext]
structure Fraction (n: ℕ) where
  /-- The underlying integer encoding: `bits = toRat * 2^n`. -/
  bits : ℤ
  deriving Repr, DecidableEq

/-- A binary fixed-point number with 60 fractional bits to match the
`U68F60` convention common in Solana DeFi.
-/
abbrev Q68_60 := Fraction 60

namespace Fraction

-- The number of fractional bits
variable {n: ℕ}



/-! ### Basic definitions -/

instance : Zero (Fraction n) := ⟨⟨0⟩⟩
instance : One (Fraction n) := ⟨⟨2^n⟩⟩

@[simp, grind =] theorem bits_zero : (0: Fraction n).bits = 0 := rfl
@[simp, grind =] theorem bits_one : (1: Fraction n).bits = 2^n := rfl

/-- Convert a natural `k` to its fixed-point encoding `k * 2^n`. -/
instance : NatCast (Fraction n) where
  natCast (k: ℕ) := ⟨k * 2^n⟩

/-- Convert an integer `k` to its fixed-point encoding `k * 2^n`. -/
instance : IntCast (Fraction n) where
  intCast (k: ℤ) := ⟨k * 2^n⟩


@[simp, grind =] theorem bits_natCast (k: ℕ) : (k : Fraction n).bits = k * 2 ^n := rfl
@[simp, grind =] theorem bits_intCast (k: ℤ) : (k : Fraction n).bits = k * 2 ^n := rfl




/-! ### Order -/

/-- The linear order on the underlying integer lifts to `Fraction n`. -/
instance : LinearOrder (Fraction n) :=
  LinearOrder.lift' bits (fun _ _ h ↦ Fraction.ext h)


@[simp] theorem bits_le_bits (f₁ f₂: Fraction n) : f₁.bits ≤ f₂.bits ↔ f₁ ≤ f₂ := by rfl
@[simp] theorem bits_lt_bits (f₁ f₂: Fraction n) : f₁.bits < f₂.bits ↔ f₁ < f₂ := by rfl


/-! ### Addition, Negation, and Subtraction

Addition, negation and subtraction on fixed-point numbers are defined on their bits.
Fixed-point numbers are closed under these operations, i.e., the results always land on the grid.

-/

instance : Add (Fraction n) where add (f₁ f₂) := ⟨f₁.bits + f₂.bits⟩

@[simp, grind =] theorem bits_add (f₁ f₂: Fraction n) : (f₁ + f₂).bits = f₁.bits + f₂.bits := rfl
@[simp] theorem add_zero (f: Fraction n) : f + 0 = f := by ext; simp
@[simp] theorem zero_add (f: Fraction n) : 0 + f = f := by ext; simp

theorem add_assoc (f₁ f₂ f₃ : Fraction n) : f₁ + f₂ + f₃ = f₁ + (f₂ + f₃) := by
  ext; simp[Int.add_assoc]

theorem add_comm (f₁ f₂ : Fraction n) : f₁ + f₂ = f₂ + f₁ := by ext; simp[Int.add_comm]

theorem add_le_add_left (f₁ f₂: Fraction n) (f: Fraction n) (h: f₁ ≤ f₂): f₁ + f ≤ f₂ + f := by
  rw[← bits_le_bits]; simp[bits_le_bits, h]


instance : Sub (Fraction n) where sub (f₁ f₂) := ⟨f₁.bits - f₂.bits⟩

@[simp, grind =] theorem bits_sub (f₁ f₂: Fraction n) : (f₁ - f₂).bits = f₁.bits - f₂.bits := rfl
@[simp] theorem sub_zero (f: Fraction n) : f - 0 = f := by ext; simp

instance : Neg (Fraction n) where neg f := ⟨-f.bits⟩

@[simp, grind =] theorem neg_bits (f: Fraction n) : (-f).bits = -(f.bits) := by rfl
@[simp] theorem neg_neg (f: Fraction n) : -(-f) = f := by ext; simp
@[simp] theorem zero_sub (f: Fraction n) : 0 - f = -f := by ext; simp
@[simp] theorem neg_add_cancel (f: Fraction n) : -f + f = 0 := by ext; simp

/-- `Fraction n` is an abelian group under addition. -/
instance : AddCommGroup (Fraction n) where
  add_assoc := add_assoc
  add_comm := add_comm
  zero_add := zero_add
  add_zero := add_zero
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := neg_add_cancel


/-- The casts from `ℕ` and `ℤ` agree with `0`, `1` and `+` on `Fraction n`. -/
instance : AddCommGroupWithOne (Fraction n) where
  natCast_zero := by ext; simp
  natCast_succ := by intro _; ext; simp[add_mul]

instance : IsOrderedAddMonoid (Fraction n) where
  add_le_add_left f₁ f₂ h c := add_le_add_left f₁ f₂ c h

/-! ### Conversion to the rational numbers -/

/-- The rational number represented by a fraction `f`. -/
def toRat (f: Fraction n) : ℚ := f.bits / 2^n

instance : (CoeOut (Fraction n)) ℚ  where
  coe := fun f ↦ f.toRat

theorem toRat_nonneg (f : Fraction n) : 0 ≤ f.toRat ↔ 0 ≤ f := by
  rw [← bits_le_bits, bits_zero, toRat, le_div_iff₀ (by positivity), zero_mul]
  norm_cast

@[simp, grind =] theorem toRat_le_toRat {f₁ f₂ : Fraction n} : f₁.toRat ≤ f₂.toRat ↔ f₁ ≤ f₂ := by
  rw [← bits_le_bits, toRat, toRat, div_le_div_iff_of_pos_right (by positivity)]
  norm_cast

@[simp, grind =] theorem toRat_add (f₁ f₂ : Fraction n) :
    (f₁ + f₂).toRat = f₁.toRat + f₂.toRat := by
  simp only [toRat, bits_add, Int.cast_add, add_div]

/-! ### Conversion to integers -/

/-- The largest integer that is at most `f`, rounding toward -∞. -/
def toIntFloor (f: Fraction n) : ℤ := ⌊f.toRat⌋

/-- The smallest integer that is at least `f`, rounding toward ∞. -/
def toIntCeil (f: Fraction n) : ℤ := ⌈f.toRat⌉

/-- The integer part of `f`, rounding toward 0. -/
def toIntTrunc (f : Fraction n) : ℤ := if 0 ≤ f.toRat then ⌊f.toRat⌋ else ⌈f.toRat⌉

theorem toIntFloor_eq_fdiv (f : Fraction n) : f.toIntFloor = f.bits.fdiv (2 ^ n) := by
  rw [toIntFloor, toRat, Int.fdiv_eq_ediv, if_pos (Or.inl (by positivity)), Int.sub_zero]
  exact_mod_cast Rat.floor_intCast_div_natCast f.bits (2 ^ n)

theorem toIntCeil_eq_neg_fdiv_neg (f : Fraction n) :
    f.toIntCeil = -((-f.bits).fdiv (2 ^ n)) := by
  have h := Rat.floor_intCast_div_natCast (-f.bits) (2 ^ n)
  push_cast at h
  rw [toIntCeil, toRat, Int.fdiv_eq_ediv, if_pos (Or.inl (by positivity)), Int.sub_zero, ← h,
    neg_div, Int.floor_neg, _root_.neg_neg]

theorem toIntTrunc_eq_tdiv (f : Fraction n) : f.toIntTrunc = f.bits.tdiv (2 ^ n) := by
  rw [toIntTrunc]
  split_ifs with h
  · have hb : 0 ≤ f.bits := (toRat_nonneg f).mp h
    rw [← toIntFloor, toIntFloor_eq_fdiv, Int.fdiv_eq_ediv, if_pos (Or.inl (by positivity)),
      Int.sub_zero, Int.tdiv_eq_ediv_of_nonneg hb]
  · have hb : f.bits < 0 := not_le.mp fun hb => h ((toRat_nonneg f).mpr hb)
    rw [← toIntCeil, toIntCeil_eq_neg_fdiv_neg, Int.fdiv_eq_ediv,
      if_pos (Or.inl (by positivity)), Int.sub_zero]
    conv_rhs => rw [← Int.neg_neg f.bits, Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by omega)]

/-! #### Roundtrips

Casting an integer or a natural number to `Fraction n` and rounding it back gives the original
number in every rounding direction.
-/

@[simp] theorem toIntFloor_intCast (z : ℤ) : (z : Fraction n).toIntFloor = z := by
  simp [toIntFloor, toRat]

@[simp] theorem toIntCeil_intCast (z : ℤ) : (z : Fraction n).toIntCeil = z := by
  simp [toIntCeil, toRat]

@[simp] theorem toIntTrunc_intCast (z : ℤ) : (z : Fraction n).toIntTrunc = z := by
  simp [toIntTrunc, toRat]

@[simp] theorem toIntFloor_natCast (k : ℕ) : (k : Fraction n).toIntFloor = k := by
  simp [toIntFloor, toRat]

@[simp] theorem toIntCeil_natCast (k : ℕ) : (k : Fraction n).toIntCeil = k := by
  simp [toIntCeil, toRat]

@[simp] theorem toIntTrunc_natCast (k : ℕ) : (k : Fraction n).toIntTrunc = k := by
  simp [toIntTrunc, toRat]

/-! #### Lamports

`Lamports` is `UInt64`. The lift `ofLamports` is exact. The reverse projection
`toLamports?` returns `Option` because the integer floor of a fraction can be negative or exceed
`u64::MAX`. -/

/-- Lift a `Lamports` (u64) to its exact `Fraction` encoding. -/
def ofLamports (l : Lamports) : Fraction n := ↑l.toNat

/-- Project a `Fraction` to `Lamports` by taking the integer floor.
Returns `none` if the floor is negative or exceeds `u64::MAX`. -/
def toLamports? (f : Fraction n) : Option Lamports := do
  let k ← f.toIntFloor.toNat?
  if h : k < UInt64.size then some (UInt64.ofNatLT k h) else none

/-- The lift preserves the integer value exactly. -/
@[simp] theorem toIntFloor_ofLamports (l : Lamports) :
    (ofLamports l : Fraction n).toIntFloor = l.toNat := by
  apply toIntFloor_natCast _

/-! #### Rounding error

Rounding `f` to an integer and casting the result back to `Fraction n` changes it by less than `1`.
`toIntFloor` gives a value at most `f`, `toIntCeil` gives a value at least `f`, and the absolute
value of `toIntTrunc` is at most `|f|`.
-/

/-- Casting `f.toIntFloor` back to `Fraction n` gives a value at most `f`. -/
theorem intCast_toIntFloor_le (f : Fraction n) : (f.toIntFloor : Fraction n) ≤ f := by
  unfold toIntFloor toRat
  rw [← bits_le_bits, bits_intCast]
  have h := Int.floor_le ((f.bits : ℚ) / 2 ^ n)
  rw [le_div_iff₀ (by simp)] at h
  exact_mod_cast h

/-- `f` is less than `f.toIntFloor + 1` cast to `Fraction n`. -/
theorem lt_intCast_toIntFloor_add_one (f : Fraction n) :
    f < ((f.toIntFloor + 1 : ℤ) : Fraction n) := by
  unfold toIntFloor toRat
  rw [← bits_lt_bits, bits_intCast]
  have h := Int.lt_floor_add_one ((f.bits : ℚ) / 2 ^ n)
  rw [div_lt_iff₀ (by simp)] at h
  exact_mod_cast h

/-- Casting `f.toIntCeil` back to `Fraction n` gives a value at least `f`. -/
theorem intCast_toIntCeil_le (f : Fraction n) : f ≤ (f.toIntCeil : Fraction n) := by
  unfold toIntCeil toRat
  rw [← bits_le_bits, bits_intCast]
  have h := Int.le_ceil ((f.bits : ℚ) / 2 ^ n)
  rw [div_le_iff₀ (by simp)] at h
  exact_mod_cast h

/-- `f.toIntCeil - 1` cast to `Fraction n` is less than `f`. -/
theorem lt_intCast_toIntCeil_add_one (f : Fraction n) :
    ((f.toIntCeil - 1 : ℤ) : Fraction n) < f := by
  unfold toIntCeil toRat
  rw [← bits_lt_bits, bits_intCast]
  have h := Int.ceil_lt_add_one ((f.bits : ℚ) / 2 ^ n)
  rw [← sub_lt_iff_lt_add, lt_div_iff₀ (by simp)] at h
  exact_mod_cast h

/-- Casting `f.toIntTrunc` back to `Fraction n` gives a value whose absolute value is at most
`|f|`. -/
theorem abs_intCast_toIntTrunc_le (f : Fraction n) :
    |(f.toIntTrunc : Fraction n)| ≤ |f| := by
  unfold toIntTrunc
  split_ifs with h
  · have h' : 0 ≤ (⌊toRat f⌋ : Fraction n) := by
      rw [← bits_le_bits, bits_zero, bits_intCast]
      exact mul_nonneg (Int.floor_nonneg.mpr h) (by positivity)
    exact abs_le_abs_of_nonneg h' (intCast_toIntFloor_le f)
  · have h' : (⌈toRat f⌉ : Fraction n) ≤ 0 := by
      rw [← bits_le_bits, bits_zero, bits_intCast]
      have hc : ⌈toRat f⌉ ≤ 0 := Int.ceil_le.mpr (by exact_mod_cast (not_le.mp h).le)
      exact mul_nonpos_iff.mpr (Or.inr ⟨hc, by positivity⟩)
    exact abs_le_abs_of_nonpos h' (intCast_toIntCeil_le f)

/-- `f` and `f.toIntTrunc` cast to `Fraction n` differ by less than `1`. -/
theorem abs_sub_intCast_toIntTrunc_lt_one (f : Fraction n) :
    |f - (f.toIntTrunc : Fraction n)| < 1 := by
  have h1 : (0 : Fraction n) < 1 := by rw [← bits_lt_bits]; simp
  unfold toIntTrunc
  rw [abs_lt]
  split_ifs
  · have hlo := intCast_toIntFloor_le f
    have hhi := lt_intCast_toIntFloor_add_one f
    rw [Int.cast_add, Int.cast_one] at hhi
    exact ⟨lt_of_lt_of_le (neg_neg_of_pos h1) (sub_nonneg.mpr hlo), sub_lt_iff_lt_add'.mpr hhi⟩
  · have hlo := lt_intCast_toIntCeil_add_one f
    have hhi := intCast_toIntCeil_le f
    rw [Int.cast_sub, Int.cast_one] at hlo
    exact ⟨by rw [lt_sub_iff_add_lt, neg_add_eq_sub]; exact hlo,
      lt_of_le_of_lt (sub_nonpos.mpr hhi) h1⟩


/-! ### Multiplication

The exact product of two fixed-point numbers with `n` fractional bits has `2n` fractional bits,
so in general it does not land on the grid.
Its value is `(f₁.bits * f₂.bits / 2^n) / 2^n`, where `f₁.bits * f₂.bits / 2^n` is in general
not an integer, so it cannot be used as the underlying bits.
Therefore, fixed-point multiplication rounds `f₁.bits * f₂.bits / 2^n` to an integer and uses it
as the bits.

We provide three definitions of multiplication, one for each rounding direction:
`mulFloor` (`*↓`, toward -∞), `mulCeil` (`*↑`, toward ∞), and `mulTrunc` (`*₀`, toward 0).

There is deliberately no `Mul` instance and no instance of a class built on it, such as
`CommMagma`, so every multiplication on `Fraction n` must state its rounding direction.
-/


/-- The largest fixed-point number that is at most the exact product of `f₁` and `f₂`. -/
def mulFloor (f₁ f₂ : Fraction n) : Fraction n := ⟨(f₁.bits * f₂.bits).fdiv (2 ^ n)⟩

@[inherit_doc] scoped infixl:70 " *↓ " => mulFloor

@[simp, grind =] theorem bits_mulFloor (f₁ f₂ : Fraction n) :
    (f₁ *↓ f₂).bits = (f₁.bits * f₂.bits).fdiv (2 ^ n) := rfl

@[simp] theorem mulFloor_zero (f : Fraction n) : f *↓ 0 = 0 := by ext; simp [mulFloor]
@[simp] theorem zero_mulFloor (f : Fraction n) : 0 *↓ f = 0 := by ext; simp [mulFloor]
@[simp] theorem mulFloor_one (f : Fraction n) : f *↓ 1 = f := by ext; simp [mulFloor]
@[simp] theorem one_mulFloor (f : Fraction n) : 1 *↓ f = f := by ext; simp [mulFloor]

theorem mulFloor_comm (f₁ f₂ : Fraction n) : f₁ *↓ f₂ = f₂ *↓ f₁ := by
  simp only [mulFloor, Int.mul_comm]

/-- The smallest fixed-point number that is at least the exact product of `f₁` and `f₂`. -/
def mulCeil (f₁ f₂ : Fraction n) : Fraction n :=
  let p := f₁.bits * f₂.bits
  if 2 ^ n ∣ p then ⟨p.fdiv (2 ^ n)⟩ else ⟨p.fdiv (2 ^ n) + 1⟩

@[inherit_doc] scoped infixl:70 " *↑ " => mulCeil

theorem mulCeil_eq (f₁ f₂ : Fraction n) :
    f₁ *↑ f₂ = ⟨-((-(f₁.bits * f₂.bits)).fdiv (2 ^ n))⟩ := by
  ext
  simp only [mulCeil]
  by_cases h : 2 ^ n ∣ f₁.bits * f₂.bits
  · rw [if_pos h, Int.neg_fdiv_of_dvd h, Int.neg_neg]
  · rw [if_neg h]
    simp only [Int.fdiv_eq_ediv, Nat.ofNat_nonneg, pow_nonneg, h, or_false, ↓reduceIte,
      _root_.sub_zero, Int.neg_ediv, Int.sign_eq_one_of_pos (by positivity : (0 : ℤ) < 2 ^ n),
      dvd_neg, neg_sub, sub_neg_eq_add]
    omega

@[simp, grind =] theorem bits_mulCeil (f₁ f₂ : Fraction n) :
    (f₁ *↑ f₂).bits = -((-(f₁.bits * f₂.bits)).fdiv (2 ^ n)) := by
  rw [mulCeil_eq]

@[simp] theorem mulCeil_zero (f : Fraction n) : f *↑ 0 = 0 := by ext; simp [mulCeil]
@[simp] theorem zero_mulCeil (f : Fraction n) : 0 *↑ f = 0 := by ext; simp [mulCeil]
@[simp] theorem mulCeil_one (f : Fraction n) : f *↑ 1 = f := by ext; simp [mulCeil]
@[simp] theorem one_mulCeil (f : Fraction n) : 1 *↑ f = f := by ext; simp [mulCeil]

theorem mulCeil_comm (f₁ f₂ : Fraction n) : f₁ *↑ f₂ = f₂ *↑ f₁ := by
  simp only [mulCeil, Int.mul_comm]

@[simp] theorem neg_mulFloor (f₁ f₂ : Fraction n) : -f₁ *↓ f₂ = -(f₁ *↑ f₂) := by
  ext; rw [mulCeil_eq]; simp [mulFloor]

/-- The fixed-point number nearest to the exact product of `f₁` and `f₂` in the direction of 0. -/
def mulTrunc (f₁ f₂ : Fraction n) : Fraction n := ⟨(f₁.bits * f₂.bits).tdiv (2 ^ n)⟩

@[inherit_doc] scoped infixl:70 " *₀ " => mulTrunc

@[simp, grind =] theorem bits_mulTrunc (f₁ f₂ : Fraction n) :
    (f₁ *₀ f₂).bits = (f₁.bits * f₂.bits).tdiv (2 ^ n) := rfl

theorem mulTrunc_comm (f₁ f₂ : Fraction n) : f₁ *₀ f₂ = f₂ *₀ f₁ := by
  simp only [mulTrunc, Int.mul_comm]

@[grind =] theorem mulTrunc_eq_mulFloor_of_nonneg {f₁ f₂ : Fraction n}
    (h : 0 ≤ f₁.bits * f₂.bits) : f₁ *₀ f₂ = f₁ *↓ f₂ := by
  ext; simp [mulTrunc, mulFloor, Int.fdiv_eq_ediv, Int.tdiv_eq_ediv_of_nonneg h]

@[grind =] theorem mulTrunc_eq_mulCeil_of_neg {f₁ f₂ : Fraction n}
    (h : f₁.bits * f₂.bits < 0) : f₁ *₀ f₂ = f₁ *↑ f₂ := by
  ext; grind [mulCeil, Int.fdiv_eq_ediv, Int.tdiv_eq_ediv]

theorem mulFloor_le_mulTrunc (f₁ f₂ : Fraction n) : f₁ *↓ f₂ ≤ f₁ *₀ f₂ := by
  rw [← bits_le_bits]
  grind [Int.fdiv_eq_ediv, Int.tdiv_eq_ediv]

theorem mulTrunc_le_mulCeil (f₁ f₂ : Fraction n) : f₁ *₀ f₂ ≤ f₁ *↑ f₂ := by
  rw [← bits_le_bits]
  grind [mulCeil, Int.fdiv_eq_ediv, Int.tdiv_eq_ediv]


/-! ### Division

The exact quotient of two fixed-point numbers with `n` fractional bits is
`f₁.toRat / f₂.toRat = f₁.bits / f₂.bits`, so in general it does not land on the grid.
Its bits would be `f₁.bits * 2^n / f₂.bits`, which is in general not an integer.
Therefore, fixed-point division rounds this value to an integer and uses it as the bits.

We provide three definitions of division, one for each rounding direction:
`divFloor` (`/↓`, toward -∞), `divCeil` (`/↑`, toward ∞), and `divTrunc` (`/₀`, toward 0).
Division by `0` returns `0` in all three.

There is deliberately no `Div` instance, so every division on `Fraction n` must state its
rounding direction.
-/

/-- The largest fixed-point number that is at most the exact quotient of `f₁` and `f₂`. -/
def divFloor (f₁ f₂ : Fraction n) : Fraction n := ⟨(f₁.bits * 2 ^ n).fdiv f₂.bits⟩

@[inherit_doc] scoped infixl:70 " /↓ " => divFloor

@[simp, grind =] theorem bits_divFloor (f₁ f₂ : Fraction n) :
    (f₁ /↓ f₂).bits = (f₁.bits * 2 ^ n).fdiv f₂.bits := rfl

/-- The smallest fixed-point number that is at least the exact quotient of `f₁` and `f₂`. -/
def divCeil (f₁ f₂ : Fraction n) : Fraction n :=
  let p := f₁.bits * 2 ^ n
  if f₂ = 0 ∨ f₂.bits ∣ p then ⟨p.fdiv f₂.bits⟩ else ⟨p.fdiv f₂.bits + 1⟩

@[inherit_doc] scoped infixl:70 " /↑ " => divCeil

/-- The fixed-point number nearest to the exact quotient of `f₁` and `f₂` in the direction of 0.
-/
def divTrunc (f₁ f₂ : Fraction n) : Fraction n := ⟨(f₁.bits * 2 ^ n).tdiv f₂.bits⟩

@[inherit_doc] scoped infixl:70 " /₀ " => divTrunc

@[simp, grind =] theorem bits_divTrunc (f₁ f₂ : Fraction n) :
    (f₁ /₀ f₂).bits = (f₁.bits * 2 ^ n).tdiv f₂.bits := rfl

theorem divCeil_eq (f₁ f₂ : Fraction n) :
    f₁ /↑ f₂ = ⟨-((-(f₁.bits * 2 ^ n)).fdiv f₂.bits)⟩ := by
  ext
  simp only [divCeil]
  by_cases h₀ : f₂ = 0
  · subst h₀
    simp
  by_cases h : f₂.bits ∣ f₁.bits * 2 ^ n
  · rw [if_pos (Or.inr h), Int.neg_fdiv_of_dvd h, Int.neg_neg]
  · have hb : f₂.bits ≠ 0 := fun hb => h₀ (Fraction.ext hb)
    have e : (-(f₁.bits * 2 ^ n)).fdiv f₂.bits = (f₁.bits * 2 ^ n).fdiv (-f₂.bits) := by
      rw [← Int.neg_fdiv_neg, Int.neg_neg]
    rw [if_neg (by tauto)]
    simp only [e, Int.fdiv_neg hb, if_neg h]
    omega

@[simp, grind =] theorem bits_divCeil (f₁ f₂ : Fraction n) :
    (f₁ /↑ f₂).bits = -((-(f₁.bits * 2 ^ n)).fdiv f₂.bits) := by
  rw [divCeil_eq]

@[simp] theorem divFloor_zero (f : Fraction n) : f /↓ 0 = 0 := by ext; simp [divFloor]
@[simp] theorem zero_divFloor (f : Fraction n) : 0 /↓ f = 0 := by ext; simp [divFloor]
@[simp] theorem divFloor_one (f : Fraction n) : f /↓ 1 = f := by ext; simp [divFloor]

@[simp] theorem divCeil_zero (f : Fraction n) : f /↑ 0 = 0 := by ext; simp [divCeil]
@[simp] theorem zero_divCeil (f : Fraction n) : 0 /↑ f = 0 := by ext; simp [divCeil]
@[simp] theorem divCeil_one (f : Fraction n) : f /↑ 1 = f := by ext; simp [divCeil]

@[simp] theorem divTrunc_zero (f : Fraction n) : f /₀ 0 = 0 := by ext; simp [divTrunc]
@[simp] theorem zero_divTrunc (f : Fraction n) : 0 /₀ f = 0 := by ext; simp [divTrunc]
@[simp] theorem divTrunc_one (f : Fraction n) : f /₀ 1 = f := by ext; simp [divTrunc]

theorem neg_divFloor (f₁ f₂ : Fraction n) : -f₁ /↓ f₂ = -(f₁ /↑ f₂) := by
  ext; rw [divCeil_eq]; simp [divFloor]

@[simp] theorem neg_divFloor_neg (f₁ f₂ : Fraction n) : -f₁ /↓ -f₂ = f₁ /↓ f₂ := by
  ext; simp only [divFloor, neg_bits, neg_mul, Int.neg_fdiv_neg]

@[simp] theorem neg_divCeil_neg (f₁ f₂ : Fraction n) : -f₁ /↑ -f₂ = f₁ /↑ f₂ := by
  rw [divCeil_eq, divCeil_eq]
  ext
  simp only [neg_bits]
  rw [neg_mul, Int.neg_fdiv_neg]

@[simp] theorem neg_divTrunc_neg (f₁ f₂ : Fraction n) : -f₁ /₀ -f₂ = f₁ /₀ f₂ := by
  ext; simp [divTrunc]

@[grind =] theorem divTrunc_eq_divFloor_of_nonneg {f₁ f₂ : Fraction n}
    (h : 0 ≤ f₁.bits * f₂.bits) : f₁ /₀ f₂ = f₁ /↓ f₂ := by
  ext
  simp only [divTrunc, divFloor]
  have h2 : (0 : ℤ) < 2 ^ n := by positivity
  rcases lt_trichotomy f₂.bits 0 with hb | hb | hb
  · have hp : f₁.bits * 2 ^ n ≤ 0 := by nlinarith
    rw [← Int.neg_tdiv_neg, ← Int.neg_fdiv_neg, Int.tdiv_eq_ediv_of_nonneg (by linarith),
      Int.fdiv_eq_ediv, if_pos (Or.inl (by linarith)), Int.sub_zero]
  · simp [hb]
  · have hp : 0 ≤ f₁.bits * 2 ^ n := by nlinarith
    rw [Int.tdiv_eq_ediv_of_nonneg hp, Int.fdiv_eq_ediv, if_pos (Or.inl hb.le), Int.sub_zero]

@[grind =] theorem divTrunc_eq_divCeil_of_neg {f₁ f₂ : Fraction n}
    (h : f₁.bits * f₂.bits < 0) : f₁ /₀ f₂ = f₁ /↑ f₂ := by
  rw [divCeil_eq]
  ext
  simp only [divTrunc]
  have h2 : (0 : ℤ) < 2 ^ n := by positivity
  rcases lt_trichotomy f₂.bits 0 with hb | hb | hb
  · have hp : 0 < f₁.bits * 2 ^ n := by nlinarith
    rw [← Int.neg_tdiv_neg, Int.neg_tdiv, ← Int.neg_fdiv_neg, Int.neg_neg,
      Int.tdiv_eq_ediv_of_nonneg hp.le, Int.fdiv_eq_ediv, if_pos (Or.inl (by linarith)),
      Int.sub_zero]
  · simp [hb] at h
  · have hp : f₁.bits * 2 ^ n < 0 := by nlinarith
    conv_lhs => rw [← Int.neg_neg (f₁.bits * 2 ^ n), Int.neg_tdiv,
      Int.tdiv_eq_ediv_of_nonneg (by linarith)]
    rw [Int.fdiv_eq_ediv, if_pos (Or.inl hb.le), Int.sub_zero]

theorem divFloor_le_divCeil (f₁ f₂ : Fraction n) : f₁ /↓ f₂ ≤ f₁ /↑ f₂ := by
  rw [← bits_le_bits]
  grind [divCeil]

theorem divFloor_le_divTrunc (f₁ f₂ : Fraction n) : f₁ /↓ f₂ ≤ f₁ /₀ f₂ := by
  grind [divFloor_le_divCeil]

theorem divTrunc_le_divCeil (f₁ f₂ : Fraction n) : f₁ /₀ f₂ ≤ f₁ /↑ f₂ := by
  grind [divFloor_le_divCeil]

/-!
### Embedding into `ℚ` and precision loss

Each `f : Fraction n` stands for the rational number `f.toRat = f.bits / 2^n`.
`toRatOrderAddIso` shows that `toRat` is a bijection between `Fraction n` and the multiples of
`1 / 2^n` in `ℚ` that preserves `+` (and therefore `0`, negation and `-`) and `≤`.

Every other rational number, such as `1 / 3`, has no representation as a `Fraction n` and must be
rounded. Multiplication and division are therefore not exact. Their correctness with respect to
`ℚ` is the bound on the rounding error in the `Precision loss` sections below.

Results:

* Embedding: `toRat` is an order-preserving additive isomorphism onto the multiples of
  `1 / 2^n`.
* Multiplication:
  * `*↓` is at most and `*↑` is at least the exact product, `|f₁ *₀ f₂|` is at most `|f₁ * f₂|`,
    and each differs from the exact product by less than `1 / 2^n`.
  * Associativity: for each rounding mode, `f₁ * f₂ * f₃` and `f₁ * (f₂ * f₃)` differ by less
    than `(|f₁| + |f₃| + 1) / 2^n`.
* Division: for `f₂ ≠ 0`, `/↓` is at most and `/↑` is at least the exact quotient, `|f₁ /₀ f₂|` is
  at most `|f₁ / f₂|`, and each differs from the exact quotient by less than `1 / 2^n`.
-/

/-- `toRat` as an order-preserving additive isomorphism from `Fraction n` onto the multiples of
`1 / 2^n` in `ℚ`. -/
def toRatOrderAddIso : Fraction n ≃+o AddSubgroup.zmultiples ((2 ^ n)⁻¹ : ℚ) where
  toFun f := ⟨f.toRat, f.bits, by simp [toRat, zsmul_eq_mul, div_eq_mul_inv]⟩
  invFun q := ⟨⌊(q : ℚ) * 2 ^ n⌋⟩
  left_inv f := by ext; simp [toRat]
  right_inv := by
    intro ⟨q, hq⟩
    simp[toRat]
    apply AddSubgroup.mem_zmultiples_iff.mp at hq
    obtain ⟨k, hk⟩ := hq
    rw[←hk]
    simp [zsmul_eq_mul, div_eq_mul_inv]
  map_add' f₁ f₂ := by ext; simp
  map_le_map_iff' := toRat_le_toRat

/-! #### Precision loss of multiplication

Each multiplication differs from the exact product `f₁.toRat * f₂.toRat` by less than `1 / 2^n`,
the distance between two neighboring fixed-point numbers.
`mulFloor` is at most the exact product, `mulCeil` is at least the exact product, and the absolute
value of `mulTrunc` is at most the absolute value of the exact product.
-/

/-- `f₁ *↓ f₂` is at most the exact product. -/
theorem toRat_mulFloor_le (f₁ f₂ : Fraction n) :
    (f₁ *↓ f₂).toRat ≤ f₁.toRat * f₂.toRat := by
  simp only [toRat, mulFloor, Int.fdiv_eq_ediv, Nat.ofNat_nonneg, pow_nonneg, true_or,
    ↓reduceIte, _root_.sub_zero]
  field_simp
  norm_cast
  simp [Int.ediv_mul_le]

-- The `grind` attribute cannot select `(f₁ *↓ f₂).toRat` as the pattern.
grind_pattern toRat_mulFloor_le => (f₁ *↓ f₂).toRat

/-- The exact product is less than `f₁ *↓ f₂ + 1 / 2 ^ n`. -/
theorem lt_toRat_mulFloor_add (f₁ f₂ : Fraction n) :
    f₁.toRat * f₂.toRat < (f₁ *↓ f₂).toRat + 1 / 2 ^ n := by
  simp only [toRat, mulFloor, Int.fdiv_eq_ediv, Nat.ofNat_nonneg, pow_nonneg, true_or,
    ↓reduceIte, _root_.sub_zero, one_div]
  field_simp
  norm_cast
  conv => rhs; rw [Int.mul_comm]
  apply Int.lt_ediv_add_one_mul_self (H := by simp)

-- The `grind` attribute cannot select `(f₁ *↓ f₂).toRat` as the pattern.
grind_pattern lt_toRat_mulFloor_add => (f₁ *↓ f₂).toRat

/-- `f₁ *↑ f₂` is at least the exact product. -/
theorem le_toRat_mulCeil (f₁ f₂ : Fraction n) :
    f₁.toRat * f₂.toRat ≤ (f₁ *↑ f₂).toRat := by
  rw [mulCeil_eq]
  simp only [toRat, Int.fdiv_eq_ediv, Nat.ofNat_nonneg, pow_nonneg, dvd_neg, true_or,
    ↓reduceIte, _root_.sub_zero, Int.cast_neg]
  field_simp
  norm_cast
  rw [le_neg, Int.mul_comm]
  apply Int.ediv_mul_le (H := by simp)

-- The `grind` attribute cannot select `(f₁ *↑ f₂).toRat` as the pattern.
grind_pattern le_toRat_mulCeil => (f₁ *↑ f₂).toRat

/-- `f₁ *↑ f₂ - 1 / 2 ^ n` is less than the exact product. -/
theorem toRat_mulCeil_sub_lt (f₁ f₂ : Fraction n) :
    (f₁ *↑ f₂).toRat - 1 / 2 ^ n < f₁.toRat * f₂.toRat := by
  rw [mulCeil_eq]
  simp only [toRat, Int.fdiv_eq_ediv, Nat.ofNat_nonneg, pow_nonneg, dvd_neg, true_or,
    ↓reduceIte, _root_.sub_zero, Int.cast_neg, one_div]
  field_simp
  norm_cast
  rw [← neg_add', mul_neg, neg_lt]
  conv => rhs; rw [Int.mul_comm]
  apply Int.lt_ediv_add_one_mul_self (H := by simp)

-- The `grind` attribute cannot select `(f₁ *↑ f₂).toRat` as the pattern.
grind_pattern toRat_mulCeil_sub_lt => (f₁ *↑ f₂).toRat

/-- The absolute value of `f₁ *₀ f₂` is at most the absolute value of the exact product. -/
theorem abs_toRat_mulTrunc_le (f₁ f₂ : Fraction n) :
    |(f₁ *₀ f₂).toRat| ≤ |f₁.toRat * f₂.toRat| := by
  rcases le_or_gt 0 (f₁.bits * f₂.bits) with h | h
  · have := (toRat_nonneg (f₁ *↓ f₂)).mpr (Int.fdiv_nonneg h (by positivity))
    grind
  · rw [mulTrunc_eq_mulCeil_of_neg h]
    apply abs_le_abs_of_nonpos _ (le_toRat_mulCeil f₁ f₂)
    rw [mulCeil_eq]
    unfold toRat
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    rw [Int.fdiv_eq_ediv, if_pos (Or.inl (by positivity)), Int.sub_zero]
    have := Int.ediv_nonneg (a := -(f₁.bits * f₂.bits)) (b := 2 ^ n) (by linarith) (by positivity)
    exact_mod_cast neg_nonpos.mpr this

/-- `f₁ *₀ f₂` differs from the exact product by less than `1 / 2 ^ n`. -/
theorem abs_sub_toRat_mulTrunc_lt (f₁ f₂ : Fraction n) :
    |f₁.toRat * f₂.toRat - (f₁ *₀ f₂).toRat| < 1 / 2 ^ n := by
  grind

/-- `f₁ *↓ f₂ *↓ f₃` and `f₁ *↓ (f₂ *↓ f₃)` differ by less than `(|f₁| + |f₃| + 1) / 2 ^ n`. -/
theorem abs_sub_toRat_mulFloor_assoc_lt (f₁ f₂ f₃ : Fraction n) :
    |(f₁ *↓ f₂ *↓ f₃).toRat - (f₁ *↓ (f₂ *↓ f₃)).toRat|
      < (|f₁.toRat| + |f₃.toRat| + 1) / 2 ^ n := by
  have err (f g : Fraction n) :
      0 ≤ f.toRat * g.toRat - (f *↓ g).toRat ∧ f.toRat * g.toRat - (f *↓ g).toRat < 1 / 2 ^ n :=
    ⟨sub_nonneg.mpr (toRat_mulFloor_le f g), sub_lt_iff_lt_add'.mpr (lt_toRat_mulFloor_add f g)⟩
  obtain ⟨hx₀, hx⟩ := err f₁ f₂
  obtain ⟨hy₀, hy⟩ := err f₂ f₃
  obtain ⟨hl₀, hl⟩ := err (f₁ *↓ f₂) f₃
  obtain ⟨hr₀, hr⟩ := err f₁ (f₂ *↓ f₃)
  set a := f₁.toRat
  set b := f₂.toRat
  set c := f₃.toRat
  set x := (f₁ *↓ f₂).toRat
  set y := (f₂ *↓ f₃).toRat
  set l := (f₁ *↓ f₂ *↓ f₃).toRat
  set r := (f₁ *↓ (f₂ *↓ f₃)).toRat
  set u : ℚ := 1 / 2 ^ n with hu
  have inner : |a * (b * c - y) - (a * b - x) * c| ≤ |a| * u + u * |c| :=
    calc |a * (b * c - y) - (a * b - x) * c|
        ≤ |a * (b * c - y)| + |(a * b - x) * c| := abs_sub _ _
      _ = |a| * (b * c - y) + (a * b - x) * |c| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hy₀, abs_of_nonneg hx₀]
      _ ≤ |a| * u + u * |c| := by
        apply add_le_add (mul_le_mul_of_nonneg_left hy.le (abs_nonneg a))
          (mul_le_mul_of_nonneg_right hx.le (abs_nonneg c))
  calc |l - r|
      = |(a * y - r) - (x * c - l) + (a * (b * c - y) - (a * b - x) * c)| := by congr 1; ring
    _ ≤ |(a * y - r) - (x * c - l)| + |a * (b * c - y) - (a * b - x) * c| := abs_add_le _ _
    _ < u + (|a| * u + u * |c|) :=
      add_lt_add_of_lt_of_le (abs_sub_lt_of_nonneg_of_lt hr₀ hr hl₀ hl) inner
    _ = (|a| + |c| + 1) / 2 ^ n := by rw [hu]; ring

/-- `f₁ *↑ f₂ *↑ f₃` and `f₁ *↑ (f₂ *↑ f₃)` differ by less than `(|f₁| + |f₃| + 1) / 2 ^ n`. -/
theorem abs_sub_toRat_mulCeil_assoc_lt (f₁ f₂ f₃ : Fraction n) :
    |(f₁ *↑ f₂ *↑ f₃).toRat - (f₁ *↑ (f₂ *↑ f₃)).toRat|
      < (|f₁.toRat| + |f₃.toRat| + 1) / 2 ^ n := by
  have err (f g : Fraction n) :
      0 ≤ (f *↑ g).toRat - f.toRat * g.toRat ∧ (f *↑ g).toRat - f.toRat * g.toRat < 1 / 2 ^ n :=
    ⟨sub_nonneg.mpr (le_toRat_mulCeil f g), sub_lt_comm.mpr (toRat_mulCeil_sub_lt f g)⟩
  obtain ⟨hx₀, hx⟩ := err f₁ f₂
  obtain ⟨hy₀, hy⟩ := err f₂ f₃
  obtain ⟨hl₀, hl⟩ := err (f₁ *↑ f₂) f₃
  obtain ⟨hr₀, hr⟩ := err f₁ (f₂ *↑ f₃)
  set a := f₁.toRat
  set b := f₂.toRat
  set c := f₃.toRat
  set x := (f₁ *↑ f₂).toRat
  set y := (f₂ *↑ f₃).toRat
  set l := (f₁ *↑ f₂ *↑ f₃).toRat
  set r := (f₁ *↑ (f₂ *↑ f₃)).toRat
  set u : ℚ := 1 / 2 ^ n with hu
  have inner : |(x - a * b) * c - a * (y - b * c)| ≤ u * |c| + |a| * u :=
    calc |(x - a * b) * c - a * (y - b * c)|
        ≤ |(x - a * b) * c| + |a * (y - b * c)| := abs_sub _ _
      _ = (x - a * b) * |c| + |a| * (y - b * c) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hx₀, abs_of_nonneg hy₀]
      _ ≤ u * |c| + |a| * u := by
        apply add_le_add (mul_le_mul_of_nonneg_right hx.le (abs_nonneg c))
          (mul_le_mul_of_nonneg_left hy.le (abs_nonneg a))
  calc |l - r|
      = |(l - x * c) - (r - a * y) + ((x - a * b) * c - a * (y - b * c))| := by congr 1; ring
    _ ≤ |(l - x * c) - (r - a * y)| + |(x - a * b) * c - a * (y - b * c)| := abs_add_le _ _
    _ < u + (u * |c| + |a| * u) :=
      add_lt_add_of_lt_of_le (abs_sub_lt_of_nonneg_of_lt hl₀ hl hr₀ hr) inner
    _ = (|a| + |c| + 1) / 2 ^ n := by rw [hu]; ring

/-- `f₁ *₀ f₂ *₀ f₃` and `f₁ *₀ (f₂ *₀ f₃)` differ by less than `(|f₁| + |f₃| + 1) / 2 ^ n`. -/
theorem abs_sub_toRat_mulTrunc_assoc_lt (f₁ f₂ f₃ : Fraction n) :
    |(f₁ *₀ f₂ *₀ f₃).toRat - (f₁ *₀ (f₂ *₀ f₃)).toRat|
      < (|f₁.toRat| + |f₃.toRat| + 1) / 2 ^ n := by
  have hx := abs_sub_toRat_mulTrunc_lt f₁ f₂
  have hy := abs_sub_toRat_mulTrunc_lt f₂ f₃
  have hl := abs_sub_toRat_mulTrunc_lt (f₁ *₀ f₂) f₃
  have hr := abs_sub_toRat_mulTrunc_lt f₁ (f₂ *₀ f₃)
  have hl' := abs_toRat_mulTrunc_le (f₁ *₀ f₂) f₃
  have hr' := abs_toRat_mulTrunc_le f₁ (f₂ *₀ f₃)
  set a := f₁.toRat
  set b := f₂.toRat
  set c := f₃.toRat
  set x := (f₁ *₀ f₂).toRat
  set y := (f₂ *₀ f₃).toRat
  set l := (f₁ *₀ f₂ *₀ f₃).toRat
  set r := (f₁ *₀ (f₂ *₀ f₃)).toRat
  set u : ℚ := 1 / 2 ^ n with hu
  have inner : |x * c - a * y| ≤ |a| * u + u * |c| :=
    calc |x * c - a * y|
        = |a * (b * c - y) - (a * b - x) * c| := by congr 1; ring
      _ ≤ |a * (b * c - y)| + |(a * b - x) * c| := abs_sub _ _
      _ = |a| * |b * c - y| + |a * b - x| * |c| := by rw [abs_mul, abs_mul]
      _ ≤ |a| * u + u * |c| :=
        add_le_add (mul_le_mul_of_nonneg_left hy.le (abs_nonneg a))
          (mul_le_mul_of_nonneg_right hx.le (abs_nonneg c))
  have outer : |l - r| < |x * c - a * y| + u := by
    rcases le_total 0 (x * c) with hp | hp <;> rcases le_total 0 (a * y) with hq | hq
    · have el : 0 ≤ x * c - l :=
        sub_nonneg.mpr ((le_abs_self l).trans (hl'.trans_eq (abs_of_nonneg hp)))
      have er : 0 ≤ a * y - r :=
        sub_nonneg.mpr ((le_abs_self r).trans (hr'.trans_eq (abs_of_nonneg hq)))
      calc |l - r|
          = |(x * c - a * y) + ((a * y - r) - (x * c - l))| := by congr 1; ring
        _ ≤ |x * c - a * y| + |(a * y - r) - (x * c - l)| := abs_add_le _ _
        _ < |x * c - a * y| + u := (add_lt_add_iff_left _).mpr
          (abs_sub_lt_of_nonneg_of_lt er (abs_lt.mp hr).2 el (abs_lt.mp hl).2)
    · calc |l - r|
          ≤ |l| + |r| := abs_sub _ _
        _ ≤ x * c + -(a * y) :=
          add_le_add (hl'.trans_eq (abs_of_nonneg hp)) (hr'.trans_eq (abs_of_nonpos hq))
        _ = x * c - a * y := (sub_eq_add_neg _ _).symm
        _ ≤ |x * c - a * y| := le_abs_self _
        _ < |x * c - a * y| + u := lt_add_of_pos_right _ (by rw [hu]; positivity)
    · calc |l - r|
          ≤ |l| + |r| := abs_sub _ _
        _ ≤ -(x * c) + a * y :=
          add_le_add (hl'.trans_eq (abs_of_nonpos hp)) (hr'.trans_eq (abs_of_nonneg hq))
        _ = a * y - x * c := neg_add_eq_sub _ _
        _ ≤ |a * y - x * c| := le_abs_self _
        _ = |x * c - a * y| := abs_sub_comm _ _
        _ < |x * c - a * y| + u := lt_add_of_pos_right _ (by rw [hu]; positivity)
    · have el : 0 ≤ l - x * c := sub_nonneg.mpr
        (neg_le_neg_iff.mp ((neg_le_abs l).trans (hl'.trans_eq (abs_of_nonpos hp))))
      have er : 0 ≤ r - a * y := sub_nonneg.mpr
        (neg_le_neg_iff.mp ((neg_le_abs r).trans (hr'.trans_eq (abs_of_nonpos hq))))
      calc |l - r|
          = |(x * c - a * y) + ((l - x * c) - (r - a * y))| := by congr 1; ring
        _ ≤ |x * c - a * y| + |(l - x * c) - (r - a * y)| := abs_add_le _ _
        _ < |x * c - a * y| + u := (add_lt_add_iff_left _).mpr
          (abs_sub_lt_of_nonneg_of_lt el (abs_lt.mp ((abs_sub_comm _ _).trans_lt hl)).2
            er (abs_lt.mp ((abs_sub_comm _ _).trans_lt hr)).2)
  calc |l - r|
      < |x * c - a * y| + u := outer
    _ ≤ |a| * u + u * |c| + u := (add_le_add_iff_right u).mpr inner
    _ = (|a| + |c| + 1) / 2 ^ n := by rw [hu]; ring


/-! #### Precision loss of division

For `f₂ ≠ 0`, each division differs from the exact quotient `f₁.toRat / f₂.toRat` by less than
`1 / 2^n`, the distance between two neighboring fixed-point numbers.
`divFloor` is at most the exact quotient, `divCeil` is at least the exact quotient, and the
absolute value of `divTrunc` is at most the absolute value of the exact quotient.
-/

/-- `f₁ /↓ f₂` is at most the exact quotient. -/
theorem toRat_divFloor_le (f₁ f₂ : Fraction n) (h₂ : f₂ ≠ 0) :
    (f₁ /↓ f₂).toRat ≤ f₁.toRat / f₂.toRat := by
  wlog hpos : 0 < f₂ generalizing f₁ f₂
  · simpa [toRat, neg_div, div_neg] using this (-f₁) (-f₂) (by grind) (by grind)
  have hb : 0 < f₂.bits := hpos
  have hb' : (0 : ℚ) < f₂.bits := by exact_mod_cast hb
  simp only [toRat, divFloor, Int.fdiv_eq_ediv, hb.le, true_or, ↓reduceIte, _root_.sub_zero]
  rw [div_div_div_cancel_right₀ (by positivity), div_le_div_iff₀ (by positivity) hb']
  norm_cast
  exact Int.ediv_mul_le _ hb.ne'

-- The `grind` attribute cannot select `(f₁ /↓ f₂).toRat` as the pattern.
grind_pattern toRat_divFloor_le => (f₁ /↓ f₂).toRat

/-- The exact quotient is less than `f₁ /↓ f₂ + 1 / 2 ^ n`. -/
theorem lt_toRat_divFloor_add (f₁ f₂ : Fraction n) (h₂ : f₂ ≠ 0) :
    f₁.toRat / f₂.toRat < (f₁ /↓ f₂).toRat + 1 / 2 ^ n := by
  wlog hpos : 0 < f₂ generalizing f₁ f₂
  · simpa [toRat, neg_div, div_neg] using this (-f₁) (-f₂) (by grind) (by grind)
  have hb : 0 < f₂.bits := hpos
  have hb' : (0 : ℚ) < f₂.bits := by exact_mod_cast hb
  simp only [toRat, divFloor, Int.fdiv_eq_ediv, hb.le, true_or, ↓reduceIte, _root_.sub_zero]
  rw [div_div_div_cancel_right₀ (by positivity), ← add_div,
    div_lt_div_iff₀ hb' (by positivity)]
  norm_cast
  exact Int.lt_ediv_add_one_mul_self _ hb

-- The `grind` attribute cannot select `(f₁ /↓ f₂).toRat` as the pattern.
grind_pattern lt_toRat_divFloor_add => (f₁ /↓ f₂).toRat

/-- `f₁ /↑ f₂` is at least the exact quotient. -/
theorem le_toRat_divCeil (f₁ f₂ : Fraction n) (h₂ : f₂ ≠ 0) :
    f₁.toRat / f₂.toRat ≤ (f₁ /↑ f₂).toRat := by
  wlog hpos : 0 < f₂ generalizing f₁ f₂
  · simpa [toRat, neg_div, div_neg] using this (-f₁) (-f₂) (by grind) (by grind)
  have hb : 0 < f₂.bits := hpos
  have hb' : (0 : ℚ) < f₂.bits := by exact_mod_cast hb
  rw [divCeil_eq]
  simp only [toRat, Int.fdiv_eq_ediv, hb.le, true_or, ↓reduceIte, _root_.sub_zero]
  rw [div_div_div_cancel_right₀ (by positivity), div_le_div_iff₀ hb' (by positivity)]
  norm_cast
  linarith [Int.ediv_mul_le (-(f₁.bits * ((2 ^ n : ℕ) : ℤ))) hb.ne']

-- The `grind` attribute cannot select `(f₁ /↑ f₂).toRat` as the pattern.
grind_pattern le_toRat_divCeil => (f₁ /↑ f₂).toRat

/-- `f₁ /↑ f₂ - 1 / 2 ^ n` is less than the exact quotient. -/
theorem toRat_divCeil_sub_lt (f₁ f₂ : Fraction n) (h₂ : f₂ ≠ 0) :
    (f₁ /↑ f₂).toRat - 1 / 2 ^ n < f₁.toRat / f₂.toRat := by
  wlog hpos : 0 < f₂ generalizing f₁ f₂
  · simpa [toRat, neg_div, div_neg] using this (-f₁) (-f₂) (by grind) (by grind)
  have hb : 0 < f₂.bits := hpos
  have hb' : (0 : ℚ) < f₂.bits := by exact_mod_cast hb
  rw [divCeil_eq]
  simp only [toRat, Int.fdiv_eq_ediv, hb.le, true_or, ↓reduceIte, _root_.sub_zero]
  rw [div_div_div_cancel_right₀ (by positivity), ← sub_div,
    div_lt_div_iff₀ (by positivity) hb']
  norm_cast
  linarith [Int.lt_ediv_add_one_mul_self (-(f₁.bits * ((2 ^ n : ℕ) : ℤ))) hb]

-- The `grind` attribute cannot select `(f₁ /↑ f₂).toRat` as the pattern.
grind_pattern toRat_divCeil_sub_lt => (f₁ /↑ f₂).toRat

/-- The absolute value of `f₁ /₀ f₂` is at most the absolute value of the exact quotient. -/
theorem abs_toRat_divTrunc_le (f₁ f₂ : Fraction n) (h₂ : f₂ ≠ 0) :
    |(f₁ /₀ f₂).toRat| ≤ |f₁.toRat / f₂.toRat| := by
  wlog hpos : 0 < f₂ generalizing f₁ f₂
  · simpa [toRat, neg_div, div_neg] using this (-f₁) (-f₂) (by grind) (by grind)
  have hb : 0 < f₂.bits := hpos
  rcases le_or_gt 0 f₁.bits with h | h
  · have := (toRat_nonneg (f₁ /↓ f₂)).mpr (Int.fdiv_nonneg (mul_nonneg h (by positivity)) hb.le)
    grind [mul_nonneg h hb.le]
  · rw [divTrunc_eq_divCeil_of_neg (mul_neg_of_neg_of_pos h hb)]
    apply abs_le_abs_of_nonpos _ (le_toRat_divCeil f₁ f₂ h₂)
    rw [divCeil_eq]
    unfold toRat
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have := Int.fdiv_nonneg (a := -(f₁.bits * 2 ^ n)) (b := f₂.bits)
      (neg_nonneg.mpr (mul_nonpos_iff.mpr (Or.inr ⟨h.le, by positivity⟩))) hb.le
    exact_mod_cast neg_nonpos.mpr this

/-- `f₁ /₀ f₂` differs from the exact quotient by less than `1 / 2 ^ n`. -/
theorem abs_sub_toRat_divTrunc_lt (f₁ f₂ : Fraction n) (h₂ : f₂ ≠ 0) :
    |f₁.toRat / f₂.toRat - (f₁ /₀ f₂).toRat| < 1 / 2 ^ n := by
  grind


end Fraction
end Solanalib
