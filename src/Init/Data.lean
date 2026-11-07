/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Data.Nat
public import Init.Data.Bool
public import Init.Data.BitVec
public import Init.Data.Cast
public import Init.Data.Char
public import Init.Data.String
public import Init.Data.List
public import Init.Data.Int
public import Init.Data.Array
public import Init.Data.Array.Subarray.Split
public import Init.Data.ByteArray
public import Init.Data.FloatArray
public import Init.Data.Fin
public import Init.Data.UInt
public import Init.Data.SInt
public import Init.Data.Float
public import Init.Data.Option
public import Init.Data.Ord
public import Init.Data.Random
public import Init.Data.ToString
public import Init.Data.Range
public import Init.Data.Hashable
public import Init.Data.LawfulHashable
public import Init.Data.OfScientific
public import Init.Data.Format
public import Init.Data.Stream
public import Init.Data.Prod
public import Init.Data.AC
public import Init.Data.Queue
public import Init.Data.Sum
public import Init.Data.BEq
public import Init.Data.Subtype
public import Init.Data.Erased
public import Init.Data.ULift
public import Init.Data.PLift
public import Init.Data.Zero
public import Init.Data.NeZero
public import Init.Data.Function
public import Init.Data.RArray
public import Init.Data.Vector
public import Init.Data.Iterators
public import Init.Data.Range.Polymorphic
public import Init.Data.Slice
public import Init.Data.Order
public import Init.Data.Rat
public import Init.Data.Dyadic

/-- Compiled implementation of the `Int` hash instance. Reducing the magnitude to
64 bits before doubling preserves the original result modulo `2^64`. -/
@[expose, macro_inline, instance_reducible] public def Hashable.intWordImpl : Hashable Int where
  hash x :=
    let v := 2 * UInt64.ofNat x.natAbs
    if x < 0 then v - 1 else v

@[csimp] public theorem instHashableInt_eq_intWordImpl : instHashableInt = Hashable.intWordImpl := by
  apply congrArg (@Hashable.mk Int)
  funext x
  cases x with
  | ofNat n =>
    change UInt64.ofNat (2 * n) = if Int.ofNat n < 0 then _ else _
    have hn : ¬ Int.ofNat n < 0 := Int.not_lt_of_ge (Int.natCast_nonneg n)
    simp only [hn, ↓reduceIte]
    exact UInt64.ofNat_mul 2 n
  | negSucc n =>
    change UInt64.ofNat (2 * n + 1) = if Int.negSucc n < 0 then _ else _
    simp only [Int.negSucc_lt_zero, ↓reduceIte]
    change UInt64.ofNat (2 * n + 1) = 2 * UInt64.ofNat (n + 1) - 1
    rw [UInt64.ofNat_add, UInt64.ofNat_mul, UInt64.ofNat_add, UInt64.mul_add]
    change 2 * UInt64.ofNat n + 1 = 2 * UInt64.ofNat n + (1 + 1) - 1
    rw [← UInt64.add_assoc, UInt64.add_sub_cancel]
