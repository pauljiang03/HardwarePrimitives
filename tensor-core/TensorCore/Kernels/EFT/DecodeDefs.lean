import TensorCore.Kernels.EFT.WordDefs
import TensorCore.Kernels.EFT.SplitDefs
import TensorCore.TC.CanonicalFormatDefs

/-! Bounded input decoding and exact products. -/

namespace TensorCore.EFMachine

inductive InputKind where
  | fp16 | bf16 | tf32
  deriving Repr, DecidableEq

def InputKind.format : InputKind → Format
  | .fp16 => TensorCore.fp16
  | .bf16 => TensorCore.bf16
  | .tf32 => TensorCore.tf19

structure Factor where
  negative : Bool
  magnitude : BitVec 11
  /-- Exponent biased by 256, with zero's conventional exponent 0. -/
  biasedExp : Grid
  mantissaBits : Grid
  deriving Repr, DecidableEq

/-- Finite IEEE-style input decoding, including subnormal mantissas and zero. -/
def decodeFactor (kind : InputKind) (bits : F32) : Option Factor :=
  let f := kind.format
  let e := ((bits >>> f.mantissaBits) &&& (((1 : F32) <<< f.exponentBits) - 1)).setWidth 10
  let m := (bits &&& (((1 : F32) <<< f.mantissaBits) - 1)).setWidth 11
  let negative := (bits >>> (f.mantissaBits + f.exponentBits)) != 0
  let bias : Grid := match kind with | .fp16 => 241 | _ => 129
  let top : Grid := match kind with | .fp16 => 31 | _ => 255
  let mant : Grid := match kind with | .bf16 => 7 | _ => 10
  if e == top then none
  else if e == 0 then
    if m == 0 then some ⟨negative, 0, 256, 0⟩
    else some ⟨negative, m, bias + 1, mant⟩
  else some ⟨negative, ((1 : BitVec 11) <<< f.mantissaBits) + m, e + bias, mant⟩

structure Term where
  word : Word
  /-- Exponent biased by 512. -/
  biasedExp : Grid
  /-- Coefficient grid, biased by 272; this may differ for equal real products. -/
  support : Grid
  deriving Repr, DecidableEq

/-- Exact 11-by-11-bit product, shifted onto the common dyadic grid. -/
def product (a b : Factor) : Term :=
  let biasedExp := a.biasedExp + b.biasedExp
  let grid := biasedExp - (a.mantissaBits + b.mantissaBits) - 240
  let m := (multiplySignificands a.magnitude b.magnitude).zeroExtend 576 <<< grid
  ⟨⟨a.negative != b.negative, m⟩, biasedExp, grid⟩

structure Accumulator where
  negative : Bool
  magnitude : BitVec 24
  biasedExp : Grid
  mantissaBits : Grid
  deriving Repr, DecidableEq

def decode32Fields (bits : F32) : Option Accumulator :=
  let e := ((bits >>> 23).setWidth 8).zeroExtend 10
  let m := (bits &&& 0x007fffff).setWidth 24
  let negative := bits.msb
  if e == 255 then none
  else if e == 0 then
    if m == 0 then some ⟨negative, 0, 256, 0⟩
    else some ⟨negative, m, 130, 23⟩
  else some ⟨negative, 8388608 + m, e + 129, 23⟩

def Accumulator.term (a : Accumulator) : Term :=
  let grid := a.biasedExp + 16 - a.mantissaBits
  ⟨⟨a.negative, a.magnitude.zeroExtend 576 <<< grid⟩, a.biasedExp + 256, grid⟩

/-- FP32 decoding directly into the common grid, without a rational conversion. -/
def decode32Term (bits : F32) : Option Term := (decode32Fields bits).map Accumulator.term

def decode32Word (bits : F32) : Option Word := (decode32Term bits).map Term.word

inductive Variant where
  | v100F16 | ampereF16 | hopperF16 | ampereBF16 | hopperBF16
  | ampereTF32 | hopperTF32Wmma | hopperTF32Mma
  deriving Repr, DecidableEq

def Variant.kind : Variant → InputKind
  | .v100F16 | .ampereF16 | .hopperF16 => .fp16
  | .ampereBF16 | .hopperBF16 => .bf16
  | .ampereTF32 | .hopperTF32Wmma | .hopperTF32Mma => .tf32

def Variant.model : Variant → Model
  | .v100F16 => v100F16F32
  | .ampereF16 => ampereF16F32
  | .hopperF16 => hopperF16F32
  | .ampereBF16 => a100BF16F32
  | .hopperBF16 => hopperBF16F32
  | .ampereTF32 => a100TF32F32
  | .hopperTF32Wmma => hopperTF32WmmaF32
  | .hopperTF32Mma => hopperTF32MmaF32

def Variant.alignmentBits : Variant → Grid
  | .v100F16 => 23
  | .ampereF16 | .ampereBF16 | .ampereTF32 => 24
  | _ => 25

def Variant.eAlignMin : Variant → Grid
  | .v100F16 => 0
  | .ampereF16 | .ampereBF16 | .ampereTF32 => 380
  | _ => 379

def decodeProduct (variant : Variant) (pair : variant.model.Word × variant.model.Word) : Option Term := do
  let a ← decodeFactor variant.kind (pair.1.zeroExtend 32)
  let b ← decodeFactor variant.kind (pair.2.zeroExtend 32)
  return product a b

/-- Finite-range FP32 scalar addition using the same bounded integer converter. -/
def add32 (a b : F32) : Option F32 := do
  let x ← decode32Word a
  let y ← decode32Word b
  let s ← x.add y
  s.round32

end TensorCore.EFMachine
