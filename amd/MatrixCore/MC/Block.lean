import MatrixCore.MC.Models

/-! # One block: inputs and products

A block is one multi-term addition of the paper: `N_FMA` products `p_ℓ = a_ℓ b_ℓ` and the
accumulator input `c`. -/

namespace MatrixCore

/-- Encoded operands of one block: the vectors `a`, `b` and the binary32 scalar `c`. -/
structure BlockInput (P : Model) where
  a : List P.a.Word
  b : List P.b.Word
  c : F32
  deriving Repr, DecidableEq

/-- Decoded finite operands. -/
structure Prepared where
  a : List Unpacked
  b : List Unpacked
  c : Unpacked
  deriving Repr, DecidableEq

/-- Decode finite operands; `none` if any word is an infinity or NaN. -/
def prepare {P : Model} (x : BlockInput P) : Option Prepared := do
  let a ← x.a.mapM fun w => (P.a.read w).toFinite
  let b ← x.b.mapM fun w => (P.b.read w).toFinite
  let c ← (binary32.decode x.c).toFinite
  return ⟨a, b, c⟩

namespace Prepared

/-- Full-precision, denormalised products `p_ℓ = a_ℓ b_ℓ`. -/
def p (x : Prepared) : List Unpacked := List.zipWith Unpacked.mul x.a x.b

/-- The exact value of Eq. (1), `Σ p_ℓ + c`. -/
def exact (x : Prepared) : ℚ := sumQ (x.p.map Unpacked.value) + x.c.value

/-- Inputs with subnormals flushed to zero (CDNA 2). -/
def flushed (x : Prepared) : Prepared := ⟨x.a.map Unpacked.flush, x.b.map Unpacked.flush, x.c.flush⟩

end Prepared

theorem Prepared.p_length (x : Prepared) : x.p.length = min x.a.length x.b.length := by
  simp [Prepared.p]

/-! ## Exponents -/

/-- One step of `e_max`: zero products are skipped. -/
def maxExpStep (acc : Option ℤ) (p : Unpacked) : Option ℤ :=
  if p.m = 0 then acc else some (match acc with | none => p.e | some v => max v p.e)

/-- `e_max`: the largest exponent of the nonzero products; `none` when all are zero. Zero
products do not take part in alignment. -/
def maxExp (ps : List Unpacked) : Option ℤ := ps.foldl maxExpStep none

/-- Larger of two optional exponents, with `none` as `−∞`. -/
def joinExp : Option ℤ → Option ℤ → Option ℤ
  | none, e => e
  | e, none => e
  | some a, some b => some (max a b)

/-- `e_c`: the exponent of `c` (`−126` for subnormal `c`), or `e_{c=0}` when `c = 0`. -/
def cExp (P : Model) (c : Unpacked) : Option ℤ := if c.m = 0 then P.cZeroExp else some c.e

/-- Products at odd positions `p₁, p₃, …` (1-based). -/
def oddIndexed : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: xs => x :: oddIndexed xs

/-- Products at even positions `p₂, p₄, …` (1-based). -/
def evenIndexed : List α → List α
  | [] => []
  | [_] => []
  | _ :: y :: xs => y :: evenIndexed xs

end MatrixCore
