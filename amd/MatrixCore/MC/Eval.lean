import MatrixCore.MC.Stages

/-! # Evaluating one block

`evalBlock` computes `d = fl{S_acc}` for finite inputs. Inputs or results outside the finite
domain are reported as errors here; `MatrixCore.MC.Special` gives the infinities and NaNs that
the hardware returns for them. -/

namespace MatrixCore

inductive ModelError where
  /-- `a` or `b` does not have `N_FMA` entries. -/
  | wrongLength
  /-- An operand is an infinity or NaN. -/
  | nonfiniteInput
  /-- A product reached `2^128` on a profile that detects product overflow (CDNA 3). -/
  | productOverflow
  /-- An intermediate `fl{·}` overflowed (CDNA 2 product conversion or pairwise sum). -/
  | intermediateOverflow
  /-- The final `fl{S_acc}` overflowed. -/
  | outputOverflow
  deriving Repr, DecidableEq

/-- Some product has `|p_ℓ| ≥ 2^128`. -/
def Prepared.productOverflows (x : Prepared) : Bool :=
  x.p.any fun p => decide (pow2 128 ≤ absQ p.value)

/-- `S_acc`, the value converted to binary32 by the final `fl{·}`. -/
def accumulate (P : Model) (x : Prepared) : Except ModelError ℚ :=
  if P.productOverflow && x.productOverflows then .error .productOverflow
  else
    match P.accumulation with
    | .correctRounding => .ok x.exact
    | .pairWiseSum =>
      match pairwiseSum P x with
      | none => .error .intermediateOverflow
      | some s => .ok s
    | .globalAlignment | .oddEvenGrouping => .ok (alignedAccumulation P x)

/-- One evaluated block. -/
structure BlockTrace (P : Model) where
  prepared : Prepared
  /-- `S_acc`. -/
  sAcc : ℚ
  /-- `d = fl{S_acc}`. -/
  d : F32
  deriving Repr, DecidableEq

/-- One block of `N_FMA` products: `d = fl{S_acc}` with RNE. -/
def evalBlock {P : Model} (x : BlockInput P) : Except ModelError (BlockTrace P) :=
  if x.a.length ≠ P.nfma ∨ x.b.length ≠ P.nfma then .error .wrongLength
  else
    match prepare x with
    | none => .error .nonfiniteInput
    | some px =>
      match accumulate P px with
      | .error e => .error e
      | .ok s =>
        match fl32 (!P.subnormals) s with
        | none => .error .outputOverflow
        | some d => .ok ⟨px, s, d⟩

/-- Output word of one block. -/
def blockBits {P : Model} (x : BlockInput P) : Except ModelError F32 :=
  (evalBlock x).map BlockTrace.d

end MatrixCore
