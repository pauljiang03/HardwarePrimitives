import OzakiTC.ADPLabels

/-! # ADP with the Z3 model's unsafe zero policies

The Z3 model of ADP lets the coarsened ESC treat zeros in three ways (`ZERO_POLICY`): as exponent
`−∞` (the paper's, and `adp`'s), skipped in the block minimum, or with the subnormal exponent
`−1022`. The estimates alone are proved unsafe in `Ozaki.ADP` (`skipZeros_unsafe`, `field0_unsafe`,
and on the model's own inputs `zeros_case_caught`, `field0_case_caught`); the model stops a run with
an unsafe policy at its assertion `[X.4]` before it returns a result.

`adpPolicy cfg pol` is the whole routine with the policy as a parameter; with `−∞` it is `adp`
(`adpPolicy_negInf`). It shows what an unsafe policy computes when nothing stops it: the coarsened
ESC is below the exact one, the width `W = 53 + ESC + 1` too small, and the entry with the
dominant product loses bits in fixed point. On the inputs of
`tests/OzakiTCTests/ADPZeroPolicy.lean`, recorded from the model, Grade A (checked exactly by
`gradeA`) gives:

* the model's `zeros_case`: no wrong result. Skipping zeros lowers the matrix ESC from `10` to `3`,
  but the dominant product's factors have so few bits that the narrower fixed point still holds
  them;
* the model's `field0_case`: with field-0 zeros the estimate is so large that the speed heuristic
  sends the product to native FP64; **with zeros skipped the ESC is `0` and the routine returns `0`
  for the one nonzero entry**;
* two constructed inputs, a large entry beside a zero and a zero paired with `2^1000`: skipping
  zeros is off by about `2^-42` for a product near `3.5` on the first and returns `0` for a nonzero
  product on the second, and field-0 zeros return `0` on the second;
* the `−∞` policy meets Grade A on all four and returns the model's values. -/

open TensorCore

namespace Ozaki.ADP

/-- How the coarsened ESC treats zeros (the Z3 model's `ZERO_POLICY`). -/
inductive ZeroPolicy where
  | negInf
  | skip
  | field0
  deriving Repr, DecidableEq

/-- The coarsened estimate under a zero policy. -/
def coarseEstPolicy : ZeroPolicy → ℕ → List Exp → List Exp → Exp
  | .negInf => coarseEst
  | .skip => coarseEstSkip
  | .field0 => coarseEstField0

/-- The coarsened ESC of one dot product under a zero policy. -/
def escCoarsePolicy (pol : ZeroPolicy) (n : ℕ) (x y : List ℚ) : Option ℤ :=
  match maxE (expsOf x), maxE (expsOf y) with
  | some xp, some yq => (coarseEstPolicy pol n (expsOf x) (expsOf y)).map fun est => xp + yq - est
  | _, _ => some 0

theorem escCoarsePolicy_negInf : escCoarsePolicy .negInf = escCoarse := rfl

end Ozaki.ADP

namespace Ozaki.TC

/-- The matrix ESC under a zero policy. -/
def matrixEscPolicy (pol : ADP.ZeroPolicy) (n : ℕ) (A cols : List (List ℚ)) : Option ℤ :=
  (A.flatMap fun x => cols.map fun y => ADP.escCoarsePolicy pol n x y).foldl maxOpt (some 0)

/-- **ADP with a zero policy**: `adp` with the coarsened ESC computed under `pol`. -/
def adpPolicy (cfg : ADPConfig) (pol : ADP.ZeroPolicy) (A B : List (List (BitVec 64))) :
    ADPPath × Option (List (List ℚ)) :=
  match decodeMatrix64 A, decodeMatrix64 B with
  | some Aq, some Bq =>
    match matrixEscPolicy pol cfg.block Aq (transpose Bq) with
    | none => (.nativeSlow, nativeGemm64 Aq (transpose Bq))
    | some esc =>
      if slicesNeeded (adpWidth esc) * slicesNeeded (adpWidth esc) ≤ cfg.speedRatio then
        (.emulated, Aq.mapM fun x => (transpose Bq).mapM fun y =>
          emulEntry (adpWidth esc) (slicesNeeded (adpWidth esc)) x y)
      else (.nativeSlow, nativeGemm64 Aq (transpose Bq))
  | _, _ => (.nativeNonfinite, none)

/-- With zeros as `−∞` the routine is `adp`. -/
theorem adpPolicy_negInf (cfg : ADPConfig) (A B : List (List (BitVec 64))) :
    adpPolicy cfg .negInf A B = adp cfg A B := rfl

/-- The matrix ESC under the `−∞` policy is `adp`'s. -/
theorem matrixEscPolicy_negInf (n : ℕ) (A cols : List (List ℚ)) :
    matrixEscPolicy .negInf n A cols = matrixEsc n A cols := rfl

/-- Grade A for one entry, checked exactly: `|C − x · y| ≤ (4k + 1) 2^-53 Σ|xᵢyᵢ| + 2^-1075`. -/
def gradeAEntry (x y : List ℚ) (c : ℚ) : Bool :=
  decide (Rat.abs (c - dot x y) ≤
    (4 * x.length + 1) * 2 ^ (-53 : ℤ) * ((List.zipWith (· * ·) x y).map Rat.abs).sum +
      2 ^ (-1075 : ℤ))

/-- Grade A for every entry of `C = AB`, `A` by rows and `B` by rows. -/
def gradeA (A B C : List (List ℚ)) : Bool :=
  (A.zip C).all fun (x, crow) => ((transpose B).zip crow).all fun (y, c) => gradeAEntry x y c

end Ozaki.TC
