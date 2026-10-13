import OzakiTCTests.LongFP64
import OzakiTCTests.Signed
import OzakiTC.Ozaki2Bounded
import OzakiTC.ADPBounded
import OzakiTC.ADPIntPipeline

/-! # Ozaki-II and ADP with bounded registers, and their signed zeros

* `tcOzaki2CRB`: correctly rounded FP64 by Ozaki-II on V100 fp16 blocks with split-K, the rounding
  test on integer enclosures and the bounded exact fallback, returns the exact-fraction oracle's
  words on both binary64 cases (twelve moduli, `P = 69`), and with no configuration at all (every
  entry through the bounded exact fallback).
* `adpCRB`: ADP-style correctly rounded slicing with integer rounding tests and the bounded exact
  fallback on the split-K INT8 matrix multiplier returns the oracle's words on both cases, and the
  correctly rounded `2^-1074` on the subnormal counterexample.
* **How often the integer rounding tests decide an entry**, against the rational tests of
  `OzakiTCTests.Correct`. The integer bound `K` charges each dropped entry a whole unit where the
  rational bound uses the largest actual loss:
  - Ozaki-II, binary64, twelve moduli: `16` of `16` on `narrow64` (rational `16`), `9` on `wide64`
    (rational `10`);
  - Ozaki-II, binary32 on the Z3 cases: Z3 moduli `0` and `0` (rational `0`, `0`); five moduli `10`
    and `6` (rational `12`, `9`); six moduli `16` and `16` (rational `16`, `16`);
  - ADP: the same counts as the rational test at every configuration tested
    (`(8, 56)`: `16`; `(11, 81)`: `16`; `(8, 62)`: `5`; `(9, 70)`: `11`).
* **Signed zeros** for Ozaki-II and ADP, rational and bounded: products that are all `−0` give
  `−0`, exact cancellation `+0`, an underflowing negative product `−0`.
* **The integer pipelines** `tcOzaki2CRZ` and `adpCRZ`, with inputs as integer pairs `(m, e)` decoded
  from the binary64 words by bit operations, return the oracle's words on both cases; the decoded
  pairs are the decoded values. -/

open TensorCore Ozaki Ozaki.TC OzakiTCTests.Correct OzakiTCTests.LongFP64

namespace OzakiTCTests.BoundedSchemes

/-! ## End to end against the oracle -/

example : (do
    let A ← decode64 A_narrow64; let B ← decode64 B_narrow64
    let C ← A.mapM fun x => (transpose B).mapM fun y =>
      tcOzaki2CRB v100F16F32 [(basis12, 69)] 11 175 x y
    encode64 C) = some C_narrow64 := by
  decide +kernel

example : (do
    let A ← decode64 A_wide64; let B ← decode64 B_wide64
    let C ← A.mapM fun x => (transpose B).mapM fun y =>
      tcOzaki2CRB v100F16F32 [(basis12, 69)] 11 175 x y
    encode64 C) = some C_wide64 := by
  decide +kernel

/-- No configuration: every entry through the bounded exact fallback. -/
example : (do
    let A ← decode64 A_wide64; let B ← decode64 B_wide64
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki2CRB v100F16F32 [] 11 175 x y
    encode64 C) = some C_wide64 := by
  decide +kernel

example : (do
    let A ← decode64 A_narrow64; let B ← decode64 B_narrow64
    let C ← A.mapM fun x => (transpose B).mapM fun y => adpCRB cfgsADP 300 x y
    encode64 C) = some C_narrow64 := by
  decide +kernel

example : (do
    let A ← decode64 A_wide64; let B ← decode64 B_wide64
    let C ← A.mapM fun x => (transpose B).mapM fun y => adpCRB cfgsADP 300 x y
    encode64 C) = some C_wide64 := by
  decide +kernel

/-- The subnormal counterexample: the integer rounding test with `8` slices of width `56` does not
decide it, the bounded exact fallback on the INT8 matrix multiplier returns the correctly rounded
`2^-1074`. -/
example : enclosureTestB 53 (-1022) 1023 (adpEnclosureB 8 56 subX subY) = none ∧
    adpCRB [(8, 56)] 300 subX subY = some ((2 : ℚ) ^ (-1074 : ℤ)) := by
  decide +kernel

/-! ## How often the integer rounding tests decide an entry -/

/-- Whether the rounding test succeeds on Ozaki-II's integer enclosure of one configuration
(binary64). -/
def succeeds2B (B : CRTBasis) (P : ℕ) (x y : List ℚ) : Bool :=
  ((ozaki2EnclosureB (tcSplitK v100F16F32 11) B P x y).bind (enclosureTestB 53 (-1022) 1023)).isSome

/-- The same with the rational enclosure. -/
def succeeds2R (B : CRTBasis) (P : ℕ) (x y : List ℚ) : Bool :=
  ((ozaki2Enclosure (tcSplitK v100F16F32 11) B P x y).bind fun p =>
    roundEnclosure rne64 p.1 p.2).isSome

/-- Whether the rounding test succeeds on ADP's integer enclosure. -/
def succeedsAB (s W : ℕ) (x y : List ℚ) : Bool := (enclosureTestB 53 (-1022) 1023 (adpEnclosureB s W x y)).isSome

def count64 (f : List ℚ → List ℚ → Bool) (A Bm : List (List (BitVec 64))) : Option ℕ := do
  let A ← decode64 A; let Bm ← decode64 Bm
  pure ((A.flatMap fun x => (transpose Bm).map fun y => f x y).count true)

example : count64 (succeeds2B basis12 69) A_narrow64 B_narrow64 = some 16 ∧
    count64 (succeeds2R basis12 69) A_narrow64 B_narrow64 = some 16 := by decide +kernel
example : count64 (succeeds2B basis12 69) A_wide64 B_wide64 = some 9 ∧
    count64 (succeeds2R basis12 69) A_wide64 B_wide64 = some 10 := by decide +kernel

/-- Ozaki-II's integer enclosure in binary32 on V100 blocks. -/
def succeeds2B32 (B : CRTBasis) (P : ℕ) (x y : List ℚ) : Bool :=
  ((ozaki2EnclosureB (tcMultiplier v100F16F32) B P x y).bind (enclosureTestB 24 (-126) 127)).isSome

def count32 (f : List ℚ → List ℚ → Bool) (A Bm : List (List F32)) : Option ℕ := do
  let A ← decodeMatrix A; let Bm ← decodeMatrix Bm
  pure ((A.flatMap fun x => (transpose Bm).map fun y => f x y).count true)

example : count32 (succeeds2B32 z3Basis 22) A_narrow B_narrow = some 0 ∧
    count32 (succeeds2B32 z3Basis 22) A_wide B_wide = some 0 := by decide +kernel
example : count32 (succeeds2B32 basis5 28) A_narrow B_narrow = some 10 ∧
    count32 (succeeds2B32 basis5 28) A_wide B_wide = some 6 := by decide +kernel
example : count32 (succeeds2B32 basis6 34) A_narrow B_narrow = some 16 ∧
    count32 (succeeds2B32 basis6 34) A_wide B_wide = some 16 := by decide +kernel

example : count64 (succeedsAB 8 56) A_narrow64 B_narrow64 = some 16 := by decide +kernel
example : count64 (succeedsAB 11 81) A_wide64 B_wide64 = some 16 := by decide +kernel
example : count64 (succeedsAB 8 62) A_wide64 B_wide64 = some 5 ∧
    count64 (succeedsAB 9 70) A_wide64 B_wide64 = some 11 := by decide +kernel

/-! ## Signed zeros -/

open OzakiTCTests.Signed in
example : tcOzaki2CRDS v100F16F32 [(basis12, 69)] 11 175 negZeros.1 negZeros.2 = some ⟨0, true⟩ ∧
    tcOzaki2CRBS v100F16F32 [(basis12, 69)] 11 175 negZeros.1 negZeros.2 = some ⟨0, true⟩ ∧
    adpCRES cfgsADP 300 negZeros.1 negZeros.2 = some ⟨0, true⟩ ∧
    adpCRBS cfgsADP 300 negZeros.1 negZeros.2 = some ⟨0, true⟩ := by
  decide +kernel

open OzakiTCTests.Signed in
example : tcOzaki2CRDS v100F16F32 [(basis12, 69)] 11 175 cancels.1 cancels.2 = some ⟨0, false⟩ ∧
    tcOzaki2CRBS v100F16F32 [(basis12, 69)] 11 175 cancels.1 cancels.2 = some ⟨0, false⟩ ∧
    adpCRES cfgsADP 300 cancels.1 cancels.2 = some ⟨0, false⟩ ∧
    adpCRBS cfgsADP 300 cancels.1 cancels.2 = some ⟨0, false⟩ := by
  decide +kernel

open OzakiTCTests.Signed in
example : tcOzaki2CRDS v100F16F32 [(basis12, 69)] 11 175 underflows.1 underflows.2 =
      some ⟨0, true⟩ ∧
    tcOzaki2CRBS v100F16F32 [(basis12, 69)] 11 175 underflows.1 underflows.2 = some ⟨0, true⟩ ∧
    adpCRES cfgsADP 300 underflows.1 underflows.2 = some ⟨0, true⟩ ∧
    adpCRBS cfgsADP 300 underflows.1 underflows.2 = some ⟨0, true⟩ := by
  decide +kernel

/-! ## The integer pipelines -/

/-- A binary64 word as an integer pair `(m, e)` worth `m 2^e`, by bit operations. -/
def pair64 (w : BitVec 64) : ℤ × ℤ :=
  let n : ℕ := w.toNat
  let e : ℕ := (n / 2 ^ 52) % 2 ^ 11
  let m : ℕ := n % 2 ^ 52
  let mag : ℤ := if e = 0 then (m : ℤ) else ((2 ^ 52 + m : ℕ) : ℤ)
  (if n / 2 ^ 63 = 1 then -mag else mag, if e = 0 then -1074 else (e : ℤ) - 1075)

def pairs (A : List (List (BitVec 64))) : List (List (ℤ × ℤ)) := A.map (·.map pair64)

/-- Columns of a matrix of pairs. -/
def transposeP : List (List (ℤ × ℤ)) → List (List (ℤ × ℤ))
  | [] => []
  | [r] => r.map fun a => [a]
  | r :: rs => List.zipWith List.cons r (transposeP rs)

example : decode64 A_narrow64 = some ((pairs A_narrow64).map entryVals) ∧
    decode64 B_narrow64 = some ((pairs B_narrow64).map entryVals) ∧
    decode64 A_wide64 = some ((pairs A_wide64).map entryVals) ∧
    decode64 B_wide64 = some ((pairs B_wide64).map entryVals) := by
  decide +kernel

example : (do
    let C ← (pairs A_narrow64).mapM fun x => (transposeP (pairs B_narrow64)).mapM fun y =>
      tcOzaki2CRZ v100F16F32 [(basis12, 69)] 11 175 x y
    encode64 C) = some C_narrow64 := by
  decide +kernel

example : (do
    let C ← (pairs A_wide64).mapM fun x => (transposeP (pairs B_wide64)).mapM fun y =>
      tcOzaki2CRZ v100F16F32 [(basis12, 69)] 11 175 x y
    encode64 C) = some C_wide64 := by
  decide +kernel

/-- No configuration: every entry through the exact fallback with integer slicing. -/
example : (do
    let C ← (pairs A_wide64).mapM fun x => (transposeP (pairs B_wide64)).mapM fun y =>
      tcOzaki2CRZ v100F16F32 [] 11 175 x y
    encode64 C) = some C_wide64 := by
  decide +kernel

example : (do
    let C ← (pairs A_narrow64).mapM fun x => (transposeP (pairs B_narrow64)).mapM fun y =>
      adpCRZ cfgsADP 300 x y
    encode64 C) = some C_narrow64 := by
  decide +kernel

example : (do
    let C ← (pairs A_wide64).mapM fun x => (transposeP (pairs B_wide64)).mapM fun y =>
      adpCRZ cfgsADP 300 x y
    encode64 C) = some C_wide64 := by
  decide +kernel

end OzakiTCTests.BoundedSchemes
