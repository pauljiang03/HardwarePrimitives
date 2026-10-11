import OzakiTCTests.Correct
import OzakiTC.Ozaki2Choice
import OzakiTC.ADPChoice

/-! # The chosen Ozaki-II and ADP configurations on the oracle cases

The cheapest configurations of `OzakiTC.Ozaki2Choice` and `OzakiTC.ADPChoice` return the
exact-fraction oracle's words on the first row of the binary64 case `narrow64`
(`data/correct-reference.json`): correctly rounded FP64 by Ozaki-II on H100 fp16 with `12` moduli at
most `2048` and `10`-bit residues, and ADP's slicing with `7` remapped slices of a `54`-bit fixed
point on the INT8 engine. -/

open TensorCore Ozaki Ozaki.TC OzakiTCTests.Correct

namespace OzakiTCTests.Ozaki2Choice

/-- Correctly rounded FP64 by Ozaki-II on H100 fp16 with the cheapest configuration. -/
example : (do
    let A ← decode64 A_narrow64; let B ← decode64 B_narrow64
    let x ← A.head?
    let row ← (transpose B).mapM fun y => tcOzaki2CRD hopperF16F32 [(moduliBasis 10 12, 55)] 10 191 x y
    encode64 [row]) = some (C_narrow64.take 1) := by
  decide +kernel

/-- ADP's slicing at `ESC = 0`, correctly rounded, on the INT8 engine. -/
example : (do
    let A ← decode64 A_narrow64; let B ← decode64 B_narrow64
    let x ← A.head?
    let row ← (transpose B).mapM fun y => adpCRE [(7, 54)] 300 x y
    encode64 [row]) = some (C_narrow64.take 1) := by
  decide +kernel

end OzakiTCTests.Ozaki2Choice
