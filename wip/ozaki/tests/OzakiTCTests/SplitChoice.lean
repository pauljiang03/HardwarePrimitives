import OzakiTCTests.Correct
import OzakiTC.SplitChoice

/-! # The cheapest configurations on the oracle cases

The binary64 cases of [`data/correct-reference.json`](../../data/correct-reference.json) through
correctly rounded FP64 Ozaki-I with the configuration `OzakiTC.SplitChoice` picks for the H100 and
A100 fp16 variants: `10`-bit slices, split-K in chunks of sixteen (one full H100 block FMA, two
chained A100 block FMAs), five then six slices, then the exact fallback at up to `191` slices. Each
returns the exact-fraction oracle's words. -/

open TensorCore Ozaki Ozaki.TC OzakiTCTests.Correct

namespace OzakiTCTests.SplitChoice

example : (do
    let A ← decode64 A_narrow64; let B ← decode64 B_narrow64
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRD hopperF16F32 10 [5, 6] 191 x y
    encode64 C) = some C_narrow64 := by
  decide +kernel

example : (do
    let A ← decode64 A_wide64; let B ← decode64 B_wide64
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRD hopperF16F32 10 [5, 6] 191 x y
    encode64 C) = some C_wide64 := by
  decide +kernel

example : (do
    let A ← decode64 A_narrow64; let B ← decode64 B_narrow64
    let C ← A.mapM fun x => (transpose B).mapM fun y => tcOzaki1CRD ampereF16F32 10 [5, 6] 191 x y
    encode64 C) = some C_narrow64 := by
  decide +kernel

end OzakiTCTests.SplitChoice
