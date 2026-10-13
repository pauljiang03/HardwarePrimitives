import OzakiMCTests.LongFP64
import OzakiMC.SplitChoice

/-! # The cheapest CDNA 3 configuration on the oracle cases

Correctly rounded FP64 Ozaki-I on CDNA 3 fp16 with the configuration `OzakiMC.SplitChoice` picks:
`10`-bit slices in chunks of sixteen (two chained blocks of eight), five then six slices, then the
exact fallback at up to `191` slices. It returns the exact-fraction oracle's words on both binary64
cases. -/

open MatrixCore Ozaki Ozaki.MC OzakiMCTests.LongFP64

namespace OzakiMCTests.SplitChoice

/-- Correctly rounded FP64 with `10`-bit slices equals the oracle on both cases. -/
def agrees10 (P : Model) : Bool :=
  [(A_narrow64, B_narrow64, C_narrow64), (A_wide64, B_wide64, C_wide64)].all fun (A, B, C) =>
    let Aq := A.map (·.map val64)
    let Bq := transpose (B.map (·.map val64))
    (Aq.zip (C.map (·.map val64))).all fun (x, crow) =>
      (Bq.zip crow).all fun (y, c) => mcOzaki1CRD P 10 [5, 6] 191 x y == some c

example : agrees10 cdna3F16 = true := by decide +kernel

end OzakiMCTests.SplitChoice
