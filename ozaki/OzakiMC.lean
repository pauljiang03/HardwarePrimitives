import OzakiMC.Exactness
import OzakiMC.MatrixMultiplier
import OzakiMC.Models
import OzakiMC.Rounding
import OzakiMC.Schemes
import OzakiMC.Limits
import OzakiMC.Success
import OzakiMC.Scaling
import OzakiMC.Correct
import OzakiMC.Native
import OzakiMC.LongDot
import OzakiMC.IEEE
import OzakiMC.Signed
import OzakiMC.Bounded
import OzakiMC.IEEESchemes
import OzakiMC.Cancellation
import OzakiMC.SplitChoice
import OzakiMC.IEEEBounded
import OzakiMC.Ozaki2Bounded
import OzakiMC.Ozaki2Checked
import OzakiMC.Ozaki2IntJ
import OzakiMC.SharpBounds
import OzakiMC.ZeroCheck
import OzakiMC.CheckedTight
import OzakiMC.Ozaki2Choice
import OzakiMC.TwoPass
import OzakiMC.CRRules
import OzakiMC.IEEEWords

/-! # The Ozaki schemes on the AMD matrix-core model

The matrix multiplier of the `Ozaki` library built from the block model of `MatrixCore`, its
exactness on the SFMA, CDNA 1, CDNA 2 and CDNA 3 fp16, bf16 and XF32 variants, and Ozaki-I and
Ozaki-II with binary32 recombination. -/
