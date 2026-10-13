import Ozaki.Basic
import Ozaki.Rounding
import Ozaki.Split
import Ozaki.Summation
import Ozaki.Ozaki1
import Ozaki.CRT
import Ozaki.Ozaki2
import Ozaki.Parameters
import Ozaki.ADP
import Ozaki.Native
import Ozaki.ADPError
import Ozaki.Success
import Ozaki.Checks
import Ozaki.Correct
import Ozaki.SplitK
import Ozaki.Width
import Ozaki.Binary
import Ozaki.Exact64
import Ozaki.TruncatedSum
import Ozaki.SignedZero
import Ozaki.SliceInt
import Ozaki.Bounded
import Ozaki.SignOracle
import Ozaki.BoundedOzaki
import Ozaki.ADPEncodings
import Ozaki.IEEEValue
import Ozaki.IEEEDot
import Ozaki.SliceRule
import Ozaki.BoundedChecked
import Ozaki.BoundedChecked2
import Ozaki.BoundedInt
import Ozaki.BoundedOzaki2
import Ozaki.BoundedOzaki2Int
import Ozaki.BoundedOzaki2J
import Ozaki.BoundedOzaki2Widths
import Ozaki.TopDownSummation
import Ozaki.IEEEInt
import Ozaki.SharpBounds
import Ozaki.ZeroCheck
import Ozaki.BoundedCheckedSigned
import Ozaki.CheckedMultipliers
import Ozaki.CheckedTight
import Ozaki.IEEEWords
import Ozaki.ModuliRule
import Ozaki.SharpBounds2
import Ozaki.AbdelfattahAcc
import Ozaki.Adaptive
import Ozaki.CRTValid
import Ozaki.CheckedSigned32
import Ozaki.SliceRuleCR
import Ozaki.UchinoCRT
import Ozaki.AbdelfattahCarry
import Ozaki.AbdelfattahCarry2
import Ozaki.UchinoConst
import Ozaki.UchinoScaling

/-! # The Ozaki schemes, independent of the hardware

Ozaki-I (error-free slicing) and Ozaki-II (modular integers and CRT reconstruction) for one
output entry `x · y` of `C = AB`, parameterised by a low-precision engine and a working-precision
rounding, and ADP's fixed-point slicing and exponent span capacity for INT8 engines. `OzakiTC`
instantiates the engine with the NVIDIA Tensor Core model of `TensorCore`, and `OzakiMC` with the
AMD matrix-core model of `MatrixCore`. -/
