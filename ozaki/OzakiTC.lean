import OzakiTC.Exactness
import OzakiTC.MatrixMultiplier
import OzakiTC.Models
import OzakiTC.Rounding
import OzakiTC.Split32
import OzakiTC.Schemes
import OzakiTC.Limits
import OzakiTC.Int8
import OzakiTC.ADP
import OzakiTC.Success
import OzakiTC.Scaling
import OzakiTC.Checks
import OzakiTC.Correct
import OzakiTC.Native
import OzakiTC.LongDot
import OzakiTC.TwoPass
import OzakiTC.ADPFix
import OzakiTC.IEEE
import OzakiTC.Signed
import OzakiTC.Bounded
import OzakiTC.Int8Semantics
import OzakiTC.ADPLabels
import OzakiTC.IEEESchemes
import OzakiTC.ADPIEEE
import OzakiTC.Cancellation
import OzakiTC.SplitChoice
import OzakiTC.ADPBounded
import OzakiTC.ADPChecked
import OzakiTC.ADPIntJ
import OzakiTC.ADPIntPipeline
import OzakiTC.ADPZeroPolicy
import OzakiTC.IEEEBounded
import OzakiTC.Ozaki2Bounded
import OzakiTC.SharpBounds
import OzakiTC.ZeroCheck
import OzakiTC.ADPCheckedSigned
import OzakiTC.ADPChoice
import OzakiTC.ADPZeroPolicyGeneral
import OzakiTC.CheckedTight
import OzakiTC.IEEEWords
import OzakiTC.Int8Checked
import OzakiTC.Ozaki2Choice
import OzakiTC.ADPZeroPolicyShapes
import OzakiTC.CRRules
import OzakiTC.Ozaki2ChoiceCR
import OzakiTC.ADPZeroPolicyGap
import OzakiTC.ADPZeroPolicyIff

/-! # The Ozaki schemes on the NVIDIA Tensor Core model

The matrix multiplier of the `Ozaki` library built from the block model of `TensorCore`, its
exactness on every supported GPU variant, the binary32 σ-trick, Ozaki-I and Ozaki-II with binary32
recombination, and Ozaki-I on an INT8 matrix multiplier modeled by the fixed-width register (ADP).
Every working-precision rounding is IEEE's round to nearest even (`round32Value`, `fp64Round`);
TensorCore's own rounding computes the same value up to the largest finite value. -/
