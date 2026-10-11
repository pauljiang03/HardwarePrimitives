import OzakiTC.Exactness
import OzakiTC.Engine
import OzakiTC.Profiles
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

/-! # The Ozaki schemes on the NVIDIA Tensor Core model

The engine of the `Ozaki` library built from the block model of `TensorCore`, its exactness on
every supported GPU path, the binary32 σ-trick, Ozaki-I and Ozaki-II with binary32
recombination, and Ozaki-I on an INT8 engine modelled by the fixed-width register (ADP). Every
working-precision rounding is IEEE's round to nearest even (`round32Value`, `fp64Round`);
TensorCore's own rounding computes the same value up to the largest finite value. -/
