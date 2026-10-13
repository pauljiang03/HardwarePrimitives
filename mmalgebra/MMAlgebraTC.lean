import MMAlgebraTC.Block
import MMAlgebraTC.Chain
import MMAlgebraTC.Completeness
import MMAlgebraTC.NegZero
import MMAlgebraTC.ChainComplete
import MMAlgebraTC.TermComplete
import MMAlgebraTC.ChainVariants
import MMAlgebraTC.Contract
import MMAlgebraTC.TermVariants
import MMAlgebraTC.OneRounding
import MMAlgebraTC.Exact
import MMAlgebraTC.ScheduleFreeExact
import MMAlgebraTC.Pinned
import MMAlgebraTC.Anchored
import MMAlgebraTC.PinnedDemo
import MMAlgebraTC.SubnormalGamma
import MMAlgebraTC.Bridge

/-! # The reduction algebra on the NVIDIA Tensor Core model

The laws of block FMAs that every GEMM schedule of one output entry obeys on the Tensor Core model
of `TensorCore`: products in a block act as a multiset, zero products are invisible, and a chain on
an input supported on a set of products equals the chain restricted to that set. With them,
completeness: on the fp16 models of V100, A100 and H100 two terms are equivalent exactly when their
rigid normal forms agree, on the bf16 and tf32 models chains with different ordered partitions
differ and terms are separated on inputs whose products lie on the binary32 grid; the block error
contract and the divergence of two schedules on every Tensor Core model; witnesses that one WMMA
`m16n16k16` instruction is not one rounding on V100 and A100, and the exact region: on integer
operands whose total magnitude is below `2^24`, or whose positive and negative products each total
below `2^24`, every schedule returns the exact sum. Pinned and anchored accumulation make every
schedule agree outside the exact region too, on a fixed-point grid, with a kernel-checked
demonstration on V100, A100 and H100; a remark shows that a subnormal factor breaks the classical
`γ_n` bound of a block FMA. The bridge to the Ozaki schemes: every schedule is an exact matrix
multiplier, so Ozaki-I, Ozaki-II and their correctly rounded versions give the same bits under every
schedule; and the three ways to make a result schedule-independent (the exact region, pinning,
correct rounding). -/
