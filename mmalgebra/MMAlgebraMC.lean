import MMAlgebraMC.Chain
import MMAlgebraMC.Witnesses
import MMAlgebraMC.OneRounding
import MMAlgebraMC.Exact
import MMAlgebraMC.Bound
import MMAlgebraMC.Pinned
import MMAlgebraMC.Counterexamples
import MMAlgebraMC.Bridge
import MMAlgebraMC.Words
import MMAlgebraMC.Blocks
import MMAlgebraMC.RigidMC
import MMAlgebraMC.RoundedMC
import MMAlgebraMC.PairwiseMC
import MMAlgebraMC.ChainBF16
import MMAlgebraMC.Contracts
import MMAlgebraMC.SFMA
import MMAlgebraMC.AllInputs
import MMAlgebraMC.ParityLaw

/-! # The reduction algebra on the AMD matrix-core model

Kernel-checked witnesses on the CDNA 1, 2 and 3 fp16 models of `MatrixCore`: inputs that separate
the summation trees of three products on CDNA 1 and CDNA 2 and the block patterns of two products
on CDNA 3, inputs on which exchanging two products inside one `k = 16` MFMA instruction changes
the output, the exact region (every schedule returns the exact sum on small integer operands), and
completeness: two terms are equivalent exactly when their normal forms agree on CDNA 3 (rigid),
CDNA 1 (correctly rounded trees) and CDNA 2 (binary summation trees), and on SFMA on inputs whose
products lie on the binary32 grid, with chains on CDNA 1 bf16; the merge laws of CDNA 1 and the
`c`-split law of CDNA 2; machine-checked divergence bounds for SFMA and CDNA 1, 2 and 3, pinned
accumulation on CDNA 3, and kernel-checked cases where pinning and anchoring fail on CDNA 1 and 2
(and anchoring on CDNA 3), and the bridge to the Ozaki schemes: every schedule is an exact matrix
multiplier on every exact configuration. On CDNA 3 binary8 a block depends on its slots only
through the unordered pair {odd-slot multiset, even-slot multiset} (the parity law), and a slot
permutation preserves the output on every input exactly when it preserves the parity partition. -/
