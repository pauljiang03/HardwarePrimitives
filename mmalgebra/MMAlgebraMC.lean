import MMAlgebraMC.Chain
import MMAlgebraMC.Witnesses
import MMAlgebraMC.OneRounding
import MMAlgebraMC.Exact
import MMAlgebraMC.Bound
import MMAlgebraMC.Pinned
import MMAlgebraMC.Counterexamples
import MMAlgebraMC.Bridge

/-! # The reduction algebra on the AMD matrix-core model

Kernel-checked witnesses on the CDNA 1, 2 and 3 fp16 models of `MatrixCore`: inputs that separate
the summation trees of three products on CDNA 1 and CDNA 2 and the block patterns of two products
on CDNA 3, inputs on which exchanging two products inside one `k = 16` MFMA instruction changes
the output, the exact region (every schedule returns the exact sum on small integer operands), and
a machine-checked divergence bound for the correctly rounded models (SFMA, CDNA 1), pinned
accumulation on CDNA 3, and kernel-checked cases where pinning and anchoring fail on CDNA 1 and 2
(and anchoring on CDNA 3), and the bridge to the Ozaki schemes: every schedule is an exact matrix
multiplier on every exact configuration. -/
