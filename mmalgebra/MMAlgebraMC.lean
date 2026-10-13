import MMAlgebraMC.Chain
import MMAlgebraMC.Witnesses
import MMAlgebraMC.OneRounding

/-! # The reduction algebra on the AMD matrix-core model

Kernel-checked witnesses on the CDNA 1, 2 and 3 fp16 models of `MatrixCore`: inputs that separate
the summation trees of three products on CDNA 1 and CDNA 2 and the block patterns of two products
on CDNA 3, and inputs on which exchanging two products inside one `k = 16` MFMA instruction changes
the output. -/
