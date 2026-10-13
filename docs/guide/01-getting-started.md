# Getting started

Run commands in this chapter from the repository root. The project needs the Lean version in `lean-toolchain`, elan, and Python 3. The first-principles library uses Lean's standard arithmetic; the independent FloatLib project has a separate toolchain and dependency graph.

```sh
lake build
lake env lean examples/GettingStarted.lean
```

The worked file prints encoded results. Their decoded FP32 values are:

| Calculation | FP32 value |
| --- | --- |
| Four products of one | `4.0` |
| TC model with four tiny products and C = 1 | `1.0` |
| EFT correction of the tiny-product result | `1.0000002384185791015625 = 1 + 2^-22` |

`Except.ok` indicates successful evaluation; `some` indicates that an optional result is present. The first block contains four products of one. The second contains four products of `2^-12 · 2^-12` and an accumulator of one. Its TC model output is `1.0`, while scalar EFT returns the correctly rounded exact sum `1 + 4·2^-24`.

## Choosing an import

`import TensorCore` supplies the production numerical, TC, reference EFT, and bounded-kernel layers. For a smaller dependency set, choose an entry point:

| Import | Contents |
| --- | --- |
| `TensorCore.Numerics` | Finite representations, exact arithmetic, encoding and rounding |
| `TensorCore.TC` | TC stages, the models of the variants, independent specification, accumulator-width proofs, error bounds, and non-monotonicity |
| `TensorCore.EFT` | Reference EFT and its scalar/chosen-grid conditions |
| `TensorCore.Kernels.EFT` | Bounded workspace operations, correction, and refinement |
| `TensorCoreTests` | Production library plus the complete regression and trust-check environment |

The production imports do not load `TensorCoreTests`. Tests have their own source root at `tests/` and use the main Lake project and toolchain.

## Encoded input, executable result, and proof

A `BlockInput p` contains a list of encoded operand pairs and an encoded FP32 accumulator. The model `p` determines the input word type and the FMA size, the number of products in the block FMA. Hexadecimal literals below denote bit patterns:

```lean
import TensorCore.TC

open TensorCore

def ones : BlockInput v100F16F32 :=
  ⟨List.replicate 4 (0x3c00, 0x3c00), 0⟩

#eval (evalBlock ones).map fun t => t.output.bits.toNat

example : ((evalBlock ones).toOption.map fun t => t.output.bits) =
    some 0x40800000 := by decide +kernel
```

The operands above are FP16 `1.0`, and the expected FP32 result is `4.0`. `evalBlock` returns an `Except ModelError BlockTrace`. On success, the trace retains the prepared terms and output word. On failure, it returns a named domain error.

`#eval` runs the calculation and prints an observation. `example` asks Lean to check a proposition. `decide +kernel` discharges this concrete equality by kernel reduction. The assertion compares the full word, including its zero sign.

A symbolic theorem connects the same evaluator to an exact-arithmetic statement:

```lean
import TensorCore.TC.StageResiduals

open TensorCore

example {p : Model} {x : BlockInput p} {t : BlockTrace}
    (h : evalBlock x = .ok t) :
    exactDot x = some (t.output.value + t.residual) :=
  evalBlock_residual_identity h
```

The input is arbitrary. Under the premise of successful model evaluation, the theorem states that the exact input sum equals the output value plus its extracted residual.

## Finding the source

Definitions and proofs are grouped by their mathematical role:

| Source | Contents |
| --- | --- |
| [TensorCore/Numerics/](../../TensorCore/Numerics/) | Exact arithmetic, finite encodings, and rounding contracts |
| [TensorCore/TC/](../../TensorCore/TC/) | Models of the variants, block evaluation, independent specification, and model properties |
| [TensorCore/EFT/](../../TensorCore/EFT/) | Extraction, scalar conditions, and reference Algorithm 1 |
| [TensorCore/Kernels/EFT/](../../TensorCore/Kernels/EFT/) | Bounded EFT operations and refinement proofs |
| [TensorCore/Scalar/](../../TensorCore/Scalar/) | IEEE operations and native FP32 addition proofs |
| [tests/TensorCoreTests/](../../tests/TensorCoreTests/) | Model, EFT, and specification regression witnesses |
| [tests/TensorCoreTests.lean](../../tests/TensorCoreTests.lean) | Complete regression and proof-audit import root |

Start with [`evalBlock`](../../TensorCore/TC/Block.lean) for the model, [`tcEftEncoded`](../../TensorCore/EFT/Encoded.lean) for reference correction, and [`EFMachine.tcEft`](../../TensorCore/Kernels/EFT/Defs.lean) for bounded execution. [What is proven](../../TensorCore/THEOREMS.md) links their correctness contracts.

Next: [follow the TC stages](02-tensor-core-model.md).
