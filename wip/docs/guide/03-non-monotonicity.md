# Non-monotonicity

A decrease in C can select a finer common alignment grid. Products that truncate to zero on the coarser grid can contribute on the finer grid, causing the model's output to increase. The construction in this chapter uses four products of `2^-12 · 2^-12 = 2^-24` on the V100 model.

```sh
lake env lean examples/NonMonotonicity.lean
```

The executable prints encoded results. Decoded as floating-point values, the observations are:

| Case | Input accumulator C | TC model output | EFT-corrected output |
| --- | --- | --- | --- |
| Before the decrease | `1.0` | `1.0` | `1.0000002384185791015625` |
| After the decrease | `0.999999940395355224609375` | `1.00000011920928955078125` | `1.0000002384185791015625` |

The input accumulator decreases from `1` to `1 - 2^-24`, while the TC model output increases from `1` to `1 + 2^-23`.

At C = 1, the grid is `2^-23`; each `2^-24` product truncates to zero. After the decrease, the grid is `2^-24`; all four products survive. The exact retained accumulator becomes `1 + 3·2^-24`, and the final truncation to FP32 yields `1 + 2^-23`.

## A kernel-checked witness

```lean
import TensorCore.TC.MonotonicityRange

open TensorCore

def before : BlockInput v100F16F32 :=
  ⟨List.replicate 4 (0x0c00, 0x0c00), 0x3f800000⟩
def after : BlockInput v100F16F32 :=
  ⟨List.replicate 4 (0x0c00, 0x0c00), 0x3f7fffff⟩

example : value32 after.c = some (1 - pow2 (-24)) ∧
    value32 before.c = some 1 ∧ (1 - pow2 (-24) : ℚ) < 1 := by
  decide +kernel

example : ((evalBlock before).toOption.map fun t => t.output.bits) = some 0x3f800000 ∧
    ((evalBlock after).toOption.map fun t => t.output.bits) = some 0x3f800001 := by
  decide +kernel
```

This checks a concrete encoded counterexample. The general family theorem is [nonmonotone_encoded](../../TensorCore/TC/Monotonicity.lean): for K products of `2^-(24+p)`, lowering C from one to its predecessor increases the output exactly when `K ≥ 3·2^p`, under the construction's factorization, exponent, minimum alignment exponent, and range hypotheses.

[nonmonotone_range_encoded](../../TensorCore/TC/MonotonicityRange.lean) extends the result to `C_j = 1 - j·2^-24`, with explicit bounds on j and a formula for the witness range and maximal output. These are family results; their theorem parameters state the permitted inputs.

[Flowback.lean](../../TensorCore/TC/Flowback.lean) proves necessary and sufficient conditions that account for changed alignment grids and final rounding. Its sufficient output-level criterion retains the required representability premises.

The complete worked file also executes EFT before and after the perturbation. Both corrected values are `1.0000002384185791015625 = 1 + 2^-22`. Before the decrease, the exact sum is `1 + 4·2^-24`, which is already representable. After the decrease, it is `1 + 3·2^-24`, exactly halfway between `1 + 2^-23` and `1 + 2^-22`. Nearest-even rounding selects the upper endpoint because its final significand bit is zero. Thus the exact sums differ by `2^-24` but round to the same FP32 value. See [the EFT chapter](04-eft.md) for that correction.

The regression witnesses for each architecture family live in [tests/TensorCoreTests/TC/Monotonicity.lean](../../tests/TensorCoreTests/TC/Monotonicity.lean). Run them individually with `lake env lean tests/TensorCoreTests/TC/Monotonicity.lean` after building.
