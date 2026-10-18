---
title: Error bounds
description: Where a Tensor Core block loses accuracy, with an exact residual identity and a two-part error bound.
---

The model loses information in exactly two places: alignment truncation and
the final truncation to FP32. The library names both losses and proves that
together they account for the whole error.

## Exact residual identity

```lean
def BlockTrace.residual (t : BlockTrace) : ℚ := t.block.extractReference t.output.value
-- = (accumulator − output) + Σ alignment residuals

theorem evalBlock_residual_identity {p : Model} {x : BlockInput p} {t : BlockTrace}
    (h : evalBlock x = .ok t) :
    exactDot x = some (t.output.value + t.residual)
```

Whenever the model succeeds, the exact sum `C + Σ aᵢbᵢ` of the decoded
inputs equals the output plus the residual. Here the residual is the
final-rounding loss plus the alignment losses. The exact sum is computed from the
input words directly (`exactDot`), not from the model's intermediate values.

## Two-part error bound

```lean
theorem evalBlock_error_bound {p : Model} {x : BlockInput p} {t : BlockTrace}
    (h : evalBlock x = .ok t) (hw : 23 ≤ p.outputMantissaBits) :
    absQ (t.block.exactDot - t.output.value) <
      (t.block.terms.length : ℚ) * pow2 t.block.alignGridExponent +
        pow2 (outputUlpExponent t.output.bits)
```

So the error is less than

```text
(K + 1) · 2^(η − F)    +    ulp(D)
  alignment loss          final-rounding loss
```

Each of the `K + 1` terms loses less than one grid step, and truncation to FP32
loses less than one output ulp. The hypothesis `hw` asks for an FP32 block
output, which every variant has except the FP8 block FMAs of Ada and Hopper.
For those, and for any other width, the same bound holds with the output term
widened to the block output's last place:

```lean
theorem evalBlock_error_bound_any {p : Model} {x : BlockInput p} {t : BlockTrace}
    (h : evalBlock x = .ok t) :
    absQ (t.block.exactDot - t.output.value) <
      (t.block.terms.length : ℚ) * pow2 t.block.alignGridExponent +
        pow2 (outputUlpExponent t.output.bits + ((23 - p.outputMantissaBits : ℕ) : ℤ))
```

With `m` output mantissa bits, truncating the FP32 word further to `m` bits
loses less than `2^(23 − m)` FP32 ulps, and the two truncations together
still lose less than that. On Ada and Hopper FP8 ([`fp8_error_bound`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/OutputWidth.lean#L414),
`m = 13`) the output term is `2^10` FP32 ulps, one unit in the last place of
the 14-bit output significand; for `m ≥ 23` the bound is `evalBlock_error_bound`.
The proof ([`evalBlock_error_bound_any`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/OutputWidth.lean#L405)) works on the FP32 magnitude as
an integer multiple of `2^-149`, which is monotone in the word, so clearing low
mantissa bits stays between zero and the value and moves it by less than one
unit of the cleared position. The bound uses only quantities in the trace,
and [`evalBlock_success_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/AcceptedDomain.lean#L36)
says exactly when it applies.

The alignment term depends on η, the **largest** exponent in the block FMA, not
on the size of the result. When large terms cancel, `2^(η − F)` can be far
bigger than the ulp of the result. In that case the relative error is large,
however exact the hardware is otherwise. This loss is what TC-EFT exists to
recover.

## Chains

For chained block FMAs,
[`runBlocks_residual_ledger`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/Composition.lean#L93)
gives the same identity across the whole chain. The initial `C` plus every
product equals the last output plus the sum of the residuals of all the blocks.
