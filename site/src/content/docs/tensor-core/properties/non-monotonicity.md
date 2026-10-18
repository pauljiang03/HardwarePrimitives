---
title: Non-monotonicity
description: Lowering the accumulator input C can raise the Tensor Core output; Lean proves exactly when.
---

In IEEE arithmetic with a fixed rounding mode, `x ≤ x'` implies
`fl(x + y) ≤ fl(x' + y)`. Tensor Cores break this. Lowering `C` can lower its
exponent, which makes the alignment grid finer, so products that were
truncated away start to count.

## The mechanism, concretely

On the V100 model, take four products `2^-12 × 2^-12 = 2^-24`:

| `C` | η | Grid | Products kept | Output |
| --- | ---: | --- | --- | --- |
| `1` | 0 | `2^-23` | none | `1` |
| `1 − 2^-24` | −1 | `2^-24` | all four | `1 + 2^-23` |

[The model at a glance](/HardwarePrimitives/tensor-core/#a-worked-trace) walks through every
stage of this example.

## The general family theorem

This formalizes Theorem III.4 of the TC-EFT paper (`nonmonotone_perturbation`),
stated here on encoded inputs.

```lean
theorem nonmonotone_encoded (K p : ℕ) (eAlignMin : Option ℤ) (hfl : ∀ f ∈ eAlignMin, f ≤ -1)
    (a b : (fp16Fp32Model K p eAlignMin).Word) (da db : Decoded)
    (ha : (fp16Fp32Model K p eAlignMin).decode a = some da)
    (hb : (fp16Fp32Model K p eAlignMin).decode b = some db)
    (hval : (denormalizedMul da db).value = pow2 (-(24 + p))) (hscale : (denormalizedMul da db).exponent ≤ -1)
    (hK : K < 2 ^ (24 + p)) :
    ∃ t t' : BlockTrace,
      evalBlock ⟨List.replicate K (a, b), 0x3f800000⟩ = .ok t ∧
      evalBlock ⟨List.replicate K (a, b), 0x3f7fffff⟩ = .ok t' ∧
      t.output.value = 1 ∧ (1 < t'.output.value ↔ 3 * 2 ^ p ≤ K)
```

In words: take any FP16 model with FMA size `K`, `p` padding bits,
and a minimum alignment exponent, if any, of at most −1. Use `K` copies of a product whose exact value is
`2^-(24+p)` and whose exponent is at most −1. With `C = 1` the output is
exactly 1. Lowering `C` to its FP32 predecessor `1 − 2^-24` makes the output
**exceed 1 exactly when `K ≥ 3 · 2^p`**.

| GPU | K | p | Threshold `3·2^p` | Non-monotone in this family? |
| --- | ---: | ---: | ---: | --- |
| V100 | 4 | 0 | 3 | yes |
| A100 | 8 | 1 | 6 | yes |
| H100 | 16 | 2 | 12 | yes |

Each row has a kernel-checked concrete witness in
[`tests/TensorCoreTests/TC/Monotonicity.lean`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/tests/TensorCoreTests/TC/Monotonicity.lean).

## The FP8 block FMAs

With `K` equal tiny products and zeros, lowering `C` to its FP32 predecessor
raises the output exactly when `K` reaches a threshold. Lean checks the
equivalence for every `K` up to the FMA size
([`TensorCore.fp8_narrow_nonmonotone`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/MonotonicityFP8.lean#L28), [`TensorCore.fp8_blackwell_nonmonotone`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/MonotonicityFP8.lean#L39)).

| Block FMA | Product | `C` | Threshold | Non-monotone? |
| --- | --- | --- | ---: | --- |
| Ada E4M3, E5M2 (K = 16) | `2^-7 · 2^-7` | `1` | 3 | yes |
| Hopper E4M3, E5M2 (K = 32) | `2^-7 · 2^-7` | `1` | 3 | yes |
| B200 E5M2 (K = 32) | `2^-13 · 2^-13` | `1` | 12 | yes |
| B200 E4M3 (K = 32) | `2^-9 · 2^-9` | `256` | 12 | yes |

Ada and Hopper keep 13 bits after alignment and in the output: `C = 1 − 2^-24`
aligns to `1 − 2^-14`, and the products `2^-14` count once the grid is
`2^-14`. B200 keeps 25 bits and an FP32 output, so its threshold is that of
H100 FP16, `3·2^2 = 12`. E4M3 products cannot be as small as `2^-26`, so its
row uses `C = 256`.

## Larger perturbations

[`nonmonotone_range_encoded`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/MonotonicityRange.lean#L262)
generalizes the result to `C = 1 − j·2^-24` for `1 ≤ j ≤ 2^23`. It gives the
exact set of `j` for which the output exceeds 1, namely
`j ≤ min(2^23, K/2^p − 2)`, a closed form for the output, and the largest
output in the family.

## Necessary and sufficient conditions in general

[`flowback_necessary` and `flowback_sufficient`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/TensorCore/TC/Flowback.lean#L200)
cover arbitrary inputs. Call the products recovered by the finer grid the
*flowback* ω, and the change in the aligned `C` term ΔA. An output increase
**requires** `ω > ΔA`. The condition is **sufficient** when both
accumulators are representable in FP32.

These theorems are about the **model**. That real GPUs are non-monotone is
supported by the model's agreement with recorded hardware outputs. The
specific witness inputs above are not among the recorded rows.
