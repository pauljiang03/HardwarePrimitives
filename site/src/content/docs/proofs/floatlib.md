---
title: FloatLib cross-check
description: A second implementation of each library, built on LeanDojo FloatLib and proven equivalent.
---

Each library has a second implementation on
[LeanDojo FloatLib](https://github.com/lean-dojo/FloatLib), a separate Lake
project with its own toolchain (Lean 4.34 with Mathlib), dependency graph, and
runtime. The libraries themselves stay free of Mathlib.

## Tensor Cores

[`tensor-core/floatlib-port/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core/floatlib-port)
reimplements the block model and the reference EFT.

[`floatlib_eq_reference`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/floatlib-port/TCFloat/Equivalence/Representations.lean#L150)
and its inverse cover every model with FP16, BF16, TF32, E5M2 or E4M3 input
(any FMA size `K`, padding bits, minimum alignment exponent, and block-output
width), every encoded input, and every `D`. This includes the six FP8 block
FMAs of Ada, Hopper and B200, with the 13-bit outputs of Ada and Hopper
([`TCFloat.Equivalence.fp8_models`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/floatlib-port/TCFloat/Equivalence/FP8.lean#L113)). The port reads E4M3 as 8-bit OCP words
with FloatLib's `e4m3fn` format, and the parent reads them in its 9-bit
layout. Both decode every word to the same value
([`TCFloat.Equivalence.e4m3fn_decode_widen`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/floatlib-port/TCFloat/Equivalence/FP8.lean#L28)), so the two implementations
agree on every E4M3 input ([`TCFloat.Equivalence.e4m3_equivalence`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/floatlib-port/TCFloat/Equivalence/FP8.lean#L142)). They prove that
the two implementations produce corresponding **complete observations**:
TC results, EFT results, error kinds, and branch tags. The correspondence is
stated through explicit `Equiv`s.

The FloatLib project compares against a generated copy of the main
library's sources. Apart from a scoped-notation file, that copy is
byte-identical to the current sources.

```sh
cd tensor-core/floatlib-port
python3 scripts/check_all.py          # builds proofs, audits axioms and independence
python3 scripts/check_equivalence.py  # 115,029 command observations, 668,944 decoding cases
```

`check_all.py` also replays 50,000 recorded FP8 GPU rows of Ada, L40S, H100,
H200 and B200 through the FloatLib implementation, with 0 mismatches. It
writes `floatlib-port/test-results/summary.json`. The file is generated at run
time and is not committed.

## Matrix Cores

[`matrix-core/floatlib-port/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/matrix-core/floatlib-port)
reimplements the model of every CDNA 1, 2 and 3 configuration on FloatLib
instead of `MatrixCore`'s own numerics.

[`block_agree`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/floatlib-port/MCFloat/Equivalence/Block.lean#L249) proves that, for every model and any input words, a block of
the FloatLib implementation gives the same observation as the model (finite
word, infinity or NaN), and [`dot_agree`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/floatlib-port/MCFloat/Equivalence/Dot.lean#L114) the same for an inner product of any
length. Every model's contract and the chaining theorems hold for the FloatLib
implementation too.

The project compares against a copy of `MatrixCore`'s sources pinned in its
manifest; a change to the model's code fails the pin check until it is pinned
again.

```sh
cd matrix-core/floatlib-port
python3 scripts/check.py   # pin check, build, proofs, audit, comparison with mc_eval
```

The comparison runs the compiled FloatLib implementation and `mc_eval` on
120,000 random inner products across all twelve models.
