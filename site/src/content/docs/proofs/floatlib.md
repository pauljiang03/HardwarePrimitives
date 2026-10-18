---
title: FloatLib cross-check
description: A second implementation of the model and reference EFT, built on LeanDojo FloatLib and proved equivalent.
---

[`floatlib-port/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/tensor-core/floatlib-port)
is a separate Lake project. It reimplements the block model and the
reference EFT on top of [LeanDojo FloatLib](https://github.com/lean-dojo/FloatLib),
with its own toolchain (Lean 4.34 with Mathlib), dependency graph, and
runtime.

## The equivalence theorem

[`floatlib_eq_reference`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/tensor-core/floatlib-port/TCFloat/Equivalence/Representations.lean#L149)
and its inverse cover every model with FP16, BF16, or TF32 input (any FMA
size `K`, padding bits, and minimum alignment exponent), every encoded input, and every `D`. They prove that
the two implementations produce corresponding **complete observations**:
TC results, EFT results, error kinds, and branch tags. The correspondence is
stated through explicit `Equiv`s.

The FloatLib project compares against a generated copy of the main
library's sources. Apart from a scoped-notation file, that copy is
byte-identical to the current sources.

## Running it

```sh
cd tensor-core/floatlib-port
python3 scripts/check_all.py          # builds proofs, audits axioms and independence
python3 scripts/check_equivalence.py  # 115,029 command observations, 668,944 decoding cases
```

`check_all.py` writes `floatlib-port/test-results/summary.json`. The file is
generated at run time and is not committed.
