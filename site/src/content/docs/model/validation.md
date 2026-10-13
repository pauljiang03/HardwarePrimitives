---
title: 10. Hardware validation
description: Recorded GPU measurements from V100, A100, and H100 are replayed through the Lean executable bit for bit.
---

The proofs connect the model to a specification. The link to silicon comes
from **replaying recorded GPU measurements** through the compiled Lean
model and comparing output words exactly.

## The data

The vectors come from the validation suite of the MATLAB Tensor Core models
(v0.5) that accompany *Accurate Models* (Khattak and Mikaitis), vendored with pinned hashes in
[`vendor/matlab-tensor-core-v0.5/model_validation/`](https://github.com/pauljiang03/TC-EFT/tree/main/vendor/matlab-tensor-core-v0.5/model_validation).
Each configuration has 5,000 rows of `a`, `b`, `c` inputs and the `d` output
measured on the GPU.

| GPU | Format | Rows | Model errors | Bit mismatches |
| --- | --- | ---: | ---: | ---: |
| V100 | FP16 | 5,000 | 0 | 0 |
| A100 | FP16 | 5,000 | 0 | 0 |
| A100 | BF16 | 5,000 | 0 | 0 |
| A100 | TF32 | 5,000 | 0 | 0 |
| H100 | FP16 | 5,000 | 0 | 0 |
| H100 | BF16 | 5,000 | 0 | 0 |
| H100 | TF32 (WMMA, K = 4) | 5,000 | 0 | 0 |
| **Total** | | **35,000** | **0** | **0** |

The BF16 and TF32 rows are run through **both** the general `InvocationSpec`
descriptor and the proved model. Both agree with the device and with each
other. The results are recorded in
[`data/regressions/device-report.json`](https://github.com/pauljiang03/TC-EFT/blob/main/data/regressions/device-report.json)
and
[`device-formats-report.json`](https://github.com/pauljiang03/TC-EFT/blob/main/data/regressions/device-formats-report.json).

```sh
python3 scripts/check_features.py
python3 scripts/check_device_formats.py
```

## What the rows don't cover

The recorded rows are random normal inputs. They exercise alignment
truncation and truncation heavily, but some features are **not covered by
hardware data**:

- **Minimum alignment exponents** (−132 and −133) are never active in these rows.
- **Zero operands** do not occur, and **subnormal** operands are rare (0, 1,
  and 5 on V100, A100, and H100 FP16). BF16 and TF32 rows have none.
- **H100 TF32 MMA (K = 8)** has no recorded rows. Its parameters come from
  *Accurate Models* alone.
- **TF32 inputs are FP16-range values.** The vendored A100 and H100 TF32
  `a`/`b` files are byte-identical to the V100 FP16 inputs. The TF32 replay
  therefore tests the TF32 grouping and alignment parameters, but not TF32's
  wider exponent range. BF16 and TF32 inputs only span biased exponents of
  about 113–128.

These features rest on *Accurate Models* and on the
[proofs](/TC-EFT/model/specification/), plus synthetic oracle cases, not on
measurements.

## Independent software oracles

Besides the hardware rows, Python oracles written from scratch in exact
rational arithmetic generate and check further cases:

- `scripts/validate.py`: 715 blocks and 2,918 rounding cases, with an
  independent IEEE decoder, bit-level alignment, and binary search over
  encodings for the output. 0 mismatches.
- `scripts/check_features.py`: 132 configurations of `K` and `p`, 2,033
  cases, including edge cases of the extra alignment bits and of subnormals.
  0 mismatches.

The oracles share no code with the Lean model. They agree with it by
implementing the same *Accurate Models* semantics separately.
