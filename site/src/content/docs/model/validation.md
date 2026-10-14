---
title: 10. Hardware validation
description: Recorded GPU measurements from V100 to B200, FP8 included, are replayed through the Lean executable bit for bit.
---

The proofs connect the model to a specification. The link to silicon comes
from **replaying recorded GPU measurements** through the compiled Lean
model and comparing output words exactly.

## The data

The vectors come from the validation suite of the MATLAB Tensor Core models
(v0.5) that accompany *Accurate Models* (Khattak and Mikaitis), vendored with pinned hashes in
[`vendor/matlab-tensor-core-v0.5/model_validation/`](https://github.com/pauljiang03/MMAlgebra/tree/main/vendor/matlab-tensor-core-v0.5/model_validation).
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
[`data/regressions/device-report.json`](https://github.com/pauljiang03/MMAlgebra/blob/main/data/regressions/device-report.json)
and
[`device-formats-report.json`](https://github.com/pauljiang03/MMAlgebra/blob/main/data/regressions/device-formats-report.json).

```sh
python3 scripts/check_features.py
python3 scripts/check_device_formats.py
```

## Ada, L40S, H100, H200 and B200

A later commit of the toolbox,
[`79143bd`](https://github.com/north-numerical-computing/MATLAB-tensor-core/tree/79143bd29a4a71dc7c2ed47741b63572498b17f6/model_validation),
records five more GPUs, again 5,000 rows per configuration. Its vectors are vendored
with pinned hashes in
[`vendor/matlab-tensor-core-79143bd/`](https://github.com/pauljiang03/MMAlgebra/tree/main/vendor/matlab-tensor-core-79143bd).
Every row is replayed through the model and through its invocation
descriptor:

| GPU | FP16 | BF16 | TF32 | E4M3 | E5M2 | Model and descriptor mismatches |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Ada (RTX 1000 Ada) | 5,000 | 5,000 | 5,000 | 5,000 | 5,000 | 0 |
| L40S | 5,000 | 5,000 | 5,000 | 5,000 | 5,000 | 0 |
| H100 | 5,000 | 5,000 | 5,000 | 5,000 | 5,000 | 0 |
| H200 | 5,000 | 5,000 | 5,000 | 5,000 | 5,000 | 0 |
| B200 | 5,000 | 5,000 | 5,000 | 5,000 | 5,000 | 0 |
| **Total** | | | | | | **125,000 rows, 0** |

The FP16, BF16 and TF32 rows use the models of A100 (Ada, L40S) and H100
(H100, H200, B200). The FP8 rows use the [FP8 models](/MMAlgebra/model/variants/#fp8-variants):
each row holds 32 products, two block FMAs on Ada and L40S and one on H100,
H200 and B200. The accumulator input follows each recording:

- **Ada and L40S FP8**, and every FP16, BF16 and TF32 row: `C` is accumulated
  in the block FMA.
- **H100 and H200 FP8** were recorded through `wgmma` with a zero
  accumulator: the outputs are `A·B`, and the replay uses `C = 0`.
- **B200 FP8** outputs add `C` after the block FMA: the block runs from
  `C = 0` and `C` is then added in binary32 with round-to-nearest-even
  (`Model.dotThenAdd`, and the descriptor `blackwellE4M3ThenAddInvocation`).

Some rows repeat: the L40S files are byte-identical to the Ada files, the H100
FP16, BF16 and TF32 files are the v0.5 files above, and H100 and H200 share
their FP8 rows. Counting each recorded output once, the two sources hold
110,000 distinct rows, 30,000 of them FP8.

Before the replay, an independent Python decoder of E4M3 and E5M2 is compared
with the Lean decoders on all 512 words. As a negative control, Ada and Hopper
FP8 with a full binary32 block output disagree with 841 to 1,415 recorded rows
per GPU and format, so the replay distinguishes the 13-bit output. The results
are in
[`data/regressions/device-replay-report.json`](https://github.com/pauljiang03/MMAlgebra/blob/main/data/regressions/device-replay-report.json).

```sh
python3 scripts/check_device_replay.py
```

## What the rows don't cover

The recorded rows are random normal inputs. They exercise alignment
truncation and truncation heavily, but some features are **not covered by
hardware data**:

- **Minimum alignment exponents** (−132 and −133) are never active in these rows,
  nor in the rows of the later commit.
- **Zero operands** do not occur in the FP16, BF16 and TF32 rows, and
  **subnormal** operands are rare (0, 1, and 5 on V100, A100, and H100 FP16;
  1 on Ada and 5 on H200 and B200). BF16 and TF32 rows have none.
- **H100 TF32 MMA (K = 8)** has no recorded rows. Its parameters come from
  *Accurate Models* alone. The H200 and B200 TF32 rows also hold four products.
- **A nonzero `C` accumulated inside an FP8 block FMA on Hopper or B200.**
  The H100 and H200 FP8 rows start from `C = 0`, and the B200 FP8 rows add `C`
  after the block FMA. Only Ada and L40S have FP8 rows with `C` accumulated in
  the block FMA.
- **E4M3's top binade** (256 to 448) and the FP8 NaNs and infinities: no
  recorded operand has them. The FP8 rows do contain zero operands (E4M3) and
  subnormals (3,373 E4M3 and 12 E5M2 operands per GPU).
- **FP4, FP6**, the FP8 `mma.sync` path of H100 and H200, and the Blackwell
  instructions *Accurate Models* does not characterize are not modeled.
- **TF32 inputs are FP16-range values.** The vendored TF32 `a`/`b` files, of
  every GPU in both sources, are byte-identical to the V100 FP16 inputs. The TF32 replay
  therefore tests the TF32 grouping and alignment parameters, but not TF32's
  wider exponent range. BF16 and TF32 inputs only span biased exponents of
  about 113–128.

These features rest on *Accurate Models* and on the
[proofs](/MMAlgebra/model/specification/), plus synthetic oracle cases, not on
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
