---
title: 10. Hardware validation
description: Recorded GPU measurements from V100 to B200, FP8 included, are replayed through the Lean executable bit for bit, and the models are cross-checked against the MMA-Sim simulator.
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
(H100, H200, B200). Each FP8 row holds 32 products. The toolbox's CUDA harness
for the FP8 rows with binary32 output
([`mma_fp8_output_fp32.cu`](https://github.com/pauljiang03/MMAlgebra/blob/main/vendor/matlab-tensor-core-79143bd/model_validation/CUDA/mma_fp8_output_fp32.cu),
vendored with a pinned hash; the same file is in release v0.1) issues
`mma.sync.aligned.m16n8k32` with FP8 operands and binary32 `C` and `D`. The model each FP8 row is replayed through
follows what its outputs agree with:

- **Ada and L40S FP8**, and every FP16, BF16 and TF32 row: `C` is accumulated
  in the block FMA. On Ada the FP8 `mma.sync` runs on Ada's FP8 block FMA
  (two 16-product blocks per row, chained through `C`).
- **B200 FP8**, recorded with the toolbox's `mma.sync` harness: the outputs
  agree with the [FP8 `mma.sync` model](/MMAlgebra/model/variants/#fp8-through-mmasync)
  (`mmaSyncFP8Dot`: FP8 converted to FP16, two interleaved Hopper FP16 block
  FMAs, then `C` added in binary32 with round-to-nearest-even), and equally with
  B200's FP8 block FMA run from `C = 0` followed by the same addition of `C`
  (`Model.dotThenAdd`, and the descriptor `blackwellE4M3ThenAddInvocation`).
  Both replays have 0 mismatches. As a control, B200's FP8 block FMA with `C`
  inside disagrees with 1,793 (E4M3) and 1,764 (E5M2) rows, so these rows are
  not evidence for `C` accumulated in `tcgen05.mma`.
- **H100 and H200 FP8** at this commit: the outputs agree with Hopper's FP8
  block FMA from a zero accumulator, the reading of the toolbox's validation
  script (at this commit,
  [`Validate_TC_models.m`](https://github.com/north-numerical-computing/MATLAB-tensor-core/blob/79143bd29a4a71dc7c2ed47741b63572498b17f6/model_validation/Validate_TC_models.m)
  sets `C` to zero for Hopper FP8: "`D = AB + D` where `D` is zero for fp8
  with WGMMA"). The replay uses `C = 0` and ignores
  the `c` file.

Some rows repeat: the L40S files are byte-identical to the Ada files, the H100
FP16, BF16 and TF32 files are the v0.5 files above, and H100 and H200 share
their FP8 rows. Counting each recorded output once, the two sources hold
110,000 distinct rows, 30,000 of them FP8.

Before the replay, an independent Python decoder of E4M3 and E5M2 is compared
with the Lean decoders on all 512 words. As a negative control, Ada and Hopper
FP8 with a full binary32 block output disagree with 841 to 1,415 recorded rows
per GPU and format, so the replay distinguishes the 13-bit output.

### H100 and H200 FP8 with `C`: release v0.1

The toolbox's releases v0.1 and v0.2 hold other H100 and H200 FP8 outputs for
the same `a`, `b` and `c` inputs (later releases replaced them). They are
vendored with pinned hashes in
[`vendor/matlab-tensor-core-v0.1/`](https://github.com/pauljiang03/MMAlgebra/tree/main/vendor/matlab-tensor-core-v0.1),
because they are the only recorded Hopper FP8 outputs in which `C` is
accumulated:

| GPU | E4M3 | E5M2 | `mma.sync` model mismatches | Control: Hopper FP8 block FMA from `C = 0` |
| --- | ---: | ---: | ---: | ---: |
| H100 | 5,000 | 5,000 | 0 | 5,000 and 5,000 rows differ |
| H200 | 5,000 | 5,000 | 0 | 5,000 and 5,000 rows differ |

Every row agrees with the FP8 `mma.sync` model with `C` from the `c` file,
and none with Hopper's 13-bit FP8 block FMA from `C = 0`. These outputs show
the path of the instruction the toolbox's FP8 harness issues: FP8 converted to
FP16, two interleaved FP16 block FMAs, `C` added afterwards. As on B200, the
random rows do not separate this model from one 32-product block with 25
mantissa bits after alignment, run from `C = 0` and followed by the addition
of `C`; the interleaving experiment of *Accurate Models* does
(`interleave_test_single_block`). One recorded B200 row excludes two
independent FP16 blocks added in binary32 (`separate_groups_excluded`,
kernel-checked).

In all, the replay covers 145,000 rows (125,000 of commit 79143bd and 20,000
of v0.1) with 0 mismatches. The results are in
[`data/regressions/device-replay-report.json`](https://github.com/pauljiang03/MMAlgebra/blob/main/data/regressions/device-replay-report.json).

```sh
python3 scripts/check_device_replay.py
```

## Cross-check against MMA-Sim

[MMA-Sim](https://github.com/microsoft/MMA-Sim) (Microsoft, MIT licence) is a
bit-accurate simulator of GPU matrix multiply-accumulate units, built and
checked by its authors against GPUs. It covers instructions with no recorded
data here, `wgmma` and `tcgen05.mma` with `C` accumulated among them.
[`scripts/check_mmasim.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/scripts/check_mmasim.py)
runs an unmodified local checkout of the commit pinned in
[`vendor/mmasim/SOURCES.json`](https://github.com/pauljiang03/MMAlgebra/blob/main/vendor/mmasim/SOURCES.json)
(`ce75698`; the script checks the SHA-256 of every file it imports; MMA-Sim's
code is not vendored) and compares it with `tc_features model-dot`, the Lean
model with each variant's parameters. MMA-Sim's FP64 FMA module, a C++ kernel
built with `-fopenmp` that Apple clang rejects, is replaced by a stub that
fails if called: no FP64 instruction is checked.

Cases are random bit patterns, wide and moderate values, sparse inputs, `C`
above or below the largest product, near-cancellation, tiny and subnormal
operands, signed zeros and inputs near overflow, over one, two or more
instructions chained through `C`. Outcomes: identical words; an Inf or NaN
operand, or a sum beyond binary32's range (the Lean models reject both);
mismatches.

| Instruction | Cases | Identical | Inf/NaN operand | Overflow | Mismatches |
| --- | ---: | ---: | ---: | ---: | ---: |
| V100 fp16 mma.m8n8k4 | 30,000 | 28,362 | 1,638 | 0 | 0 |
| A100 fp16 mma.m16n8k16 | 30,000 | 27,524 | 2,476 | 0 | 0 |
| A100 fp16 mma.m16n8k8 | 30,000 | 27,966 | 2,034 | 0 | 0 |
| A100 bf16 mma.m16n8k16 | 30,000 | 21,349 | 738 | 7,913 | 0 |
| A100 tf32 mma.m16n8k8 | 30,000 | 21,997 | 573 | 7,430 | 0 |
| Ada fp16 mma.m16n8k16 | 30,000 | 27,483 | 2,517 | 0 | 0 |
| Ada bf16 mma.m16n8k16 | 30,000 | 21,311 | 706 | 7,983 | 0 |
| Ada tf32 mma.m16n8k8 | 30,000 | 22,023 | 531 | 7,446 | 0 |
| H100 fp16 mma.m16n8k16 | 30,000 | 27,513 | 2,487 | 0 | 0 |
| H100 bf16 mma.m16n8k16 | 30,000 | 21,327 | 727 | 7,946 | 0 |
| H100 tf32 mma.m16n8k8 | 30,000 | 21,978 | 584 | 7,438 | 0 |
| H100 tf32 mma.m16n8k4 (as WMMA HMMA.1684) | 30,000 | 23,007 | 484 | 6,509 | 0 |
| H100 fp16 wgmma.m64n8k16 | 30,000 | 27,526 | 2,474 | 0 | 0 |
| H100 bf16 wgmma.m64n8k16 | 30,000 | 21,302 | 786 | 7,912 | 0 |
| H100 tf32 wgmma.m64n8k8 | 30,000 | 21,971 | 547 | 7,482 | 0 |
| B200 fp16 mma.m16n8k16 | 30,000 | 27,491 | 2,509 | 0 | 0 |
| B200 bf16 mma.m16n8k16 | 30,000 | 21,317 | 746 | 7,937 | 0 |
| B200 tf32 mma.m16n8k8 | 30,000 | 21,927 | 592 | 7,481 | 0 |
| B200 fp16 tcgen05.kind::f16 | 30,000 | 27,492 | 2,508 | 0 | 0 |
| B200 bf16 tcgen05.kind::f16 | 30,000 | 21,342 | 745 | 7,913 | 0 |
| B200 tf32 tcgen05.kind::tf32 | 30,000 | 21,970 | 588 | 7,442 | 0 |
| RTX PRO 6000 fp16 mma.m16n8k16 | 30,000 | 27,526 | 2,474 | 0 | 0 |
| Ada e4m3 mma.m16n8k32 | 20,000 | 18,921 | 1,079 | 0 | 0 |
| Ada e5m2 mma.m16n8k32 | 20,000 | 18,163 | 1,837 | 0 | 0 |
| Ada e4m3 mma.m16n8k16 | 30,000 | 28,797 | 1,203 | 0 | 0 |
| H100 e4m3 wgmma.m64n8k32 | 20,000 | 18,947 | 1,053 | 0 | 0 |
| H100 e5m2 wgmma.m64n8k32 | 20,000 | 18,144 | 1,856 | 0 | 0 |
| B200 e4m3 tcgen05.kind::f8f6f4 | 20,000 | 19,003 | 997 | 0 | 0 |
| B200 e5m2 tcgen05.kind::f8f6f4 | 20,000 | 18,142 | 1,858 | 0 | 0 |
| RTX PRO 6000 e4m3 mma.m16n8k32 | 20,000 | 18,976 | 1,024 | 0 | 0 |
| RTX PRO 6000 e5m2 mma.m16n8k32 | 20,000 | 18,156 | 1,844 | 0 | 0 |
| **Total** | **850,000** | **708,953** | **42,215** | **98,832** | **0** |

Of the identical cases, 581,052 have a nonzero `C`, so
`C` accumulated inside `wgmma`, `tcgen05.mma` and the RTX PRO 6000's FP8
`mma.sync` agrees with the models wherever both return a value.

MMA-Sim does not list FP8 `mma.sync` for Hopper or Blackwell. The second part
composes that path from MMA-Sim's own pieces (torch's FP8 to FP16
conversion, MMA-Sim's FP16 `mma.sync` for each interleaved group, `C` added in
binary32) and compares it with `tc_features mma-sync`. This checks the
arithmetic of the `mma.sync` model given its structure; the structure itself
is tested by the recorded rows above.

| FP8 `mma.sync` composite | Cases | Identical | Inf/NaN operand | Mismatches |
| --- | ---: | ---: | ---: | ---: |
| Hopper e4m3 k=32 | 10,000 | 9,482 | 518 | 0 |
| Hopper e4m3 k=16 | 10,000 | 9,567 | 433 | 0 |
| Hopper e5m2 k=32 | 10,000 | 9,055 | 945 | 0 |
| Hopper e5m2 k=16 | 10,000 | 9,198 | 802 | 0 |
| Blackwell e4m3 k=32 | 10,000 | 9,501 | 499 | 0 |
| Blackwell e4m3 k=16 | 10,000 | 9,543 | 457 | 0 |
| Blackwell e5m2 k=32 | 10,000 | 9,064 | 936 | 0 |
| Blackwell e5m2 k=16 | 10,000 | 9,179 | 821 | 0 |

The report is
[`data/regressions/mmasim-report.json`](https://github.com/pauljiang03/MMAlgebra/blob/main/data/regressions/mmasim-report.json).
The check needs a Python with `torch` and `ninja` for MMA-Sim and a checkout of
the pinned commit; it is not part of the clean-build report.

```sh
git clone https://github.com/microsoft/MMA-Sim && git -C MMA-Sim checkout ce75698
python3 scripts/check_mmasim.py --mmasim MMA-Sim --python /path/to/python-with-torch
```

This is a simulator, not a hardware measurement: agreement shows that the
Lean models and MMA-Sim implement the same arithmetic, which MMA-Sim's
authors checked against GPUs.

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
- **A nonzero `C` accumulated inside `wgmma` or `tcgen05.mma`.** The H100 and
  H200 FP8 rows of 79143bd start from `C = 0`; the v0.1 rows and the B200 rows
  come from `mma.sync`, which adds `C` after the FP16 block FMAs. Only Ada and
  L40S have FP8 rows with `C` accumulated in an FP8 block FMA. For `wgmma` and
  `tcgen05.mma` with `C`, the evidence is the MMA-Sim cross-check below, a
  simulator rather than a recording.
- **E4M3's top binade** (256 to 448) and the FP8 NaNs and infinities: no
  recorded operand has them. The FP8 rows do contain zero operands (E4M3) and
  subnormals (3,373 E4M3 and 12 E5M2 operands per GPU).
- **FP4, FP6** and the Blackwell instructions *Accurate Models* does not
  characterize are not modeled. The RTX PRO 6000 has no recorded rows; its
  FP8 `mma.sync` model rests on *Accurate Models* and on MMA-Sim.
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
  cases, including edge cases of the padding bits and of subnormals.
  0 mismatches.

The oracles share no code with the Lean model. They agree with it by
implementing the same *Accurate Models* semantics separately.
