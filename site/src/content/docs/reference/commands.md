---
title: Commands
description: Executable adapters, the tc launcher, and validation scripts.
---

## The `tc` launcher

```sh
./tc doctor --json     # check toolchain and environment
./tc build             # lake build
./tc audit             # axiom audit
./tc check             # validation suite
./tc trace 3e00 3d00 3e00 3d00 3e00 3d00 3e00 3d00 3f7fffff
./tc eft data/examples/eft.txt
```

The `trace` example runs the V100 model on four products `1.5 × 1.25` with
`C = 1 − 2^-24`, and prints every stage as JSON. The products, kept in
denormalized form, have exponent 0, so η = 0 and the grid is `2^-23`. The `C` term loses its last bit,
and the exact sum `8.5 − 2^-24` truncates to the output `0x4107ffff ≈ 8.4999995`.
The trace also reports `correctedBits`, the TC-EFT result `0x41080000 = 8.5`.

## Native adapters

| Executable | Input | Purpose |
| --- | --- | --- |
| `tc_trace` | eight FP16 hex words and one FP32 word; `--file`, `--round-file` | V100 stage trace |
| `tc_features` | `canonical K PADDING E_ALIGN_MIN …`, `bf16 …`, `tf32 …`, `block MODEL …`, `dot MODEL …`, `dot-then-add MODEL …`, `chain DESCRIPTOR …`, `decode`, `round` | general models, the named variants of every GPU (FP8 included), decimal words |
| `tc_eft_reference` | `block FORMAT K PADDING E_ALIGN_MIN a0 b0 … c D`, `round`, `family p K j` | reference EFT, in the TC-EFT paper's input format |
| `tc_bounded_eft` | `block VARIANT a0 b0 … c D`, `round SIGNED_COEFFICIENT` | 576-bit bounded EFT |
| `tc_lean_eft_check` | JSON Lines on stdin | native Float32 vs bounded scalar fold |

The variants for `tc_bounded_eft` are `v100-fp16`, `a100-fp16`, `h100-fp16`,
`a100-bf16`, `h100-bf16`, `a100-tf32`, `h100-tf32-wmma`, and `h100-tf32-mma`.

## Validation scripts

| Script | Checks |
| --- | --- |
| `check_clean_build.py` | everything below, from a fresh snapshot |
| `check_axioms.py` | axiom allowlist over all public theorems |
| `check_independent_spec.py` | model = *Accurate Models* specification, independence negative control |
| `check_features.py` | 132 configurations and recorded FP16 device vectors |
| `check_device_formats.py` | recorded BF16 and TF32 device vectors |
| `check_device_replay.py` | recorded Ada, L40S, H100, H200 and B200 vectors (FP16, BF16, TF32, E4M3, E5M2) and the FP8 decoders |
| `check_eft.py` | EFT proofs, oracles, and the TC-EFT paper's test vectors |
| `check_bounded_eft.py` | bounded kernel vs reference |
| `check_docs.py` | every Lean block in the docs elaborates |

The scripts refuse to run under `python -O` or `PYTHONOPTIMIZE`, because
their checks use `assert`. Run timings are written to `tmp/timings/`, which is
not tracked, so rerunning the checks on unchanged sources leaves `git status`
clean.
