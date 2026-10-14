---
title: Project status
description: Build, audit, and validation status, and known open items.
---

## Current state

| Check | Status |
| --- | --- |
| `lake build` (235 targets) | passes, no Lean warnings |
| Axiom audit | only `propext`, `Classical.choice`, `Quot.sound`; no `sorry` |
| Model = independent specification | proved for all inputs on the 8 FP16/BF16/TF32 variants (also Ada's, H200's and B200's) and on B200 FP8 |
| Model = bitvector datapath | proved for all inputs on the 8 FP16/BF16/TF32 variants |
| Recorded GPU vectors | 35,000 rows of V100, A100, H100 and 125,000 rows of Ada, L40S, H100, H200, B200 (FP16, BF16, TF32, E4M3, E5M2), 0 mismatches |
| Software oracle cases | 715 blocks, 2,918 rounding cases, 2,033 feature cases, 0 mismatches |
| FloatLib equivalence | proved; 115,029 + 668,944 comparison cases, 0 mismatches |

## Known open items

- **Hardware coverage.** Active minimum alignment exponents, subnormal and
  zero operands, wide-exponent BF16/TF32 inputs, and the H100 TF32 K = 8
  variant have no recorded GPU rows.
  The TF32 input files duplicate the V100 FP16 inputs.
- **FP8 coverage.** No recorded row has a nonzero `C` accumulated inside the
  FP8 block FMA of Hopper or B200 (the H100 and H200 rows start from `C = 0`,
  and the B200 rows add `C` after the block FMA), and no recorded E4M3
  operand lies in the top binade. FP4, FP6, the FP8 `mma.sync` path of Hopper
  and the Blackwell instructions *Accurate Models* does not characterize are
  not modeled.
- **The paper's input-based precondition** (17) derives five of the fast-path
  check's nine conditions for FP32; the other four depend on the particular
  sum and remain assumptions.
