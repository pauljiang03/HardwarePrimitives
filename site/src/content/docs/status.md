---
title: Project status
description: Build, audit, and validation status, and known open items.
---

## Current state

| Check | Status |
| --- | --- |
| `lake build` (248 targets) | passes, no Lean warnings |
| Axiom audit | only `propext`, `Classical.choice`, `Quot.sound`; no `sorry` |
| Model = independent specification | proved for all inputs on every model, for every block-output width (FP8 included) |
| Model = bitvector datapath | proved for all inputs on the 8 FP16/BF16/TF32 variants and the 6 FP8 block FMAs |
| Recorded GPU vectors | 35,000 rows of V100, A100, H100, 125,000 rows of Ada, L40S, H100, H200, B200 (FP16, BF16, TF32, E4M3, E5M2) and 20,000 H100 and H200 FP8 rows of toolbox release v0.1, 0 mismatches |
| MMA-Sim cross-check | 850,000 cases on 31 instructions (581,052 identical with a nonzero `C`) and 80,000 FP8 `mma.sync` cases, 0 mismatches |
| Software oracle cases | 715 blocks, 2,918 rounding cases, 2,033 feature cases, 0 mismatches |
| FloatLib equivalence | proved; 115,029 + 668,944 comparison cases, 0 mismatches |

## Known open items

- **Hardware coverage.** Active minimum alignment exponents, subnormal and
  zero operands, wide-exponent BF16/TF32 inputs, and the H100 TF32 K = 8
  variant have no recorded GPU rows.
  The TF32 input files duplicate the V100 FP16 inputs.
- **FP8 coverage.** No recorded row has a nonzero `C` accumulated inside
  `wgmma` or `tcgen05.mma` (the H100 and H200 rows of commit 79143bd start
  from `C = 0`; the B200 rows and the v0.1 H100 and H200 rows come from
  `mma.sync`, which adds `C` after the FP16 block FMAs); there the evidence is
  the MMA-Sim cross-check, a simulator. No recorded E4M3 operand lies in the
  top binade. FP4, FP6 and the Blackwell instructions *Accurate Models* does
  not characterize are not modeled.
- **The paper's input-based precondition** (17) derives five of the fast-path
  check's nine conditions for FP32; the other four depend on the particular
  sum and remain assumptions.
