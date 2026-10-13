---
title: Project status
description: Build, audit, and validation status, and known open items.
---

## Current state

| Check | Status |
| --- | --- |
| `lake build` (235 targets) | passes, no Lean warnings |
| Axiom audit | only `propext`, `Classical.choice`, `Quot.sound`; no `sorry` |
| Model = independent specification | proved for all inputs on 8 variants |
| Model = bitvector datapath | proved for all inputs on 8 variants |
| Recorded GPU vectors | 35,000 rows, 0 mismatches |
| Software oracle cases | 715 blocks, 2,918 rounding cases, 2,033 feature cases, 0 mismatches |
| FloatLib equivalence | proved; 115,029 + 668,944 comparison cases, 0 mismatches |

## Known open items

- **Hardware coverage.** Active minimum alignment exponents, subnormal and
  zero operands, wide-exponent BF16/TF32 inputs, and the H100 TF32 K = 8
  variant have no recorded GPU rows.
  The TF32 input files duplicate the V100 FP16 inputs.
- **The paper's input-based precondition** (17) derives five of the fast-path
  check's nine conditions for FP32; the other four depend on the particular
  sum and remain assumptions.
