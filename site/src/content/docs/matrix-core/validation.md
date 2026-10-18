---
title: 9. Hardware validation
description: How the AMD model is tied to hardware - the paper's test vectors as kernel-checked regressions, differential testing against the authors' MATLAB models and against MMA-Sim, and a second implementation on FloatLib proven equivalent.
---

The proofs connect the model to an independent specification. Its link to
the hardware comes from four checks.

## The paper's test vectors

Every test vector of the paper's Section 4, for CDNA 1, 2 and 3 and the FP32,
FP16, BF16, BF16 `_1k`, XF32 and FP8 variants, is a regression proven by kernel
evaluation that reproduces the output the paper reports for the hardware
([`tests/MatrixCoreTests/Paper/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/matrix-core/tests/MatrixCoreTests/Paper)).
Parameterized families, such as `j = 24 … 32`, are checked for every listed
value. Inputs are written by decoded value and encoded exactly, so an input a
format cannot represent fails the test instead of being rounded silently.

Where a vector cannot be formed in the stated format, or where the paper's
prose and its Algorithm 1 disagree, the test records which it follows and why
([paper notes](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/docs/paper-notes.md)).
For example, the paper's FP16 cancellation test `c = 2^10, p₁ = −p₂ = 2^35`
cannot be formed from FP16 operands, whose products are below `2^32`, so the
suite runs it with BF16, which the paper says behaves identically.

No recorded hardware vectors for AMD GPUs are published, so unlike the
[Tensor Core validation](/HardwarePrimitives/tensor-core/validation/) the suite uses the paper's
explicit vectors rather than bulk measurements.

## Differential testing against the MATLAB models

[`scripts/matlab_diff.py`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/scripts/matlab_diff.py)
compares the Lean model with the authors' MATLAB matrix-core models, run in
GNU Octave, on random inputs sampled as in the paper's Section 5 (normal,
subnormal and uniform random bits) and on the paper's targeted vectors.
The Lean side is `mc_eval`, which prints the observed result of an inner
product for given words.

On 600,000 random inner products across all ten models, the two agree once
two special-value lines and one unread flag in the MATLAB code are corrected.
The two remaining differences are two of the paper's BF16 vectors that test
the subnormal-aware normalization, where the Lean model returns the outputs
the paper reports for the hardware. The MATLAB models have no FP32 SFMA and
no mixed FP8 formats, so those variants are compared through the paper's
vectors only. The method and the per-model counts are in
[`matrix-core/docs/differential.md`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/docs/differential.md).

Random sampling rarely reaches the parts of the FP8 algorithm (Algorithm 2)
that set it apart, so
[`scripts/matlab_fp8.py`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/scripts/matlab_fp8.py)
draws FP8 inputs from six regimes
([`scripts/fp8_cases.py`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/scripts/fp8_cases.py)):
random bits, large odd slots with small even slots, `c` near the FP8
cutoff, cancellation across the two groups, sparse blocks, and `c` larger than
every product, with one or two chained blocks. On 20,000 such inner products
(E4M3 and E5M2) the two models agree once the unread flag is set; with the
MATLAB code as shipped, 2 differ, both through that flag.

## Differential testing against MMA-Sim

[MMA-Sim](https://github.com/microsoft/MMA-Sim) (Microsoft, MIT licence) is a
bit-accurate simulator of the matrix units of NVIDIA and AMD GPUs. For CDNA 3
FP8 it computes blocks of 16 products in two groups of slots, each truncated
relative to the group's largest exponent, rounds the group sums down to the
larger exponent, adds `c`, and rounds to nearest even FP32 (its
`gtr_fdpa`).
[`scripts/mmasim_fp8.py`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/scripts/mmasim_fp8.py)
transcribes that function, at MMA-Sim's commit `aab7f2a`, in exact rational
arithmetic with MMA-Sim's licence notice, and compares it with the Lean model
on the FP8 cases above: 90,000 inner products, 30,000 each on E4M3,
E5M2 and mixed E4M3 × E5M2 operands, with no mismatch. The mixed formats,
which the MATLAB models lack, are covered here.

## A second implementation on FloatLib

[`matrix-core/floatlib-port/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/matrix-core/floatlib-port)
reimplements the model on FloatLib, and Lean proves that it gives the same
observation as the model for every input. See the
[FloatLib cross-check](/HardwarePrimitives/proofs/floatlib/#matrix-cores).

## Running the checks

```sh
cd matrix-core
lake build                    # library, paper regressions, audit
python3 scripts/check.py      # clean build, examples, documentation blocks
python3 scripts/matlab_diff.py --cases 20000 --seed 1   # needs GNU Octave
python3 scripts/matlab_fp8.py --cases 10000 --seed 2026  # targeted FP8, GNU Octave
python3 scripts/mmasim_fp8.py --cases 30000 --seed 1     # FP8 against MMA-Sim
```
