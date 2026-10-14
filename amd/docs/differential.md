# Differential testing against the MATLAB models and MMA-Sim

`scripts/matlab_diff.py` compares the Lean model with the authors' MATLAB Tensor Core v0.6
matrix-core models (`MI100MC.m`, `MI210MC.m`, `MI300AMC.m`, and the generalized model
`models/tools/Generic_BFMA_TC.m`, commit `79143bd`) on random and targeted inputs.

```sh
brew install octave            # GNU Octave runs the MATLAB models
python3 scripts/matlab_diff.py --cases 20000 --seed 1
```

The script fetches the MATLAB repository at the pinned commit into `.lake/`, builds `mc_eval`,
and writes `.lake/matlab-diff/report.json` with the counts, the SHA-256 of the model files, and
up to five mismatching inputs per run.

## Method

* **Lean side.** `mc_eval` reads words and prints the result of `dotOutcome`: the binary32 word,
  an infinity, or NaN.
* **MATLAB side.** `scripts/matlab/driver.m` calls `Generic_BFMA_TC` with the parameters of
  `MI100MC.m`, `MI210MC.m` and `MI300AMC.m`, chaining blocks as `GEMM.m` does (zero padding to a
  multiple of `N_FMA`, each block's `d` the next block's `c`). Inputs arrive as exact binary64
  values; XF32 inputs arrive already truncated to tf19, as CPFloat would deliver them.
* **Octave.** Four functions behave differently from MATLAB in ways that change the model's
  results (`string`, `fma`, `bitshift` by 64 or more bits, `dot` of empty vectors);
  `scripts/matlab/shims` restores MATLAB's behavior without changing the model files
  ([paper notes](paper-notes.md#running-the-matlab-models-in-gnu-octave)).
* **Inputs**, as in the paper's Section 5, with the paper's inner dimensions `k`:
  * `normal`: exponent-mantissa sampling, significands uniform in `(−2, 2)` and exponents uniform
    over the normal range of each format;
  * `subnormal`: the same between the minimum subnormal and minimum normal exponents;
  * `bits`: independent uniform bits, with infinities and NaN redrawn;
  * `paper`: the paper's CDNA 3 vectors for the two RD steps of Algorithm 1.
* **MATLAB variants.**
  * `shipped`: the parameters exactly as in the model files;
  * `rdfix` (CDNA 3): the field `rd_borrow_carry` set, so that `Generic_BFMA_TC.m` reads
    `MI300AMC.m`'s `rd_norm_aware` and executes the RD of `S_acc`;
  * `patched` (CDNA 2 and 3): `rdfix` plus two changes to the product-overflow block (lines
    106–114): the infinity takes the sign of the overflowing products, and a NaN `c` stays NaN.
* Results are compared as values: equal binary32 values, the same infinity, or NaN.

## Results

20,000 cases per model and sampling scheme (seed 1): 600,000 random inner products, plus 85 of
the paper's targeted vectors. Mismatches per variant:

| Model | `k` | shipped | `rdfix` | `patched` |
| --- | --- | --- | --- | --- |
| CDNA 1 fp16 | 16 | 0 / 60,000 | — | — |
| CDNA 1 bf16 | 8 | 0 / 60,000 | — | — |
| CDNA 2 fp16 | 16 | 0 / 60,000 | — | 0 / 60,000 |
| CDNA 2 bf16 | 16 | 6,625 / 60,000 | — | 0 / 60,000 |
| CDNA 2 bf16 `_1k` | 16 | 8,212 / 60,000 | — | 0 / 60,000 |
| CDNA 3 fp16 | 16 | 16 / 60,000 + 5 / 28 paper | 0 | 0 |
| CDNA 3 bf16 | 16 | 7,535 / 60,000 + 2 / 57 paper | 7,532 + 2 paper | **2 paper** |
| CDNA 3 XF32 | 8 | 5,388 / 60,000 | 5,384 | 0 |
| CDNA 3 fp8 E4M3 | 16 | 1 / 60,000 | 0 | 0 |
| CDNA 3 fp8 E5M2 | 16 | 8 / 60,000 | 0 | 0 |

Every mismatch is accounted for:

* **shipped → `rdfix`**: the RD of `S_acc` that v0.6 never executes. Random sampling meets it
  rarely (32 of 300,000 CDNA 3 cases); five of the paper's fp16 vectors need it.
* **`rdfix` → `patched`**: the sign of an overflowing product's infinity and the loss of a NaN
  `c`. Random bits give bf16 and tf19 products beyond `2^128` often; every such case agrees once
  the two lines are corrected.
* **The two remaining cases** are the paper's bf16 vectors that test the subnormal-aware
  normalization (`c = 2^-127 − 2^-140, p₁ + ⋯ = 2^-140 + 2^-150 + 2^-158` and
  `c = 0, p₁ = 2^-150, p₂ = 2^-158`). There the MATLAB model keeps 32 fractional bits below
  `2^-126`, and the Lean model returns the outputs the paper reports for the hardware.

With the two MATLAB defects corrected, the Lean model and the MATLAB model agree on all 600,000
random inner products on every CDNA variant the MATLAB model implements (it has no fp32 SFMA and no
mixed fp8 formats), and the Lean model alone matches the paper's hardware results on the two
normalization vectors.

## Targeted binary8 inputs

Random sampling rarely reaches the parts of Algorithm 2 that set binary8 apart: two groups with
different exponents, cancellation across the groups, `c` at the binary8 cutoff. `scripts/fp8_cases.py`
draws inner products (`k = 16` and `k = 32`, two chained blocks) from six regimes, cycled case
by case:

0. random bits: uniformly random words and a random binary32 `c`;
1. operands of magnitude `2^2`–`2^7` in the odd slots and `2^-9`–`2^-3` in the even slots, so the
   two groups have different exponents and the smaller sum is rounded down to the common grid;
2. `c` near the cutoff, where `e_max − e_c` is about 22 to 28;
3. pairs `x·y` and `−x·y` in adjacent slots, which cancel across the groups, with three small
   products;
4. two or three nonzero products in random slots;
5. `c` larger than every product (the shifted-sum path).

`scripts/matlab_fp8.py` compares the Lean model with the MATLAB model on these inputs, run as
above (`MI300AMC.m` parameters, commit `79143bd`, GNU Octave):

```sh
python3 scripts/matlab_fp8.py --cases 10000 --seed 2026
```

The MATLAB model takes one input format, so only E4M3 × E4M3 and E5M2 × E5M2 are compared:
10,000 inner products each, 1,666 or 1,667 per regime.

| Model | `shipped` | `rdfix` |
| --- | --- | --- |
| CDNA 3 fp8 E4M3 | 2 / 10,000 (both random bits) | 0 / 10,000 |
| CDNA 3 fp8 E5M2 | 0 / 10,000 | 0 / 10,000 |

The two `shipped` mismatches are the RD of `S_acc` that v0.6 does not execute, as above; with
`rdfix` the two models agree on all 20,000 targeted inner products.

## MMA-Sim

[MMA-Sim](https://github.com/microsoft/MMA-Sim) (Microsoft, MIT licence) is a bit-accurate
simulator of the matrix multiply-accumulate units of NVIDIA and AMD GPUs, described in
[arXiv:2511.10909](https://arxiv.org/abs/2511.10909). For CDNA 3 `float8_e4m3fnuz` and
`float8_e5m2fnuz` inputs it selects `MMA_GTR_FDPA(F=24, F2=31, rho="RNE-FP32", L_max=16)`
(`src/mmasim/mmasim/amd/sim.py`): blocks of 16 products, the products of the two groups of slots
each truncated relative to the group's largest exponent, the group sums rounded down to the
larger exponent, `c` added, and the sum rounded to nearest even binary32 (`gtr_fdpa`,
`src/mmasim/mmasim/arithmetic/fdpa.py`). Its groups are indexed from 0, so its even group is the
paper's odd slots.

`scripts/mmasim_fp8.py` transcribes `gtr_fdpa` at commit `aab7f2a` step by step in exact
rational arithmetic, with MMA-Sim's licence notice, and compares it with `mc_eval` on the cases of
`scripts/fp8_cases.py`. MMA-Sim's code (which evaluates in PyTorch `float64`) is neither run nor
vendored. Each operand is normalized with its own format's subnormal exponent, as MMA-Sim's
`frexp_and_normalize` does, so the comparison also covers mixed formats, which the MATLAB model
does not have.

```sh
python3 scripts/mmasim_fp8.py --cases 30000 --seed 1
```

| Inputs | Inner products | Mismatches |
| --- | --- | --- |
| E4M3 × E4M3 FNUZ | 30,000 (5,000 per regime) | 0 |
| E5M2 × E5M2 FNUZ | 30,000 | 0 |
| E4M3 × E5M2 FNUZ | 30,000 | 0 |

All 90,000 outputs are the same binary32 word (the exact transcription has no `−0`, so a zero
would be compared by value; none occurred). The script writes `.lake/mmasim-fp8/report.json` with
the counts and MMA-Sim's commit. MMA-Sim's model of CDNA 3 comes from its authors' experiments,
the Lean model from Khattak, Mikaitis and Graziani's: the two agree on every binary8 inner product
tested.
