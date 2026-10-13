# Differential testing against the MATLAB models

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
