# Paper notes

Sources: Khattak, Mikaitis and Graziani, *Accurate Models of AMD Matrix Cores*,
arXiv:2609.14845 (TeX source of v2), and, for clarification only, the authors' MATLAB Tensor
Core v0.6 (`models/MI100MC.m`, `MI210MC.m`, `MI300AMC.m`, `models/tools/Generic_BFMA_TC.m`,
commit `79143bd`). Where the two differ, the formalization follows the paper.

## Modeling choices the paper leaves open

* **NaN.** The GPUs return a NaN with a negative sign; its payload is not characterized, so the
  model reports `Outcome.nan` without a word.
* **Zero signs.** An exact zero `S_acc` gives `+0`. A nonzero `S_acc` that rounds or flushes to
  zero keeps its sign. The paper does not test zero signs.
* **`∞ · 0`.** NaN, as in IEEE 754 and the MATLAB model; the paper does not test it.
* **Inner dimension `k = 0`.** Not an instruction; `dotBits` returns `c` unchanged.
* **CDNA 2 special values.** Products are converted to FP32 and summed with FP32
  additions, so an intermediate overflow is an infinity that propagates with IEEE 754 rules
  (`+∞ + −∞` is NaN). This reproduces the paper's `p₁ = 2^128, p₂ = −p₁` vector.
* **XF32 NaN words** are classified before the significand is truncated.
* **Zero products** take no part in `e_max`, and a group of odd or even FP8 products that is
  entirely zero has no exponent; a group whose nonzero products cancel keeps its exponent, as the
  paper's `c = 2^-20, a₂ = −a₄ = 2^5` vector requires.

## Where the regression suite and the paper's prose differ

* **BF16, `e_{c=0} = −126`, `i = 23`.** For `c = 0, p₁ = −2^-150, p₂ = −2^(-152-i)`, the paper
  reports `d = −2^-149` "for all values of `i ≥ 0`" with `i` from `0` to `23`. At `i = 23`,
  `p₂ = −2^-175` lies at the 25th mantissa bit below `e_max = −150`, and Algorithm 1 truncates it
  while aligning the products; `S_acc = −2^-150` then rounds to `−0`. The MATLAB model also
  truncates the product magnitudes, and the paper's own FP16 interleaving test
  (`±1, 0, ±(2^-24 + 2^-25)` giving `±1`) rules out rounding the negative product down. The suite
  checks `i = 0 … 22` and records `i = 23` separately.
* **The FP16 cancellation test** `c = 2^10, p₁ = −p₂ = 2^35` cannot be formed from FP16 operands
  (products of FP16 values are below `2^32`). The suite runs it with BF16, which the paper says
  behaves identically, and runs `c = 2^4, p₁ = −p₂ = 2^29` with FP16.
* **FP8 operand precision.** FP8 products carry at most six significant bits, so the FP8
  vectors that place `2^-24 + 2^(-24-i)` in a product are run for the values FP8 operands can
  form (`i = 1, 2`); the same values in `c` are run for `i = 1 … 11`.
* **FP8 `N_FMA`.** The text gives `16`; the feature table gives `8` with odd/even grouping.
  Both describe sixteen products in two groups of eight.
* **FP8 names.** The paper says AMD calls E5M2 `fp8` and E4M3 `bf8`. The AMD intrinsics and the
  MATLAB model's `fpformatinfo` use `fp8` for E4M3 and `bf8` for E5M2. The formalization names
  formats by layout (`e4m3fnuz`, `e5m2fnuz`).
* **XF32 shapes.** The paper names `f32_16x16x8_xf32` and `f32_16x16x4_xf32`; the CDNA 3 k = 4
  XF32 instruction is `32x32x4`. The instruction table lists only `16x16x8`; the arithmetic of
  either is one block of `N_FMA = 4` per element.

## Differences from the MATLAB model

These were found by reading the source and confirmed by running the MATLAB models in GNU Octave
against the Lean model ([differential testing](differential.md)).

* **The RD of `S_acc` is not executed in v0.6.** `Generic_BFMA_TC.m` reads the CDNA 3
  normalization-aware RD flag only if the field `rd_borrow_carry` exists (line 54), but
  `MI300AMC.m` sets `rd_norm_aware` (line 60). The RD at lines 614–623 therefore never runs, and
  `S_acc` keeps 32 mantissa bits until the final RNE. Five of the paper's FP16 vectors that
  depend on this step give a different result in the shipped model, for example
  `c = 2 − 2^-22, p₁ = 2^-22, p₂ = 2^-23 + 2^-32`, where the hardware (and the Lean model) give
  `2` and the MATLAB model gives `2 + 2^-22`. With the field set, all five agree.
* **Subnormal-aware normalization.** With the RD enabled, the model keeps the leading 32 bits
  of the integer `S_acc`. Below `2^-126` that is 32 mantissa bits relative to `−126`, while the
  paper's hardware results require 31. Two of the paper's BF16 vectors differ:
  `c = 2^-127 − 2^-140, p₁ + ⋯ = 2^-140 + 2^-150 + 2^-158` (hardware `2^-127`, MATLAB
  `2^-127 + 2^-149`) and `c = 0, p₁ = 2^-150, p₂ = 2^-158` (hardware `0`, MATLAB `2^-149`).
* **Sign of a product overflow.** When products reach `2^128` on one side only, the model returns
  `max(prd)*Inf` (line 112): the sign of the largest product, not of the overflowing one, and NaN
  when the largest product is zero. The paper reports `±∞` for `|p₁| ≥ 2^128` with the sign of
  `p₁`.
* **NaN `c` with an overflowing product** is replaced by `±∞` (lines 106–114 do not test
  `isnan(c)`), so a NaN produced by an earlier block of a chained inner product is lost.
* **CDNA 2 BF16 group size.** `MI210MC.m` uses `fma = 4` for every BF16 instruction; the paper
  reports a group size of `2` without the `_1k` suffix. The formalization has both
  (`cdna2BF16`, `cdna2BF16_1k`), and the differential test runs the MATLAB model with each.
* **FP8 parameters by name.** `GEMM.m` maps the name `fp8` to E5M2 parameters while
  `fpformatinfo` maps `fp8` to E4M3.
* **Mixed FP8 formats.** The MATLAB model takes one input format for `a` and `b`, so mixed
  E4M3 × E5M2 blocks are not compared.

## Running the MATLAB models in GNU Octave

The paper states that the models also run in GNU Octave. Four differences between Octave and
MATLAB affect `Generic_BFMA_TC.m`; the differential test supplies MATLAB's behavior through
small functions on Octave's load path (`scripts/matlab/shims`), without changing the model files:

* `string` (used to hold the aligned bit strings of the CDNA 1 accumulator) does not exist;
* `fma` (used for every CDNA 2 addition) does not exist;
* `bitshift` by 64 or more bits reduces the shift count modulo the word width instead of giving
  zero, which reinserts a fully shifted-out `s_c` into the sum on CDNA 3;
* `dot` of two empty vectors of different shapes is an error instead of `0`, which occurs when
  every product of a block is zero.
