# Ozaki schemes on the Tensor Core and matrix core models

This Lean project formalizes the Ozaki schemes for emulating a high-precision matrix product on a
low-precision matrix multiplier, following a set of bit-precise Z3 models of the schemes (the "Z3
models" below):

* **Ozaki-I** (Ozaki, Ogita, Oishi and Rump, 2012): error-free slicing into small integers, exact
  slice products on the matrix multiplier, and recombination;
* **Ozaki-II** (Ozaki, Uchino and Imamura, 2025): scaling to integers, one product on the matrix
  multiplier per modulus, and Chinese-remainder reconstruction;
* **ADP and ESC** (Schwarz et al., NVIDIA, arXiv:2511.13778): Ozaki-I on INT8 matrix multipliers, with the
  unsigned slice encoding and the exponent span capacity.

The Z3 models take the matrix multiplier to have fp16 inputs and binary32 round-to-nearest
additions. Here the matrix multiplier is a hardware model of this repository: the NVIDIA Tensor Core model of
[`TensorCore`](../../tensor-core/README.md) and the AMD matrix-core model of [`MatrixCore`](../../matrix-core/README.md).
The scheme itself is proved once, for any matrix multiplier, and each hardware model is shown to
satisfy what the scheme needs. Every labeled check of the three Z3 models has a Lean theorem or a
kernel-checked test, except the ones listed under [what is not proved](THEOREMS.md#not-proved).

Beyond the Z3 models:

* **Long dot products.** Split-K (chunks of the inner dimension, each an exact call to the matrix
  multiplier, added exactly) lifts the limit `k · 2^(2b) ≤ 2^24` of the exactness bound, so every
  result holds for every `k`.
* **FP64 emulation** on fp16, bf16 and tf32 Tensor Cores and on AMD matrix cores: Ozaki-I and
  Ozaki-II on binary64 inputs, with binary64 error bounds and correctly rounded binary64 results.
* **Correct rounding.** All three schemes have a version that returns the round to nearest even of
  the exact product for every input on which the matrix multiplier is exact ([below](#correct-rounding)).
* **IEEE special values.** `±Inf` on overflow, NaN and infinite inputs, and signed zeros, for every
  correctly rounded scheme, native GEMM, plain Ozaki-I and Ozaki-II, and the ADP routine, whose
  Inf and NaN results match the Z3 model's.
* **One rounding on both vendors.** Every scheme rounds with IEEE's round to nearest even;
  TensorCore's and MatrixCore's own roundings are proved to compute the same values on their ranges.
* **Fixed-width integer arithmetic.** Each correctly rounded scheme is also one integer function
  from `(significand, exponent)` inputs, with one theorem bounding every register; no width depends
  on the inputs' exponents.
* **What the hardware semantics give.** The exact condition for a call to the matrix multiplier,
  cancellation included, the two-pass recovery of full block FMAs, and the cheapest exact choice of slices, chunks
  and passes on each GPU.
* **Sharper error bounds**: an entrywise Ozaki-I bound, different slice counts per matrix,
  Abdelfattah et al.'s accumulation by levels, Ozaki-II's truncation bound without its cross term,
  Uchino et al.'s binary64 CRT reconstruction, and Jeannerod–Rump's `k·u` for native dot products
  in any summation order.

[What is proven](THEOREMS.md) · [Tests](tests/README.md) · [Examples](examples/README.md)

## Build and run

`ozaki/` is a standalone Lake project that requires the two models by path (`../tensor-core` and `../matrix-core`);
all three use Lean 4.33.1. From this directory:

```sh
lake build
lake env lean examples/TensorCore.lean
lake env lean examples/MatrixCore.lean
python3 scripts/check.py
```

`lake build` builds the three libraries and the two test libraries, which check the Z3 models'
recorded outputs and an exact-arithmetic oracle by kernel evaluation, and audit the axioms.
`scripts/check.py` also checks the examples and every Lean block in the documentation.

**Independent re-check.** [`scripts/conleche.sh`](scripts/conleche.sh) exports every module of
`TensorCore`, `MatrixCore` and the Ozaki libraries, with their tests, and re-checks every
declaration with [con-leche](https://github.com/leanprover/con-leche), an external Lean checker
proved never to accept a proof of `False`. On 2026-10-13, con-leche at revision `3b37939`, in
`--verified` mode, accepted every declaration: 168,810 for `TensorCore` and its tests, 166,049 for
`MatrixCore` and its tests, 175,851 for the Ozaki core with the Tensor Core side and its tests,
and 171,967 with the AMD side (each count includes Lean's own library). Lean does not record
`example`s as declarations, so the kernel-checked regression examples are checked by Lean's kernel
only; every named theorem, including the kernel-computed tables, is re-checked. The test
modules evaluate large terms in the kernel, the largest for about two minutes each; a bare
`lake build` runs them in parallel, which can exhaust memory (it did on a 24 GB machine), so
`check.py` builds them one at a time.

## Layout

| Import / directory | What belongs here |
| --- | --- |
| [`Ozaki`](Ozaki.lean) | The schemes for any matrix multiplier: slicing, recombination, CRT reconstruction and their error bounds (including the sharpest published ones that apply), ADP's slice encodings, ESC, fixed point and Grade-A bound, native GEMM's bounds, split-K, correct rounding (Ziv's rounding test, the exact fallback, the bound that counts only nonzero positions), fixed-width integer forms of every correctly rounded scheme with one theorem bounding every register, a hardware-independent IEEE round to nearest for any binary format, IEEE special values and signed zeros, and the Z3 models' parameters. It imports only Lean's standard library. |
| [`OzakiTC`](OzakiTC.lean) | The NVIDIA instantiation: exact integer blocks and chains on the Tensor Core model, the exact condition with cancellation, the matrix multiplier on all eight GPU variants, split-K, the two-pass recovery, the choice of slices, chunks and passes, IEEE rounding and TensorCore's agreement with it, the σ-trick, both schemes in binary32 and FP64, the INT8 matrix multiplier and its semantics, the full ADP routine with its guardrail, zero policies, Z3 test-level checks and special values, and every correctly rounded version. |
| [`OzakiMC`](OzakiMC.lean) | The AMD instantiation: exact integer blocks, chains and inner products on the CDNA 1, 2 and 3 models, the exact condition per architecture, the matrix multiplier on the SFMA, fp16, bf16 and XF32 variants, split-K, the choice of slices and chunks, binary32 rounding (proved IEEE's), both schemes in binary32 and FP64, and their correctly rounded, fixed-width and special-value versions. |
| [`tests/`](tests/README.md) | Regression tests against the Z3 models' outputs and an exact-fraction oracle, and the axiom audits. |
| [`examples/`](examples/README.md) | Worked examples. |
| [`data/`](data/) | The Z3 models' inputs and outputs, and correctly rounded reference products, as binary32 and binary64 words. |
| [`scripts/`](scripts/) | `check.py` (validation); `z3_reference.py`, `z3_adp_reference.py`, `z3_adp_labels.py`, `z3_adp_zero_policies.py`, `z3_specials_reference.py` and `correct_reference.py` (record `data/`); `fallback_sim.py` and `tile_sim.py` (simulated costs of correct rounding, per entry and per tile); `targeted_validation.py` with `targeted/` (the test suite for real hardware). |

`TensorCore` and `MatrixCore` cannot be imported into the same file: both declare the `ℕ ℤ ℚ`
notation and their own arithmetic. `Ozaki` therefore uses Lean's types directly, so it can be
imported beside either, and `OzakiTC` and `OzakiMC` are separate libraries.

## The scheme for one output entry

Every entry of `C = AB` is a dot product `x · y` of a row of `A` and a column of `B`, and the
schemes treat each entry separately. A `MatrixMultiplier` is a function from two integer vectors to the
value the hardware returns; `MatrixMultiplier.ExactOn b bound` says it returns `Σ xᵢyᵢ` exactly for
entries of magnitude at most `2^b` whose products total at most `bound`, the exactness bound.

* Ozaki-I splits `x` into `s` slices `2^gₜ qₜ` of integers with `|qₜ,ᵢ| ≤ 2^b`, multiplies the
  `s(s+1)/2` pairs with `t + u < s`, and adds the scaled products. With an exact matrix multiplier the error
  is exactly `r · y + Σₜ 2^gₜ (qₜ · r'ₛ₋ₜ)`, which gives `|x · y − C| ≤ (s + 1) k 2^(E + F − s(b+1))`
  before the additions (`Ozaki.exactTerms_error`).
* Ozaki-II truncates `x` and `y` to `P`-bit integers `a` and `c`, computes `a · c` modulo each
  modulus on the matrix multiplier, reconstructs it exactly when `2 k 2^(2P) < M` (`Ozaki.crt_eq`), and
  rounds once. The only approximation is the truncation (`Ozaki.truncProduct_error`).
* ADP converts each row and column to `W`-bit fixed point (`W = 53 + ESC + 1`), cuts the integers
  into byte slices, multiplies all `s²` slice pairs on an INT8 matrix multiplier, recombines exactly and rounds
  once to binary64. For normal or zero entries, with full fidelity on the largest product, the
  result meets the paper's Grade-A bound `|C − x · y| ≤ (4k + 1) 2^-53 Σ|xᵢyᵢ|` plus an underflow
  term (`Ozaki.ADP.emulated_gradeA`). Subnormal entries can break it (see the findings).

## Long dot products and FP64

A call to the matrix multiplier is exact while its products total at most `2^24`, the exactness
bound, which allows only four terms of `11`-bit slices. Split-K cuts the inner dimension into chunks of `2^(24 − 2b)` terms (four for
`11`-bit slices, `256` for `8`-bit), runs each chunk on the matrix multiplier, and adds the integer chunk
results exactly; it is exact for every length (`Ozaki.chunked_exactOn`). On the Tensor Core model
the chunk results can be accumulated in `TensorCore`'s fixed-width register, exact while the products
total less than `2^63` in a 64-bit register (`Ozaki.TC.tcSplitKReg_exactOn`).

With split-K:

* Ozaki-I's binary32 error bound holds for every `k` (`Ozaki.TC.tcOzaki1L_error`,
  `Ozaki.MC.mcOzaki1L_error`);
* **FP64 emulation**: Ozaki-I with binary64 recombination has the same bound with `u = 2^-53`
  (`Ozaki.TC.tcOzaki1D_error`, `Ozaki.MC.mcOzaki1D_error`), and Ozaki-I and Ozaki-II return the
  correctly rounded binary64 product for binary64 inputs of any length on every variant whose matrix multiplier is exact
  (`Ozaki.TC.tcOzaki1CRD_eq`, `Ozaki.TC.tcOzaki2CRD_eq`, `Ozaki.MC.mcOzaki1CRD_eq`,
  `Ozaki.MC.mcOzaki2CRD_eq`), for example on V100 fp16 with `11`-bit slices and on A100 bf16 with
  `8`-bit slices (`Ozaki.TC.v100_fp64CR`, `Ozaki.TC.a100BF16_fp64CR`).

Every working-precision rounding is `Ozaki.roundRNE`, a hardware-independent IEEE round to nearest
even proved for any binary format (`Ozaki.roundRNE_nearest`), with IEEE overflow: values that
round to at most the largest finite value succeed. Its instances are `Ozaki.rne32Q` and
`Ozaki.rne64`. The hardware libraries' own roundings compute the same values:

* TensorCore's binary32 and binary64 round to nearest use the same exponent, grid and
  ties-to-even step (`Ozaki.TC.signedRounded_eq_rneU`, `Ozaki.TC.binarySignedRounded_eq_rneU`),
  so they agree with IEEE's on every input up to the largest finite value
  (`Ozaki.TC.round32ValueTC_eq`, `Ozaki.TC.fp64RoundTC_eq`). They differ only above it, where they
  return nothing and IEEE rounds values within half an ulp down to the largest finite value.
* MatrixCore's binary32 round to nearest is IEEE's on every input
  (`Ozaki.MC.round32Value_eq_rne32Q`).

So the NVIDIA and AMD instantiations round with literally the same function, and the correctly
rounded versions return the same value on both for the same inputs.

## Correct rounding

Each scheme holds an exact value `H` before its last rounding (the slice products added exactly,
the reconstructed product, the recombined fixed-point product) and a proved bound
`B ≥ |x · y − H|`. If `H − B` and `H + B` round to the same value, so does `x · y`, which lies
between them: rounding to nearest is monotone, which Lean proves from the nearest-value property
alone (`Ozaki.round_monotone`). Otherwise the next configuration is tried, more slices or moduli,
and then an exact fallback (`Ozaki.roundingTest_eq`). The structure is TC-EFT's guarded fast path
with an exact fallback; the test itself is Ziv's rounding test.

There are two kinds of correctly rounded versions, and the difference matters:

* `Ozaki.ozaki1CR_eq`, `Ozaki.ozaki2CR_eq`, `Ozaki.TC.adpCR_eq` fall back to the exact rational
  `x · y`, computed off the matrix multiplier. Their theorems would hold for a scheme that never
  calls the matrix multiplier; their content is that the enclosures computed on it are sound.
* `Ozaki.ozaki1CRE_eq`, `Ozaki.ozaki2CRE_eq` and their hardware instances (`*CRE`, `*CRL`, `*CRD`)
  take the exact fallback on the matrix multiplier: Ozaki-I with all `s²` slice products is exact once nothing is
  left over (`Ozaki.ozaki1Full_eq`), and inputs on a grid `2^m` leave nothing over after enough
  slices (`Ozaki.split_residual_zero`): `24` slices of `11` bits for binary32, `175` for binary64.
  Every product on the matrix multiplier, including those of the exact fallback, then runs on
  Tensor Core or matrix-core block FMAs. The slicing and the rounding test are exact arithmetic in
  the proofs.

**The rounding test needs only a fixed number of bits.** Correct rounding has to decide only on which side of
the nearest rounding boundary `x · y` lies, so the sum of the slice products need not be exact:
round each scaled product down to `W` bits below the largest possible product, add them exactly,
and add the truncation loss to `B` (`Ozaki.ozaki1CRW_eq`). The truncated sum needs
`W + log₂ (s(s+1)/2 · (k + 1)) + 1` bits whatever the inputs' exponents
(`Ozaki.ozaki1Truncated_register`): with `W = 96`, up to seven `11`-bit slices and `k ≤ 2^14`, under
two 64-bit words, for binary32 and FP64 alike (`Ozaki.TC.tcOzaki1CRDW_eq`,
`Ozaki.MC.mcOzaki1CRDW_eq`, `Ozaki.TC.v100_fp64CRW`).

**The exact fallback needs only signs.** Added exactly, the slice products of
inputs spanning the whole exponent range take about `580` bits for binary32
(`Ozaki.exactTerms_sum_register32`). Rounding needs less: only the sign of the sum against a few
rounding boundaries. A top-down summation decides it. In a `W`-bit register it adds the parts of
the terms that fall within `W` bits below the current leading position, carries the sum to the
next lower range only when cancellation has left it small, jumps over empty gaps, and visits at
most `n · bitlen(max |v|) + 1` ranges whatever the exponents (`Ozaki.roundSumJ_eq`, `Ozaki.rangesJ_le`). The final round to nearest even is a few
integer comparisons (`Ozaki.roundExact_eq`), and the rounding test's truncated sum is held in
a two's-complement register that never wraps (`Ozaki.fixedSum_eq`, `Ozaki.ozaki1TestB_register`).

**Each scheme is one integer function.** From `(significand, exponent)` inputs through integer
slicing or conversion, the matrix multiplier, the integer rounding test, the exact fallback and
the final rounding,
correctly rounded Ozaki-I, Ozaki-II and ADP-style slicing are integer functions proved correctly
rounded, with signed-zero versions (`Ozaki.ozaki1CRI_eq`, `Ozaki.ozaki2CRJ_eq`,
`Ozaki.TC.adpCRJ_eq`, `Ozaki.ozaki1CRIS_eq`). For Ozaki-II and ADP the bound of the rounding test is
itself an integer built from the scaled integers the matrix multiplier already multiplies (`Ozaki.enclosureTestB_eq`).

**One theorem bounds every register.** A version of each pipeline with overflow checks guards
every integer it computes, data against `2^R` and exponents and counters against `2^X`, and under explicit formulas
returns exactly what the unchecked pipeline returns (`Ozaki.ozaki1CRIC_eq`,
`Ozaki.ozaki2CRJC_eq`, `Ozaki.TC.adpCRJC_eq`):

| Pipeline | `R` | `X` |
| --- | --- | --- |
| Ozaki-I, FP64 (`11`-bit slices, up to `175`, `k ≤ 2^20`) | 263 | 17 |
| Ozaki-I, binary32 (up to `24` slices) | 207 | 15 |
| Ozaki-II, FP64 (twelve moduli up to `4096`, `P ≤ 69`) | 263 | 17 |
| Ozaki-II, binary32 (six moduli) | 161 | 15 |
| ADP-style, FP64 (up to `11` slices of width up to `81`) | 259 | 17 |

The guards cover the internals of the matrix multipliers too (split-K's partial sums, the 32-bit
register of the INT8 matrix multiplier, proved never to wrap) and the signed-zero pipelines. Kernel tests show the guards fail
at narrower widths. Comparisons, bit lengths and shift amounts are not guarded
([THEOREMS.md](THEOREMS.md#not-proved)).

**How often the fallback runs, measured.** A CPU simulation of the schemes with exact arithmetic
([`scripts/fallback_sim.py`](scripts/fallback_sim.py), [`data/fallback-sim.json`](data/fallback-sim.json))
at `k` up to `4096`: for binary64 output and uniform inputs, the rounding test succeeds on 98–99 % of entries
(90–96 % with exponents spread over `2^±8`) and saves about 40 % of the products on the matrix
multiplier against always taking the exact fallback; the slice counts must grow with `k` (at
`k ≥ 256` the test with five `11`-bit slices almost never succeeds);
products with condition number `10^6` or more need a deeper list of slice counts (from 100 % to
about 2 % fallback); with the bound that counts only nonzero positions, the test succeeds at once
on entries with no shared nonzero; and low-precision inputs are cheaper on the exact fallback
directly. Ozaki-II decides almost every entry with the rounding test at twelve moduli. These are
model costs on chosen distributions, not GPU time. Both rules
are proved: slice counts chosen for precision `t + ⌈log₂ k⌉` remove the factor `k` from the bound of
the first test (`Ozaki.ozaki1Bound_le_cr`), which brings binary64 fallbacks to about `0 %` on
well-conditioned data in the rerun; and taking the exact fallback first when it is cheaper
never costs more (`Ozaki.ozaki1CRA_cost_le`).

**Per tile, measured.** A GEMM computes each slice product for a whole tile at once, so what the
early exit saves also depends on scheduling. A second simulation
([`scripts/tile_sim.py`](scripts/tile_sim.py), [`data/tile-sim.json`](data/tile-sim.json)) runs full
`256 × 256` GEMMs with binary64 output at `k = 256, 1024, 4096`, about two million entries, under
three schedules. Scheduling per entry gives the lower bound. Uniform scheduling per tile gives a
whole `16 × 8` tile the next refinement if the test fails for any of its entries. Compaction packs
the entries whose test failed into new tiles, either ideally or by gathering rows and columns, which
accounts for the lost reuse of data. Uniform per-tile scheduling keeps 0–43 % of the per-entry
saving with the plain list of slice counts, 48–95 % (median 60 %) with the `k`-dependent rule and
48–100 % (median 86 %) for Ozaki-II. Gathering keeps a median of 93 % with the `k`-dependent rule
and 94 % for Ozaki-II. Under heavy cancellation (condition number `10^6`), uniform per-tile Ozaki-I
costs 8 % more than always taking the exact fallback. The work off the matrix multiplier is
0.24–2.5 % of its multiply-adds for Ozaki-I and 3.5–9.6 % for Ozaki-II, under assumed weights per
operation. Every interval and every result of a successful test was checked against the exact
product. These are instruction counts, not GPU time.

**A test suite for real hardware.** [`scripts/targeted_validation.py`](scripts/targeted_validation.py)
and the Lean files in [`scripts/targeted/`](scripts/targeted/) produce
[`data/targeted-validation.json`](data/targeted-validation.json) (summarized in
[`data/targeted-validation.md`](data/targeted-validation.md)). It holds 140 cases, 85 for NVIDIA and
55 for AMD, whose predicted outputs distinguish the models' numerical features: full block FMAs,
cancellation, two passes, non-monotonicity, minimum alignment exponents, signed zeros, subnormals,
TF32 and padding bits. Each case gives the input words, a suggested instruction, the
predicted output word and what a mismatch would mean. Of the cases, 56 come from theorems, whose
values the script re-checks. The suite has not yet been run on hardware.

**The rounding test succeeds at once on exact zeros.** The slicing bound counts only the positions
where both entries are nonzero, so on an entry whose products are all zero, such as sparse rows and
columns with no shared nonzero, the first test succeeds (`Ozaki.exactTerms_error_overlap`,
`Ozaki.ozaki1CREZ_zero`). The count costs one extra dot product on the matrix multiplier per entry.

What the rounding test itself achieves is a separate theorem: on the enclosure from the matrix
multiplier the test succeeds whenever `x · y − 2B` and `x · y + 2B` round to the same value, in particular whenever `x · y` lies
more than `2B` from every rounding boundary (`Ozaki.roundEnclosure_of_margin`,
`Ozaki.ozaki1Enclosure_succeeds`). On the test matrices:

* Ozaki-I decides every Z3 entry with four slices and all but two with three;
* Ozaki-II with the Z3 models' four moduli (`P = 22`) decides none, five moduli decide 21 of 32,
  six decide all;
* ADP decides every entry at the configuration its own ESC rule picks for the two random binary64
  cases (`8` and `11` slices), and fewer with fewer slices.

Every version rounds with IEEE's round to nearest even, on both vendors. The rounding test runs on
exact values, never on a Tensor Core, whose output is not monotone in its inputs (TC-EFT's
non-monotonicity theorems).

**Signed zeros.** IEEE formats have two zeros, rationals one. The specification `Ozaki.crSigned`
is IEEE's: a nonzero exact sum that rounds to zero keeps its sign, and an exact zero is `−0` only
when every product is `−0`. The signed rounding test takes the sign of a zero result from the
enclosure when it lies on one side of zero, and otherwise from the exact fallback; correctly
rounded Ozaki-I with a truncated sum returns `crSigned` on both vendors, in binary32 and FP64
(`Ozaki.ozaki1CRWS_eq`, `Ozaki.TC.tcOzaki1CRDS_eq`, `Ozaki.MC.mcOzaki1CRDS_eq`).

**IEEE special values.** On IEEE data (finite with a sign bit, `±Inf`, NaN) the specification
`Ozaki.dotIEEE` is the exact dot product rounded once: NaN for a NaN input, `Inf · 0` or opposite
infinities, `±Inf` for an infinite product or an overflowing sum, and IEEE's zero sign. IEEE 754
leaves a dot product's order and precision to the implementation; this is the "exact, then round
once" reading. A wrapper handles the special inputs and takes the sign of an overflowing sum from
the integer terms of the exact fallback; with it every correctly rounded scheme meets the specification for
every input (`Ozaki.crIEEE_eq`, `Ozaki.TC.tcOzaki1CRDI_eq`, `Ozaki.MC.mcOzaki2CRDI_eq` and the
others in [THEOREMS.md](THEOREMS.md#ieee-rounding-special-values-and-signed-zeros)). Native GEMM and
plain Ozaki-I and Ozaki-II run with IEEE operations and agree with the rational schemes whenever
those are finite (`Ozaki.nativeDotIEEE_fin`, `Ozaki.ozaki1IEEE_fin`).

## On the Tensor Core model

The Tensor Core aligns every product to the largest exponent of the block FMA, keeps `F` bits below it
(`F = 23` on V100, `24` on A100, `25` on H100), adds exactly, and truncates to binary32 (the
exactness theorems take a binary32 block output, `IntExact.output`). For
integer operands this loses nothing when `2b ≤ F` and `|c| + Σ|aᵢbᵢ| ≤ 2^24`
(`Ozaki.TC.evalBlock_int`), also across chained block FMAs (`Ozaki.TC.runBlocks_int`). With fp16 or
tf32 operands `b = 11`, with bf16 `b = 8`, and every FP16, BF16 and TF32 variant satisfies `2b ≤ F`
(`Ozaki.TC.v100_exactOn` and seven more). The Z3 models' `4 × 4` configuration therefore runs
exactly on V100: four `11`-bit slices for Ozaki-I, moduli `{4096, 4095, 4093, 4091}` with `P = 22`
for Ozaki-II (`Ozaki.TC.v100_ozaki1_z3`, `Ozaki.TC.v100_ozaki2_z3`). On the Z3 models' own test
matrices the Lean pipelines return the same binary32 words as the Z3 models on all six fp16 and
tf32 variants ([tests](tests/README.md)).

What changes from the Z3 models:

* **The exactness bound comes from the output, not the accumulator.** The Z3 models' matrix
  multiplier rounds every partial sum to binary32; the Tensor Core adds a block FMA exactly and
  rounds once. On the Tensor Core only the final sum must fit binary32: an A100 block FMA is exact on products whose binary32 running sum
  is not (`Ozaki.TC.a100_exact_where_binary32_is_not`).
* **Full block FMAs on A100 and H100 exceed the exactness bound.** With `11`-bit slices,
  `k · 2^22 ≤ 2^24` allows four products; A100 and H100 block FMAs take eight and sixteen, and seven products `2047²`
  already lose a bit (`Ozaki.TC.a100_full_blockFMA`). Split-K with chunks of four, `10`-bit slices,
  or at most four nonzero products per block FMA restore exactness.
* **Two passes recover a full block FMA exactly (a TC-EFT technique).** Run the block FMA once from
  `c = 0`, giving `D1`, the truncation of the exact sum `S`; run it again from `c = −D1`. Because
  `c` takes part in alignment (the mechanism behind TC-EFT's non-monotonicity), the second pass is
  exact as long as `|D1| ≤ 2^(F+1)`, and it returns `S − D1`, so `D1 + D2 = S`
  (`Ozaki.TC.twoPass_exact`). `F` grows by one bit each time the FMA size doubles, so a full
  block FMA of `11`-bit products always fits: `8 · 2^22 = 2^25` on A100, `16 · 2^22 = 2^26` on H100.
  The two-pass matrix multiplier is exact for every length on all eight variants, with full block
  FMAs of `11`-bit
  slices on fp16 and tf32 and `8`-bit slices on bf16 (`Ozaki.TC.a100F16_exactOn2`,
  `Ozaki.TC.h100F16_exactOn2` and six more). It is the matrix-instruction analogue of TwoProdFMA.
  On H100 it needs half the Tensor Core calls of `11`-bit split-K with chunks of four, but
  `10`-bit slices that fill the block FMA are cheaper still: one extra slice costs less than a second
  pass (below).
* **The exact condition, with cancellation.** A block of `b`-bit integers with `2b ≤ F` and
  `|c| < 2^(F+1)` returns the exact sum whenever that sum is a binary32 value, however large the
  products, and the condition on the sum is necessary (`Ozaki.TC.evalBlock_cancel`,
  `Ozaki.TC.evalBlock_exact_needs_binary32`): eight products `±2^22` on A100 return `0`. It is
  the precise boundary, not a scheduling rule, since the sums are known only after computing them.
* **The choice of slices, chunks and passes.** Every candidate configuration on every variant is
  proved exact for every length, and a cost in block FMAs picks the cheapest
  (`Ozaki.TC.candidates_exact`, `Ozaki.TC.h100F16_best`). Wherever a block FMA holds more than four
  products, `10`-bit slices that fill it win: on H100 fp16, FP64 at `k = 1024`, 1344 blocks
  against 3840 for `11`-bit chunks of four and 1920 for two passes. The conservative rule allows
  this configuration too; what the model adds is the proof, and the evidence that two passes do
  not pay by this count. The count is of model instructions, not time.
* **Ozaki-II against Ozaki-I.** The same choice for Ozaki-II (the fewest moduli that meet the same
  accuracy target, `Ozaki.moduliFor_spec`) makes it `1.4×` to `2×` cheaper than Ozaki-I for FP64 on
  every variant, in block FMAs (`Ozaki.TC.h100F16_best2`), and `1.75×` to `2.25×` with correct
  rounding's margin included in both (`Ozaki.TC.h100F16_bestCR`); it leaves out Ozaki-II's
  reconstruction with integers of about `2P + log₂ k` bits.
* **The σ-trick.** For a binary32 `a` with `|a| ≤ 2^(g+b)`, `b ≤ 21` and `−149 ≤ g ≤ 104`,
  `fl(fl(a + σ) − σ)` with IEEE binary32 addition is `a` rounded to the grid `2^g` and
  `fl(a − hi)` is exact
  (`Ozaki.TC.sigma_split`); the remainder is exact for every grid
  (`Ozaki.TC.finiteValue32_sub_round`). The Z3 lemma covers `|a| ≤ 1`. A split computed with
  binary32 operations equals the scheme's split when every grid lies in `[−149, 104]`
  (`Ozaki.TC.splitFrom32_eq`). Outside that range σ overflows (above about `2^115`) or the grid
  falls below binary32's (the long exact fallbacks reach grids far below `2^-149`). Slicing with
  integer operations covers every grid: on significands and exponents it shifts, divides with
  round-half-even and compares, and it equals the scheme's split for every vector and grid
  (`Ozaki.splitInt_eq`). Its coefficients have at most `b + 1` bits, its significands never grow,
  and no division needs more than `p + 2` bits (`Ozaki.splitInt_width`,
  `Ozaki.split_binary32_int`, `Ozaki.split_binary64_int`).
* **INT8 matrix multipliers as fixed-width registers.** ADP's matrix multiplier is a 32-bit
  wrapping accumulator
  (`TensorCore`'s `machineAccumulate 32`) over exact integer products. Its result is the exact sum
  reduced modulo `2^32`, so it does not depend on the accumulation order, and a saturating
  register agrees with it on ADP's operands (`Ozaki.TC.int8Dot_any_order`,
  `Ozaki.TC.int8_wrap_sat_exact`); it is not validated against INT8 hardware. It is exact on byte
  operands within `2^31` and wraps at 16 bits
  (`Ozaki.TC.int8Dot_bytes`, `Ozaki.TC.int8Dot_16_wraps`), and Ozaki-I on it is one binary64
  rounding of the exact fixed-point product (`Ozaki.TC.int8Recombine_eq`, `Ozaki.TC.int8Ozaki_eq`).
* **The whole ADP routine.** `Ozaki.TC.adp` follows the Z3 model `adp.py` step by step: scan for
  non-finite inputs, matrix ESC, width, slice count, the speed heuristic, then emulation or native
  binary64. Whenever it returns values on normal or zero entries of matching shapes with
  `k · 2^14 < 2^31`, every entry meets Grade A on the emulated path and the native `γₖ` bound
  otherwise (`Ozaki.TC.adp_accuracy`). On the five cases recorded from the Z3 model it takes the
  same path and returns the same values, and every test-level check of the Z3 model that concerns
  ADP itself is a theorem or a kernel-checked test on the model's own inputs: decoding, the
  paper's remap example, the three slice encodings agreeing, ESC with block size `1`, the valid
  paths, emergent overflow, subnormal inputs and the zero policies (`Ozaki.TC.encodings_agree`,
  `Ozaki.TC.adp_finite_path`, `Ozaki.TC.emulEntry_none_iff`, and
  [THEOREMS.md](THEOREMS.md#the-adp-pipeline-on-the-int8-matrix-multiplier)). It returns values for finite inputs of matching shapes
  whose products are within range (`Ozaki.TC.adp_isSome`).
* **A guardrail for subnormal inputs.** `Ozaki.TC.adpSafe` adds one test to the routine: an input
  with a nonzero entry below `2^-1022` goes to native FP64. With it, Grade A holds with no
  normality hypothesis (`Ozaki.TC.adpSafe_accuracy`), the routine returns values for every finite
  input in range (`Ozaki.TC.adpSafe_isSome`), and on the five recorded Z3 cases it returns what
  `adp` returns.
* **Correctly rounded ADP-style slicing.** `adpCR` is correctly rounded fixed-point Ozaki-I on the
  INT8 matrix multiplier with given `(s, W)`, not the ADP routine with its ESC and guardrails; its last resort
  is exact rational arithmetic. `adpCRE` runs every product on the INT8 matrix multiplier, split into
  chunks so that INT32 never wraps, including its exact fallback (all slice products of `6`-bit
  slices), and
  is correctly rounded for binary64 inputs of any length (`Ozaki.TC.adpCRE_eq`).

## On the matrix-core model

A CDNA block computes `S_acc` by one of three configurations and rounds it once to binary32 with
round to nearest: CDNA 1 sums exactly, CDNA 2 rounds pairwise sums of binary32 products in groups and
flushes subnormals to zero, and CDNA 3 aligns the products to `24` mantissa bits and adds `c` late with
two rounding-down steps. For integer operands and an integer `c` with `|c| + Σ|aᵢbᵢ| ≤ 2^24`, all
three return `c + Σ aᵢbᵢ` exactly (`Ozaki.MC.evalBlock_int`), across chained blocks and inner
products of any length (`Ozaki.MC.runBlocks_int`, `Ozaki.MC.dotBits_int`). The matrix multiplier is
exact on the binary32 SFMA (`b ≤ 24`), CDNA 1, 2 and 3 fp16 and CDNA 3 XF32 (`b ≤ 11`), and the
bf16 variants (`b ≤ 8`) (`Ozaki.MC.cdna3F16_exactMultiplier` and the others in
[`OzakiMC/Models.lean`](OzakiMC/Models.lean)); CDNA 3's fp8 variants are not covered.

On the Z3 models' test matrices, every variant with `11`-bit slices returns the Z3 models' binary32
words for both schemes ([tests](tests/README.md)). The binary32 SFMA, which rounds after every
product, is the Z3 models' matrix multiplier: binary32 products accumulated with round to nearest.

What the model shows:

* **The same exactness bound as on the Tensor Core.** Alignment never loses bits of integer products within
  `2^24`; the bound is set by the binary32 output.
* **bf16 variants need `8`-bit slices**: bf16 holds `256` but not `2047`
  (`Ozaki.MC.bfloat16_holds_256`).
* **A full CDNA 3 block FMA of `11`-bit products exceeds the exactness bound**: seven products `2047²` total
  `29331463`, which the final round to nearest returns as `29331464`, where the Tensor Core,
  which truncates, returns `29331462` (`Ozaki.MC.cdna3F16_full_blockFMA`).
* **The fp16 variants are exact where the SFMA is not**: products `5 × 2047², 1, −2 × 2047²` give the
  exact `12570628` on CDNA 1, 2 and 3 fp16, and `12570626` on the SFMA
  (`Ozaki.MC.fp16_exact_where_sfma_is_not`).
* **CDNA 2 does not round inside an Ozaki block.** Four products of `11`-bit integers total at
  most `2^24`, so every pairwise sum is exact (`Ozaki.MC.pairwiseGroupSum_int`).
* **Cancellation differs by architecture.** CDNA 1 and CDNA 3 return the exact sum whenever every
  product, `c` and the sum are within `2^24`; CDNA 2 also needs every pairwise sum
  within `2^24` (`Ozaki.MC.evalBlock_cancel`, `Ozaki.MC.pairwiseGroupSum_cancel`). On CDNA 3 fp16,
  `10`-bit slices are the cheapest exact configuration (`Ozaki.MC.cdna3F16_best`).
* **Two passes on AMD.** The second pass from `c = −D1` recovers the exact sum on the SFMA (where
  it is TwoProdFMA), CDNA 1 and CDNA 3 (`Ozaki.MC.mcMultiplier2_exactOn`,
  `Ozaki.MC.cdna3F16_twoPass_full_blockFMA`), but not in general on CDNA 2, whose pairwise sums are rounded
  before `c` is added (`Ozaki.MC.cdna2_twoPass_fails`).

## Findings from formalizing

* The Ozaki-I error has a closed form: pairing slice `t` of `x` with the residual of `y` after
  `s − t` slices gives the exact identity behind the bound above, without enumerating the omitted
  slice pairs.
* At `P = 23` the Z3 counterexample to CRT reconstruction is `c = M` itself, whose residues are
  all zero (`Ozaki.crt_fails_at_23`).
* The ESC coarsening theorem holds for every block size, and its funnel bound does not need the
  Z3 query's assumption `e_a + e_b ≤ F` (`Ozaki.ADP.coarseEst_le`, `Ozaki.ADP.funnel`).
* Grade A needs no `u²` term: full fidelity makes the largest product exact, so each product's
  fixed-point error is at most `2^(F−52)`, half what the Z3 query allows (`Ozaki.ADP.term_bound`).
* **ADP's guarantee needs normal inputs.** With a subnormal entry, `x = [2^-1074, 2^-1023 × 7]`
  and `y = [1, −2^-60 × 7]`, the Lean model of ADP takes its emulated path and returns `−2^-1074`
  for a positive exact product, breaking Grade A even with its underflow term; the exponent clamp
  at `−1022` lets `2^F` exceed the dominant product by up to `2^52`. The unmodified Z3 model fails
  its own final-rounding check `[R.2]` on the same input. No guardrail of the routine catches it;
  one more does (`Ozaki.TC.adpSafe`). This concerns the routine as the ADP paper describes it,
  which the paper and the cuBLAS documentation say is accurate for subnormal values too; shipping
  cuBLAS is not modeled, and it passes an independent underflow test (Demmel et al., 2026) by
  detecting the wide range and using its FP64 path, much as `adpSafe` does.
* **ADP's zero policy matters for the result, not only the estimate.** Without the Z3 model's
  `[X.4]` assertion, "skip zeros" returns `0` for a nonzero product for every block size of at
  least `2`, every length in range and every matrix shape, and giving zeros exponent `−1022` fails
  likewise; with block size `1` skipping is safe (`Ozaki.TC.adpPolicy_skip_wrong_shape`,
  `Ozaki.TC.adpPolicy_field0_wrong_shape`). Other rows hide the failure only by raising the matrix
  estimate: every input of an exponent pattern meets Grade A when each factor loses at most about
  `log₂(2k)` bits, and some input breaks it when one factor loses about `log₂(2k + 2)` bits or more,
  leaving about one value between (`Ozaki.TC.adpPolicy_entry_gradeA_loss`,
  `Ozaki.TC.adpPolicy_unmasked_fails_full_left`); the pattern alone does not decide an input.
* Correct rounding is cheap where a scheme already carries margin: the Z3 configuration's fourth
  Ozaki-I slice, which adds nothing at binary32 output precision, lets the rounding test
  succeed on every entry, and with ADP's own ESC choice the test succeeds on every entry of the
  random binary64 tests. Ozaki-II with
  `P = 22` carries no margin: none of its results on the Z3 matrices is correctly rounded.

## Scope

The proofs concern the models. That GPUs behave like them rests on the validation of `TensorCore`
and `MatrixCore`. As in the Z3 models, the CRT residues and reconstruction are exact integer
arithmetic; Ozaki-I's power-of-two rescaling is proved exact when its exponent is in range
(`Ozaki.TC.scaled_slice_product_exact`). Not covered: FP8 variants, and INT8 hardware semantics,
which are out of scope for now on both vendors
([issue #2](https://github.com/pauljiang03/HardwarePrimitives/issues/2)): ADP runs on an idealized INT8
matrix multiplier. [THEOREMS.md](THEOREMS.md#not-proved) lists the rest.
