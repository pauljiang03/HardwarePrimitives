---
title: Correct rounding
description: How Ozaki-I, Ozaki-II and ADP-style slicing return the correctly rounded product for every input - Ziv's rounding test with an exact fallback on the matrix multiplier, fixed-width integer arithmetic with one theorem bounding every register, IEEE special values, and the same results on NVIDIA and AMD.
---

The Ozaki schemes guarantee an error bound, not the correctly rounded result.
Each has a correctly rounded version here: for every input on which the
matrix multiplier is exact, it returns the IEEE round to nearest even of the
exact product `x · y`, the same value on the NVIDIA and AMD models. Every
claim on this page is a Lean theorem using only Lean's standard axioms.

## The method: a rounding test, then an exact fallback

Each scheme holds an exact value `H` before its last rounding and a proven
bound `B ≥ |x · y − H|`:

- **Ozaki-I:** `H` is the sum of the slice products computed so far, and `B`
  bounds what the omitted slice pairs would add.
- **Ozaki-II:** `H` is the reconstructed integer product, and `B` the
  truncation bound.
- **ADP-style slicing:** `H` is the recombined fixed-point product, and `B`
  the fixed-point bound.

Then for each entry:

1. **Rounding test.** If `H − B` and `H + B` round to the same float, so does `x · y`,
   which lies between them. Rounding to nearest is monotone; Lean proves it
   from the nearest-value property alone ([`round_monotone`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Correct.lean#L56),
   [`round_eq_of_enclosure`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Correct.lean#L72)).
2. **Refine.** Otherwise try more slices, or more moduli, which shrinks `B`.
3. **Exact fallback.** Otherwise compute `x · y` exactly, also on the matrix
   multiplier. Ozaki-I
   with all `s²` slice products and enough slices that nothing is left over is
   exact ([`ozaki1Full_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Correct.lean#L473)). Floats lie on a finite grid, so this always
   ends: at most `24` slices of `11` bits for binary32 inputs and `175` for
   binary64 ([`split_residual_zero`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Correct.lean#L418)).

The result is correctly rounded whichever step decides it ([`roundingTest_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Correct.lean#L124),
[`ozaki1CRE_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Correct.lean#L524), [`ozaki2CRE_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Correct.lean#L542), [`adpCRE_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/ADPFix.lean#L226)). The fallback is part of
the method, not a failure: it is slower and never wrong.

The test in step 1 is Ziv's rounding test, classical in correctly rounded
math libraries. What is new is using it as an early-exit test on Ozaki
matrix products, with refinement and a proven exact fallback on the matrix
multiplier,
for all three schemes, machine-checked. See
[Related work and novelty](/HardwarePrimitives/ozaki/literature/) for the prior work
closest to it.

## When the rounding test succeeds

The rounding test succeeds on an entry whenever `x · y − 2B` and `x · y + 2B` round to
the same value, in particular whenever `x · y` lies more than `2B` from every
rounding boundary; at exactly `2B` an endpoint can be a tie that rounds the
other way ([`roundEnclosure_of_margin`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Correct.lean#L322),
[`ozaki1Enclosure_succeeds`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Correct.lean#L343)). Each extra slice of `11` bits divides `B` by
about `2^12`. The fallback is needed for:

- **exact ties**, results exactly halfway between two floats, which no
  enclosure can decide;
- **results very close to a boundary**, mostly products with heavy
  cancellation, where `B` is large compared with the result's spacing.

**The rounding test succeeds at once on exact zeros.** The bound counts only
the positions where both entries are nonzero ([`exactTerms_error_overlap`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/ZeroCheck.lean#L199)), so an entry whose
products are all zero, such as sparse rows and columns with no shared
nonzero, is decided by the first test with `0` and its IEEE sign
([`supportOverlap_eq_zero_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/ZeroCheck.lean#L127), [`ozaki1CREZ_zero`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/ZeroCheck.lean#L535),
[`ozaki1CRWSZ_zero`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/ZeroCheck.lean#L831)). The count costs one extra dot product on the matrix multiplier per entry.

### Measured at realistic sizes

A CPU simulation follows the Lean definitions with exact arithmetic and an
exact matrix multiplier, at `k` = 256, 1024 and 4096, on about 356,000 entries; every
enclosure and every decided result was checked against the exact product
([`scripts/fallback_sim.py`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/scripts/fallback_sim.py),
[`data/fallback-sim.json`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/data/fallback-sim.json)).
For binary64 output, Ozaki-I with `11`-bit slices tried at `5` and then `6`:

| Inputs | Entries reaching the exact fallback (`k` = 256 / 1024 / 4096) | Products on the matrix multiplier per entry vs the exact fallback alone (`k = 4096`) |
| --- | --- | --- |
| uniform in `(−1, 1)` | 0.6 / 1.2 / 1.9 % | 21 vs 36 |
| exponents spread over `2^±8` | 3.6 / 6.1 / 10.5 % | 23 vs 36 |
| exponents spread over `2^±40`, entrywise bound | 32 / 17 / 18 % | 61 vs 144 (23 with slices `4` to `7`) |
| condition number `10^2` | 1.1 / 3.6 / 13.8 % | 23 vs 37 |
| condition number `10^6` and beyond | 100 % (1.4–2.4 % with slices `4` to `7`) | 36 vs 36 |
| 90 % sparse, bound counting nonzero positions | 0.1 / 0.2 / 0.3 % | 22 vs 36 |
| no shared nonzeros, normwise bound / bound counting nonzero positions | 75 % / 0–0.2 % | 18 vs 36 (nonzero positions) |
| fp16 values, small integers | ≤ 0.3 %; integers up to `2^26`: 13–22 %, all ties | the exact fallback alone costs 1–9 |

Ozaki-II decides almost every entry with the rounding test at twelve moduli,
with about `12` products on the matrix multiplier against `34–36`, largely
because its truncation is often lossless; on lossy inputs the test still
succeeds on 75–98 %.

What this shows:

- **On well-conditioned data the rounding test saves about 40 % of the
  products on the matrix multiplier**, and more when exponents vary widely.
- **The slice counts must grow with `k`.** At `k ≥ 256` the five-slice test
  almost never succeeds, because the bound grows with `k`; correct
  rounding needs about `log₂ k + 2` bits beyond the output precision.
- **Ill-conditioned products need deeper refinement.** A longer list of slice
  counts brings their fallback rate from 100 % to about 2 %.
- **Low-precision inputs should skip the rounding test.** Their exact
  fallback needs only a few slices, so taking it directly is cheaper; the slice count is known
  once the inputs are sliced.

These are model costs, in dot products on the matrix multiplier per entry,
not GPU time, on
distributions chosen for the simulation; the entries of one GEMM share rows
and columns.

### Two rules from the measurements, proven

- **Slice counts that grow with `k`.** The first test uses the slice count
  for the target precision plus `⌈log₂ k⌉` bits; its bound is then at most
  `max|x| max|y| 2^-t`, with no factor `k` ([`slicesForCR`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SliceRuleCR.lean#L60),
  [`ozaki1Bound_le_cr`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SliceRuleCR.lean#L64)). The schemes using it stay correctly rounded
  ([`ozaki1CRK_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Adaptive.lean#L61), [`ozaki1CRIK_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Adaptive.lean#L87), [`tcOzaki1CRDKA_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/CRRules.lean#L65)). Rerun with the
  rule, the binary64 fallback rate drops to about `0 %` on uniform,
  wide-exponent and mildly ill-conditioned data (from up to 18 %), and to
  about 2 % at condition number `10^6` (from 100 %); at `10^10` a deeper list
  is needed and saves nothing over the exact fallback. For binary32 the rule
  does not pay: its exact fallback is already cheap.
- **Go straight to the exact fallback when it is cheaper.** The exact
  fallback's slice count is known once the inputs are sliced; when its `s²`
  products cost no more than the first test's `s(s+1)/2`, the scheme takes it
  directly. It stays correctly rounded, never costs more, and costs only the
  exact fallback when the shortcut applies ([`ozaki1CRA_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Adaptive.lean#L128), [`ozaki1CRA_cost_le`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Adaptive.lean#L236),
  [`ozaki1CRA_cost_shortcut`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Adaptive.lean#L253)); on low-precision inputs that is 4–9
  products on the matrix multiplier instead of 21.

([`data/fallback-sim-rules.json`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/data/fallback-sim-rules.json)
has the rerun.)

### Per tile

A GEMM computes each slice product for a whole tile at once, so what the early
exit saves also depends on scheduling. A second simulation
([`scripts/tile_sim.py`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/scripts/tile_sim.py),
[`data/tile-sim.json`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/data/tile-sim.json)) runs full `256 × 256` GEMMs with
binary64 output at `k` = 256, 1024 and 4096, about two million entries, under
three schedules:

- **Per entry**, the lower bound.
- **Uniform per tile**: a whole `16 × 8` tile takes the next refinement if the
  test fails for any of its entries.
- **Compaction**: the entries whose test failed are packed into new tiles,
  either ideally or by gathering rows and columns, which accounts for the lost
  reuse of data.

| Schedule | Ozaki-I, slices `5` then `6` | Ozaki-I, `k`-dependent slices | Ozaki-II |
| --- | --- | --- | --- |
| Uniform per tile: share of the per-entry saving kept | 0–43 % | 48–95 % (median 60 %) | 48–100 % (median 86 %) |
| Gathering: share kept | median 44 % | 39–99 % (median 93 %) | 59–100 % (median 94 %) |

Ideal compaction stays within 4.4 % of the per-entry cost, so the real loss is
the reuse of data. Under heavy cancellation (condition number `10^6`), uniform
per-tile Ozaki-I costs 8 % more than always taking the exact fallback. The work
off the matrix multiplier is 0.24–2.5 % of its multiply-adds for Ozaki-I and
3.5–9.6 % for Ozaki-II, under assumed weights per operation. Every interval and
every result of a successful test was checked against the exact product. These
are instruction counts, not GPU time.

### A test suite for real hardware

[`scripts/targeted_validation.py`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/scripts/targeted_validation.py) and the
Lean files in [`scripts/targeted/`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/scripts/targeted) produce
[`data/targeted-validation.json`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/data/targeted-validation.json), summarized
in [`data/targeted-validation.md`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/data/targeted-validation.md). It holds 140
cases, 85 for NVIDIA and 55 for AMD, whose predicted outputs distinguish the
models' numerical features: full block FMAs, cancellation, two passes,
non-monotonicity, minimum alignment exponents, signed zeros, subnormals, TF32
and padding bits. Each case gives the input words, a suggested
instruction, the predicted output word and what a mismatch would mean. Of the
cases, 56 come from theorems, whose values the script re-checks. The suite has
not yet been run on hardware.

## Fixed-width integer arithmetic

Everything after the matrix multiplier can run in integer registers whose
widths do not depend on the inputs' exponents.

- **Slicing** works on significands and exponents with shifts, a
  round-half-even division and comparisons. It equals the slicing of the
  proofs for every grid ([`splitInt_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SliceInt.lean#L582), [`splitInt_width`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SliceInt.lean#L605)).
- **The rounding test** adds each scaled slice product, rounded down to `W`
  bits below the largest possible product, in a truncated sum whose register
  never wraps ([`ozaki1Truncated_register`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/TruncatedSum.lean#L150),
  [`ozaki1CRW_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/TruncatedSum.lean#L136)). The final round to nearest even is a few integer
  comparisons ([`roundExact_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Bounded.lean#L635)).
- **The exact fallback** decides the rounding of a sum of terms `v · 2^e` by
  a top-down summation. It adds, in a `W`-bit register, the parts of the terms
  within `W` bits below the current leading position, carries the sum to the
  next lower range only when cancellation has made it small, and jumps over
  empty gaps ([`roundSumJ_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/TopDownSummation.lean#L510)). It visits at most
  `n · bitlen(max |v|) + 1` ranges, whatever the exponents
  ([`rangesJ_le`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/TopDownSummation.lean#L437)).
- **The whole pipeline**, from `(significand, exponent)` inputs to the rounded
  result, is one integer function proven correctly rounded: for Ozaki-I
  ([`ozaki1CRI_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/BoundedInt.lean#L186)), Ozaki-II ([`ozaki2CRJ_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/BoundedOzaki2J.lean#L112)) and ADP-style slicing
  ([`adpCRJ_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/ADPIntJ.lean#L34)), on both vendors (ADP on the Tensor Core side), with
  signed-zero versions ([`ozaki1CRIS_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/BoundedInt.lean#L332), [`ozaki2CRJS_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/BoundedOzaki2J.lean#L174),
  [`adpCRJS_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/ADPIntJ.lean#L60)).

**One theorem bounds every register.** A version of each pipeline with
overflow checks guards every integer it computes: data against `2^R`, exponents and counters
against `2^X`. Under explicit formulas for `R` and `X`, the checked version
returns exactly what the unchecked one returns, so no register ever
overflows ([`ozaki1CRIC_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/BoundedChecked.lean#L2183), [`ozaki2CRJC_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/BoundedChecked2.lean#L665), [`adpCRJC_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/ADPChecked.lean#L434)):

| Pipeline | Data bits `R` | Exponent and counter bits `X` |
| --- | --- | --- |
| Ozaki-I, FP64 (`11`-bit slices, up to `175`, `k ≤ 2^20`) | 263 | 17 |
| Ozaki-I, binary32 (up to `24` slices) | 207 | 15 |
| Ozaki-II, FP64 (twelve moduli up to `4096`, `P ≤ 69`) | 263 | 17 |
| Ozaki-II, binary32 (six moduli) | 161 | 15 |
| ADP-style, FP64 (up to `11` slices of width up to `81`) | 259 | 17 |

The guards cover the internal arithmetic of the matrix multipliers too: every
chunk result and partial sum of split-K, and every partial sum of the 32-bit
register of the INT8 matrix multiplier, which is proven never to wrap ([`chunkedC_exactOn`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/CheckedMultipliers.lean#L52),
[`int8DotC_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Int8Checked.lean#L59)). The signed-zero pipelines have checked versions as well
([`ozaki2CRJSC_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/BoundedCheckedSigned.lean#L138), [`adpCRJSC_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/ADPCheckedSigned.lean#L27)); the tightened widths are
[`ozaki1CRIC_binary64_tight`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/CheckedTight.lean#L38) and its siblings. Kernel-checked tests show the
guards are real: at narrower widths the checked versions fail. Comparisons,
signs, bit lengths and powers of two used as shift amounts are not guarded,
as they create no new magnitude.

## IEEE special values

On IEEE data the specification is the exact dot product rounded once
([`dotIEEE`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/IEEEDot.lean#L55)):

- NaN for a NaN input, a product `Inf · 0`, or opposite infinities;
- `±Inf` for an infinite product or an overflowing sum;
- otherwise the rounded sum, with IEEE's zero sign: a nonzero sum that rounds
  to zero keeps its sign, and an exact zero is `−0` only when every product
  is `−0`.

IEEE 754 leaves a dot product's order and precision to the implementation;
this is the "exact, then round once" reading. A wrapper handles the special
inputs and takes the sign of an overflowing sum from the integer terms of the
exact fallback; with it every correctly rounded version, rational or integer, meets the
specification for every input ([`crIEEE_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/IEEEDot.lean#L148), [`crIEEEI_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/IEEEInt.lean#L105),
[`tcOzaki1CRDI_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/IEEESchemes.lean#L60), [`mcOzaki1CRDI_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiMC/IEEESchemes.lean#L44)). Kernel tests cover the table of
cases on both vendors. On stored words, the decoding and the detection of
infinities, NaN and zeros are themselves integer operations on the sign,
exponent and significand fields, and agree with TensorCore's and
MatrixCore's classifications ([`Ozaki.MC.decodeWord_decodeNat`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiMC/IEEEWords.lean#L31),
[`dotSpecialI_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/IEEEWords.lean#L177), [`crIEEEWord_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/IEEEWords.lean#L212), [`decodeWord_classifyNat`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/IEEEWords.lean#L52)).

## The same result on NVIDIA and AMD

Every correctly rounded version rounds with a hardware-independent IEEE
round to nearest even,
proven for any binary format ([`roundRNE_nearest`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Binary.lean#L448)). The hardware libraries'
own roundings compute the same values: TensorCore's up to the largest finite
value, where it returns nothing above it ([`round32ValueTC_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Rounding.lean#L136),
[`fp64RoundTC_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/IEEE.lean#L33)), and MatrixCore's on every input
([`round32Value_eq_rne32Q`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiMC/IEEE.lean#L38)). So on the two vendors' models the correctly
rounded versions return the same value for the same inputs, even though the
matrix multipliers underneath differ: the Tensor Core truncates and CDNA 3
rounds.

## What runs where

- **On the matrix multiplier:** every slice and residue product, including
  those of the exact fallback.
- **In fixed-width integer registers:** slicing, the rounding test, the
  top-down summation of the exact fallback and the final rounding.
- **Never on a Tensor Core:** the rounding test. A Tensor Core's output is not
  monotone in its inputs ([non-monotonicity](/HardwarePrimitives/tensor-core/properties/non-monotonicity/)),
  and the rounding test relies on monotone rounding.

## What is not covered

- A GPU implementation and measurements: the cost claims come from the model
  and small test matrices.
- The exactness of the matrix multiplier rests on the hardware models, which
  are validated against GPUs by measurement, not proven. ADP runs on an
  idealized INT8 matrix multiplier ([issue #2](https://github.com/pauljiang03/HardwarePrimitives/issues/2)).
- NaN payloads and signalling NaNs.
