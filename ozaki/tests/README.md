# Tests

`lake build` builds both test libraries, so every check below runs on every build. Each check is
an `example` proved by kernel evaluation (`decide +kernel`) of the definitions the theorems are
about.

## The Z3 models' outputs

The Z3 models of the schemes emulate a binary32
`4 × 4` GEMM on two test cases drawn with `random.Random(2026)`: exponents in `[2^-1, 2^1]`
("narrow") and in `[2^-6, 2^6]` ("wide"). [`scripts/z3_reference.py`](../scripts/z3_reference.py)
imports the two models from an unmodified clone (commit `dfe24cf`), regenerates both cases as their
`main()` does, runs `ozaki1_gemm` with four slices and `ozaki2_gemm` with four moduli, and records
every input and output as a binary32 word in
[`data/z3-reference.json`](../data/z3-reference.json).

[OzakiTCTests/Z3Matrices.lean](OzakiTCTests/Z3Matrices.lean) checks that the Lean pipelines on the
V100 Tensor Core model return the same words: Ozaki-I with four `11`-bit slices (ten V100 slice
products per entry) and Ozaki-II with moduli `{4096, 4095, 4093, 4091}` and `P = 22`, on both
cases. Every engine call in these pipelines is exact (`Ozaki.TC.v100_exactOn`), so agreement with
the Z3 models, whose engine rounds every addition, is expected; the test checks it on the actual
words, including the binary32 recombination order. The same file checks that the slices computed
with binary32 σ-trick operations, as the Z3 model computes them, equal the exact slices of the
scheme library on every row of `A` and column of `B`.

[OzakiMCTests/Z3Matrices.lean](OzakiMCTests/Z3Matrices.lean) runs the same comparison on the AMD
models: the binary32 SFMA, CDNA 1, 2 and 3 fp16, and CDNA 3 XF32 return the Z3 models' words for
both schemes on both cases (twenty checks), and a bf16 path, which cannot encode `11`-bit slices,
returns `none`.

## All eight GPU paths

[OzakiTCTests/AllPaths.lean](OzakiTCTests/AllPaths.lean) runs the Z3 cases on every Tensor Core
path. The A100 and H100 fp16 paths and the three tf32 paths return the Z3 models' words for both
schemes and both cases. The two bf16 paths return `none` with `11`-bit slices; with `8`-bit slices
(and moduli `{512, 511, 509, 503}`, `P = 16` for Ozaki-II) they return the exact-engine result.

## Accuracy

[OzakiTCTests/Accuracy.lean](OzakiTCTests/Accuracy.lean) (V100) and
[OzakiMCTests/Accuracy.lean](OzakiMCTests/Accuracy.lean) (CDNA 3 fp16) check the Z3 models' measured
comparisons on their matrices: four slices are at least as accurate as one (`I:[M.2]`), four
moduli at least as accurate as one (`II:[M.3]`), and every componentwise and normwise error the Z3
models print in their `output.txt` is reproduced to within `±0.0005`. These are facts about the
test matrices, not theorems: more slices need not help on every input.

## ADP against the Z3 model

[`scripts/z3_adp_reference.py`](../scripts/z3_adp_reference.py) imports the Z3 ADP model
(`ozaki-NVIDIA/adp.py`) from the unmodified clone, runs five cases (uniform and signed inputs, Test 2
with `b = 2` and `b = 64`, and an input with an infinity) and records inputs, outputs, path, ESC, `W` and
slice count in [`data/z3-adp-reference.json`](../data/z3-adp-reference.json).
[OzakiTCTests/ADPMatrices.lean](OzakiTCTests/ADPMatrices.lean) checks that `Ozaki.TC.adp` takes the
same path and returns the same values in every case, with the same ESC, `W` and slice count on the
three emulated ones. The values are compared as rationals, so the sign of a zero is not checked.

### The test-level checks

[`scripts/z3_adp_labels.py`](../scripts/z3_adp_labels.py) reruns, from the same unmodified clone,
the inputs of the Z3 model's test-level checks that concern particular matrices and records them
in [`data/z3-adp-labels.json`](../data/z3-adp-labels.json):
the decode edge values (`[T.1]`), the paper's remap example (`[T.2]`), the `signed` case with all
three slice encodings (`[T.4]`), two wide-exponent cases (`[T.7]`), Test 2 with `n = 8` and
`b = 0` and `b = 64`, through ADP and through a fixed `55`-bit emulation without guardrails
(`[T.8]`), the emergent-overflow case (`[T.10]`), the subnormal case (`[T.11]`) and the zero-policy
and identity cases (`[T.12]`).
[OzakiTCTests/ADPLabels.lean](OzakiTCTests/ADPLabels.lean) checks the Lean routine against every one:
the same paths, ESC, `W`, slice counts and values; the fixed-width emulation meets Grade A at
`b = 0` and fails it at `b = 64`, as the Z3 model's does; and on the overflow case `adp` returns no
values where the Z3 model returns `+Inf`.

## Correct rounding against exact arithmetic

[`scripts/correct_reference.py`](../scripts/correct_reference.py) computes correctly rounded
products with exact fractions and its own round to nearest even, sharing no code with Lean, and
records them in [`data/correct-reference.json`](../data/correct-reference.json): the two Z3 cases,
a product with heavy cancellation (`x · y = 2^-40` with `max|x| = 1`), a product exactly halfway
between two binary32 values, and two random binary64 `4 × 8` by `8 × 4` products.

[OzakiTCTests/Correct.lean](OzakiTCTests/Correct.lean) checks that the correctly rounded schemes
return exactly these words: Ozaki-I (three, then four slices) and Ozaki-II (five, then six moduli)
on V100, ADP on the INT8 engine (`7`, `8`, then `9` slices), and Ozaki-I with its exact path on V100
blocks, including a run where every entry takes the exact path. It also counts how often the check
settles an entry without the exact path: Ozaki-I settles every Z3 entry with four slices and all
but two with three; Ozaki-II settles none with the Z3 models' four moduli (`P = 22`), 12 and 9 of 16
with five, all with six; ADP settles every entry of both binary64 cases at the configuration its own
ESC rule picks (`8` slices of width `56`, `11` of width `81`), and 5 and 11 of 16 on `wide64` with
`8` and `9` slices. These counts are what the fast path achieves; the theorems hold regardless,
because the last resort is exact.
[OzakiMCTests/Correct.lean](OzakiMCTests/Correct.lean) checks the same words on the SFMA, CDNA 1, 2
and 3 fp16 and CDNA 3 XF32 paths.

## Long dot products and FP64

[OzakiTCTests/LongFP64.lean](OzakiTCTests/LongFP64.lean) checks FP64 emulation on V100 fp16 blocks
against the binary64 oracle cases (`k = 8`, so split-K runs two chunks of four per slice product):
correctly rounded Ozaki-I (five, then six slices, then the exact path on V100 blocks) on both
cases, correctly rounded Ozaki-II with twelve moduli at most `4096` (`P = 69`), and plain Ozaki-I
with binary64 recombination and six slices within `2^-50 Σ|xᵢyᵢ|` of the exact product. The
correctly rounded Ozaki-I results are also checked with the check running on a `96`-bit window
sum instead of the exact sum (`tcOzaki1CRDW`).
[OzakiMCTests/LongFP64.lean](OzakiMCTests/LongFP64.lean) checks correctly rounded Ozaki-I on CDNA 3
fp16 against the same oracle values; `MatrixCore` has no binary64 decoding, so the test decodes the
words itself.

## Fixed-width integer arithmetic

[OzakiTCTests/Bounded.lean](OzakiTCTests/Bounded.lean) (V100 fp16) and
[OzakiMCTests/Bounded.lean](OzakiMCTests/Bounded.lean) (CDNA 3 fp16) run correctly rounded FP64
Ozaki-I in bounded integer registers (`tcOzaki1CRBD`, `mcOzaki1CRBD`) and as one integer function
from `(significand, exponent)` inputs (`tcOzaki1CRID`, `mcOzaki1CRID`) on both binary64 oracle
cases and return the oracle's words: once with the check settling entries (five, then six slices,
a `96`-bit window), and once with no check (`ss = []`), so that every entry goes through the
exact path; plus signed-zero cases. These are the slowest files of the suite, about two minutes
each.

[OzakiTCTests/BoundedSchemes.lean](OzakiTCTests/BoundedSchemes.lean) and
[OzakiMCTests/BoundedSchemes.lean](OzakiMCTests/BoundedSchemes.lean) do the same for Ozaki-II with
twelve moduli up to `4096` (`P = 69`) and, on the Tensor Core side, for ADP-style slicing on the
INT8 engine: integer checks and the fixed-width exact path return the oracle's words, the
subnormal counterexample settles through the exact path at `2^-1074`, and the integer checks
settle as many entries as the rational ones, or nearly (Ozaki-II binary64: 16 and 9 of 16 against
16 and 10; ADP at `(8, 56)`, `(11, 81)`, `(8, 62)`, `(9, 70)`: 16, 16, 5 and 11, identical).

[OzakiTCTests/FinalPipelines.lean](OzakiTCTests/FinalPipelines.lean) and
[OzakiMCTests/FinalPipelines.lean](OzakiMCTests/FinalPipelines.lean) run the integer Ozaki-II and
ADP pipelines with the jumping exact path on four entries per case, signed zeros, the checked
copies at their proved widths and failing at narrower ones, and the IEEE special cases. The library files carry their
own kernel checks of the integer pieces: a register that wraps mid-sum, ties, binary32 normal,
subnormal and overflowing results, heavy cancellation, a tie after cancellation, and an end-to-end
binary32 tie through the exact path.

### Tighter widths

[OzakiTCTests/CheckedTight.lean](OzakiTCTests/CheckedTight.lean) runs the checked pipelines at the
tightened widths on the guarded engines, including exact-path-only runs, shows them failing with a
`64`-bit data register or an `8`-bit exponent register, checks the signed checked copies, and shows
the INT8 register refusing to wrap where TC-EFT's wraps.

## Exact zeros

[OzakiTCTests/Zeros.lean](OzakiTCTests/Zeros.lean) (V100) and
[OzakiMCTests/Zeros.lean](OzakiMCTests/Zeros.lean) (CDNA 3) run a row and a column with no shared
nonzero through the zero-aware check: with a sentinel in place of the exact path, the normwise
check returns the sentinel and the zero-aware check returns `0`, with the right signed zero; the
binary64 oracle cases stay correct.

## Signed zeros

[OzakiTCTests/Signed.lean](OzakiTCTests/Signed.lean) (V100) and
[OzakiMCTests/Signed.lean](OzakiMCTests/Signed.lean) (CDNA 3 fp16) run correctly rounded FP64
Ozaki-I with signed zeros (`tcOzaki1CRDS`, `mcOzaki1CRDS`) on three inputs whose result is zero, and
check each against the specification `crSigned` and the expected IEEE result: products that are all
`−0` give `−0`, products that cancel exactly give `+0`, and a negative product that underflows
(`2^-540 · (−2^-540)`) gives `−0`.

## Error bounds

[OzakiTCTests/SharpBounds.lean](OzakiTCTests/SharpBounds.lean) checks, on every entry of the Z3
binary32 cases and the binary64 oracle cases, that the actual error is at most each sharper bound
and each sharper bound at most the earlier one: Ozaki-I entrywise against normwise, Ozaki-II's
mixed truncation bound against `4k` and `8k`, and Jeannerod–Rump against `γₖ` for native dot
products.

## Slice choice

[OzakiTCTests/SplitChoice.lean](OzakiTCTests/SplitChoice.lean) and
[OzakiMCTests/SplitChoice.lean](OzakiMCTests/SplitChoice.lean) run the cheapest configurations,
`10`-bit slices filling the group, on H100 and A100 fp16 and CDNA 3 fp16: correctly rounded FP64
returns the oracle's words.

[OzakiTCTests/Ozaki2Choice.lean](OzakiTCTests/Ozaki2Choice.lean) and
[OzakiMCTests/TwoPassChoice.lean](OzakiMCTests/TwoPassChoice.lean) run the chosen Ozaki-II and ADP
configurations on oracle entries, the two-pass engine on CDNA 3 on over-budget `11`-bit vectors,
and two-pass Ozaki-I on the SFMA.

[OzakiTCTests/CRRules.lean](OzakiTCTests/CRRules.lean) checks the slice-count rule's table, the
shortcut on oracle entries and the correct-rounding-margin configuration costs.

## How often the fallback runs

[`scripts/fallback_sim.py`](../scripts/fallback_sim.py) is not a Lean test: it simulates the
correctly rounded schemes in Python with exact arithmetic, following the Lean definitions, at
`k` = 256, 1024 and 4096 on uniform, wide-exponent, ill-conditioned, sparse and low-precision
inputs, checks every enclosure and settled result against the exact product, and records how
often each step settles an entry and what it costs in
[`data/fallback-sim.json`](../data/fallback-sim.json); with `--rules` it reruns the configurations
with the slice-count rule and the exact-path shortcut, in
[`data/fallback-sim-rules.json`](../data/fallback-sim-rules.json).

## IEEE special values

[OzakiTCTests/Specials.lean](OzakiTCTests/Specials.lean) (V100) and
[OzakiMCTests/Specials.lean](OzakiMCTests/Specials.lean) (CDNA 3 fp16) run correctly rounded FP64
Ozaki-I with special values (`tcOzaki1CRDI`, `mcOzaki1CRDI`) on the cases of the IEEE specification
and check each against `dotIEEE`: a NaN input, `Inf · 0`, `+Inf` and `−Inf` products, an infinity
with finite products, a finite dot product overflowing to `±Inf`, products that are all `−0`,
exact cancellation (`+0`), a negative product that underflows (`−0`), and an ordinary sum.
[`scripts/z3_specials_reference.py`](../scripts/z3_specials_reference.py) records the Z3 ADP model's
outputs on an input with an infinity, one with a NaN, and one whose emulated products overflow
beside a row that cancels exactly, in [`data/z3-specials-reference.json`](../data/z3-specials-reference.json);
`adpIEEE` and `adpSafeIEEE` take the same paths and return the same words, NaN compared by class.

## ADP's zero policies

[`scripts/z3_adp_zero_policies.py`](../scripts/z3_adp_zero_policies.py) records the Z3 model's
zero-policy inputs and outputs in [`data/z3-adp-zero-policies.json`](../data/z3-adp-zero-policies.json).
[OzakiTCTests/ADPZeroPolicy.lean](OzakiTCTests/ADPZeroPolicy.lean) runs the routine with each
policy without the model's `[X.4]` assertion: the `−∞` policy returns the model's results, the
"skip zeros" policy returns `0` for a nonzero entry on the model's `field0_case`, breaking Grade A,
and the `−1022` policy fails on a constructed input.
[OzakiTCTests/ZeroPolicyGeneral.lean](OzakiTCTests/ZeroPolicyGeneral.lean) runs the general
counterexample family on explicit words with the default configuration: both unsafe policies
emulate and return `0`, block size `1` with skipping goes native and returns the right value, and
`adp` returns the right values.
[OzakiTCTests/ZeroPolicyShapes.lean](OzakiTCTests/ZeroPolicyShapes.lean) runs it padded to a `2 × 4`
by `4 × 3` product, and [OzakiTCTests/ZeroPolicyIff.lean](OzakiTCTests/ZeroPolicyIff.lean) and
[OzakiTCTests/ZeroPolicyGap.lean](OzakiTCTests/ZeroPolicyGap.lean) check both directions of the
masking conditions on explicit words, including one exponent pattern with an input that meets
Grade A and one that breaks it.

## ADP's guardrail and the INT8 exact path

[OzakiTC/ADPFix.lean](../OzakiTC/ADPFix.lean) carries its own kernel checks: on the subnormal
counterexample `adp` returns `−2^-1074` for a positive product, `adpSafe` takes the native path and
returns the correctly rounded `2^-1074`, and `adpCRE` returns `2^-1074` through its exact path on the
INT8 engine after the enclosure of `8` slices fails to settle it; on the five recorded Z3 cases
`adpSafe` returns what `adp` returns.

## Published analyses

[OzakiTCTests/PublishedAccum.lean](OzakiTCTests/PublishedAccum.lean),
[OzakiTCTests/AbdelfattahCarry.lean](OzakiTCTests/AbdelfattahCarry.lean) and
[OzakiTCTests/AbdelfattahCarry2.lean](OzakiTCTests/AbdelfattahCarry2.lean) check Abdelfattah et al.'s
accumulation by levels and their spare-carry recursion on their INT8/binary64 setting and on `11`-bit
fp16 slices: the level boundaries each rule accepts, where the two rules coincide and where they
differ. [OzakiTCTests/UchinoConst.lean](OzakiTCTests/UchinoConst.lean) and
[OzakiTCTests/UchinoScaling.lean](OzakiTCTests/UchinoScaling.lean) instantiate Uchino et al.'s binary64
reconstruction on their first twelve moduli, check the constant R64 on concrete products, and run
the end-to-end theorem with their scaling on a binary64 dot product, every hypothesis checked by the
kernel.

## Axiom audits

[OzakiTCTests/Audit.lean](OzakiTCTests/Audit.lean) and [OzakiMCTests/Audit.lean](OzakiMCTests/Audit.lean)
check that every theorem in the `Ozaki` namespace, of the scheme library and of the respective
instantiation, depends only on `propext`, `Classical.choice` and `Quot.sound`.
