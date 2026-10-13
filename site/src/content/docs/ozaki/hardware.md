---
title: What the hardware semantics give
description: Where the bit-level Tensor Core and matrix-core models enter the Ozaki proofs - exact slice products derived instead of assumed, the exact condition with cancellation, the two-pass recovery, the per-GPU choice of slices and chunks, and where NVIDIA and AMD differ.
---

Every Ozaki scheme assumes the matrix engine multiplies its small integers
exactly. Prior work states that assumption and backs it with documentation
and tests. Here it is a theorem on each path, derived from the bit-level
NVIDIA Tensor Core model of this repository and the AMD matrix-core model in
`amd/`. Both models are validated against GPUs by measurement, and the
theorems are about the models.

The detailed semantics do three things:

1. They turn the main assumption into a theorem.
2. They show exactly where it breaks.
3. They enable, and rule out, design choices.

They do not, by themselves, make the schemes faster; see
[the slice choice](#choosing-slices-chunks-and-passes) below.

## Exact slice products, derived

A Tensor Core aligns every product of a group to the largest exponent, keeps
`F` bits below it (`F = 23` on V100, `24` on A100, `25` on H100), adds
exactly and truncates to binary32. For integer operands of `b` bits with
`2b ≤ F`, alignment loses nothing, and the binary32 output holds every
integer up to `2^24`.

| Fact | Lean |
| --- | --- |
| A block of `b`-bit integers with `\|c\| + Σ\|aᵢbᵢ\| ≤ 2^24` returns `c + Σ aᵢbᵢ`; so does a chain of blocks. | [`Ozaki.TC.evalBlock_int`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/Exactness.lean#L184), [`Ozaki.TC.runBlocks_int`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/Exactness.lean#L335) |
| The engine is exact on all eight NVIDIA paths (`b = 11` for fp16 and tf32, `8` for bf16). | [`tcMultiplier_exactOn`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/MatrixMultiplier.lean#L193), [`v100_exactOn`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/Models.lean#L31) and seven more |
| The same on the AMD SFMA, CDNA 1, 2 and 3 fp16, bf16 and XF32 paths. | [`mcMultiplier_exactOn`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/MatrixMultiplier.lean#L326), [`cdna3F16_exactMultiplier`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/Models.lean#L92) |

The model shows why the output, not the accumulator, sets this budget. A
Tensor Core adds a whole group exactly and rounds once, so an A100 block is
exact on products whose binary32 running sum is not
([`a100_exact_where_binary32_is_not`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/Limits.lean#L62)). A model that rounds every partial
sum, like the Z3 models' engine, is stricter than the hardware.

## The exact condition, with cancellation

The budget `Σ|aᵢbᵢ| ≤ 2^24` is sufficient, not necessary. On the Tensor Core
model a block of `b`-bit integers with `2b ≤ F` and an integer `c` with
`|c| < 2^(F+1)` returns the exact sum whenever that sum is a binary32 value,
however large the products are ([`Ozaki.TC.evalBlock_cancel`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/Cancellation.lean#L70)). The
condition on the sum is also necessary
([`evalBlock_exact_needs_binary32`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/Cancellation.lean#L118)). For example:

- eight products `±2^22` on A100 total `2^25` and return `0` exactly
  ([`a100_cancel_zero`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/Cancellation.lean#L349));
- a full H100 group of sixteen products does the same
  ([`h100_cancel_zero`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/Cancellation.lean#L368)).

The AMD architectures differ:

- **CDNA 1 and CDNA 3:** exact whenever every product, `c` and the exact
  sum are within `2^24`.
- **CDNA 2:** it adds a pairwise tree of binary32 products, so every node of
  the tree must also be within `2^24` ([`Ozaki.MC.pairwiseGroupSum_cancel`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/Cancellation.lean#L41),
  [`pairwiseSumsBounded_of_bound`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/Cancellation.lean#L66)). Cancellation inside a node is free; cancellation
  across the tree is not.

This is the precise boundary, not a scheduling rule: the running sums are
known only after computing them. Its use is in knowing exactly when results
are right, and why.

## Where the budget breaks, and how the vendors differ

- **Full groups.** With `11`-bit slices, `k · 2^22 ≤ 2^24` allows four
  products, but A100 and H100 groups take eight and sixteen. Seven products
  `2047²` already lose a bit ([`a100_full_group`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/Limits.lean#L51)).
- **NVIDIA and AMD fail differently.** Past the budget the Tensor Core
  truncates and CDNA 3 rounds to nearest. The same seven products return
  `29331462` on the Tensor Core and `29331464` on CDNA 3, where the exact sum
  is `29331463` ([`cdna3F16_full_group`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/Limits.lean#L33)). Configurations that rely on luck
  give different wrong answers on the two vendors.
- **The check cannot run on a Tensor Core.** A Tensor Core's output is not
  monotone in its inputs ([non-monotonicity](/TC-EFT/properties/non-monotonicity/)),
  and the correct-rounding check relies on monotone rounding, so it runs on
  exact values.

## Two passes recover a full group

Run a group once from `c = 0`, giving `D1`, the truncation of the exact sum
`S`. Run it again from `c = −D1`. Because `c` takes part in alignment, the
mechanism behind the non-monotonicity, the second pass is exact as long as
`|D1| ≤ 2^(F+1)`, and it returns `S − D1`, so `D1 + D2 = S`
([`twoPass_exact`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/TwoPass.lean#L254)). `F` grows by one bit each time the group size doubles,
so a full group of `11`-bit products always fits. The two-pass engine is
exact for every length on all eight paths ([`tcMultiplier2_exactOn`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/TwoPass.lean#L401),
[`h100F16_exactOn2`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/TwoPass.lean#L471) and seven more).

This is the matrix-instruction analogue of the scalar TwoProdFMA, for a
multi-term truncating adder. It needs the precise semantics: from "FP32
accumulation" alone it cannot be designed safely. By instruction count it is
not the cheapest way to fill a group, as the next section shows.

**On AMD it depends on the architecture.**

- **SFMA and CDNA 1: it holds.** On the SFMA, whose block is one product, the
  two passes are exactly TwoProdFMA: `(2^24 − 1)²` comes back exact where one
  pass rounds it ([`sfma_twoProd`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/TwoPass.lean#L639), [`mcTwoPass_exact_cr`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/TwoPass.lean#L425)).
- **CDNA 3: it holds.** Global alignment is exact for larger `c` than the
  budget assumed ([`alignedAccumulation_wide`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/TwoPass.lean#L83)), so the second pass recovers
  what the final rounding lost: the full group that one pass returns as
  `29331464` comes back as `29331463` ([`cdna3F16_twoPass_full_group`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/TwoPass.lean#L632),
  [`mcTwoPass_exact_ga`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/TwoPass.lean#L438)). The two-pass engine is exact for every length
  ([`mcMultiplier2_exactOn`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/TwoPass.lean#L510)).
- **CDNA 2: it fails in general.** Its pairwise tree rounds before `c` is
  added, so the second pass sees the same rounded node; products `2^22` and
  `2^-14` return `2^22` on CDNA 2 and are recovered on CDNA 1
  ([`cdna2_twoPass_fails`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/TwoPass.lean#L650)). For integer slices the tree never rounds, so
  Ozaki is unaffected.

A second pass is needed on AMD only on CDNA 3 fp16 and the SFMA: elsewhere
full groups of the widest slices fit the budget ([`full_groups_fit`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/TwoPass.lean#L622)).

## Choosing slices, chunks and passes

For each path, the model gives every exact configuration: a slice width `b`
up to the input format's limit, a chunk length, one or two passes. Each
candidate is proved exact for every length ([`candidates_exact`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/SplitChoice.lean#L117),
[`mcCandidates_exact`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/SplitChoice.lean#L48)). The cost counts matrix-engine blocks for the
`s(s+1)/2` slice products of Ozaki-I, with the slice count from a stated
normwise rule ([`slicesFor`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/Ozaki/SliceRule.lean#L25), [`slicing_term_le_maxAbs`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/Ozaki/SliceRule.lean#L30)). At `k = 1024`:

| Path | FP64: cheapest | `11`-bit, chunks of 4 | `11`-bit, two passes | binary32: cheapest |
| --- | --- | --- | --- | --- |
| V100 fp16 | `b = 11`, 3840 blocks | 3840 | 7680 | `b = 11`, 1536 |
| A100 fp16 | `b = 10`, 2688 | 3840 | 3840 | `b = 10`, 768 |
| H100 fp16 | `b = 10`, 1344 | 3840 | 1920 | `b = 10`, 384 |
| A100 / H100 bf16 | `b = 8`, 3584 / 1792 | — | — | `b = 8`, 1280 / 640 |
| H100 tf32 `mma` | `b = 10`, 2688 | 3840 | 3840 | `b = 10`, 768 |
| CDNA 3 fp16 | `b = 10`, 2688 | 3840 | — | `b = 10`, 768 |

The theorems are [`h100F16_best`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/SplitChoice.lean#L185), [`cdna3F16_best`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/SplitChoice.lean#L92) and the others in
[`OzakiTC/SplitChoice.lean`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/SplitChoice.lean)
and [`OzakiMC/SplitChoice.lean`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/SplitChoice.lean).
The chosen configurations are proved exact and correctly rounded
([`h100F16_fp64CR10`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/SplitChoice.lean#L246), [`cdna3F16_fp64CR10`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/SplitChoice.lean#L113)).

Two findings:

- **`10`-bit slices that fill the group are the cheapest exact
  configuration** wherever a group holds more than four products. One extra
  slice costs less than a second pass, so the two-pass engine never wins by
  this count on the Tensor Core paths.
- **The gain does not need the detailed semantics.** The conservative rule
  `k · 2^(2b) ≤ 2^24` with `k = 16` also allows `10`-bit slices in an H100
  group. The reduction, about `2.9×` on H100 and `1.4×` on A100 over chunks of
  four, comes from matching the slice width to the group size. What the
  semantics add is the proof, and the evidence that the alternatives,
  two passes included, do not pay.

**Ozaki-II and ADP.** The same choice for Ozaki-II picks the fewest
pairwise-coprime moduli up to `2^(b+1)` whose product covers `2k · 2^(2P)`,
with `P` set so the truncation error meets the same target as Ozaki-I's slice
rule ([`moduliFor_spec`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/Ozaki/ModuliRule.lean#L103)); every candidate is proved exact
([`ozaki2Candidates_ok`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/Ozaki2Choice.lean#L60), [`mcRunCandidates_exact`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/Ozaki2Choice.lean#L76)). In FP64 Ozaki-II is
cheaper than Ozaki-I on every path, by `1.4×` to `2×` in engine blocks
(H100 fp16 at `k = 1024`: 768 against 1344; CDNA 3 fp16: 1536 against 2688;
[`h100F16_best2`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/Ozaki2Choice.lean#L109), [`cdna3F16_best12`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/Ozaki2Choice.lean#L134)); in binary32 they mostly tie. Two
passes win only on the SFMA, for Ozaki-I. For ADP-style slicing the remap
encoding is never worse than naive signed bytes ([`adpCost_remap_le_naive`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/ADPChoice.lean#L70)),
but when the fixed-point width is `7` mod `8` the floor encoding saves a slice
([`adp_best`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/ADPChoice.lean#L82)). The chosen configurations are correctly rounded
([`h100F16_fp64CR2`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/Ozaki2Choice.lean#L146), [`cdna3F16_fp64CR2`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/Ozaki2Choice.lean#L157), [`sfma_fp64CR2pass`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiMC/Ozaki2Choice.lean#L171),
[`adp_fp64CR_esc0`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/ADPChoice.lean#L96)).

The cost counts model instructions, not time: it leaves out slicing,
Ozaki-II's reconstruction with integers of about `130` bits, memory traffic,
and the extra moduli Ozaki-II's correct rounding may need. On a GPU, where an
extra slice costs memory traffic and a second pass reuses loaded operands,
two passes might still pay; only benchmarks can say. INT8 blocks are not
comparable with fp16 blocks without throughput figures.

**With correct rounding's margin.** Correct rounding needs about
`log₂ k + 2` more bits than the accuracy target: one more slice for Ozaki-I
(`15` to `21` slice products) and one more modulus for Ozaki-II. With the
margin included in both ([`moduliForCR_spec`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/Ozaki/SliceRuleCR.lean#L109), [`truncation_le_cr`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/Ozaki/SliceRuleCR.lean#L116)),
Ozaki-II remains `1.75×` to `2.25×` cheaper than Ozaki-I for FP64 on every
Tensor Core path and AMD fp16, bf16 and XF32 path (H100 fp16 at `k = 1024`: 832
blocks against 1792; [`h100F16_bestCR`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/OzakiTC/Ozaki2ChoiceCR.lean#L75)), and `1.25×` to `1.5×` for binary32,
except on the SFMA, where two-pass Ozaki-I wins. Any positive, pairwise-coprime
moduli give a valid CRT basis ([`crtBasis_valid`](https://github.com/pauljiang03/TC-EFT/blob/main/ozaki/Ozaki/CRTValid.lean#L148)), so the chosen bases need
no case-by-case check.

## What is not modelled

- **FP8 and FP4 engines**, deferred. FP8 accumulation keeps about `13`
  fractional bits on H100, so conservative assumptions there are likely wrong
  and exact semantics would decide which configurations are possible.
- **INT8 instructions**, out of scope for now on both vendors
  ([issue #2](https://github.com/pauljiang03/TC-EFT/issues/2)). ADP runs on
  an idealized INT8 engine.
- **Blackwell.**
