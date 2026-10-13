---
title: 'Schedules: the reduction algebra'
description: The third part of MMAlgebra, the algebra of reduction schedules. For each modeled matrix multiplier, the exact laws under which two GEMM schedules give bitwise identical results, how far apart they can be, and how pinned accumulation makes every schedule agree, with proofs, concrete witnesses, a decision procedure, and a plan for Triton.
---

The third part of MMAlgebra, the **reduction algebra**, answers one question for every matrix
multiplier modeled on this site: when do two ways of computing the same matrix product
give the same result, bit for bit? For one entry of `D = C + AB`, every GEMM schedule (split-K,
stream-K, the k-tile depth, the instruction shape, and whether `C` is added in the first block FMA
or in the epilogue) is a small term built from block FMAs and binary32 additions. The block
semantics of [the Tensor Core model](/MMAlgebra/model/) and [the AMD matrix-core
model](/MMAlgebra/amd/) determine which rewrites of these terms preserve the output word for every
input. The answer is an algebra per architecture: a short list of laws, a completeness result
saying that no other laws hold (proved in Lean for two products, checked exhaustively on small
terms), and, for any two schedules that are not equivalent, a concrete input on which they
differ.

The three algebras are simple to state. On NVIDIA Tensor Cores, AMD CDNA 3 and SFMA, the algebra
is **rigid**: the products inside one block FMA can be permuted, zero products can be dropped and
the two operands of an addition can be swapped, but every other change to a schedule changes the
result on some input. On CDNA 1 (fp16), a block
FMA is **correctly rounded**, which allows a few more rewrites. On CDNA 2, a block is a
**binary32 summation tree** with `c` added last, so `c` can be moved out of a block.

| Part | Status |
| --- | --- |
| Products in a block act as a multiset; zero products are invisible; restriction to a support (Tensor Core model, every variant) | Proved in Lean |
| Chains holding two products in different patterns differ on some input (V100, A100, H100 fp16) | Proved in Lean |
| Separating inputs on CDNA 1, 2 and 3; one instruction is not one rounding on V100, A100 and CDNA 1–3 | Kernel-checked in Lean |
| The laws and normal forms on every modeled variant | Random testing; exhaustive enumeration over 2, 3 and 4 products |
| Distinct normal forms always differ on some input (completeness) | Reduced to supports of at most 3 products; checked exhaustively; two lemmas remain in Lean |
| The CDNA 1 merge law and the CDNA 2 `c`-split law | Tested; follow directly from the block formulas; not yet in Lean |
| How far apart two schedules can be: structural bound, divergence of two schedules, shared work | Proved in Lean for any matrix multiplier, instantiated for SFMA and CDNA 1; other block constants derived on paper and checked numerically |
| Inside the exact region (small integer operands) every schedule agrees | Proved in Lean on every Tensor Core model and on CDNA 1, 2 and 3 |
| Pinned and anchored accumulation make every schedule agree on Tensor Cores (pinned also on CDNA 3), and fail on CDNA 1 and 2 | Proved in Lean; kernel-checked demonstration and counterexamples; simulated; not yet run on a GPU |
| Decision procedure with separating inputs; Triton front end | Python prototype; Triton front end planned |

The Lean development is the [`mmalgebra/`](https://github.com/pauljiang03/MMAlgebra/tree/main/mmalgebra)
project of this repository, which requires the two models, and the Python prototype is in
[`mmalgebra/prototype/`](https://github.com/pauljiang03/MMAlgebra/tree/main/mmalgebra/prototype).

## The problem: bitwise reproducibility of matrix products

Floating-point addition is not associative, so the result of a long dot product depends on the
order in which its terms are added. A GPU matrix product fixes that order through many choices
that are usually made for speed: the tile shapes, the depth of the k-loop step, which matrix
instruction is used, whether the inner dimension is split across thread blocks (split-K, or the
work-centric decomposition of Stream-K by Osama, Merrill, Cecka, Garland and Owens,
[arXiv:2301.03598](https://arxiv.org/abs/2301.03598)), how the partial results are combined, and
where `C` and a bias are added. Several of these choices depend on the problem shape, and some
depend on the batch size.

This matters in practice:

- **Batch invariance in LLM inference.** Thinking Machines Lab
  ([*Defeating Nondeterminism in LLM Inference*](https://thinkingmachines.ai/blog/defeating-nondeterminism-in-llm-inference/),
  Horace He, September 2025) traced nondeterministic outputs at temperature 0 mainly to kernels
  that are not batch-invariant: a request's numerics depend on the batch it is served in, and
  split-K reductions chosen for small batches are one cause. Their fix compiles one kernel
  configuration for all shapes; with default kernels, 1,000 completions at temperature 0 gave 80
  distinct outputs, and with batch-invariant kernels all 1,000 were identical. SGLang
  ([deterministic inference](https://lmsys.org/blog/2025-09-22-sglang-deterministic/), building on
  those kernels) and vLLM ([batch invariance](https://docs.vllm.ai/en/latest/features/batch_invariance.html),
  `VLLM_BATCH_INVARIANT=1`, in beta) now ship such modes, at a cost in throughput.
- **Libraries promise little.** cuBLAS guarantees
  [bitwise identical results](https://docs.nvidia.com/cuda/cublas/index.html#results-reproducibility)
  run to run only for one toolkit version on GPUs of the same architecture with the same number
  of SMs, with conditions on streams and workspaces. PyTorch states that
  [completely reproducible results](https://docs.pytorch.org/docs/stable/notes/randomness.html)
  are not guaranteed across releases, commits or platforms.
- **Autotuning.** An autotuner that picks the fastest configuration per shape can pick
  configurations with different numerics for different shapes, or on a different day.
- **Across GPUs.** The same schedule gives different bits on different matrix multipliers, since
  their block FMAs align, truncate and round differently.

Practitioners' working rule is that only an identical schedule reproduces. The algebra makes that
rule exact: it says which schedule changes are harmless on which hardware, proves it, and shows
with a concrete input that every other change is harmful. It also finds the exceptions, where
two schedules that look different always agree.

## Background: block FMAs

A matrix multiplier does not add one product at a time. Following Khattak and Mikaitis
([NVIDIA](https://arxiv.org/abs/2512.07004); with Graziani for
[AMD](https://arxiv.org/abs/2609.14845)), one **block FMA** computes `d = c + a₁b₁ + … + a_K b_K`
for an FMA size `K` (`N_FMA`) of 1 to 16, with a binary32 accumulator `c` and output `d`, and an
MMA or MFMA instruction whose inner dimension `k` exceeds `K` is a chain of `k / K` block FMAs, in
increasing `k`, each block's output being the next block's `c` (see [instructions and
chaining](/MMAlgebra/model/instructions/)). How a block forms its sum is what differs:

| Variant | `K` (fp16) | How one block FMA adds |
| --- | ---: | --- |
| V100, A100, H100 Tensor Cores | 4, 8, 16 | Exact products in denormalized form; every term, `c` included, aligned to the largest exponent with `23 + n_eab` fractional bits (0, 1, 2 extra alignment bits) and truncated; one exact multi-term addition; truncation to binary32 ([the model](/MMAlgebra/model/), [variants](/MMAlgebra/model/variants/)) |
| CDNA 1 (MI100) | 4 | Exact sum of `c` and the products, rounded once to nearest ([correct rounding](/MMAlgebra/amd/architectures/#cdna-1-mi100-correct_rounding)) |
| CDNA 2 (MI210, MI250) | 4 | Each product rounded to binary32, pairwise sums `fl{fl{p₁ + p₂} + fl{p₃ + p₄}}`, then `c` added last; subnormals flushed ([pairwise sums](/MMAlgebra/amd/architectures/#cdna-2-mi210-mi250-pair_wise_sum)) |
| CDNA 3 (MI300) | 8 | Products aligned to their largest exponent with 24 fractional bits; `c` added late, with rounding down; final rounding to nearest ([global alignment](/MMAlgebra/amd/architectures/#cdna-3-mi300a-mi300x-algorithms-1-and-2)) |
| SFMA (fp32 inputs, all CDNA) | 1 | A sequential FMA, each step rounded to nearest |

Every variant above has a bit-level Lean model on this site, validated against recorded or
published hardware outputs ([NVIDIA](/MMAlgebra/model/validation/), [AMD](/MMAlgebra/amd/validation/)).
The algebra uses the models as its semantics, through a Python port that agrees with them bit for
bit on 1,800 random blocks.

## The algebra

### Terms

Fix one output entry, with products `pᵢ = aᵢbᵢ` of a row of `A` and a column of `B`. A schedule
for that entry is a term:

| Term | Meaning |
| --- | --- |
| `0` | The zero accumulator (a product computed with `β = 0`, or with `C` added later) |
| `c` | The initial accumulator, the entry of `C` |
| `blk(t, I)` | One block FMA whose accumulator input is the value of `t` and whose products are the set `I` of at most `K` indices; the other slots hold zero pairs |
| `t ⊕ u` | A binary32 round-to-nearest-even addition, done outside the matrix multiplier (combining split-K partials, or adding `C` or a bias in the epilogue) |

Each product appears exactly once. A chain of blocks from `0` is written `[0 1 2 3] [4 5 6 7]`.
On V100 (`K = 4`), with `k = 16`:

| Schedule | Term |
| --- | --- |
| One pass, `C` in the first block | `blk(blk(blk(blk(c, 0–3), 4–7), 8–11), 12–15)` |
| One pass, `C` in the epilogue | `[0–3] [4–7] [8–11] [12–15] ⊕ c` |
| Split-K by two, partials added | `blk(blk(c, 0–3), 4–7) ⊕ [8–11] [12–15]` |
| Stream-K, cut after 12 products | `blk(blk(blk(c, 0–3), 4–7), 8–11) ⊕ [12–15]` |

The k-tile depth `BLOCK_K`, the tile shapes, the number of warps and the number of pipeline
stages do not appear: they change which thread computes an entry and when, but not the sequence of
block FMAs that the entry goes through, as long as the products are still consumed in increasing
`k`. Neither does the instruction shape, as long as the instruction's `k` is a multiple of `K`:
one `k = 16` instruction on V100 and two `k = 8` instructions are the same four blocks.

Two terms are **equivalent** on a variant when they produce the same output word, sign of zero
included, on every input (an input on which one overflows must make the other overflow too).

### A hand-sized example

Take three products, `x = 1.5 × 1.5 = 2.25` and `y = z = 2^-12 × 2^-11 = 2^-23` (fp16 words
`0x3e00`, `0x0c00`, `0x1000`), and three schedules for them:

| Schedule | V100 | A100, H100 | CDNA 1 | CDNA 2 | CDNA 3 |
| --- | --- | --- | --- | --- | --- |
| One block `[x y z]` | `2.25 + 2^-22` | `2.25 + 2^-22` | `2.25 + 2^-22` | `2.25` | `2.25 + 2^-22` |
| Two blocks `[x] [y z]` | `2.25` | `2.25 + 2^-22` | `2.25 + 2^-22` | `2.25 + 2^-22` | `2.25 + 2^-22` |
| Split-K `[x] ⊕ [y z]` | `2.25 + 2^-22` | `2.25 + 2^-22` | `2.25 + 2^-22` | `2.25 + 2^-22` | `2.25 + 2^-22` |

On V100 the single block aligns to the largest exponent among its terms, which is `0` (the
product `x` keeps the exponent sum `0 + 0` with significand `2.25`), so the grid is `2^-23` and
both small products survive. In the two-block schedule, the first block returns `2.25`, which as a
binary32 accumulator has exponent `1`; the second block aligns to `2^(1 − 23) = 2^-22`, and both
products of `2^-23` are truncated away. A100 and H100 keep one or two extra alignment bits, so the
same input does not separate these schedules there (other inputs do). On CDNA 2 the order of
events is reversed: the single block adds `y` to `x` first in its pairwise tree, and `2.25 + 2^-23`
is a tie that rounds to even, `2.25`, twice; the chain adds `y + z = 2^-22` first.

The same products show early and late accumulation of `C` on V100. With `c = 2.25`,
`blk(c, {y, z})` returns `2.25`, while `c ⊕ [y z]` returns `2.25 + 2^-22`. In Lean:
[`MMAlgebraTCTests.v100_block_boundary`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/tests/MMAlgebraTCTests/Examples.lean#L17), [`MMAlgebraTCTests.a100_block_boundary`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/tests/MMAlgebraTCTests/Examples.lean#L29) and
[`MMAlgebraMCTests.cdna2_block_boundary`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/tests/MMAlgebraMCTests/Examples.lean#L13).

## Laws by architecture

A **law** is an equation between terms that holds for every input. The table lists the candidate
laws and where they hold; the counts below it are violations in 300 random trials per variant
(the inputs mix normal, subnormal and wide-exponent words).

| Law | Tensor Cores | CDNA 1 fp16 | CDNA 2 | CDNA 3 | SFMA |
| --- | --- | --- | --- | --- | --- |
| Products in a block act as a multiset | proved | proved | only the 8 symmetries of the pairwise tree | proved | n/a |
| Zero products are invisible | proved | holds | holds, slot by slot | holds | holds |
| `t ⊕ u = u ⊕ t` | holds | holds | holds | holds | holds |
| A one-product first block merges into the next: `[x] [J] = [x J]` | fails | holds | fails | fails | n/a |
| Two one-product blocks added: `[x] ⊕ [y] = [x y]` | fails | holds | holds | fails | n/a |
| `c` splits off: `blk(t, I) = t ⊕ blk(0, I)` | fails | fails | holds | fails | fails |
| Negating every input negates the output | holds | holds | holds | fails | holds |

| Violations / 300 | V100 | A100 | H100 | CDNA 1 | CDNA 2 | CDNA 3 | SFMA |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Permute the products of a block | 0 | 0 | 0 | 0 | 25 | 0 | 0 |
| Move a block boundary by one product | 36 | 51 | 48 | 33 | 43 | 48 | n/a |
| Merge a one-product first block | 10 | 8 | 4 | 0 | 41 | 31 | n/a |
| `[x] ⊕ [y] = [x y]` | 35 | 34 | 47 | 0 | 0 | 17 | n/a |
| `c` splits off a block | 121 | 117 | 123 | 23 | 0 | 42 | 24 |
| Split-K, chain of 3 blocks as 2 + 1 | 106 | 108 | 129 | 25 | 0 | 47 | 26 |
| Negate every input | 0 | 0 | 0 | 0 | 0 | 40 | 0 |

SFMA has `K = 1`, so the laws about several products in one block do not apply to it (n/a).
The random tests found no violation of a law marked as holding, and a violation of every law
marked as failing. On CDNA 2 the permutations that violate are the 199 trials outside the 8
symmetries of the tree (25 violations); the 101 inside them gave none.

### Why each law holds or fails

**Products act as a multiset** wherever a block adds its terms in one step after aligning them to
a common exponent: the largest exponent and the exact sum of truncated terms do not depend on the
order. In Lean this is [`MMAlgebra.TC.evalBlock_bits_perm`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Block.lean#L89) for every Tensor Core model, and
[`MatrixCore.accumulate_perm`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Order.lean#L37) for the sum that CDNA 1 and CDNA 3 round at the end of a block. CDNA 2's block is a fixed tree
`((p₁ + p₂) + (p₃ + p₄))` with a rounding at every node, so only the tree's own symmetries (swap
within a pair, swap the pairs) preserve it ([`MatrixCore.pairWiseSum_order_dependent`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Order.lean#L53)).

**Zero products are invisible**: a product with a zero factor adds nothing to the exact sum and
is ignored when the alignment exponent is chosen, so it can replace an empty slot and the reverse
([`MMAlgebra.TC.evalBlock_bits_zero`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Block.lean#L230)). A block with no products returns its accumulator input
when that input is finite and not `−0` ([`zero_products_passthrough`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/Instruction.lean#L147)). The exception is real: in
the random tests, one SFMA block returned `−0` (a tiny negative product rounded to zero), and an
empty block after it returned `+0`. On CDNA 2 a zero product prunes
its leaf of the tree, but moving it to another slot reshapes the tree.

**The merge law of CDNA 1** follows from correct rounding: a block returns the binary32 value
nearest to the exact sum of `c` and its products ([`MatrixCore.correctRounding_nearestEven`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/CorrectRounding.lean#L30)),
and an fp16 product (at most 22 significant bits, magnitude between `2^-48` and `2^32`) is exactly
representable in binary32. So a block from `0` holding one product returns that product exactly,
and `[x] [J]` rounds the same exact sum as `[x J]`; likewise `[x] ⊕ [y]` and `[x y]` both round
`x + y`. On the Tensor Cores the merge fails because the product and the accumulator are aligned
differently: inside a block, `x` takes part with its exponent sum, while as an accumulator it has
been normalized, as in the hand-sized example.

**The `c`-split law of CDNA 2** follows from the block formula
`d = fl{c + fl{fl{p₁ + p₂} + fl{p₃ + p₄}}}` ([`MatrixCore.pairwiseSum_four`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/PairWiseSum.lean#L24)): `c` is added last,
in one binary32 addition. The equation holds with an addition that, like CDNA 2's own, flushes
subnormal inputs and results to zero. One consequence: a split-K whose last part is a single
block gives the unsplit chain's bits on CDNA 2. On every other variant, `c` takes part in the
block's alignment or rounding (early accumulation), and moving it changes the result.

**Negation** is a symmetry of truncation toward zero and of rounding to nearest. CDNA 3 rounds
down in two of its steps, so negating every input can change the magnitude of the output
([`MatrixCore.globalAlignment_sign_asymmetric`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Order.lean#L71)). This is not a schedule law, but where it holds, a
separating input still separates after negation.

### Normal forms: three algebras

Applying the laws in one direction gives a normal form for each term, and two terms with the same
normal form are equivalent by the laws.

- **Rigid** (V100, A100 and H100, fp16 and bf16; CDNA 3; SFMA). A block is determined by its
  accumulator input's normal form and its set of products, and an addition by the unordered pair
  of its operands. A chain from `0` is an **ordered partition** of its products into blocks of at
  most `K`. With `K ≥ 4`, over 3 products there are 13 chains and 28 terms with additions, in 13
  and 28 classes, and over 4 products, 301 terms in 301 classes.
- **Correctly rounded nodes** (CDNA 1 fp16). Every block and every addition rounds the exact sum
  of its children, so a term is a **rooted tree** whose internal nodes have at least two children,
  in no order, and whose leaves are the products and `c`. Over 2 products all schedules agree; over
  3 products the 28 terms fall into 4 classes (`((x + y) + z)`, `((x + z) + y)`, `((y + z) + x)`, and
  the fan `x + y + z`); over 4 products, 301 terms fall into 26.
- **Summation trees** (CDNA 2). Blocks contribute their pairwise trees, and `c` and every addition
  are further binary32 additions, so a term is an **unordered binary tree** of additions. Over 3
  products, the 1,608 terms (counting slot positions) fall into the 3 binary trees; over `n`
  products there are `(2n − 3)!! = 1, 3, 15, 105, …` classes.

CDNA 1 bf16 is a boundary case. Its blocks are correctly rounded too, but a bf16 product can fall
below binary32's range, and then a one-product block rounds it: with `p₀ = 2^-149` and
`p₁ = 2^-150`, `[p₀] [p₁]` returns `2^-148` (the tie `1.5 · 2^-149` rounds to even) while
`[p₁] [p₀]` returns `2^-149`, because `[p₁]` alone rounds `2^-150` to `+0`
([`MMAlgebraMCTests.cdna1BF16_tie`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/tests/MMAlgebraMCTests/Examples.lean#L23)). Over all inputs its chains are rigid: the twelve
chain patterns of three products are pairwise separated.

## Completeness

**Statement.** On each modeled variant, two terms with different normal forms produce different
output words on some input. In other words, the laws above are all the laws: whatever they do not
equate, the hardware model separates. The status of this statement, proved in part and checked
in full on small terms, is at the end of this section.

The argument has three steps.

1. **Restriction.** Set `aᵢ = 0` for every product outside a support `S`. Every block then behaves
   as the block with those slots emptied (zero products are invisible), so the term evaluates as
   its restriction to `S`, with empty blocks and additions of an all-zero part dropped. In Lean,
   [`MMAlgebra.TC.chain_restrict`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Chain.lean#L41) proves this for chains on every Tensor Core model. Dropping an
   empty block or an addition of `+0` needs the value passing through to be other than `−0`.
2. **Small supports.** Two different normal forms already differ after restriction to some
   support of at most three products. For rigid chains, two products suffice: an ordered partition
   is the same thing as a total preorder ("`x` is not after `y`"), and a total preorder is
   determined by how it orders each pair. For trees, three suffice: a rooted tree whose internal
   nodes have at least two children is determined by its restrictions to triples of leaves, a
   classical fact about phylogenetic trees. For terms
   with additions the step was checked exhaustively: over 4 products, every one of the 45,150 pairs
   of distinct rigid normal forms (325 on CDNA 1, 14,535 on SFMA) differs on a support of at most
   3; for chains it holds over up to 6 products (4,670 rigid classes, 1,436 on CDNA 1).
3. **Base witnesses.** For each pair of different normal forms over at most three products, there
   is an input that separates them; planted on the support, with zero products elsewhere, it
   separates the full terms.

The base witnesses are concrete. On V100 and A100, take `x = 0.0066986… × 0.0047111… ≈ 3.156·10⁻⁵`
and `y = 56224 × (105 · 2^-24) ≈ 0.351877`:

| Chain | Output | |
| --- | --- | --- |
| `[x y]` | `0.35190868377685547` | `0x3eb42d60` |
| `[x] [y]` | `0.35190868377685547` | `0x3eb42d60` |
| `[y] [x]` | `0.35190874338150024` | `0x3eb42d62` |
| exact `x + y` | `0.35190877068…` | |

The product `y` has a subnormal factor, so the exponent the hardware sees for it is `15 + (−14) =
1`, although its value is about `0.35`. In any block that holds `y`, the grid is `2^(1 − 23) =
2^-22`, and `x` keeps only 132 units of `2^-22`. When `y` has been rounded by an earlier block, it
enters the next block as a binary32 accumulator with exponent `−2`; the grid is `2^-25`, and 1,058
units of `2^-25` of `x` survive, two units of the last place more. The pair `[x] [y]` against `[x y]`
is separated by exchanging the roles of the two products. Lean turns this into a theorem about
all chains: [`MMAlgebra.TC.complete_pair`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Completeness.lean#L377) shows that two chains holding `x` and `y` in different
patterns differ on an input supported on `{x, y}`, given five concrete block evaluations, which
[`MMAlgebra.TC.v100_complete_pair`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Completeness.lean#L469), [`MMAlgebra.TC.a100_complete_pair`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Completeness.lean#L485) and
[`MMAlgebra.TC.h100_complete_pair`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Completeness.lean#L504) discharge by kernel evaluation (H100 needs different words:
`x = 0x0052 × 0x6587`, `y = 0x0ba7 × 0x3ff9`, where `[x] [y]` is three units in the last place
above `[x y] = [y] [x]`).

On the AMD models the witnesses are kernel-checked: products `p₀ ≈ 0.002458`, `p₁ ≈ 12.41` and
`p₂ ≈ 0.000948` give `((p₀ + p₁) + p₂) = 12.4131507…` but `((p₀ + p₂) + p₁) = 12.4131498…` on
both CDNA 1 and CDNA 2, and on CDNA 1 the chains `[p₀] [p₁ p₂]` and `[p₀ p₁ p₂]` agree with the
second, as the merge law says ([`MMAlgebra.MC.cdna1_trees`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Witnesses.lean#L21), [`MMAlgebra.MC.cdna2_trees`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Witnesses.lean#L35)). On
CDNA 3, two products separate the three chain patterns ([`MMAlgebra.MC.cdna3_pair`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Witnesses.lean#L47)).

**Status.** Every enumeration agrees with the statement: chains and terms over 2 and 3 products
on all variants, and terms over 4 products on V100, H100, CDNA 1, CDNA 3 and SFMA, gave no unsound
class, and every pair of classes was separated, directly by an input found by search or through a
support of at most three products. The exceptions are on CDNA 1 bf16: its chains needed the tie
input above, and its terms with additions near binary32's underflow threshold are not yet all
separated. In Lean, completeness is proved for two products on V100, A100 and H100. Two lemmas would give it for
all chains there: that an ordered block partition is determined by its pairwise patterns (step 2),
and that an fp16 block started from `+0` never returns `−0` (step 1, to drop empty parts).

## One instruction is not one rounding

A natural abstraction treats each matrix instruction as one operation: it adds its `k` products
and the incoming accumulator exactly and rounds once, so the products inside one instruction have
no order of their own, and the reduction order is the chain of instructions. Yang, Riasanovsky,
Deng and Sarkar ([arXiv:2609.11356](https://arxiv.org/abs/2609.11356), September 2026) state this
assumption for NVIDIA's fp16, bf16 and tf32 instructions (their Section 3.2.1) and report that
their measurements, made on GB300, agree with it. On the models of V100, A100 and CDNA 1–3 it is
both unsound and incomplete, because an instruction whose `k` exceeds the FMA size is a chain of
block FMAs.

**Unsound: it accepts a rewrite that changes the bits.** Exchange the products at `k = 0` and
`k = 15` inside one `k = 16` instruction. A single rounding cannot see the change; a chain of
blocks can, because the two products move to different blocks.

| Variant | Blocks per `k = 16` instruction | In order | `k = 0` and `k = 15` exchanged | Lean |
| --- | --- | --- | --- | --- |
| V100 (`HMMA.844`) | 4 × 4 | `−14.43653488…` | `−14.43653583…` | [`MMAlgebra.TC.v100_wmma_swap`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/OneRounding.lean#L17) |
| A100 (`HMMA.1688`) | 2 × 8 | `4.57211368…·10⁻⁴` | `4.57211397…·10⁻⁴` | [`MMAlgebra.TC.a100_wmma_swap`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/OneRounding.lean#L27) |
| CDNA 1 | 4 × 4 | `487.12280…` | `487.12277…` | [`MMAlgebra.MC.cdna1_k16_swap`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/OneRounding.lean#L16) |
| CDNA 2 | 4 × 4 | `239.79177…` | `239.79176…` | [`MMAlgebra.MC.cdna2_k16_swap`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/OneRounding.lean#L26) |
| CDNA 3 | 2 × 8 | `−0.0011084491…` | `−0.0011084490…` | [`MMAlgebra.MC.cdna3_k16_swap`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/OneRounding.lean#L36) |
| H100 (`HMMA.16816`) | 1 × 16 | never changes | | [`MMAlgebra.TC.evalBlock_bits_perm`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Block.lean#L89) |

Each witness has two or three nonzero products and zeros elsewhere; the outputs differ in the last
place.

**Incomplete: it rejects rewrites that preserve the bits.** One `k = 16` instruction and two
`k = 8` instructions round a different number of times under the abstraction, but on V100, A100
and CDNA 1–3 both are the same chain of block FMAs and give the same bits on every input. On
CDNA 2, moving `C` out of a block into a separate addition preserves the bits (the `c`-split law),
while the abstraction counts one rounding against two. A checker built on the abstraction would
keep such kernels apart, and would merge kernels that differ only in the order of products inside
one instruction. Whether the second situation arises in compiled kernels has not been checked
here.

## Deciding equivalence

Completeness turns into a decision procedure that always gives evidence:

1. Compute both normal forms. If they are equal, the terms are **equivalent**, and the chain of
   laws that rewrote one into the other is the certificate.
2. Otherwise, search the supports of at most three products for one on which the restricted
   normal forms differ; step 2 of the completeness proof guarantees one exists.
3. Look up an input that separates the two small restricted terms (a finite table per variant,
   filled by search), place it on the support, and set every other product to zero.
4. Evaluate both full terms on the model and confirm that the output words differ. The procedure
   returns this input only after the check, so a wrong table entry or a gap in the theory would
   surface as an undecided case rather than a wrong answer.

The normal forms take nearly linear time in the size of the terms, and the support search
examines `O(n³)` restrictions for `n` products. On 210 random pairs of chain and split-K schedules over 6
products (30 per variant on V100, A100, H100, CDNA 1, 2 and 3, and SFMA), it found 40 pairs
equivalent and 170 different, and gave a separating input, confirmed on the model, for every one
of the 170; no pair was left undecided.

## How far apart can two schedules be?

Bitwise equality is a yes-or-no question. When two schedules are not equivalent, the next
question is how far apart their results can be. The answer has three parts: a bound that holds
for every input, the worst case that an adversarial search finds, and the typical difference on
realistic data. Throughout, `M = Σ|aᵢbᵢ| + |c|` is the magnitude of an entry's inputs and
`u = 2^-24` is the unit roundoff of binary32.

### A structural bound

Every operation in a term has a proven error bound. The per-block theorems of the two models
bound the distance between a block's output and the exact sum of its inputs, and a binary32
addition rounds once:

| Operation | Error of one operation | Per unit of input magnitude, normal operands | Lean |
| --- | --- | --- | --- |
| V100, A100, H100 block FMA | `< (K + 1)·2^(η − F) + ulp(D)` | `12u`, `11u`, `10.5u` | [`evalBlock_error_bound`](https://github.com/pauljiang03/MMAlgebra/blob/main/TensorCore/TC/ErrorBounds.lean#L81) |
| CDNA 1 block, SFMA step | `≤ 2^-24 A + 2^-150` | `u` | [`MatrixCore.correctRounding_apriori`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/AprioriBounds.lean#L76) |
| CDNA 2 block | `≤ (flushed inputs) + 2^-21 A + 2^-120` | `8u` | [`MatrixCore.pairwise_apriori`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/AprioriBounds.lean#L473) |
| CDNA 3 block | `≤ 2^-23 A + (n + 4)·2^(e_max − 24) + 2^-149` | `14u` | [`MatrixCore.aligned_apriori`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/AprioriBounds.lean#L238) |
| binary32 addition | `≤ 2^-24 \|x + y\| + 2^-150` | `u` | [`MMAlgebra.MC.add_le`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Bound.lean#L122) |

Here `A = |c| + Σ|p|` for the block. For the Tensor Cores the per-unit constant follows from the
model bound because, with normal operands, every term's magnitude is at least 2 to the power of
its exponent, so `2^η ≤ A`, and the truncated output satisfies `ulp(D) ≤ 2^-23 |D| + 2^-149` with
`|D| ≤ A`; CDNA 3 is the same with `2^(e_max) ≤ A`. With a subnormal factor, 2 to the power of a
product's exponent can exceed its magnitude by a factor of up to `2^10` per subnormal fp16 factor,
and the bound then uses the exponent itself. This matters in practice: error analyses often assume that a
block of `n` terms is within `γ_n Σ|aᵢbᵢ|` of its exact sum, with `γ_n = nu/(1 − nu)`, as if each
addition rounded with unit roundoff `u`. With one subnormal fp16 factor, which sets the block's
alignment while contributing little to its value, a block exceeds that bound by up to 99 times on
V100, 20 times on A100 and 5 times on H100 in a search over the model, and a kernel-checked V100
block exceeds it by more than 50 times ([`MMAlgebra.TC.SubnormalRemark.v100_subnormal_exceeds_gamma`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/SubnormalGamma.lean#L28)).
The model's own bound, stated with the alignment exponent, remains valid; a checker that assumed
`γ_n` would not be.

A block's accumulator input is a computed value, so its magnitude is at most the magnitude of its
subterm plus that subterm's error. The bound therefore composes over the term:

```text
E(blk(t, I)) = E(t) + err_block(M(t) + E(t), I)
E(t ⊕ u)     = E(t) + E(u) + 2^-24 (M(t) + E(t) + M(u) + E(u)) + 2^-150
```

Unrolled, each product contributes its magnitude times the sum of the constants of the operations
it passes through. A chain of `m` block FMAs costs about `m` times the block constant: for
`k = 1024` with `C` in the epilogue, `3,073u·M` (about `1.8·10⁻⁴ M`) on V100, `1,409u·M` on A100,
`673u·M` on H100 and `257u·M` on CDNA 1. A split-K shortens the chains, which is why it is often
more accurate than the unsplit loop, though not bitwise equal to it.

**Two schedules.** For two terms over the same products and `c`, on one GPU or on two,
`|t₁(x) − t₂(x)| ≤ E(t₁) + E(t₂)`. **Shared work does not diverge**: when both terms contain the
same subterm, evaluated on the same GPU, that subterm has the same computed value in both, so it
counts as an exact leaf, and the bound counts only the work after the point where the schedules
part. For `k = 64` on V100, the plain bound for no split against split-K by two is `291u·M`, and
with the first half's chain as a shared prefix it is `99u·M`. Two runs of a split-K by four with
atomic additions share all four partials, so they differ only through the order of four additions:
the bound is `8u·M`, although each partial alone carries an error bound of hundreds of `u·M`.
(The `k = 64` figures are the bound evaluated on the worst input found below.)

**The exact region.** If every block FMA and every addition of two terms is exact, the terms
agree exactly. A sufficient condition is the one the Ozaki schemes use: integer operands of at
most 11 bits (for fp16), an integer `c`, and `|c| + Σ|aᵢbᵢ| < 2^24`. Then every partial sum is a
binary32 integer, every block of every model returns the exact sum of its inputs (the exactness
theorems of the Ozaki development, cancellation included), and every schedule returns the exact
result. This is the hinge of the whole picture: inside the exact region every schedule agrees,
and outside it, by completeness, the schedules that the laws do not equate disagree on some input.
For example, products `2047·2047`, `2047·1000`, `−1000·3` and `3·3` with `c = 12345` give
`6,246,563` under one block from `c`, a split-K whose partials are added before `c`, and a
reversed chain with `c` in the epilogue alike. The total magnitude is more than needed: every
running value of every order and grouping of the products is the sum of some of them, so it lies
between minus the total of the negative products and the total of the positive ones. On the Tensor
Core model every schedule is therefore exact as soon as the positive products and the negative
products each total below `2^24` ([`MMAlgebra.TC.runBlocks_exact_of_posneg`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/ScheduleFreeExact.lean#L69),
[`MMAlgebra.TC.schedules_agree_of_posneg`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/ScheduleFreeExact.lean#L94)); for sign-balanced data that allows up to twice the
usual total.

In Lean, the composition is proved once for any matrix multiplier with a binary32 addition
([`MMAlgebra.eval_error`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebra/Divergence.lean#L51), [`MMAlgebra.divergence`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebra/Divergence.lean#L138), [`MMAlgebra.divergence_shared`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebra/Divergence.lean#L160)), and
instantiated for the correctly rounded models, SFMA and CDNA 1 ([`MMAlgebra.MC.block_le_cr`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Bound.lean#L67),
[`MMAlgebra.MC.cdna1_divergence`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Bound.lean#L153)). The exact region is proved on every Tensor Core model and on
the exact configurations of CDNA 1, 2 and 3 ([`MMAlgebra.TC.eval_agree`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Exact.lean#L172),
[`MMAlgebra.MC.eval_agree`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Exact.lean#L261), with the example [`MMAlgebraTCTests.v100_exact_region`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/tests/MMAlgebraTCTests/Examples.lean#L44)). The block
constants for the Tensor Cores, CDNA 2 and CDNA 3 are derived from the per-block theorems by the
argument above, which is not yet in Lean; the prototype checks the composed bound on 1,800 random
evaluations, subnormal operands included, with no violation.

### The worst case, and how tight the bound is

An adversarial search maximizes `|t₁(x) − t₂(x)| / M` over inputs with normal fp16 operands. It
starts from structured inputs and improves them by local changes, and every witness it reports is
checked on the model against the bound. The structured inputs that win are an **anchor and dust**:
one product, or `c`, of about `1`, and many products just below the anchor's alignment grid. On
V100, in a chain whose accumulator holds the anchor, every later block aligns to `2^-23` and
truncates every dust product it receives; a schedule that sums the dust first, from zero, loses
nothing. For `k = 1024`, `C` in the first block against `C` in the epilogue differ by
`2,040u·M`, about 1,020 dust products' worth of `2^-23` each.

For `k = 64`, with the shared-work bound:

| Pair, `k = 64` | V100 | A100 | H100 | CDNA 1 | CDNA 2 | CDNA 3 |
| --- | --- | --- | --- | --- | --- | --- |
| No split against split-K by 2 | 64 / 99 | 32 / 47 | 18 / 24 | 5.4 / 11 | 5.4 / 67 | 4 / 11 |
| No split against split-K by 4, pairwise | 96 / 148 | 54 / 70 | 24 / 36 | 12 / 16 | 12 / 100 | 6 / 16 |
| `C` in the first block against the epilogue | 126 / 193 | 64 / 89 | 32 / 43 | 16 / 17 | 16 / 129 | 8 / 17 |
| Stream-K cut after 24 against after 16 | 65 / 136 | 26 / 66 | 12 / 37 | 2 / 6 | 2 / 20 | 2 / 6 |

Each cell is the worst case found over the bound, in units of `u·M`. The search reaches 31 to 94
percent of the bound on the Tensor Cores, CDNA 1 and CDNA 3, so the bound is tight within a factor
of about three there. On CDNA 2 it reaches about a tenth: the a-priori constant `2^-21` per block
is loose, since a block rounds only three times. The search gives lower bounds on the true worst
case; the bound is an upper bound.

### Typical differences

On realistic data the differences are small in absolute terms but almost always present. For
every pair of programs that are not equivalent, 69 to 100 percent of entries differ (about half
for two arrival orders of atomic additions), by a median of 1 to 25 ulps of the result on uniform,
normal and LLM-like data. Where an entry's result is much smaller than its magnitude `M`, as on
near-cancelling data, the difference in ulps of the result reaches hundreds or thousands.
Measured against `M`, typical differences stay below `23u·M`, one to two orders of magnitude
below the worst cases (CDNA 2 on LLM-like data aside, for a reason given below). The next section
gives the numbers program by program.

## How different can BLAS programs be?

A BLAS library chooses among many programs for the same matrix product. The table models a
realistic set for one problem size, `k = 1024` with fp16 inputs and binary32 output, on the A100
model, each compared with a reference program (no split-K, `C` added in the epilogue). Bitwise
equality is decided by the algebra; the bound is the constant form of the structural bound for
normal operands; the worst case is the best of an adversarial search; the typical columns give the
share of 200 entries that differ and the median difference in ulps of the result, on normal data
(entries of `A` and `B` drawn from `N(0, 1)`) and on LLM-like data (activations from `N(0, 1)` with
1 percent outlier channels 64 times larger, weights from `N(0, 0.02²)`).

| Program (A100), against the reference | Bitwise equal | Bound (`u·M`) | Worst found (`u·M`) | Normal data | LLM-like data |
| --- | --- | ---: | ---: | --- | --- |
| Other `BLOCK_K`, tile shapes, `k = 8` or `16` instructions | yes | 0 | 0 | 0% | 0% |
| `C` in the first block FMA | no | 2,817 | 1,014 | 100%, 25 ulps | 91%, 7.5 ulps |
| Split-K 2, partials added serially | no | 1,411 | 510 | 92%, 7 ulps | 92%, 10 ulps |
| Split-K 4, serial | no | 1,413 | 715 | 97%, 10 ulps | 95%, 14 ulps |
| Split-K 4, pairwise | no | 1,412 | 788 | 96%, 10 ulps | 96%, 14 ulps |
| Split-K 8, serial | no | 1,417 | 933 | 98%, 11 ulps | 98%, 15.5 ulps |
| Split-K 8, pairwise | no | 1,413 | 892 | 98%, 11 ulps | 96%, 15 ulps |
| Stream-K, cut after 384 products | no | 1,763 | 667 | 96%, 8 ulps | 94%, 11 ulps |
| Split-K 4 with atomic additions, two arrival orders | no | 8 | 2 | 48%, 0 ulps | 50%, 0.5 ulps |
| CUDA-core fallback (sequential binary32 FMA) | no | 2,434 | 1,024 | 96%, 12 ulps | 98%, 16 ulps |

The same program on different GPUs:

| Reference program on | Bitwise equal | Bound (`u·M`) | Worst found (`u·M`) | Normal data | LLM-like data |
| --- | --- | ---: | ---: | --- | --- |
| A100 and H100 | no | 2,082 | 546 | 92%, 3 ulps | 91%, 6 ulps |
| V100 and A100 | no | 4,482 | 1,021 | 97%, 10.5 ulps | 97%, 18 ulps |
| A100 and CDNA 3 | no | 3,202 | 1,018 | 95%, 12 ulps | 98%, 17 ulps |
| H100 and CDNA 3 | no | 2,466 | 516 | 96%, 10 ulps | 98%, 13 ulps |
| A100 and CDNA 1 | no | 1,666 | 1,022 | 97%, 11.5 ulps | 98%, 17 ulps |
| A100 and CDNA 2 | no | 3,458 | 1,024 | 96%, 11.5 ulps | 100%, 130.5 ulps |

And one program change, split-K by 2 against the reference, on every modeled GPU:

| Split-K 2 against the reference | V100 | A100 | H100 | CDNA 1 | CDNA 2 | CDNA 3 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Bound (`u·M`) | 3,075 | 1,411 | 675 | 259 | 2,051 | 1,795 |
| Worst found (`u·M`) | 1,020 | 510 | 256 | 128 | 128 | 64 |
| Entries that differ, normal data | 86% | 92% | 92% | 80% | 77% | 72% |
| Median difference, normal data | 4 ulps | 7 ulps | 6 ulps | 2 ulps | 2 ulps | 1 ulp |

Three observations stand out. First, nearly every program change alters nearly every entry, by a
few ulps on typical data and by up to about a thousand `u·M` on adversarial data; only the changes
the algebra proves harmless (tile shapes, `BLOCK_K`, instruction shapes) leave every bit in place.
Second, the bounds and the worst cases shrink from V100 to A100 to H100, with longer blocks and
more extra alignment bits, and are smallest on the correctly rounded CDNA 1 and on CDNA 3, whose
late addition of `c` defeats the anchor-and-dust inputs; typical medians are a few ulps on every
GPU. Third, CDNA 2 differs from
every other GPU on LLM-like data by far more than elsewhere: about 0.24 percent of weights drawn
from `N(0, 0.02²)` are fp16 subnormals, which CDNA 2 flushes to zero, so their products vanish.

These are modeled programs. The internals of cuBLAS and rocBLAS are not public, so which program a
library runs for a given shape is not known here; probing a real library's reduction order by
testing, in the manner of FPRev, needs GPU access and is future work. The study covers fp16
inputs at one size; the worst cases are lower bounds from a heuristic search, and the bounds
assume normal operands. The full results, including uniform and near-cancelling data and the 99th
percentiles, are in the prototype's recorded output.

## Making every schedule agree: pinned and anchored accumulation

The algebra says that on Tensor Cores and CDNA 3 only identical schedules reproduce, and the bounds
say how far apart the others can be. Both statements are about the native arithmetic. If a kernel
may add a few products of its own, every schedule can be made to agree, on Tensor Cores and CDNA 3,
at little or no cost, by making the hardware's truncation work on a grid that does not move. This
part is proved on the models and simulated on them; it has not yet been run on a GPU.

### The idea

A Tensor Core block FMA truncates every term toward zero on the grid `2^(η − F)`, where `η` is the
largest exponent of a nonzero term in the block. Two things make the result depend on the
schedule: `η` moves with the running value and with the products that share the block, and the
final truncation of the sum depends on the binade of the result. Both can be pinned down.

- **Pinned accumulation.** Put a cancelling pair of products `+2^α` and `−2^α` in every block FMA,
  and keep every other product, and the running value, at or below exponent `α`. Then `η = α` in
  every block, every product is truncated to the same grid `2^g` with `g = α − F`, and the pair
  cancels exactly. As long as the running value stays below `2^(g + 24)`, the sum is a binary32
  value and the final truncation loses nothing. Each block adds exactly `Σ trunc_g(aᵢbᵢ)`, and a
  chain returns `c₀ + Σ trunc_g(aᵢbᵢ)` over all its products: a fixed function of the multiset of
  products. Every order, every grouping into blocks, and every split-K gives the same bits, since
  the partial results are on the grid and add exactly in binary32. With the same `g`, V100, A100
  and H100 compute the same function. So does CDNA 3: it aligns the products among themselves, to
  their largest exponent with 24 fractional bits, which the pin fixes at `α`, and then adds a `c`
  on the grid without loss; there `g = α − 24`.
- **Anchored accumulation.** Start the accumulator at `1.5·2^α` instead of `0`, and subtract it at
  the end. While the running value stays in `[2^α, 2^(α+1))`, every block aligns to `α`, the
  exponent of its accumulator, truncates each product to `2^(α − F)`, and its final truncation is
  a floor on `2^(α − 23)`, which commutes with adding the on-grid accumulator. Each block then adds
  an increment that depends on its own products alone, and a chain returns the anchor plus the sum
  of the increments: every order of the blocks, and every split-K at block boundaries, gives the
  same bits, and no product slot is spent. On V100, where `F = 23`, the floor is the identity, so
  the increment is again a sum over products.

The constructions rest on exactly the features that make these matrix multipliers rigid:
truncation toward zero, and an alignment grid set by one exponent. CDNA 1 and CDNA 2 round to
nearest inside a block, so the position of the rounding moves with the running value, and neither
construction works there. CDNA 3 adds `c` after aligning the products among themselves, so an
anchor in `c` does not fix the alignment, while a pin among the products does.

| Model | Pinned | Anchored |
| --- | --- | --- |
| V100, A100, H100 | proved ([`MMAlgebra.TC.runBlocks_pinned`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Pinned.lean#L214)) | proved, block by block ([`MMAlgebra.TC.runBlocks_anchored`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Anchored.lean#L150)) |
| CDNA 3 | proved ([`MMAlgebra.MC.runBlocks_pinned`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Pinned.lean#L195)) | fails ([`MMAlgebra.MC.PinnedCases.cdna3_anchored_order_dependent`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Counterexamples.lean#L83)) |
| CDNA 1 | fails ([`MMAlgebra.MC.PinnedCases.cdna1_pinned_order_dependent`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Counterexamples.lean#L43)) | fails ([`MMAlgebra.MC.PinnedCases.cdna1_anchored_order_dependent`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Counterexamples.lean#L31)) |
| CDNA 2 | fails ([`MMAlgebra.MC.PinnedCases.cdna2_pinned_order_dependent`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Counterexamples.lean#L70)) | fails ([`MMAlgebra.MC.PinnedCases.cdna2_anchored_order_dependent`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Counterexamples.lean#L55)) |

Each failure is a kernel-checked pair of block orders whose outputs differ in the last place. A
kernel-checked demonstration on the Tensor Cores uses 28 fp16 products with values between about
`−4` and `4`:

| Chain | Output |
| --- | --- |
| H100, native, two block FMAs in one order | `−3.86069369…` (`0xc077159b`) |
| H100, native, the other order | `−3.86069393…` (`0xc077159c`) |
| H100, pinned, both orders (pin `±2^10`, grid `2^-15`) | `−3.86065674` (`0xc0771500`) |
| A100, pinned, five blocks of six products in two orders (pin `±2^9`) | `−3.86065674` (`0xc0771500`) |
| V100, pinned, fourteen blocks of two products in two orders (pin `±2^8`) | `−3.86065674` (`0xc0771500`) |

The pinned value is the exact sum of the 28 products, each truncated toward zero to a multiple of
`2^-15` ([`MMAlgebra.TC.PinnedDemo.h100_native_order_dependent`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/PinnedDemo.lean#L70),
[`MMAlgebra.TC.PinnedDemo.pinned_agree_v100_a100_h100`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/PinnedDemo.lean#L78)). In simulation, eleven schedules of
`k = 1024` products (sequential, split-K by 2, 3, 4 and 8, and six random stream-K partitions
combined in random order) gave up to 11 distinct native results per entry, and exactly one
anchored result on every Tensor Core model, fp16 and bf16 (two or three on CDNA 1 to 3). Pinned
accumulation at `k = 1680` gave the same bits on V100 (anchored, at the same grid), A100, H100 and
CDNA 3 in all 40 fp16 cases, and on A100, H100 and CDNA 3 in all 40 bf16 cases, always equal to the
truncated sum.

### The algorithm

1. **A bound per entry.** Compute `β = ‖aᵢ‖·‖bⱼ‖` for each output entry. By Cauchy–Schwarz it
   bounds every partial sum of every schedule; it costs `O((m + n)k)` and does not depend on the
   batch.
2. **Pinned.** Choose `g = ⌈log₂ β⌉ + 1 − 24`, so that every partial sum stays below `2^(g + 24)`,
   and `α = g + F` for each GPU (`g + 25` on H100, `g + 24` on A100 and CDNA 3, `g + 23` on V100);
   with normal operands every product's exponent is then below `α`. Put one pin pair `±2^α` in every block FMA; on A100, whose `k = 16` instruction is two blocks of
   eight, that means one pair in each half. Start from `0`. Partial results of a split-K add
   exactly in binary32.
3. **Anchored.** Start at `1.5·2^E`, with `E` chosen from `β` so that the running value stays in
   its binade, and subtract the anchor exactly at the end. The anchor must sit inside the MMA
   accumulator, as the `C` operand of the first instruction of the chain, not in a library's
   `β·C` epilogue, which adds it after the reduction.
4. **Bias correction (optional).** Truncation toward zero shortens each product by half a grid step
   on average; adding `2^(g−1)` times the number of positive products minus the number of negative
   ones removes most of that bias, deterministically.

The cost: anchored accumulation spends no slots, so it runs at full speed; pinned accumulation
spends two of the `K` slots of every block FMA, `16/14 = 1.14×` on H100 and `8/6 = 1.33×` on A100
and CDNA 3. On V100 a pin pair would take half of each four-slot block, but there anchoring
already computes the same function product by product. The norms add `O((m + n)k)` work.

### Accuracy, honestly

The result is fixed point: the grid is set in advance from `β`, not from the running value. The
table gives `log₂` of the median relative error against the exact product, for fp16 inputs on the
H100 model (30 entries each, 10 at `k = 16384`):

| Data | `k` | Native | Pinned | Pinned with bias correction |
| --- | ---: | ---: | ---: | ---: |
| Normal | 1024 | −19.6 | −13.5 | −15.2 |
| Normal | 4096 | −17.4 | −11.3 | −12.0 |
| Normal | 16384 | −15.4 | −9.6 | −10.9 |
| LLM-like | 4096 | −18.1 | −11.5 | −12.3 |
| Uniform on `[0, 1)`, same sign | 4096 | −15.4 | −11.0 | −18.1 |
| Strongly correlated rows | 4096 | −15.6 | −11.3 | −18.5 |
| Log-normal magnitudes, random sign | 4096 | −17.6 | −10.3 | −11.4 |

On random-sign data the grid must cover `‖a‖·‖b‖`, which exceeds `|a·b|` by about `√k`, so about
`½·log₂ k` bits are lost: six at `k = 4096`, which is the gap in the table (about `2^-11` to
`2^-13` against about `2^-17` natively). On same-sign data the slack is small, the loss comes from
the truncation bias, and with the correction pinned accumulation is more accurate than native.
Anchored accumulation is less accurate (on H100 at `k = 4096`, `2^-7.7` on normal data, `2^-11.5`
with its correction). Against the usual portable exact option, per-vector INT8 quantization with
an exact integer dot product, pinned accumulation of bf16 inputs is 5 to 9 bits more accurate on
normal and LLM-like data at `k = 1024` and `4096` (at `4096`, `2^-11.2` and `2^-12.0` against
`2^-6.1` and `2^-4.8`), and 3 to 6 bits at `k = 16384`; on same-sign data INT8 does as well as
pinned accumulation with its bias correction. Rounded to BF16, pinned results differ from the correctly
rounded BF16 value by one unit in the last place in some entries (up to a third of them at
`k = 4096` on log-normal data), where native results almost never do.

**Why fixed point is unavoidable.** A floating-point accumulator rounds on a grid that follows the
running value, and the running value depends on the schedule; that is exactly what makes native
results schedule-dependent. A result that is the same under every schedule, computed with a single
accumulator, cannot use a grid that depends on partial sums, so the grid must be fixed in advance
from a bound on every partial sum of every schedule: the scheme is fixed point. Recovering accuracy
needs more than one accumulator, as in reproducible summation, where Demmel and Nguyen pre-round
every summand to grids set from a bound on the maximum and ReproBLAS keeps a few binned
accumulators ([ReproBLAS](https://bebop.cs.berkeley.edu/reproblas/)); on a matrix multiplier that
costs extra GEMMs. Two mitigations follow:

- **Two folds.** Split `A = A₁ + A₂` and `B = B₁ + B₂`, with `A₁` and `B₁` rounded to a coarse grid
  so that `A₁B₁` is exact under pinning, and compute `A₁B₁ + A₁B₂ + A₂B` with three pinned GEMMs.
  On H100 with bf16 inputs at `k = 1024` this recovers native accuracy on normal data (`2^-20.5`
  against `2^-20.2`), and at `k = 4096` it gains four bits over one pinned GEMM (`2^-16.0` against
  `2^-12.0`, native `2^-18.1`); on LLM-like data the gain is smaller.
- **Selective pinning.** Pin only the products whose results must reproduce across schedules or
  GPUs, and leave the rest native.

### When it is worth it

| Option | Cost | Same bits under | Accuracy at `k = 4096` (normal data) |
| --- | --- | --- | --- |
| Native | `1×` | one schedule on one GPU | about `2^-17` |
| Anchored | `1.0×`, plus the norms | every schedule on one Tensor Core model | about `2^-7` to `2^-12` |
| Pinned | `1.14–1.33×` | every schedule on V100, A100, H100 and CDNA 3 | about `2^-11` to `2^-12` |
| Pinned with three GEMMs | about `3.4×` | the same | about `2^-15` to `2^-16` |
| Correctly rounded Ozaki | `4–9×` for low-precision inputs | every schedule on every modeled GPU, both vendors | correctly rounded |

The cost is manageable where the outputs are rounded to BF16 or FP16 anyway, as in inference, so
that the fixed-point loss mostly disappears in the output rounding; for verifiable or consensus
inference across GPUs and vendors, where agreement is the requirement; and for regression testing
across platforms. It is a deal breaker for training reductions with `k` of `10^5` to `10^6`, where
eight to ten bits would be lost on random-sign data; for HPC accuracy requirements; for entries
dominated by cancellation, where `|a·b|` is far below `‖a‖·‖b‖`; and for determinism on a single
GPU, where batch-invariant kernels with a fixed schedule already reproduce at full FP32 accuracy.
The costs are model counts of block FMAs, or of calls to the matrix multiplier, not GPU time; the
correctly rounded Ozaki figures come from the [correct-rounding page](/MMAlgebra/ozaki/correct-rounding/).
The accuracy ranges cover the corrected and uncorrected variants on the H100 and A100 models.

In Lean: [`MMAlgebra.TC.evalBlock_pinned`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Pinned.lean#L147) (one pinned block adds exactly the truncated products),
[`MMAlgebra.TC.truncSum_pair`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Pinned.lean#L56) (the pin pair adds nothing), [`MMAlgebra.TC.runBlocks_pinned`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Pinned.lean#L214),
[`MMAlgebra.TC.pinned_schedule_free`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Pinned.lean#L259) and [`MMAlgebra.TC.pinned_splitK`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Pinned.lean#L273) on the Tensor Core
models; [`MMAlgebra.TC.evalBlock_anchored`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Anchored.lean#L63), [`MMAlgebra.TC.runBlocks_anchored`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Anchored.lean#L150) and
[`MMAlgebra.TC.anchored_blocks_perm`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Anchored.lean#L182) for anchoring; [`MMAlgebra.MC.evalBlock_pinned`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Pinned.lean#L117) and
[`MMAlgebra.MC.runBlocks_pinned`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Pinned.lean#L195) on CDNA 3, where the conditions on each block's accumulator are
derived along the chain rather than assumed.

## Applications and value

### Split-K, stream-K and the placement of `C`

For a `k = 64` entry, ten common configurations (no split, split by 2 or 4 with partials combined
serially or pairwise, stream-K cuts after 24 or 16 products, each with `C` in the first block or in
the epilogue) give **ten different bitwise classes on every model**, V100, A100, H100 and CDNA 1,
2 and 3. They also differ often on ordinary data:

| Pair of configurations (random dense inputs, out of 60) | V100 | A100 | H100 | CDNA 1 | CDNA 2 | CDNA 3 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| No split against split-K by 2 | 45 | 36 | 29 | 33 | 28 | 33 |
| `C` in the first block against `C` in the epilogue | 7 | 5 | 4 | 6 | 6 | 8 |
| Split-K by 4, serial against pairwise combination | 20 | 12 | 19 | 13 | 16 | 20 |
| Stream-K cut after 24 against after 16 products | 35 | 28 | 33 | 24 | 31 | 35 |

What is safe follows from the same theory: `BLOCK_K`, the tile shapes `BLOCK_M` and `BLOCK_N`,
the number of warps and of pipeline stages, and the instruction shape (when its `k` is a multiple
of `K`) never change the bits on any modeled variant, as long as they leave the block sequence of
every entry unchanged, which holds when the compiler still feeds the products to the matrix
multiplier in increasing `k`. A split-K with atomic additions is also covered: two partials added atomically
into a buffer that starts at `+0` give the same bits in either order (`(0 ⊕ P₁) ⊕ P₂` and
`(0 ⊕ P₂) ⊕ P₁` agree by commutativity), but with three partials, or with `C` already in the
buffer, the arrival order changes the result on some input.

### Batch invariance

A serving system is batch-invariant when the term for each output entry does not depend on the
batch size `M`. With the algebra this becomes checkable: enumerate the configurations a launch
heuristic picks for each `M`, compute the term for one entry under each, and decide whether they
are equivalent. If not, the separating input, embedded as one row of `A` in batches of the two
sizes, is a test case that shows the difference. Today's batch-invariant modes fix one
configuration for all shapes; the algebra says which other configurations could be allowed
without changing a bit, and shows with a concrete input that each excluded one changes some.

### Reproducible autotuning

The configurations of a kernel fall into equivalence classes per architecture. Restricting an
autotuner to the class of a reference configuration keeps the results bitwise reproducible while
it still tunes everything that does not change the numerics; on rigid hardware that means tile
shapes, `BLOCK_K`, warps and stages (while the block sequence is unchanged), and on CDNA 1 and
CDNA 2 the classes are larger. Triton's
[`triton.autotune`](https://triton-lang.org/main/python-api/generated/triton.autotune.html) already
accepts a pruning function (`prune_configs_by` with `early_config_prune`) through which such a
restriction can be applied.

### Across GPUs

The term of a schedule is portable; its bits are not. The same term gives different bits on
different variants, since their block FMAs differ, and the algebra says which rewrites are safe on
each target. Because the models are executable, a term can also be evaluated on a CPU to obtain
the exact bits a modeled GPU would return, which makes a reference result for one GPU checkable
on another machine. Identical bits across vendors need a common semantics instead, such as the
[correctly rounded Ozaki schemes](/MMAlgebra/ozaki/correct-rounding/).

### Who benefits, and how this compares

Engineers of LLM inference and of reinforcement learning, who need a request's numerics to be
independent of the batch or the rollout and the trainer to agree; kernel and compiler engineers,
who want to know whether a transformation or a tuning choice can change results; and numerical
analysts, who get exact statements in place of rules of thumb.

| Approach | What it gives | What the algebra adds |
| --- | --- | --- |
| Fixing one kernel configuration (Thinking Machines, SGLang, vLLM) | Batch invariance by construction, at a cost in throughput | Which other configurations are provably safe, and a witness for each unsafe one |
| Library guarantees (cuBLAS, PyTorch) | Run-to-run reproducibility under fixed versions and hardware | Reasons tied to the schedule, valid across configurations |
| Correctly rounded or order-invariant arithmetic (RepDL, Xie, Zhang and Chen, [arXiv:2510.09180](https://arxiv.org/abs/2510.09180)) | Bits independent of order and platform, by changing the arithmetic | Reproducibility of the native kernels, where it holds |
| Revealing accumulation orders by testing (FPRev, Xie, Gao, Wang and Xue, [arXiv:2411.00442](https://arxiv.org/abs/2411.00442), USENIX ATC 2025) and bit-accurate models of MMA units (MMA-Sim, Xie, Xu, Wang, Yang and Yang, [arXiv:2511.10909](https://arxiv.org/abs/2511.10909); Khattak, Mikaitis and Graziani) | The order and semantics of the hardware | The equational theory that the semantics induce on schedules, with proofs |
| Static bitwise-equivalence checking of compiled kernels (Yang et al., [arXiv:2609.11356](https://arxiv.org/abs/2609.11356)) | Equivalence classes of compiled Triton kernels from PTX and AMDGCN, validated on 51,152 configurations on GB300 and 4,500 on gfx942, used to prune Triton's autotuner; on reductions and GEMMs it returns 1.0 to 2.5 times the true number of classes, and it reports classes rather than separating inputs | Semantics from validated block-FMA models instead of one rounding per instruction; laws proved for every input on the Tensor Core models; completeness, with a separating input for every inequivalent pair it decides; the extra equivalences of CDNA 1 and CDNA 2 |

The closest work is Yang et al.'s checker, which already works on real compiled kernels, covers
reductions beyond GEMM and attention, and was measured on Hopper and Blackwell GPUs, none of which
the algebra does yet. The two are complementary: the algebra could serve as the arithmetic core of
such a checker on the architectures it models.

What is not new should be said plainly. That only identical schedules reproduce on rigid
hardware matches practitioners' experience. The contribution is the proofs, the completeness
result with its reduction to three products, the counterexamples to a natural abstraction, the
AMD exceptions, and a decision procedure that always returns evidence.

## Triton integration plan

The goal is a reproducibility checker for Triton GEMM kernels: given a kernel, its autotuning
configurations and a target architecture, report which configurations give identical bits, and
for any two that do not, an input that shows it.

1. **Extract the term.** For one output entry, read off the reduction: the K-loop over `BLOCK_K`
   steps with `tl.dot` accumulating into a register (`acc = tl.dot(a, b, acc)`), a split over K
   through a program id with partials combined by atomic additions or a second pass, and the
   epilogue that adds `C` or a bias. The first front end will match this canonical structure in
   Triton's intermediate representation, where the loop, the dot operations and the atomics are
   explicit, and will reject kernels it does not understand rather than guess.
2. **Lower to block FMAs.** Map each `tl.dot` to the MMA or MFMA instruction the compiler selects
   for the target and data type, and that instruction to its chain of block FMAs from the models
   (`HMMA.844` as four blocks of four on V100, `HMMA.1688` as two blocks of eight on A100, and so
   on). Instructions without a model, such as Hopper's `wgmma` and Blackwell's `tcgen05.mma`, are
   reported as unsupported.
3. **Decide per architecture.** Group the configurations into classes with the decision
   procedure, and attach a separating input to every pair of classes.
4. **Reproducible autotuning.** Offer a pruning function for `triton.autotune` that keeps only the
   configurations equivalent to a reference configuration.
5. **Batch-invariance verification.** Given the launch heuristic as a function of `(M, N, K)`,
   prove that the term of every entry is independent of `M` over a range of sizes, or return two
   sizes and an input on which they disagree.
6. **Confirm on hardware.** Run the separating inputs on GPUs of each modeled architecture, to
   test the models where the recorded data is thin.

## Roadmap and open problems

- **Completeness in Lean.** The two lemmas named above (ordered partitions are determined by
  their pairwise patterns; an fp16 block started from `+0` never returns `−0`), then completeness
  for terms with additions, and for the AMD models beyond base witnesses.
- **The AMD laws in Lean.** The CDNA 1 merge law and the CDNA 2 `c`-split law are tested and follow
  directly from the block formulas, but are not yet theorems.
- **Divergence constants in Lean.** The block contracts of the Tensor Cores, CDNA 2 and CDNA 3
  (bounding `2^η` and the output ulp by magnitudes), a sharper CDNA 2 constant than `2^-21`, and
  closed forms for chains and split-K.
- **Real libraries.** Which programs cuBLAS and rocBLAS run for which shapes, probed on GPUs by
  testing, so that the modeled programs can be replaced by measured ones.
- **Pinned and anchored accumulation on GPUs.** A first kernel, with a pin pair in each half of
  A100's `k = 16` instruction, to confirm the models' prediction on hardware; a multi-fold variant
  for accuracy; selective pinning.
- **Extremes of the formats.** CDNA 1 bf16 terms with additions near binary32's underflow
  threshold are not fully classified, and FP8 is not covered (CDNA 3's FP8 blocks group odd and
  even products separately and depend on positions).
- **Newer instructions.** WGMMA on Hopper and the `tcgen05` instructions of Blackwell have no model
  in this repository.
- **Attention.** Online softmax rescales the accumulator between block FMAs, so its terms need a
  scaling operation, with laws of its own.
- **Epilogues.** `β·C` with `β ≠ 1`, bias and activation functions add multiplications and other
  operations to the terms.
- **Hardware confirmation** of the separating inputs, and the **Triton front end** above.

## Evidence

| Claim | Evidence | Where |
| --- | --- | --- |
| Products in a block act as a multiset (every Tensor Core model) | Proved | [`MMAlgebra.TC.evalBlock_bits_perm`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Block.lean#L89) |
| Zero products are invisible (every Tensor Core model) | Proved | [`MMAlgebra.TC.evalBlock_bits_zero`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Block.lean#L230) |
| A chain on an input supported on `S` equals the chain restricted to `S` | Proved | [`MMAlgebra.TC.chain_restrict`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Chain.lean#L41) |
| Chains with different patterns of two products differ (V100, A100, H100 fp16) | Proved, with kernel-checked base witnesses | [`MMAlgebra.TC.complete_pair`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Completeness.lean#L377), [`MMAlgebra.TC.v100_complete_pair`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Completeness.lean#L469), [`MMAlgebra.TC.a100_complete_pair`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Completeness.lean#L485), [`MMAlgebra.TC.h100_complete_pair`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Completeness.lean#L504) |
| Multiset law on CDNA 1 and CDNA 3 (for the sum before the final rounding); order dependence on CDNA 2 | Proved in the AMD library | [`MatrixCore.accumulate_perm`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Order.lean#L37), [`MatrixCore.pairWiseSum_order_dependent`](https://github.com/pauljiang03/MMAlgebra/blob/main/amd/MatrixCore/MC/Order.lean#L53) |
| Base witnesses on CDNA 1, 2 and 3 | Kernel-checked | [`MMAlgebra.MC.cdna1_trees`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Witnesses.lean#L21), [`MMAlgebra.MC.cdna2_trees`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Witnesses.lean#L35), [`MMAlgebra.MC.cdna3_pair`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Witnesses.lean#L47) |
| One instruction is not one rounding | Kernel-checked | [`MMAlgebra.TC.v100_wmma_swap`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/OneRounding.lean#L17), [`MMAlgebra.TC.a100_wmma_swap`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/OneRounding.lean#L27), [`MMAlgebra.MC.cdna1_k16_swap`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/OneRounding.lean#L16), [`MMAlgebra.MC.cdna2_k16_swap`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/OneRounding.lean#L26), [`MMAlgebra.MC.cdna3_k16_swap`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/OneRounding.lean#L36) |
| The worked examples on this page | Kernel-checked | [`MMAlgebraTCTests.v100_block_boundary`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/tests/MMAlgebraTCTests/Examples.lean#L17), [`MMAlgebraTCTests.a100_block_boundary`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/tests/MMAlgebraTCTests/Examples.lean#L29), [`MMAlgebraMCTests.cdna2_block_boundary`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/tests/MMAlgebraMCTests/Examples.lean#L13), [`MMAlgebraMCTests.cdna1BF16_tie`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/tests/MMAlgebraMCTests/Examples.lean#L23) |
| The laws on every modeled variant | Random testing, 300 trials per law and variant | [`laws.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/laws.py) |
| Normal forms sound and complete over 2 and 3 products on every variant, and over 4 on five variants | Exhaustive enumeration, separating inputs found by search | [`classes.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/classes.py), [`terms.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/terms.py), [`terms4.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/terms4.py), [`bf16_extremes.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/bf16_extremes.py) |
| Completeness reduces to supports of at most 3 products | Exhaustive: chains over up to 6 products, terms over 4 | [`restriction_lemma.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/restriction_lemma.py), [`terms4.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/terms4.py) |
| The decision procedure, the configuration study, the one-rounding comparison | 210 random pairs; 10 configurations on 6 variants | [`decide_equiv.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/decide_equiv.py), [`config_study.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/config_study.py), [`oneround.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/oneround.py) |
| The structural bound, divergence of two schedules, and shared work, for any matrix multiplier | Proved | [`MMAlgebra.eval_error`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebra/Divergence.lean#L51), [`MMAlgebra.divergence`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebra/Divergence.lean#L138), [`MMAlgebra.divergence_shared`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebra/Divergence.lean#L160) |
| The divergence bound on SFMA and CDNA 1 | Proved | [`MMAlgebra.MC.crContract`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Bound.lean#L141), [`MMAlgebra.MC.cdna1_divergence`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Bound.lean#L153) |
| Inside the exact region every schedule agrees | Proved; kernel-checked example | [`MMAlgebra.TC.eval_agree`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Exact.lean#L172), [`MMAlgebra.MC.eval_agree`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Exact.lean#L261), [`MMAlgebraTCTests.v100_exact_region`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/tests/MMAlgebraTCTests/Examples.lean#L44) |
| The composed bound on the Tensor Cores, CDNA 2 and CDNA 3; worst cases and tightness | 1,800 random evaluations with no violation; adversarial search, witnesses checked on the model | [`divergence.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/divergence.py) |
| How different BLAS programs are | Modeled programs, `k = 1024`, 200 entries on each of four kinds of data | [`blas_programs.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/blas_programs.py) |
| Every schedule is exact when the positive and the negative products each total below `2^24` | Proved | [`MMAlgebra.TC.runBlocks_exact_of_posneg`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/ScheduleFreeExact.lean#L69), [`MMAlgebra.TC.schedules_agree_of_posneg`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/ScheduleFreeExact.lean#L94) |
| Pinned accumulation on the Tensor Core models and on CDNA 3; anchored accumulation on the Tensor Core models | Proved | [`MMAlgebra.TC.runBlocks_pinned`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Pinned.lean#L214), [`MMAlgebra.TC.pinned_schedule_free`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Pinned.lean#L259), [`MMAlgebra.TC.pinned_splitK`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Pinned.lean#L273), [`MMAlgebra.TC.runBlocks_anchored`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Anchored.lean#L150), [`MMAlgebra.TC.anchored_blocks_perm`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/Anchored.lean#L182), [`MMAlgebra.MC.runBlocks_pinned`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Pinned.lean#L195) |
| The 28-product demonstration; pinning and anchoring fail on CDNA 1 and 2, anchoring on CDNA 3 | Kernel-checked | [`MMAlgebra.TC.PinnedDemo.pinned_agree_v100_a100_h100`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/PinnedDemo.lean#L78), [`MMAlgebra.MC.PinnedCases.cdna1_pinned_order_dependent`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Counterexamples.lean#L43), [`MMAlgebra.MC.PinnedCases.cdna2_pinned_order_dependent`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Counterexamples.lean#L70), [`MMAlgebra.MC.PinnedCases.cdna3_anchored_order_dependent`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraMC/Counterexamples.lean#L83) |
| A subnormal factor breaks the `γ_n` bound of a block FMA | Kernel-checked on V100; searched on V100, A100, H100 | [`MMAlgebra.TC.SubnormalRemark.v100_subnormal_exceeds_gamma`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/MMAlgebraTC/SubnormalGamma.lean#L28), [`subnormal_gamma.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/subnormal_gamma.py) |
| Pinned and anchored accumulation: schedules, GPUs, accuracy, cost | Simulated with a fast integer port of the models (3,600 blocks checked against the validated port) | [`pinned_sim.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/pinned_sim.py), [`anchor_sim.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/anchor_sim.py), [`pinned_acc.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/pinned_acc.py), [`anchored_acc.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/anchored_acc.py), [`portable_cmp.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/portable_cmp.py), [`pinned3.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/pinned3.py) |
| The Python port computes the Lean models' output words | 1,800 random blocks on 12 variants, bit for bit | [`validate_port.py`](https://github.com/pauljiang03/MMAlgebra/blob/main/mmalgebra/prototype/validate_port.py) |
| The models match the hardware | Replayed measurements and published vectors; assumed beyond them | [NVIDIA validation](/MMAlgebra/model/validation/), [AMD validation](/MMAlgebra/amd/validation/) |

Every theorem uses only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`),
which the project's audit checks. The prototype's recorded outputs are in
[`mmalgebra/prototype/results/`](https://github.com/pauljiang03/MMAlgebra/tree/main/mmalgebra/prototype/results),
and `python3 scripts/check.py --prototype` in `mmalgebra/` reproduces them. The theorems are about
the models; that GPUs behave like them rests on the models' validation.
