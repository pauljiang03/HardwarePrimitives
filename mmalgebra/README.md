# Schedules: the reduction algebra

The third part of MMAlgebra characterizes, for each matrix multiplier modeled in this repository,
exactly when two GEMM schedules give the same result bit for bit. For one output entry, every schedule (split-K,
stream-K, the k-tile depth, the instruction shape, and whether `C` is added in the first block FMA
or in the epilogue) is a term built from four operations: the zero accumulator, the initial
accumulator `c`, one block FMA with a given accumulator input and a given set of products, and a
binary32 round-to-nearest addition. Two terms are equivalent on an architecture when they give the
same output word on every input.

The models fall into three algebras:

* **Rigid** (NVIDIA V100, A100 and H100 Tensor Cores; AMD CDNA 3; SFMA): only the trivial laws
  hold. Products inside one block FMA act as a multiset, zero products are invisible, and binary32
  addition is commutative; any other rewrite changes the result on some input.
* **Correctly rounded nodes** (CDNA 1 fp16): a block is the binary32 value nearest to its exact
  sum, so a one-product first block merges into the next block.
* **Summation trees** (CDNA 2): a block is a fixed tree of binary32 additions with `c` added last,
  so `c` can be moved out of a block into a separate addition.

The FP8 block FMAs add two more. Blackwell FP8 is rigid. Ada and Hopper FP8 keep a 13-bit mantissa
after alignment, so an empty block FMA truncates its accumulator input to a 13-bit mantissa
(proved for every finite input): their algebra is rigid with **truncation nodes**, an empty block
over an addition, which the next nonempty block absorbs. CDNA 3 FP8 is **parity-rigid**: a block
depends on its slots only through the unordered pair {multiset of the odd slots, multiset of the
even slots} (the parity law, proved), and a slot permutation preserves the output on every input
exactly when it preserves the parity partition. An enumeration of every term over three products
separates all classes of the three FP8 algebras (28 on Blackwell, 43 on Ada and Hopper, 40 on
CDNA 3), and one input with three products gives four different results on Ada, Hopper, Blackwell
and CDNA 3 (kernel-checked).

The laws are complete: terms with distinct normal forms differ on some input, and already on an
input with at most three nonzero products. This is proved in Lean for terms with additions on the
fp16 models of V100, A100, H100, CDNA 1, CDNA 2 and CDNA 3, for chains on the bf16 and tf32 Tensor
Cores, CDNA 1 bf16 and CDNA 3 bf16 and xf32, and for terms on the bf16 and tf32 Tensor Cores, SFMA
and CDNA 3 bf16 and xf32 on inputs whose products are multiples of `2^-149`; on the FP8 block FMAs
it is proved for chains on Ada, Hopper, Blackwell and CDNA 3, and for terms with additions on
Blackwell on every input (every FP8 product is a multiple of `2^-149`); it is checked exhaustively
over three and four products on every model (see the status below). The consequences: split-K, stream-K and moving `C` give
different bits on every model; a natural abstraction, "each MMA instruction is one rounding", is
both unsound (exchanging two products inside one `k = 16` instruction changes the output on V100,
A100 and CDNA 1–3) and incomplete (one `k = 16` instruction equals two `k = 8` instructions on
those models); and a decision procedure returns either a proof of equivalence or a separating input
checked on the model.

On truncating hardware every schedule can also be made to agree: with a cancelling pair of
products `±2^α` in every block FMA (pinned accumulation), or an accumulator started at `1.5·2^α`
(anchored accumulation), a chain computes the sum of its products each truncated to a fixed grid,
a function of the multiset of products; pinned accumulation gives the same bits on V100, A100,
H100 and CDNA 3, at a fixed-point loss of accuracy.

When two schedules are not equivalent, a structural error bound, built from the per-block error
theorems of the models, bounds how far apart they can be, `|t₁ − t₂| ≤ E(t₁) + E(t₂)`, and work
the two schedules share does not count. Inside the exact region (small integer operands, as in the
Ozaki schemes) every schedule returns the exact sum, so every schedule is an exact matrix
multiplier for the Ozaki schemes and they give the same bits under every schedule. An adversarial search shows the bound is tight
within a factor of about three on most models, and a study of modeled BLAS programs (split-K,
stream-K, the placement of `C`, a CUDA-core fallback, and six GPUs) gives worst cases and typical
differences.

The full explanation, with the laws per architecture, concrete witnesses, the decision procedure,
applications to batch invariance and reproducible autotuning, a plan for Triton, and the open
problems, is on the [schedules page](https://pauljiang03.github.io/MMAlgebra/schedules/) of the
website.

## Status

| Part | Status |
| --- | --- |
| Multiset and zero laws, restriction to a support (Tensor Core model, every variant) | Proved in Lean |
| Completeness for chains and for terms with additions: two terms are equivalent exactly when their normal forms agree (V100, A100, H100 fp16 and CDNA 3 fp16: rigid; CDNA 1 fp16: correctly rounded trees; CDNA 2 fp16: binary summation trees) | Proved in Lean on every input, with kernel-checked fingerprint tables |
| Completeness for chains (A100 and H100 bf16 and tf32, CDNA 1 bf16, CDNA 3 bf16 and xf32) | Proved in Lean on every input |
| Completeness for terms with additions (A100 and H100 bf16 and tf32, SFMA, CDNA 3 bf16 and xf32) | Proved in Lean on inputs whose products are multiples of `2^-149` |
| Completeness for terms on CDNA 1 bf16 (not all separated) and CDNA 2 bf16, and off the binary32 grid on the bf16 Tensor Cores, SFMA and CDNA 3 bf16 | Enumeration only ([prototype](prototype/README.md)) |
| Completeness for tf32 and CDNA 3 xf32 terms off the binary32 grid | Not yet covered |
| FP8 algebras: Blackwell rigid, Ada and Hopper rigid with truncation nodes, CDNA 3 parity-rigid | Enumeration of every term over 3 products, all classes separated ([prototype](prototype/README.md)) |
| Completeness for chains on the FP8 block FMAs: two chains from `+0` are equivalent exactly when their ordered partitions agree (Ada, Hopper, Blackwell; E4M3 and E5M2); on CDNA 3 FP8 two chains that differ in the ordered partition, or in how some block splits its products into the two parity groups, differ on some input (every mix of E4M3 and E5M2) | Proved in Lean on every input, with kernel-checked base witnesses |
| Completeness for terms with additions on Blackwell FP8: two terms are equivalent exactly when their rigid normal forms agree | Proved in Lean on every input (every FP8 product is a multiple of `2^-149`), with kernel-checked fingerprint tables |
| Completeness for terms with additions on Ada, Hopper and CDNA 3 FP8 | Enumeration only ([prototype](prototype/README.md)): an addition can leave more than 13 mantissa bits, which a following empty block truncates on Ada and Hopper |
| On Ada and Hopper FP8 an empty block FMA truncates `c` to a 13-bit mantissa (`+0` if that is zero); on Blackwell FP8 it passes `c` through | Proved in Lean on every finite input |
| CDNA 3 FP8 parity law; a slot permutation preserves every output exactly when it preserves the parity partition; separating witnesses for every mix of E4M3 and E5M2 | Proved in Lean |
| One input with four different results on Ada, Hopper, Blackwell and CDNA 3 FP8 | Kernel-checked in Lean on both models |
| Pinned accumulation on CDNA 3 FP8 needs one pin in each parity group; pinned FP8 is bitwise identical on Ada, Hopper and CDNA 3 | Kernel-checked instance in Lean; simulated ([`fp8_pinned.py`](prototype/fp8_pinned.py)) |
| Reduction of completeness to supports of at most 3 products | Proved in Lean (an ordered partition is determined by its pairwise patterns; a tree by its restrictions to triples of leaves); exhaustive for chains over up to 6 products and terms over 4 |
| An fp16 Tensor Core block never returns `−0`; neither does any Tensor Core block whose products are multiples of `2^-149` | Proved in Lean |
| Base witnesses on CDNA 1, 2 and 3; one-instruction swap witnesses on V100, A100, CDNA 1–3 | Kernel-checked in Lean |
| Laws and normal forms on all modeled variants | Random testing and exhaustive enumeration over 2, 3 and 4 products ([prototype](prototype/README.md)) |
| CDNA 1 merge laws (`[x] [J] = [x J]`, `[x] ⊕ [y] = [x y]`) and CDNA 2 `c`-split law | Proved in Lean on every input |
| How far apart two schedules can be: structural bound, divergence, shared work | Proved for any matrix multiplier with a binary32 addition; block contracts and divergence proved for the Tensor Core models (V100, A100, H100), SFMA, CDNA 1, CDNA 2 and CDNA 3 (fp16) |
| Inside the exact region (integer operands, `\|c\| + Σ\|aᵢbᵢ\|` at most `2^24`) every schedule returns the exact sum | Proved on every Tensor Core model and on CDNA 1, 2 and 3 |
| Every schedule is an exact matrix multiplier in the sense of the Ozaki schemes, so Ozaki-I, Ozaki-II and their correctly rounded versions give the same bits under every schedule | Proved on every Tensor Core model and on CDNA 1, 2 and 3 |
| How different modeled BLAS programs are (bounds, worst cases, typical differences) | Prototype study ([`blas_programs.py`](prototype/blas_programs.py)) |
| Every schedule is exact when the positive and the negative products each total below `2^24` | Proved in Lean (Tensor Core models) |
| Pinned accumulation (a cancelling pin pair `±2^α` in every block FMA) and anchored accumulation (start at `1.5·2^α`) make every schedule agree, on a fixed-point grid | Proved in Lean for the Tensor Core models (pinned also on CDNA 3, with the conditions on `c` derived); kernel-checked demonstration on V100, A100 and H100 and counterexamples on CDNA 1 and 2; simulated accuracy and cost; not yet run on a GPU |

## Build and run

`mmalgebra/` is a standalone Lake project that requires the two models by path (`..` and
`../amd`) and the Ozaki project (`../ozaki`), whose exactness theorems it builds on; all use Lean
4.33.1. Build the models and `ozaki/` in their own directories first, then, from this directory:

```sh
lake build
python3 scripts/check.py                  # build, axiom audit, README blocks, local links
python3 scripts/check.py --prototype      # also rerun the prototype and compare its output
python3 scripts/check.py --port           # also validate the Python port against Lean
```

`lake build` builds the three libraries and the two test libraries; the test libraries
kernel-check the worked examples and audit the axioms (only `propext`, `Classical.choice` and
`Quot.sound`). `TensorCore` and `MatrixCore` cannot be imported into the same file, so the Tensor
Core and matrix-core parts are separate libraries, and the hardware-independent theory uses Lean's
rationals directly so that it can be imported beside either.

A block FMA on V100 depends on its products only as a multiset, while moving a block boundary
changes the result. Products `x = 1.5 × 1.5` and `y = z = 2^-12 × 2^-11 = 2^-23`: one block holding
all three returns `2.25 + 2^-22`, but after a block holding `x` alone, whose output `2.25` has
binary32 exponent `1`, the block `[y z]` aligns to `2^-22` and drops both small products:

```lean
import MMAlgebraTC

open TensorCore MMAlgebra.TC

example : blockOut (p := v100F16F32)
    ⟨[(0x3e00, 0x3e00), (0x0c00, 0x1000), (0x0c00, 0x1000), (0, 0)], 0⟩ = .ok 0x40100001 := by
  decide +kernel

example : blockOut (p := v100F16F32)
    ⟨[(0x0c00, 0x1000), (0x0c00, 0x1000), (0, 0), (0, 0)], 0x40100000⟩ = .ok 0x40100000 := by
  decide +kernel
```

## Layout

| Import / directory | What belongs here |
| --- | --- |
| [`MMAlgebra`](MMAlgebra.lean) | Hardware-independent: reduction terms and their evaluation on any matrix multiplier ([`Term`](MMAlgebra/Term.lean)), the structural error bound, the divergence of two schedules and the shared-work bound ([`Divergence`](MMAlgebra/Divergence.lean)), schedules for every length ([`Schedule`](MMAlgebra/Schedule.lean)), and completeness from laws and base witnesses: ordered partitions and their pairwise patterns ([`Partition`](MMAlgebra/Partition.lean)), chain completeness on any rigid multiplier ([`ChainComplete`](MMAlgebra/ChainComplete.lean)), labeled trees determined by triples of leaves ([`LTree`](MMAlgebra/LTree.lean)), the generic theorem for terms ([`TermComplete`](MMAlgebra/TermComplete.lean), [`Shapes`](MMAlgebra/Shapes.lean)), the rigid, correctly rounded and pairwise normal forms with their soundness ([`Rigid`](MMAlgebra/Rigid.lean), [`Rounded`](MMAlgebra/Rounded.lean), [`Pairwise`](MMAlgebra/Pairwise.lean)), machines on a subset of their inputs ([`Sub`](MMAlgebra/Sub.lean)), and chain completeness on a parity-pair multiplier, whose blocks depend on their slots through the unordered pair {odd-slot multiset, even-slot multiset} ([`ParityChain`](MMAlgebra/ParityChain.lean)). |
| [`MMAlgebraTC`](MMAlgebraTC.lean) | The Tensor Core side: the multiset and zero laws of one block FMA ([`Block`](MMAlgebraTC/Block.lean)), chains and restriction to a support ([`Chain`](MMAlgebraTC/Chain.lean)), two-product completeness ([`Completeness`](MMAlgebraTC/Completeness.lean)), fp16 blocks never return `−0` ([`NegZero`](MMAlgebraTC/NegZero.lean)), completeness for chains and terms ([`ChainComplete`](MMAlgebraTC/ChainComplete.lean), [`TermComplete`](MMAlgebraTC/TermComplete.lean), [`ChainVariants`](MMAlgebraTC/ChainVariants.lean), [`TermVariants`](MMAlgebraTC/TermVariants.lean)), the block contract and divergence ([`Contract`](MMAlgebraTC/Contract.lean)), the WMMA swap witnesses ([`OneRounding`](MMAlgebraTC/OneRounding.lean)), the exact region ([`Exact`](MMAlgebraTC/Exact.lean), [`ScheduleFreeExact`](MMAlgebraTC/ScheduleFreeExact.lean)), pinned and anchored accumulation ([`Pinned`](MMAlgebraTC/Pinned.lean), [`Anchored`](MMAlgebraTC/Anchored.lean), [`PinnedDemo`](MMAlgebraTC/PinnedDemo.lean)), the subnormal remark ([`SubnormalGamma`](MMAlgebraTC/SubnormalGamma.lean)), and the bridge to the Ozaki schemes ([`Bridge`](MMAlgebraTC/Bridge.lean)), and the FP8 models: the empty block truncates `c` on Ada and Hopper, witnesses and the cross-vendor input ([`FP8`](MMAlgebraTC/FP8.lean)), completeness for chains on Ada, Hopper and Blackwell FP8 and for terms on Blackwell FP8 ([`FP8Complete`](MMAlgebraTC/FP8Complete.lean)). |
| [`MMAlgebraMC`](MMAlgebraMC.lean) | The matrix-core side: chains of MFMA blocks, base witnesses on CDNA 1, 2 and 3 ([`Witnesses`](MMAlgebraMC/Witnesses.lean)), the MFMA swap witnesses ([`OneRounding`](MMAlgebraMC/OneRounding.lean)), the exact region ([`Exact`](MMAlgebraMC/Exact.lean)), the divergence bound of the correctly rounded models ([`Bound`](MMAlgebraMC/Bound.lean)) and of CDNA 2 and 3 ([`Contracts`](MMAlgebraMC/Contracts.lean)), the laws and completeness for chains and terms ([`Words`](MMAlgebraMC/Words.lean), [`Blocks`](MMAlgebraMC/Blocks.lean), [`RigidMC`](MMAlgebraMC/RigidMC.lean), [`RoundedMC`](MMAlgebraMC/RoundedMC.lean), [`PairwiseMC`](MMAlgebraMC/PairwiseMC.lean), [`ChainBF16`](MMAlgebraMC/ChainBF16.lean), [`SFMA`](MMAlgebraMC/SFMA.lean), [`AllInputs`](MMAlgebraMC/AllInputs.lean)), pinned accumulation on CDNA 3 ([`Pinned`](MMAlgebraMC/Pinned.lean)), where pinning and anchoring fail ([`Counterexamples`](MMAlgebraMC/Counterexamples.lean)), the bridge to the Ozaki schemes ([`Bridge`](MMAlgebraMC/Bridge.lean)), the CDNA 3 FP8 parity law ([`ParityLaw`](MMAlgebraMC/ParityLaw.lean)), the cross-vendor input and pinned accumulation on CDNA 3 FP8 ([`FP8`](MMAlgebraMC/FP8.lean)), completeness for chains on CDNA 3 FP8 ([`ParityFP8`](MMAlgebraMC/ParityFP8.lean)), and completeness for chains and grid terms on CDNA 3 bf16 and xf32 ([`CDNA3Formats`](MMAlgebraMC/CDNA3Formats.lean)). |
| [`tests/`](tests/) | Kernel-checked worked examples and the axiom audits. |
| [`prototype/`](prototype/README.md) | The Python port of both models and a fast integer port, the port of the FP8 models, the enumerations and random tests of the laws (FP8 included), the decision procedure, the configuration study, the divergence bounds and worst-case search, the study of modeled BLAS programs, the simulations of pinned and anchored accumulation, the cross-vendor FP8 search, and their recorded outputs. |
| [`scripts/check.py`](scripts/check.py) | Validation. |
