# MMAlgebra: the algebra of matrix multiply-accumulate reductions

MMAlgebra characterizes, for each matrix multiplier modeled in this repository, exactly when two
GEMM schedules give the same result bit for bit. For one output entry, every schedule (split-K,
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

The laws are complete: terms with distinct normal forms differ on some input, and already on an
input with at most three nonzero products. This is proved in Lean for chains holding two products
on V100, A100 and H100, and checked exhaustively over three and four products on every model (see
the status below). The consequences: split-K, stream-K and moving `C` give
different bits on every model; a natural abstraction, "each MMA instruction is one rounding", is
both unsound (exchanging two products inside one `k = 16` instruction changes the output on V100,
A100 and CDNA 1–3) and incomplete (one `k = 16` instruction equals two `k = 8` instructions on
those models); and a decision procedure returns either a proof of equivalence or a separating input
checked on the model.

The full explanation, with the laws per architecture, concrete witnesses, the decision procedure,
applications to batch invariance and reproducible autotuning, a plan for Triton, and the open
problems, is on the [MMAlgebra page](https://pauljiang03.github.io/TC-EFT/mmalgebra/) of the
website.

## Status

| Part | Status |
| --- | --- |
| Multiset and zero laws, restriction to a support (Tensor Core model, every variant) | Proved in Lean |
| Two-product completeness for chains (V100, A100, H100 fp16) | Proved in Lean, with kernel-checked base witnesses |
| Base witnesses on CDNA 1, 2 and 3; one-instruction swap witnesses on V100, A100, CDNA 1–3 | Kernel-checked in Lean |
| Laws and normal forms on all modeled variants | Random testing and exhaustive enumeration over 2, 3 and 4 products ([prototype](prototype/README.md)) |
| Reduction of completeness to supports of at most 3 products | Exhaustive for chains over up to 6 products and terms over 4 |
| CDNA 1 merge law and CDNA 2 `c`-split law | Tested; not yet proved in Lean |
| Full completeness | Two lemmas missing in Lean: an ordered block partition is determined by its pairwise patterns, and an fp16 block started from `+0` never returns `−0` |

## Build and run

`mmalgebra/` is a standalone Lake project that requires the two models by path (`..` and
`../amd`), like [`ozaki/`](../ozaki/README.md); all three use Lean 4.33.1. Build the models in
their own directories first, then, from this directory:

```sh
lake build
python3 scripts/check.py                  # build, axiom audit, README blocks, local links
python3 scripts/check.py --prototype      # also rerun the prototype and compare its output
python3 scripts/check.py --port           # also validate the Python port against Lean
```

`lake build` builds the two libraries and the two test libraries; the test libraries kernel-check
the worked examples and audit the axioms (only `propext`, `Classical.choice` and `Quot.sound`).
`TensorCore` and `MatrixCore` cannot be imported into the same file, so the Tensor Core and
matrix-core parts are separate libraries.

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
| [`MMAlgebraTC`](MMAlgebraTC.lean) | The Tensor Core side: the multiset and zero laws of one block FMA ([`Block`](MMAlgebraTC/Block.lean)), chains and restriction to a support ([`Chain`](MMAlgebraTC/Chain.lean)), two-product completeness ([`Completeness`](MMAlgebraTC/Completeness.lean)), and the WMMA swap witnesses ([`OneRounding`](MMAlgebraTC/OneRounding.lean)). |
| [`MMAlgebraMC`](MMAlgebraMC.lean) | The matrix-core side: chains of MFMA blocks, base witnesses on CDNA 1, 2 and 3 ([`Witnesses`](MMAlgebraMC/Witnesses.lean)), and the MFMA swap witnesses ([`OneRounding`](MMAlgebraMC/OneRounding.lean)). |
| [`tests/`](tests/) | Kernel-checked worked examples and the axiom audits. |
| [`prototype/`](prototype/README.md) | The Python port of both models, the enumerations and random tests of the laws, the decision procedure, the configuration study, and their recorded outputs. |
| [`scripts/check.py`](scripts/check.py) | Validation. |
