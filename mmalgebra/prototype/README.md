# MMAlgebra prototype

Plain Python 3 (3.9 or later, standard library only) with exact rational arithmetic. Every script
runs from this directory and needs no GPU. The scripts rely on `assert` and refuse to run under
`python -O`.

## The model port

[`models.py`](models.py) is a bit-exact port of two Lean models of this repository: the Tensor Core
block FMA (`TensorCore.evalBlock`, V100, A100 and H100 with fp16 and bf16 inputs) and the AMD
matrix-core block (`MatrixCore.blockBits`: SFMA, CDNA 1, CDNA 2, and CDNA 3 with global
alignment). [`validate_port.py`](validate_port.py) generates 150 random blocks per variant (1,800 in
all), evaluates them with the Lean models, and compares the output words bit for bit; from
`mmalgebra/`, `python3 scripts/check.py --port` runs it end to end. On 2026-10-13 all 1,800 agreed.

[`semantics.py`](semantics.py) evaluates a reduction term for one output entry on any variant.
A term is `('zero',)`, `('c0',)` (the initial accumulator), `('blk', t, slots)` (one block FMA
with accumulator input `t`, each slot a product index or `None` for a zero pair) or
`('add', t, u)` (a binary32 round-to-nearest addition; `'addftz'` flushes subnormal results).

## The algebra

| Script | What it checks | Recorded output |
| --- | --- | --- |
| [`laws.py`](laws.py) `300` | Each candidate law on 300 random inputs per variant: violations / trials | [`results/laws.txt`](results/laws.txt) |
| [`normal.py`](normal.py), [`terms.py`](terms.py) | Normal forms of chains and of terms with additions: rigid, correctly rounded nodes, summation trees | |
| [`classes.py`](classes.py) `300` | Every chain over 2 and 3 products: one class per normal form (soundness) and every two classes separated by some input (completeness) | [`results/classes.txt`](results/classes.txt) |
| [`terms.py`](terms.py) `300` | The same for every term with additions over 2 and 3 products | [`results/terms.txt`](results/terms.txt) |
| [`terms4.py`](terms4.py) | Terms over 4 products: soundness, and every two distinct normal forms differ on a support of at most 3 products | [`results/terms4.txt`](results/terms4.txt) |
| [`restriction_lemma.py`](restriction_lemma.py) | Chains over up to 6 products: distinct normal forms differ on a support of at most 3 products | [`results/restriction_lemma.txt`](results/restriction_lemma.txt) |
| [`bf16_extremes.py`](bf16_extremes.py) | CDNA 1 bf16, whose products can fall below binary32's range: its chain patterns over 3 products are pairwise separated | [`results/bf16_extremes.txt`](results/bf16_extremes.txt) |
| [`decide_equiv.py`](decide_equiv.py) | The decision procedure on 30 random pairs of chain and split-K terms over 6 products per variant; every separating input is checked on the model | [`results/decide_equiv.txt`](results/decide_equiv.txt) |
| [`config_study.py`](config_study.py) | Ten split-K, stream-K and C-placement configurations of a `k = 64` GEMM: their bitwise classes per variant | [`results/config_study.txt`](results/config_study.txt) |
| [`oneround.py`](oneround.py) | The abstraction "one MMA instruction is one rounding" against the models | [`results/oneround.txt`](results/oneround.txt) |
| [`examples.py`](examples.py) | Every concrete input and output cited in the documentation, with decoded values | [`results/examples.txt`](results/examples.txt) |
| [`divergence.py`](divergence.py) | How far apart two schedules can be: the structural error bound of a term from the per-block theorems, the divergence bound of two terms (with shared subterms as exact leaves), a check of the bound on random inputs, and an adversarial search for the worst `\|t₁ − t₂\| / M` at `k = 64` | [`results/divergence.txt`](results/divergence.txt) |
| [`blas_programs.py`](blas_programs.py) `200 800` | How different BLAS programs can be: ten modeled GEMM programs for `k = 1024` on six GPU models, against a reference and across GPUs, with bitwise equality, the bound, the searched worst case, and typical differences on uniform, normal, LLM-like and near-cancelling data | [`results/blas_programs.txt`](results/blas_programs.txt) |
| [`witness_search.py`](witness_search.py), [`wsearch2.py`](wsearch2.py) | Search for one input that separates every chain pattern at once (used to find the Lean witnesses; slow) | |

From `mmalgebra/`, `python3 scripts/check.py --prototype` reruns the fast scripts and compares
their output with the recorded files; `--slow` adds `terms4.py`, `classes.py`, `terms.py`,
`divergence.py` and `blas_programs.py`, which take from a few seconds to a few minutes each and use
up to twelve processes.

The programs of `blas_programs.py` are modeled: the internals of cuBLAS and rocBLAS are not
public, and which program a library runs for a given shape would have to be probed on GPUs.

## Variants and families

| Family | Variants | Normal form |
| --- | --- | --- |
| Rigid | V100, A100 and H100 (fp16, bf16), CDNA 3 (fp16, bf16), CDNA 1 bf16, SFMA | Each block keeps its accumulator input and the set of its products; additions are unordered pairs |
| Correctly rounded nodes | CDNA 1 fp16 | A tree whose nodes round the exact sum of their children; one-child nodes vanish |
| Summation trees | CDNA 2 (fp16, bf16, bf16 `_1k`) | An unordered binary tree of binary32 additions |

CDNA 1 bf16 follows the correctly rounded algebra while every product is representable in
binary32, but a bf16 product can fall below binary32's range, and over all inputs its chains are
rigid ([`bf16_extremes.py`](bf16_extremes.py)). Its terms with additions at the extremes of the
range are not yet classified (`terms.py` leaves pairs unseparated there).
