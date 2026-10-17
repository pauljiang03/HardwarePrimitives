# Reduction-algebra prototype

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
`divergence.py`, `blas_programs.py`, `anchor_sim.py`, `pinned_sim.py`, `pinned_acc.py`,
`pinned3.py` and `fp8_enum.py`, which take from a few seconds to a few minutes each (`fp8_enum.py`
about twenty); the divergence and BLAS studies use up to twelve processes, the FP8 enumeration
six. `fp8_validate.py` needs `mc_eval`, built in `../amd`.

The programs of `blas_programs.py` are modeled: the internals of cuBLAS and rocBLAS are not
public, and which program a library runs for a given shape would have to be probed on GPUs.

## Making every schedule agree: pinned and anchored accumulation

These scripts use [`fastmodels.py`](fastmodels.py), an integer port of the same models (every value
is an integer multiple of `2^-640`), which [`validate_fast.py`](validate_fast.py) checks bit for bit
against `models.py` on 3,600 random blocks.

| Script | What it checks | Recorded output |
| --- | --- | --- |
| [`validate_fast.py`](validate_fast.py) | The integer port against the validated port | [`results/validate_fast.txt`](results/validate_fast.txt) |
| [`anchor_sim.py`](anchor_sim.py) | Anchored accumulation: distinct results over eleven schedules (sequential, split-K, random stream-K) natively and anchored, on every model, `k = 1024` | [`results/anchor_sim.txt`](results/anchor_sim.txt) |
| [`pinned_sim.py`](pinned_sim.py) | Pinned accumulation: invariance over schedules on A100, H100 and CDNA 3 (anchored on V100), and the same bits across them, `k = 1680`, fp16 and bf16 | [`results/pinned_sim.txt`](results/pinned_sim.txt) |
| [`pinned_acc.py`](pinned_acc.py) | Accuracy of pinned accumulation with and without the bias correction, against native H100 and A100, `k` from 256 to 16384, five kinds of data | [`results/pinned_acc.txt`](results/pinned_acc.txt) |
| [`anchored_acc.py`](anchored_acc.py) | Accuracy of anchored accumulation | [`results/anchored_acc.txt`](results/anchored_acc.txt) |
| [`portable_cmp.py`](portable_cmp.py) | Pinned accumulation of bf16 inputs against per-vector INT8 quantization with an exact integer dot product | [`results/portable_cmp.txt`](results/portable_cmp.txt) |
| [`pinned3.py`](pinned3.py) | Two folds: three pinned GEMMs against one | [`results/pinned3.txt`](results/pinned3.txt) |
| [`find_demo.py`](find_demo.py), [`amd_cex.py`](amd_cex.py) | Search for the 28-product demonstration and the AMD cases that the Lean files check | [`results/find_demo.txt`](results/find_demo.txt), [`results/amd_cex.txt`](results/amd_cex.txt) |
| [`subnormal_gamma.py`](subnormal_gamma.py) | Search for blocks with a subnormal factor that exceed the classical `γ_n` bound | [`results/subnormal_gamma.txt`](results/subnormal_gamma.txt) |

## The FP8 models

[`fp8models.py`](fp8models.py) is a bit-exact port of the FP8 block FMAs: `TensorCore.evalBlock`
with the models of Ada, Hopper and Blackwell (E4M3 and E5M2) and `MatrixCore.blockBits` for
CDNA 3 binary8 (E4M3 FNUZ and E5M2 FNUZ, any mix). [`fp8_validate.py`](fp8_validate.py) replays
the 50,000 recorded FP8 outputs of Ada, L40S, H100, H200 and B200 through it, and compares the
CDNA 3 port with the Lean model (`mc_eval`, built in `../amd`) on 6,000 random and targeted inner
products; on 2026-10-13 both agreed on every case.

| Script | What it checks | Recorded output |
| --- | --- | --- |
| [`fp8_validate.py`](fp8_validate.py) | The port against the recorded GPU outputs and the Lean CDNA 3 model, and its sparse block evaluators against full blocks | [`results/fp8_validate.txt`](results/fp8_validate.txt) |
| [`fp8_enum.py`](fp8_enum.py) | Every term over 3 products (up to 3 nonempty blocks, 2 additions and 1 empty block) on each FP8 model, its class of equal outputs on 800 random inputs, and conjectured normal forms: rigid on Blackwell, rigid with truncation nodes on Ada and Hopper, parity-rigid on CDNA 3 (the plain rigid forms are unsound there). Pairs left unseparated by the random inputs are separated by a targeted search | [`results/fp8_enum.txt`](results/fp8_enum.txt) |
| [`fp8_laws.py`](fp8_laws.py) | An empty block: `c` truncated to a 13-bit mantissa on Ada and Hopper, `c` itself on Blackwell and CDNA 3; absorbed by the next nonempty block; the identity on block outputs | [`results/fp8_laws.txt`](results/fp8_laws.txt) |
| [`fp8_crossvendor.py`](fp8_crossvendor.py) | Search for a short input with four different results on Ada, Hopper, Blackwell and CDNA 3 (the one checked in Lean) | [`results/fp8_crossvendor.txt`](results/fp8_crossvendor.txt) |
| [`fp8_pinned.py`](fp8_pinned.py) | Pinned accumulation on CDNA 3 FP8 with the pins in one or in both parity groups, and pinned FP8 on Ada, Hopper and CDNA 3 against each other and against the sum of the truncated products | [`results/fp8_pinned.txt`](results/fp8_pinned.txt) |

The enumeration gives the three FP8 algebras. Blackwell: 28 normal forms, every class separated (one
pair needs the targeted search). Ada and Hopper: 43 normal forms with truncation nodes, all
separated; the 28 rigid normal forms are unsound there. CDNA 3: 40 parity-rigid normal forms on
E4M3, E5M2 and mixed E4M3 × E5M2 operands, all separated (two pairs on the mixed formats need the
targeted search); the rigid normal forms are unsound there. The Tensor Core inputs use E4M3
operands of magnitude at most 240, the values E4M3 shares with E4M3 FNUZ; `fp8_enum.py` takes about
an hour of CPU time in six processes, and `check.py --prototype --slow` reruns it.

## Variants and families

| Family | Variants | Normal form |
| --- | --- | --- |
| Rigid | V100, A100 and H100 (fp16, bf16), CDNA 3 (fp16, bf16), CDNA 1 bf16, SFMA | Each block keeps its accumulator input and the set of its products; additions are unordered pairs |
| Correctly rounded nodes | CDNA 1 fp16 | A tree whose nodes round the exact sum of their children; one-child nodes vanish |
| Summation trees | CDNA 2 (fp16, bf16, bf16 `_1k`) | An unordered binary tree of binary32 additions |
| Rigid | Blackwell FP8 (E4M3) | As above |
| Rigid with truncation nodes | Ada and Hopper FP8 (E4M3) | Rigid, and an empty block over an addition is a truncation node, absorbed by a following nonempty block |
| Parity-rigid | CDNA 3 FP8 (E4M3, E5M2, E4M3 × E5M2 FNUZ) | Rigid, but each block keeps the unordered pair of the multisets of its odd and of its even slots |

CDNA 1 bf16 follows the correctly rounded algebra while every product is representable in
binary32, but a bf16 product can fall below binary32's range, and over all inputs its chains are
rigid ([`bf16_extremes.py`](bf16_extremes.py)). Its terms with additions at the extremes of the
range are not yet classified (`terms.py` leaves pairs unseparated there).
