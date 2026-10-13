# FloatLib implementation of the AMD matrix-core model

`floatlib-port/` is a second implementation of the Matrix-Core model, written against
[FloatLib](https://github.com/lean-dojo/FloatLib) instead of Matrix-Core's own numerics. It
covers the same blocks: Khattak, Mikaitis and Graziani, *Accurate Models of AMD Matrix Cores*
([arXiv:2609.14845](https://arxiv.org/abs/2609.14845)), for CDNA 1, CDNA 2 and CDNA 3. Lean proves
that, for every input, it gives the same observed result as Matrix-Core.

It is a separate Lake project (Lean 4.34.0, FloatLib `0d91825`, which brings in mathlib), so
Matrix-Core itself stays free of mathlib. It follows the layout of the root project's `floatlib-port/`.

## Build and run

```sh
python3 scripts/check.py        # reference pin, build + proofs + audit, comparison with mc_eval
lake build                      # the implementation, the proofs, the audit and the examples
echo "cdna1F16 3c00,3c00,3c00,3c00 3c00,3c00,3c00,3c00 0" | .lake/build/bin/mc_floatlib
```

`mc_floatlib` reads the same lines as Matrix-Core's `mc_eval` (`<model> <a> <b> <c>`, words in
hexadecimal) and prints `F <word>`, `I+`, `I-` or `N`. The example prints `F 40800000`, the
binary32 word of `4`.

`lake build` first needs `reference-compat/`, which `scripts/prepare_reference.py` creates (and
`check.py` runs). The first build downloads mathlib's cache through Lake.

## What FloatLib does in each step

| Paper | [MCFloat/Model.lean](MCFloat/Model.lean) | FloatLib |
| --- | --- | --- |
| Decoding `a_ℓ`, `b_ℓ`, `c` (fp32, fp16, bf16, fp8 E4M3/E5M2 FNUZ) | `classify` | `Model.ofBits`, `Model.isNaN`, `Model.isInf`, `Model.signBit`, `Model.toDyadic?` with the catalog formats `binary32`, `binary16`, `bfloat16`, `e4m3fnuz`, `e5m2fnuz` |
| XF32: binary32 truncated to tf19 | `Operand.read .xf32` | the `tf32` format applied to the upper 19 bits of the word |
| `p_ℓ = a_ℓ b_ℓ`, exact, in denormalized form | `Term.mul` | `Dyadic.mul` |
| `fl{·}`, RNE to binary32, `±∞` on overflow | `round32`, `fl` | `Model.roundRatWithRounding .binary32 .nearestEven` |
| Flush to zero (CDNA 2) | `flush` | `Model.isSubnormal`, `Model.zero` |
| Results with special values | `special`, `add32` | `Model.posInf`, `Model.negInf`, `Model.canonicalNaN` |
| Alignment, truncation, RD | `truncGrid`, `rdGrid` | mathlib's `⌊·⌋` on `ℚ` |
| Subnormal-aware normalization | `normExp` | `RationalBinary.floorLog2` |

Every block returns a FloatLib binary32 word, including infinities and NaN, so an inner product
passes FloatLib words from block to block.

## What is proved

All statements are for every input word. `observe` reads a FloatLib binary32 word with FloatLib's
classification as Matrix-Core's `Outcome` (finite word, `±∞`, NaN).

| What it says | Lean name | File |
| --- | --- | --- |
| For each of the 12 models (SFMA; CDNA 1 fp16, bf16; CDNA 2 fp16, bf16, bf16 `_1k`; CDNA 3 fp16, bf16, XF32, fp8 in all four format combinations), the FloatLib parameter record (`MCFloat.MCModel`) corresponds to Matrix-Core's `Model`. | `sfma`, `cdna1F16`, …, `cdna3E5M2E4M3` | [Equivalence.lean](MCFloat/Equivalence.lean) |
| One block gives the same observation as `blockOutcome`. | `block_agree` | [Equivalence/Block.lean](MCFloat/Equivalence/Block.lean) |
| An inner product of any length gives the same observation as `dotOutcome`. | `dot_agree` | [Equivalence/Dot.lean](MCFloat/Equivalence/Dot.lean) |
| Where Matrix-Core's `blockBits` returns a word, the FloatLib block returns the same word. | `blockBits_agree` | [Equivalence.lean](MCFloat/Equivalence.lean) |
| For every rational, FloatLib's binary32 RNE word is Matrix-Core's `rne32` word, and FloatLib returns `±∞` exactly when `rne32` overflows; with flushing, the same holds for `fl32`. | `round32_bits`, `fl_bits` | [Equivalence/Rounding.lean](MCFloat/Equivalence/Rounding.lean) |
| For every word of every operand format, FloatLib's classification agrees with Matrix-Core's decoder: the same NaNs and infinities, and finite words with the same value, exponent, zero and subnormal tests and sign. | `binary32_agree`, …, `operand_xf32` | [Equivalence/Decode.lean](MCFloat/Equivalence/Decode.lean) |

### Contracts and chaining

[MCFloat/Contracts.lean](MCFloat/Contracts.lean) states Matrix-Core's per-model contracts and
chaining theorems for the FloatLib implementation. Whenever a FloatLib block returns a finite word
(`Finite w`):

| What it says | Lean name |
| --- | --- |
| The input is an accepted Matrix-Core block with the same word, and the word is FloatLib's own `fl{S_acc}` (`MCFloat.fl`); any property of accepted blocks holds. | `floatlib_block`, `floatlib_contract` |
| SFMA and CDNA 1: the word is FloatLib's round-to-nearest-even (`MCFloat.round32`) of the exact `Σ a_ℓ b_ℓ + c`, with `CorrectRoundingContract`. | `floatlib_sfma`, `floatlib_cdna1F16`, `floatlib_cdna1BF16` |
| CDNA 2: `PairwiseContract`; CDNA 3: `AlignedContract` (Algorithm 1 or 2, its error bounds, and the 30/29/31-bit register width). | `floatlib_cdna2F16`, …, `floatlib_cdna3FP8` |
| A finite FloatLib inner product is a run of linked, accepted blocks ending in the same word; every block satisfies any block property, and the initial `c` plus the products equal the output plus the blocks' residuals. | `floatlib_dot_blocks`, `floatlib_dot_contract` |
| The contracts include the output error bound (`error`) and the bound from the inputs alone (`apriori`); a finite FloatLib inner product is within the sum of its blocks' bounds of `c` plus all products, and of the exact `c + Σ_ℓ a_ℓ b_ℓ`. | `floatlib_dot_error`, `floatlib_dot_exact_error` |
| For the same `a` and `b`, a larger `c` never gives a smaller finite FloatLib output, for blocks and inner products. | `floatlib_c_monotone`, `floatlib_dot_c_monotone` |
| SFMA and CDNA 1: the FloatLib output is monotone in the exact sum; every CDNA 2 and CDNA 3 non-monotone pair of Matrix-Core is one for the FloatLib implementation. | `floatlib_correctRounding_monotone`, `floatlib_nonmonotone` |

The intermediate stages are proved separately: products, `e_max`, aligned and odd/even sums, and
late `c` in [Stages.lean](MCFloat/Equivalence/Stages.lean); products with special values and
FloatLib's special results in [Special.lean](MCFloat/Equivalence/Special.lean); the CDNA 2
pairwise sums in [Block.lean](MCFloat/Equivalence/Block.lean).

The rounding proof uses FloatLib's closed form of its rational rounder
(`roundRatScaled_false_eq_of_isIEEE`) and matches each branch (overflow, underflow, subnormal,
normal, carry) with Matrix-Core's `rneFields`. Negative values use FloatLib's sign-toggling
negation.

## Trust

[tests/Audit.lean](tests/Audit.lean) runs in every build:

* all 223 theorems in the `MCFloat` namespace use only `propext`, `Classical.choice` and
  `Quot.sound` (no `native_decide` or `bv_decide`);
* the executable definitions (`dot`, `block`, `classify`, `round32`, …) reach no declaration
  from a Matrix-Core module, and they do reach FloatLib's decoder, classifiers, dyadic product
  and rounder;
* a negative control checks that the audit detects a Matrix-Core dependency.

The proofs refer to a copy of Matrix-Core's sources in `reference-compat/`.
`scripts/prepare_reference.py` creates it after checking each file's code tokens against
[reference-manifest.json](reference-manifest.json). The copy changes only the notation module,
where `ℕ`, `ℤ` and `ℚ` become scoped so they do not clash with mathlib. A change to Matrix-Core's
code fails the check until it is pinned again with `--pin`.

## Differential check

`scripts/compare.py` runs `mc_floatlib` and Matrix-Core's `mc_eval` on random inner products
for all 12 models. It uses five input schemes: uniform bits, normal values across the range,
values within a few binades of each other, subnormals, and inputs with infinities, NaN and
extreme values. With 20,000 cases per model and scheme (seed 7, 1,200,000 inner products),
all outputs agree bit for bit. The proofs already cover every input; this run tests the compiled
executables and the scripts.

## What the equivalence does and does not show

| Claim | Evidence |
| --- | --- |
| The FloatLib and Matrix-Core implementations give the same observed result for every input. | `block_agree`, `dot_agree`. |
| Matrix-Core implements the paper's algorithms. | Matrix-Core's independent specification and its equivalence proofs. |
| The model describes the hardware. | The paper's experiments, replayed as Matrix-Core's regression tests. This is not a proof about hardware. |

An assumption shared by both implementations would not be caught by the equivalence. The
FloatLib side shares only the block structure of the paper with Matrix-Core: it was written
independently, against FloatLib's formats and rounding.

Writing this port found one edge case in Matrix-Core: `dotOutcome` with an empty inner dimension
returned `c` as a finite word even when `c` was an infinity or NaN. `dotOutcome` now starts from
`observe32 c`. Results for `k ≥ 1` are unchanged.

## Folder map

| File | Purpose |
| --- | --- |
| [MCFloat/Model.lean](MCFloat/Model.lean) | The FloatLib implementation: decoding, products, `fl{·}`, the four accumulation configurations, special values, blocks and inner products. |
| [MCFloat/Equivalence/](MCFloat/Equivalence/) | Arithmetic, rounding, decoding, stage, block and inner-product proofs. |
| [MCFloat/Equivalence.lean](MCFloat/Equivalence.lean) | Correspondences between the FloatLib parameter records and Matrix-Core's models, and the main theorems. |
| [MCFloat/Contracts.lean](MCFloat/Contracts.lean) | Per-model contracts and chaining, transported to the FloatLib implementation. |
| [Main.lean](Main.lean) | `mc_floatlib`, the executable. |
| [tests/](tests/) | Audit and checked examples. |
| [scripts/](scripts/) | Reference preparation, comparison with `mc_eval`, and `check.py`. |
| [reference-manifest.json](reference-manifest.json) | Code-token hashes of the pinned Matrix-Core sources. |
| `reference-compat/` | Generated, ignored copy of Matrix-Core used by the proofs. |
