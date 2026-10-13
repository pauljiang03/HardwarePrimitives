# Matrix-Core

This Lean library formalizes the arithmetic of AMD matrix cores (the MFMA instructions of the
CDNA 1, CDNA 2 and CDNA 3 GPUs). It follows Khattak, Mikaitis and Graziani, *Accurate Models of
AMD Matrix Cores* ([arXiv:2609.14845](https://arxiv.org/abs/2609.14845)), and uses the paper's
notation throughout. Executable calculations and correctness proofs use the same definitions.

Matrix-Core lives in the `amd/` folder of the TC-EFT repository, as a standalone Lake project: it
has its own numerical foundation and does not depend on TC-EFT, the NVIDIA Tensor Core
formalization in the rest of the [repository](../README.md).

Start with the [guide](docs/README.md). It maps the paper's notation to Lean, describes each
architecture, and explains the independent specification and the tests.

[What is proved](MatrixCore/THEOREMS.md) · [Paper notes](docs/paper-notes.md) · [Tests](tests/README.md)

## Build and run

Install [elan](https://github.com/leanprover/elan) and use the pinned `lean-toolchain`. From this
directory:

```sh
lake build
lake env lean examples/GettingStarted.lean
python3 scripts/check.py
```

`lake build` builds the library, the paper's test vectors as kernel-checked regressions, and the
trust audit. `scripts/check.py` does a clean build and then checks the examples and every Lean
code block in the documentation.

## A calculation and a proof

Four fp16 products `1 · 1` (`0x3C00 = 1`) with `c = 0` on CDNA 1:

```lean
import MatrixCore

open MatrixCore

def ones : BlockInput cdna1F16 := ⟨List.replicate 4 0x3C00, List.replicate 4 0x3C00, 0⟩

#eval blockBits ones

example : blockBits ones = .ok 0x40800000 := by decide +kernel
```

The result is the binary32 encoding of `4`. The same words give different results on the three
architectures; [GettingStarted.lean](examples/GettingStarted.lean) shows one such input and the
main theorems.

## The model

One MFMA block computes `d = Σ_{ℓ=1}^{N_FMA} a_ℓ b_ℓ + c` with binary32 `c` and `d`. The paper's
four configurations are the constructors of `Accumulation`:

| Architecture | Inputs | Configuration | `N_FMA` |
| --- | --- | --- | --- |
| CDNA 1, 2, 3 | fp32 | SFMA: `correct_rounding`, one product per step | 1 |
| CDNA 1 (MI100) | fp16 / bf16 | `correct_rounding`: exact sum, one RNE | 4 / 2 |
| CDNA 2 (MI210, MI250) | fp16 / bf16 / bf16 `_1k` | `pair_wise_sum`, subnormals flushed | 4 / 2 / 4 |
| CDNA 3 (MI300A, MI300X) | fp16 / bf16 / XF32 | `global_alignment` with late `c` (Algorithm 1) | 8 / 8 / 4 |
| CDNA 3 | fp8 E4M3/E5M2 FNUZ, any mix | `odd_even_grouping` (Algorithm 2) | 16 |

Longer inner products chain blocks, with each block's `d` as the next block's `c`.
`blockOutcome` and `dotOutcome` give the observed result for any input words, including
infinities, NaN, and overflow.

On CDNA 3 each aligned product is an integer number of grid steps (`alignedBits`).
`evalBlockMachine w` adds them in `w`-bit wrapping registers, and `evalBlockMachine_eq` proves it
gives the model's output for every input at 30 bits (fp16, bf16), 29 (XF32) and 31 (binary8).

For downstream proofs, each model has a contract (`cdna1F16_contract`, …, `cdna3FP8_contract`)
bundling what is proved about one block, including its output error bound, and `dotBits_blocks`
carries any of them to every block of an inner product, together with the loss accounting of the
whole inner product; `dotBits_error_bound` sums the blocks' error bounds.

The output is monotone in `c` on every configuration (`evalBlock_c_monotone`,
`dotBits_c_monotone`): unlike NVIDIA Tensor Cores, where `c` is aligned with the products, `c` never
sets the alignment exponent. It is monotone in the products only on SFMA and CDNA 1; CDNA 2 (operand flushing) and CDNA 3 (alignment to the largest exponent sum `e_a + e_b`)
have kernel-checked counterexamples on every input format (`cdna3F16_nonmonotonic`, …). The error bounds are also stated from the inputs
alone (`correctRounding_apriori`, `pairwise_apriori`, `aligned_apriori`), and the inner product and
`D = AB + C` results are stated against the exact `c + Σ_ℓ a_ℓ b_ℓ` of the whole vectors
(`dotBits_exact_error`, `mfma_error`).

## Repository layout

| Import / directory | What belongs here |
| --- | --- |
| [`MatrixCore.Numerics`](MatrixCore/Numerics.lean) | Exact arithmetic, Table 1 formats, decoding, fixed-point alignment (truncation and RD), binary32 RNE and its correctness and uniqueness |
| [`MatrixCore.MC`](MatrixCore/MC.lean) | Models of the variants, block stages, evaluation, special values, chaining, the fixed-width accumulator, and their theorems |
| [`MatrixCore.Specification`](MatrixCore/Specification.lean) | Independent transcription of the paper's algorithms and its equivalence with the model |
| [`tests/`](tests/README.md) | The paper's test vectors and the trust audit |
| [`examples/`](examples/) | Checked worked examples |
| [`docs/`](docs/README.md) | Guide and paper notes |
| [`Main/`](Main/) | `mc_eval`, which evaluates inner products from words |
| [`scripts/`](scripts/) | Validation runner and the MATLAB differential test |
| [`floatlib-port/`](floatlib-port/README.md) | A second implementation on FloatLib, proved equivalent to this one (separate Lake project with mathlib) |

## Validation and scope

* Every test vector of the paper's Section 4 (CDNA 1, 2 and 3; fp32, fp16, bf16, `_1k`, XF32,
  fp8) is a kernel-checked regression that reproduces the output the paper reports for the
  hardware. Where the paper's prose and its Algorithm 1 disagree at one point, the test records
  the algorithm's result and the note explains it ([paper notes](docs/paper-notes.md)).
* The model equals an independently written transcription of the paper's algorithms on every
  variant, CDNA 1, 2 and 3, for every input
  ([`Spec.blockBits_eq_spec`](MatrixCore/Specification/Equivalence.lean),
  [`Spec.pairwise_eq_spec`](MatrixCore/Specification/Pairwise.lean)).
* It agrees with the authors' MATLAB models on 600,000 random inner products across all ten
  models, once two special-value lines and one unread flag in the MATLAB code are corrected; the
  remaining two differences are paper vectors where the Lean model, not the MATLAB model, returns
  the reported hardware result ([differential testing](docs/differential.md)).
* A second implementation written on FloatLib (its formats, classification and binary32
  rounding) gives the same observed result as this model for every input of every model:
  finite word, infinity or NaN ([FloatLib implementation](floatlib-port/README.md)).
* All theorems use only Lean's standard axioms; the audit checks this and that the specification
  shares no definitions with the implementation.

The proofs concern the model. That the hardware behaves like it rests on the paper's experiments,
which the regression suite replays. No recorded hardware vectors for AMD GPUs are published, so
the suite uses the paper's explicit vectors.
