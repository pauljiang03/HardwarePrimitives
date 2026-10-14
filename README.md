# MMAlgebra

MMAlgebra is a Lean 4 development about the arithmetic of GPU matrix multipliers and the software built on them. It verifies the boundary between the two: what NVIDIA Tensor Cores and AMD matrix cores actually compute, what software can rely on, and which changes to the software leave the result bit for bit the same. Executable calculations and correctness proofs use the same definitions.

It has three parts, each building on the one before:

1. **Hardware semantics.** Executable models of the block FMAs of NVIDIA Tensor Cores (Volta to Blackwell: V100, A100, Ada, H100, H200 and B200, with FP8 on Ada, Hopper and Blackwell) and of AMD matrix cores (CDNA 1, 2 and 3), following Khattak and Mikaitis, *Accurate Models of NVIDIA Tensor Cores* ([paper](https://arxiv.org/html/2512.07004v4)) and *Accurate Models of AMD Matrix Cores* ([paper](https://arxiv.org/abs/2609.14845)). On top of the Tensor Core model: error bounds, a characterization of non-monotonicity, and TC-EFT, an error-free transformation that recovers the correctly rounded sum of a block FMA. The non-monotonicity results and the TC-EFT algorithm come from the TC-EFT paper (*TC-EFT: Characterizing and Correcting Tensor Core Arithmetic*). The root library `TensorCore` holds the Tensor Core model; [`amd/`](amd/README.md) holds the matrix core model.
2. **Emulation.** [`ozaki/`](ozaki/README.md) proves the Ozaki schemes and NVIDIA's automatic dynamic precision on both models, with correctly rounded variants and integer pipelines of bounded width.
3. **Schedules.** [`mmalgebra/`](mmalgebra/README.md) is an algebra of reduction schedules that decides which ways of computing a matrix product give identical bits on each architecture, and bounds how far apart they can be when they do not.

Lean names describe what each result states; docstrings cite the paper and number where one applies.

Start with the [guide](docs/README.md). It follows a calculation from encoded input words through alignment and correction, then explains how to run the Lean tests and add cases.

[Website](https://pauljiang03.github.io/MMAlgebra/) · [Status and roadmap](STATUS.md) · [Reviewer guide](ARTIFACT.md) · [Test walkthrough](tests/README.md) · [What is proven](TensorCore/THEOREMS.md) · [AMD matrix cores](amd/README.md) · [Ozaki schemes](ozaki/README.md) · [FloatLib implementation](floatlib-port/README.md)

## Build and run

Install [elan](https://github.com/leanprover/elan) and Python 3, use the pinned `lean-toolchain`, and run from this directory. A complete source ZIP works as well as a clone; the Git history is unnecessary. The FloatLib project also needs Git to fetch its pinned dependencies.

```sh
lake build
lake env lean examples/GettingStarted.lean
lake env lean examples/NonMonotonicity.lean
```

`lake build` builds the production library, the separate regression library, and the native test adapters. To build only the production library, use `lake build TensorCore`.

## A calculation and a proof

Four FP16 products of one produce the FP32 encoding of four:

```lean
import TensorCore.TC

open TensorCore

def ones : BlockInput v100F16F32 :=
  ⟨List.replicate 4 (0x3c00, 0x3c00), 0⟩

#eval (evalBlock ones).map fun t => t.output.bits.toNat

example : ((evalBlock ones).toOption.map fun t => t.output.bits) =
    some 0x40800000 := by decide +kernel
```

The calculation succeeds with the FP32 value `4.0`. It prints the encoded result; `Except.ok` indicates success. The `example` proves its exact bit pattern by kernel reduction. [GettingStarted.lean](examples/GettingStarted.lean) also shows how TC-EFT recovers contributions lost during alignment and returns the correctly rounded sum.

## Repository layout

| Import / directory | What belongs here |
| --- | --- |
| [`TensorCore.Numerics`](TensorCore/Numerics.lean) | Exact arithmetic, finite representations, encodings, and rounding contracts |
| [`TensorCore.TC`](TensorCore/TC.lean) | Tensor Core models (the numerical features of each variant, [including FP8](TensorCore/TC/GPUs.lean)), alignment, accumulation, normalization and final rounding, independent specification, error and non-monotonicity theory |
| [`TensorCore.EFT`](TensorCore/EFT.lean) | Reference extraction, scalar preconditions, chosen-grid conditions, and Algorithm 1 |
| [`TensorCore.Kernels`](TensorCore/Kernels.lean) | The bitvector Tensor Core datapath, bounded 576-bit EFT execution, and their equivalence proofs |
| [`TensorCore.Scalar`](TensorCore/Scalar.lean) | Native FP32 addition proof support used by the bounded EFT execution |
| [`Main/`](Main/) | Command-line entry points that call the library and print results for test comparisons |
| [`tests/`](tests/README.md) | Separate `TensorCoreTests` regression modules and executable-test walkthrough |
| [`examples/`](examples/README.md) | Checked worked examples and Lean batch adapters |
| [`amd/`](amd/README.md) | Matrix-Core: the AMD matrix-core (CDNA 1–3) formalization of *Accurate Models of AMD Matrix Cores*, a standalone Lake project with its own FloatLib implementation |
| [`ozaki/`](ozaki/README.md) | The Ozaki schemes (Ozaki-I, Ozaki-II, and ADP/ESC) on the Tensor Core and Matrix-Core models, with correctly rounded versions of all three; a standalone Lake project that requires both |
| [`mmalgebra/`](mmalgebra/README.md) | The reduction algebra of schedules: when two GEMM schedules give bitwise identical results on the Tensor Core and Matrix-Core models, and how far apart they can be, with a Python prototype; a standalone Lake project that requires both models and `ozaki/` |
| [`floatlib-port/`](floatlib-port/README.md) | Independent FloatLib implementation and equivalence proofs, with its own Lake project |
| [`docs/`](docs/README.md) | Numbered guide, command reference, and trust boundaries |
| [`scripts/`](scripts/) | Validation runners, exact-arithmetic oracles, and proof audits |
| [`data/`](data/) | Executable example inputs, regression fixtures, and recorded check reports |
| [`vendor/`](vendor/SOURCES.json) | Pinned paper inputs and expected outputs, reference models, licenses, and source hashes ([v0.5](vendor/SOURCES.json), [79143bd](vendor/matlab-tensor-core-79143bd/SOURCES.json)) |

`import TensorCore` loads all production layers. Smaller imports let you use the reference EFT without the bounded kernels. Bounded EFT declarations use the `TensorCore.EFMachine` namespace; scalar IEEE declarations use `TensorCore.IEEE`. The [guide's source map](docs/guide/01-getting-started.md#finding-the-source) links the main definitions and proofs.

## Two implementations

The first-principles implementation defines the model from encoded bits and exact integer and rational arithmetic. The [FloatLib implementation](floatlib-port/README.md) defines the same block model and reference EFT using LeanDojo FloatLib. Kernel-checked theorems prove equivalence between their encoded interfaces. The FloatLib project has its own pinned Lean toolchain:

```sh
cd floatlib-port
python3 scripts/check_all.py
python3 scripts/check_equivalence.py
```

The FloatLib implementation covers the reference algorithm; the bounded backend has a separate refinement proof. Reference preparation verifies the parent sources against the bundled manifest before building the equivalence proofs.

## Validation and scope

```sh
python3 scripts/check_clean_build.py
```

This builds a fresh snapshot, audits theorem dependencies, checks every worked Lean file and documentation example, and compares executable results with independent exact-arithmetic oracles and recorded hardware vectors. See [the test walkthrough](tests/README.md) for individual checks and their failure behavior.

The variants use FP16, BF16, TF32, E4M3 or E5M2 input formats and FP32 `c` and output; the final rounding is truncation, as in *Accurate Models*. Ada (RTX 1000 Ada, L40S) has A100's FP16, BF16 and TF32 features, H200 and B200 have H100's. The FP8 block FMAs are Ada's (16 products, a 13-bit mantissa after alignment, ten bits fewer than FP32), Hopper's through `wgmma` (32 products, a 13-bit mantissa) and B200's through `tcgen05.mma` (32 products, the 23-bit mantissa plus 2 padding bits); on Ada and Hopper the block output is truncated to a 13-bit mantissa, a parameter of the model that is a full binary32 output everywhere else. The FP8 `mma.sync` path of H100, H200 and B200 is modeled separately: the FP8 operands are converted exactly to FP16, the products at positions `k mod 4 ∈ {0, 1}` and `{2, 3}` go through two chained Hopper FP16 block FMAs from `+0`, and `c` is added afterwards in binary32 with round-to-nearest-even; the RTX PRO 6000's FP8 `mma.sync` is B200's FP8 block FMA with `c` inside. The error bound and the independent specification hold for every block-output width, FP8 included; the bitvector datapath covers the FP16, BF16 and TF32 variants and the six FP8 block FMAs; the non-monotonicity theorems concern the FP16, BF16 and TF32 variants. Any value TC-EFT returns is the exact sum correctly rounded to FP32, and it returns one exactly when that rounded sum is finite. Its fast FP32 path is taken whenever its check passes; otherwise a 576-bit exact fallback gives the answer. The non-monotonicity theorems cover specified families of encoded inputs. Hardware comparisons replay recorded GPU outputs bit for bit: 35,000 rows of V100, A100 and H100 (Accurate Models toolbox v0.5), 125,000 rows of Ada, L40S, H100, H200 and B200 (toolbox commit 79143bd: 75,000 FP16/BF16/TF32 and 50,000 FP8), and 20,000 H100 and H200 FP8 rows of the toolbox's release v0.1. The second set repeats rows: its L40S files are its Ada files, its H100 FP16/BF16/TF32 files are the v0.5 files, and H100 and H200 share their FP8 rows, so there are 110,000 distinct recorded outputs, 30,000 of them FP8. The FP8 rows follow their recordings: Ada's and L40S's, recorded with the toolbox's `mma.sync` harness, accumulate `c` in Ada's block FMA; B200's, recorded with the same harness, agree with the FP8 `mma.sync` model (and with B200's block FMA from `+0` followed by the addition of `c`), not with `c` inside B200's block FMA; the H100 and H200 rows of 79143bd agree with Hopper's FP8 block FMA from `c = 0`, as the toolbox's validation script reads them (`wgmma` with `D = 0`); the H100 and H200 rows of v0.1, on the same inputs, agree with the FP8 `mma.sync` model with `c`. No recorded data covers a nonzero `c` accumulated inside `wgmma` or `tcgen05.mma`; there the evidence is a cross-check against Microsoft's MMA-Sim simulator (850,000 cases on 31 instructions, no mismatch), not a hardware recording. The rows do not exercise the minimum alignment exponent, TF32's wide exponent range, E4M3's top binade, or the H100 TF32 variant with FMA size K = 8, and FP16/BF16/TF32 zero or subnormal operands are rare or absent. FP4, FP6 and the Blackwell instructions *Accurate Models* does not characterize are not modeled. The proofs concern the formal model under their stated hypotheses. Software checks require neither MATLAB nor CUDA. The scripts refuse to run under `python -O`, and rerunning them on unchanged sources leaves `git status` clean.

[What is proven](TensorCore/THEOREMS.md) · [What is tested](https://pauljiang03.github.io/MMAlgebra/proofs/tested/) · [Executable reference](docs/reference.md) · [Trust and style](docs/style.md)

## License

MMAlgebra's code and documentation are available under the [MIT license](LICENSE). Vendored materials retain their own notices, including the BSD 2-Clause license ([v0.5](vendor/matlab-tensor-core-v0.5/LICENCE), [79143bd](vendor/matlab-tensor-core-79143bd/LICENCE), [v0.1](vendor/matlab-tensor-core-v0.1/LICENCE)) for the Accurate Models code and recorded vectors. MMA-Sim (MIT license, Microsoft) is not vendored: its cross-check runs a local checkout of the commit pinned in [`vendor/mmasim/SOURCES.json`](vendor/mmasim/SOURCES.json). Downloaded dependencies retain their upstream licenses.
