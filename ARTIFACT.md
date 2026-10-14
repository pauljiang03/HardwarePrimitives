# Reviewer guide

This artifact contains the Lean formalization, executable TC model and TC-EFT algorithm, and validation data supporting the TC-EFT paper (*TC-EFT: Characterizing and Correcting Tensor Core Arithmetic*); the TC model follows Khattak and Mikaitis, *Accurate Models of NVIDIA Tensor Cores*. Use this guide to check the main claims; [What is proven](TensorCore/THEOREMS.md) and the [FloatLib correspondence](floatlib-port/COMPARISON.md) give the detailed proof map and hypotheses.

Install elan, Python 3, and Git as described in the [build instructions](README.md#build-and-run). Each Lean project uses its own pinned toolchain. Run the commands below from the repository root. The scripts use `assert` and refuse to run under `python -O` or `PYTHONOPTIMIZE`. The checks require no MATLAB, CUDA, or GPU.

## 1. Smoke check

```sh
lake build
lake env lean examples/GettingStarted.lean
lake env lean examples/NonMonotonicity.lean
```

All three commands must exit successfully. The three numerical results from `GettingStarted.lean`, decoded as FP32 values, are:

| Calculation | FP32 value |
| --- | --- |
| Four products of one | `4.0` |
| TC model with four tiny products and C = 1 | `1.0` |
| EFT correction of the tiny-product result | `1.0000002384185791015625 = 1 + 2^-22` |

The executable prints encoded results; `Except.ok` indicates success and `some` indicates that an optional result is present. The table shows their floating-point values. The file checks these outputs with proof assertions.

`NonMonotonicity.lean` decreases the accumulator from `1.0` to `0.999999940395355224609375 = 1 - 2^-24`, while the model output rises from `1.0` to `1.00000011920928955078125 = 1 + 2^-23`. Both EFT-corrected outputs are `1.0000002384185791015625 = 1 + 2^-22`: the first exact sum is already representable, and the second is a midpoint that nearest-even rounding maps to the same FP32 value. The file checks these assertions and prints the general theorem types.

## 2. Paper claims and evidence

Run the individual commands after the smoke build. Lean files check their proof assertions and may finish without printing output; a successful check exits with code zero.

| Paper claim | Proof or data to inspect | Review command |
| --- | --- | --- |
| Consistency of finite binary encodings, including subnormals and signed zero | [`signedFiniteBinaryBijection`](TensorCore/Numerics/Binary/SignedBijection.lean) and its inverse laws | `lake env lean examples/BinaryFoundation.lean` |
| TC block model and total output error bound | [`IndependentSpec.supported_eq_spec`](TensorCore/TC/Specification/Supported.lean); [`evalBlock_error_bound`](TensorCore/TC/ErrorBounds.lean) | `python3 scripts/check_independent_spec.py` |
| Model conditions for non-monotonicity and the perturbation range | [`nonmonotone_encoded`](TensorCore/TC/Monotonicity.lean); [`nonmonotone_range_encoded`](TensorCore/TC/MonotonicityRange.lean) | `lake env lean tests/TensorCoreTests/TC/Monotonicity.lean` |
| Exact Sum Recovery | [`overlap_recovery`](TensorCore/EFT/Extraction.lean) | `lake env lean tests/TensorCoreTests/EFT/EFT.lean` |
| Precondition for Correct Rounding and its application to TC-EFT | [`ExtractionGrid.inputGrid_scalarPredicate_fp32`](TensorCore/EFT/ExtractionGrid.lean); [`scalarCorrected_correct`](TensorCore/EFT/Extraction.lean); [`tcEftEncoded_correct`](TensorCore/EFT/Encoded.lean); [`EFMachine.Components.scalar_of_guard`](TensorCore/Kernels/EFT/ScalarGuard.lean) | `python3 scripts/check_eft.py` |
| Bitwise agreement with all 35,000 published validation cases | [Pinned source hashes](vendor/SOURCES.json) and [recorded inputs/outputs](vendor/matlab-tensor-core-v0.5/model_validation/) | `python3 scripts/check_features.py` followed by `python3 scripts/check_device_formats.py` |
| Beyond the paper: bitwise agreement on Ada, L40S, H100, H200 and B200 for FP16, BF16, TF32, E4M3 and E5M2 (125,000 recorded rows) | [Pinned source hashes](vendor/matlab-tensor-core-79143bd/SOURCES.json), [recorded inputs/outputs](vendor/matlab-tensor-core-79143bd/model_validation/) and [the FP8 models](TensorCore/TC/GPUs.lean) | `python3 scripts/check_device_replay.py` |
| Correspondence between the first-principles and FloatLib implementations | [`floatlib_eq_reference`](floatlib-port/TCFloat/Equivalence/Representations.lean) and `floatlib_eq_reference_inverse` | Run the FloatLib commands in section 3 |

The reviewed Tensor Core variants use FP16, BF16, or TF32 input formats and the FP32 output format; the final rounding is truncation. The repository also models the FP8 (E4M3, E5M2) block FMAs of Ada, Hopper and Blackwell and replays their recorded outputs; the TC-EFT paper's claims concern the FP16, BF16 and TF32 variants. Any value TC-EFT returns is the exact sum correctly rounded to FP32, and it returns one exactly when that rounded sum is finite. Its fast FP32 path is taken whenever its check passes, which uses the lowest bit actually set in the low parts, as the TC-EFT paper's generator does; otherwise exact accumulation gives the answer. The paper's input-based precondition (17) derives five of the check's nine conditions for FP32. Hardware evidence consists of replaying recorded GPU outputs, which do not exercise the minimum alignment exponent, zero or subnormal operands, TF32's wide exponent range (the TF32 input files duplicate the V100 FP16 inputs), or the H100 TF32 variant with FMA size K = 8. The universal proofs concern the defined model under their hypotheses. [What is proven](TensorCore/THEOREMS.md) also identifies the bounded backend and native FP32 refinement proofs.

## 3. Full validation

For the first-principles implementation:

```sh
python3 scripts/check_clean_build.py
```

This creates a source snapshot without a build cache, checks the proofs and allowed axioms, runs exact-arithmetic comparisons and recorded-vector replay, and checks the examples, documentation, and layout. Expected evidence is `success: true` in [data/regressions/clean-build.json](data/regressions/clean-build.json), zero numerical mismatches, and an audit permitting only `propext`, `Classical.choice`, and `Quot.sound`. The command regenerates the reports under `data/regressions/`; run timings go to the untracked `tmp/timings/`, so rerunning on unchanged sources leaves `git status` clean. It takes about 3 minutes on a recent laptop; the FloatLib suite below takes about 10.

For the independent FloatLib implementation, run this block from the repository root:

```sh
(
  set -e
  cd floatlib-port
  python3 scripts/check_all.py
  python3 scripts/check_equivalence.py
)
```

`check_all.py` builds the universal equivalence proofs, audits executable independence and allowed axioms, and runs the numerical suites. It must print `All FloatLib-port checks passed.` and write `status: passed` in `floatlib-port/test-results/summary.json`. The direct comparator then checks 115,029 command observations and 668,944 decoding cases, with zero mismatches and a passing comparator negative control in `floatlib-port/test-results/equivalence/report.json`. Run the commands in this order because the comparator uses generated test inputs. The finite comparisons supplement the universal equivalence proofs.

Any failed proof, process, comparison, or negative control stops its runner with a nonzero exit code. See the [test walkthrough](tests/README.md) for individual suites, input formats, and failure behavior.
