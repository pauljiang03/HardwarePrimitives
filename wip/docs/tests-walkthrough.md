# Executable Lean tests

The production library is under `TensorCore/`. Maintained regression witnesses are in the separate `TensorCoreTests` library under this directory. Worked calculations and batch IO adapters live in `examples/`; compiled batch entry points live in `Main/`. All use the parent project's pinned Lean toolchain.

Run commands below from the repository root unless a command explicitly enters `floatlib-port/`.

## 1. Build the imports

```sh
lake build
```

This builds `TensorCore`, `TensorCoreTests`, and five native adapters. `lake build TensorCore` builds production alone; `lake build TensorCoreTests` also builds the regression imports. Tests are included in the default validation build, while `import TensorCore` has no test dependencies.

The regression root is [TensorCoreTests.lean](TensorCoreTests.lean). It imports every maintained test module, allowing the trust audit to see the complete environment.

## 2. Run a worked calculation and its assertions

```sh
lake env lean examples/GettingStarted.lean
```

The file contains encoded inputs, `#eval` observations, concrete `example` assertions, and a symbolic application of a universal recovery theorem. It prints encoded results whose decoded FP32 values are:

| Calculation | FP32 value |
| --- | --- |
| Four products of one | `4.0` |
| TC model with four tiny products and C = 1 | `1.0` |
| EFT correction of the tiny-product result | `1.0000002384185791015625 = 1 + 2^-22` |

`Except.ok` indicates success; `some` indicates that an optional result is present. The second calculation loses four tiny products in the TC model; the third uses scalar EFT to recover their contribution before final nearest-even rounding.

The assertions compare complete words and, for EFT, the branch constructor. `decide +kernel` constructs the proof through Lean's kernel reduction. If a computed word differs from the asserted word, Lean reports an error and the command exits unsuccessfully. The symbolic example checks a proof for arbitrary inputs satisfying its premises.

`#eval` executes code and prints a value; it does not assert that value is correct. `#check` displays a term's type and verifies that it exists; it does not run a numerical test. The proof assertions are what make the worked calculation a checked regression.

For the non-monotonicity witness:

```sh
lake env lean examples/NonMonotonicity.lean
```

Decoded as FP32 values, the first two outputs are `1.0` and `1.00000011920928955078125 = 1 + 2^-23`: decreasing the accumulator from `1.0` to `0.999999940395355224609375 = 1 - 2^-24` raises the TC model output by one FP32 step. The next two outputs are both `1.0000002384185791015625 = 1 + 2^-22`, from EFT correction. The exact sums differ by `2^-24`, but nearest-even rounding gives the same result. The file then prints the general K/p and j-range theorem types. [The non-monotonicity chapter](../docs/guide/03-non-monotonicity.md) explains the changing alignment grid and midpoint rounding.

## 3. Check an individual regression module

```sh
lake env lean tests/TensorCoreTests/TC/Monotonicity.lean
lake env lean tests/TensorCoreTests/EFT/EFT.lean
lake env lean tests/TensorCoreTests/EFT/NativeEFT.lean
```

A successful module may print nothing. Lean elaborates and checks its definitions and proofs. These files are mathematical regression modules; they do not each define an IO `main`.

| Test area | Main contents |
| --- | --- |
| [TC/Cases.lean](TensorCoreTests/TC/Cases.lean) | Named denormalized-product/alignment traces and snapshot observations |
| [TC/Monotonicity.lean](TensorCoreTests/TC/Monotonicity.lean) | V100/Ampere/Hopper family theorems, thresholds, and witness-range boundaries |
| [TC/Features.lean](TensorCoreTests/TC/Features.lean) | Canonical alignment, minimum alignment exponents, padding bits and machine-refinement witnesses |
| [TC/FP8.lean](TensorCoreTests/TC/FP8.lean) | Every special and boundary E4M3 and E5M2 encoding, the widened E4M3 layout, the 13-bit block output of Ada FP8, two-block sums and the B200 recording convention |
| [TC/Instruction.lean](TensorCoreTests/TC/Instruction.lean) | Instruction variants with their block FMAs in order, input width, and block-order examples |
| [TC/Composition.lean](TensorCoreTests/TC/Composition.lean) | Encoded residual ledger of chained block FMAs and cancellation correction |
| [TC/Datapath.lean](TensorCoreTests/TC/Datapath.lean) | Bitvector datapath words: alignment loss, overflow, subnormal output, −0, and input errors |
| [EFT/EFT.lean](TensorCoreTests/EFT/EFT.lean) | Low parts, overlap, scalar acceptance/rejection, and unsafe-unchecked counterexamples |
| [EFT/EncodedEFT.lean](TensorCoreTests/EFT/EncodedEFT.lean) | Encoded Algorithm 1 results and supplied-D/domain behavior |
| [EFT/ScalarEFT.lean](TensorCoreTests/EFT/ScalarEFT.lean) | Correction precision and scalar-summation conditions |
| [EFT/MachineSplit.lean](TensorCoreTests/EFT/MachineSplit.lean) | Fixed-width splitting boundaries |
| [EFT/BoundedEFT.lean](TensorCoreTests/EFT/BoundedEFT.lean) | Bounded-backend results and range boundaries |
| [EFT/NativeEFT.lean](TensorCoreTests/EFT/NativeEFT.lean) | Native FP32 scalar fold and bounded algorithm preservation |
| [Specification/NegativeControls.lean](TensorCoreTests/Specification/NegativeControls.lean) | Wrong normalization, alignment, minimum alignment exponents, order, and zero-sign alternatives |
| [Specification/Audit.lean](TensorCoreTests/Specification/Audit.lean) | Compiled dependency independence of the mathematical specification |

The test root also includes binary rounding, canonical-format, public-domain, directed-rounding, and flowback modules. [What is proven](../TensorCore/THEOREMS.md) links the general production results that these witnesses exercise.

## 4. Understand a Lean IO adapter

Checking `lake env lean FILE` does not call `main`. To execute `main`, use `lake env lean --run FILE INPUT` or a compiled executable.

[examples/EFTCoverage.lean](../examples/EFTCoverage.lean) reads a batch file, parses encoded operands, evaluates the model and scalar correction, and writes one JSON observation per row. The coverage harness creates that input:

```sh
python3 scripts/check_eft_coverage.py
```

Its data flow is:

```text
Python case generator / recorded vectors
  -> encoded batch file
  -> lake env lean --run examples/EFTCoverage.lean INPUT
  -> main parses operands and evaluates the Lean definitions
  -> JSON observations with bits, components, and predicate decisions
  -> Python exact-arithmetic expectations and assertions
```

Rational diagnostics use `numerator/denominator` strings. Python parses them with `fractions.Fraction` and compares them exactly. Words are integers, so a one-bit difference or signed-zero difference remains visible. The harness checks process success and record counts before accepting comparisons.

[examples/InstructionGroups.lean](../examples/InstructionGroups.lean) is another IO adapter. `python3 scripts/check_instruction_groups.py` generates 99 encoded cases and compares the Lean instruction outputs with an independent exact-arithmetic oracle applied block FMA by block FMA. The cases cover all 16 positions, populated block FMAs, reversed block order, signed zeros, subnormals, and cancellation. This check runs entirely in software.

## 5. Run a compiled Lean executable

The paper adapter accepts text commands. Create a file with this line:

```text
block fp16 4 0 none 3072 3072 3072 3072 3072 3072 3072 3072 1065353216 1065353216
```

Run:

```sh
.lake/build/bin/tc_eft_reference /path/to/input.txt
```

The command encodes four `2^-12 · 2^-12` products, with C and supplied D both `1.0`. Decoded as FP32 values, the model result is `1.0` and the EFT correction is `1.0000002384185791015625 = 1 + 2^-22`, with branch `scalar`. The executable also prints exact ideal and extraction diagnostics.

| Executable | Input and purpose |
| --- | --- |
| `tc_trace` | V100 FP16 hexadecimal words, or `--file`/`--round-file` batches; full trace observations |
| `tc_features` | Decimal commands for formats, models, generic block FMAs, and rounding |
| `tc_eft_reference` | Generic FP16/BF16/packed-TF32 block, rounding, and perturbation-family commands |
| `tc_bounded_eft` | Blocks of the named variants and fixed-workspace rounding; bounded/native scalar execution |
| `tc_lean_eft_check` | JSON Lines on stdin; compares bounded and native scalar execution |

For the last adapter, one request is:

```json
{"acc":0,"terms":[1065353216]}
```

The encoded request adds FP32 `1.0` to `0.0`. Decoding the returned results gives:

| Execution | FP32 value |
| --- | --- |
| Reference | `1.0` |
| Native | `1.0` |

The [executable reference](../docs/reference.md) specifies word widths, variant names, packed/register TF32 conventions, and command formats. Lean checks proofs during elaboration; compiled execution evaluates the functions with proofs erased. Numerical comparisons additionally check the compiled code.

## 6. Run independent comparisons and trust audits

```sh
python3 scripts/validate.py
python3 scripts/check_features.py
python3 scripts/check_device_formats.py
python3 scripts/check_device_replay.py
python3 scripts/check_eft.py
python3 scripts/check_lean_eft.py
python3 scripts/check_axioms.py
python3 scripts/check_docs.py
```

`validate.py` and the feature scripts compare traces/rounding with independent exact arithmetic and recorded GPU words. `check_eft.py` runs scalar coverage, instruction-variant comparisons, pinned paper generators, and the bounded EFT comparisons. `check_lean_eft.py` compares native scalar folds with an ordered-encoding rounding oracle.

The Accurate Models paper's recorded inputs and expected outputs are under [`vendor/matlab-tensor-core-v0.5/model_validation/`](../vendor/matlab-tensor-core-v0.5/model_validation/), with hashes in [`vendor/SOURCES.json`](../vendor/SOURCES.json). Both implementations replay all 35,000 rows: V100/A100/H100 FP16 and A100/H100 BF16/TF32, 5,000 per variant. The files contain the published A/B/C inputs and D outputs.

The toolbox's later recordings, at commit 79143bd, are under [`vendor/matlab-tensor-core-79143bd/model_validation/`](../vendor/matlab-tensor-core-79143bd/model_validation/), with hashes and conventions in [its `SOURCES.json`](../vendor/matlab-tensor-core-79143bd/SOURCES.json): Ada, L40S, H100, H200 and B200 with FP16, BF16, TF32, E4M3 and E5M2 inputs, 5,000 rows each. [check_device_replay.py](../scripts/check_device_replay.py) checks the hashes, compares an independent Python decoder of E4M3 and E5M2 with the Lean decoders on all 512 words, and replays the 125,000 rows of that commit through the models (`tc_features dot`) and the invocation descriptors (`tc_features block` and `chain`). FP8 rows hold 32 products: two block FMAs on Ada and L40S, chained through `c` (`Model.dot`), one on H100, H200 and B200. Each FP8 row is replayed through the model its outputs agree with: Ada and L40S accumulate `c` in the block FMA; the H100 and H200 FP8 rows agree with Hopper's FP8 block FMA from `c = 0`, as the toolbox's validation script reads them (`wgmma` with `D = 0`); the B200 FP8 rows, recorded with the toolbox's `mma.sync` harness ([`model_validation/CUDA/mma_fp8_output_fp32.cu`](../vendor/matlab-tensor-core-79143bd/model_validation/CUDA/mma_fp8_output_fp32.cu), vendored), are replayed through the FP8 `mma.sync` model (`tc_features mma-sync`, `mmaSyncFP8Dot`) and through B200's block FMA from `c = 0` followed by the addition of `c` in binary32 with round-to-nearest-even (`tc_features dot-then-add`, `Model.dotThenAdd`). The H100 and H200 FP8 outputs of the toolbox's release v0.1, on the same inputs, are under [`vendor/matlab-tensor-core-v0.1/`](../vendor/matlab-tensor-core-v0.1/) (hashes in its `SOURCES.json`) and are replayed through the `mma.sync` model with `c`: 20,000 more rows. Negative controls must disagree with the recordings: Ada and Hopper FP8 with a binary32 block output, B200's FP8 block FMA holding `c`, and, for the v0.1 rows, Hopper's FP8 block FMA from `c = 0`. The report is [`data/regressions/device-replay-report.json`](../data/regressions/device-replay-report.json).

[check_mmasim.py](../scripts/check_mmasim.py) cross-checks the models against Microsoft's MMA-Sim simulator (MIT licence) at the commit pinned in [`vendor/mmasim/SOURCES.json`](../vendor/mmasim/SOURCES.json): 31 instructions of V100 to B200 and the RTX PRO 6000 (`tc_features model-dot`), `wgmma` and `tcgen05.mma` with `c` included, and the FP8 `mma.sync` path composed from MMA-Sim's FP16 `mma.sync` (`tc_features mma-sync`). It runs a local checkout, unmodified except that the FP64 FMA module (built with `-fopenmp`, which Apple clang rejects) is replaced by a stub that fails if called, and checks the hashes of the files it imports; it needs a Python with `torch` and `ninja`, so `check_clean_build.py` does not run it. The report is [`data/regressions/mmasim-report.json`](../data/regressions/mmasim-report.json): 850,000 cases, 708,953 identical (581,052 with `c ≠ 0`), 42,215 with an Inf or NaN operand and 98,832 overflowing binary32 (both rejected by the Lean models), 0 mismatches; 80,000 `mma.sync` cases, 0 mismatches.

```sh
python3 scripts/check_mmasim.py --mmasim /path/to/MMA-Sim --python /path/to/python-with-torch
```

Follow one recorded V100 row through the implementation:

1. [check_device.py](../scripts/check_device.py) reads A/B/C and converts the FP32-stored operand values exactly to FP16 words. D is reserved as the expected output.
2. [Main/Trace.lean](../Main/Trace.lean) parses the words into `BlockInput` and calls the [snapshot adapter](TensorCoreTests/TC/Cases.lean).
3. The adapter calls `evalBlock` in [TC/Block.lean](../TensorCore/TC/Block.lean), which performs decoding, exact multiplication with the products kept in denormalized form, grid selection, signed truncation, accumulation, and rounding to FP32.
4. Python compares the returned `bits` with the recorded D word and fails on any mismatch. D is never supplied to this model calculation.

The first published V100 row can be run directly:

```sh
lake build tc_trace
.lake/build/bin/tc_trace 3bd5 38ca 3c3e b935 b534 36bf 3df8 34ec 3f7f418c
python3 scripts/check_device.py
```

The JSON reports `bits` as an integer whose hexadecimal representation is `3f9b7dec`, matching the first recorded D. Its alignment exponent `alignExp` is `-1` and grid exponent `alignGridExponent` is `-24`. The final command compares all 5,000 V100 rows.

The semantic proof is a separate guarantee: [`IndependentSpec.supported_eq_spec`](../TensorCore/TC/Specification/Supported.lean) equates the executable evaluator with the independent mathematical specification for every input of each supported variant, including rejection. `python3 scripts/check_independent_spec.py` checks this development and its dependency-independence controls. [What is proven](../TensorCore/THEOREMS.md) identifies the non-monotonicity and EFT results and their premises.

The universal proofs concern the defined finite-domain model under their stated hypotheses. Agreement with recorded GPU outputs covers those recorded inputs; correspondence between the specification, the paper, and physical hardware remains a separate specification question.

`check_axioms.py` rebuilds the full regression environment before auditing theorem roots and scanning maintained Lean sources for proof shortcuts. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`. The audit regression deliberately puts broken source behind a valid cache and requires rejection. Specification and bounded-execution audits also contain deliberate dependency-contamination controls that must fail.

Use ordinary `python3`: numerical harness assertions form part of the check, and every script refuses to run under `-O` or `PYTHONOPTIMIZE`. A parse error, failed Lean process, unexpected record count, or failed comparison stops the harness. Successful reports go under `data/regressions/` (run timings go to the untracked `tmp/timings/`); intermediate batches and logs go under ignored `tmp/`.

For the complete gate:

```sh
python3 scripts/check_clean_build.py
```

It builds a fresh source snapshot without `.lake`, runs the maintained checks, checks every worked `.lean` file, and verifies Markdown Lean examples and local links. Source hashes must remain stable before it publishes the reports.

## 7. Check the independent FloatLib implementation

```sh
cd floatlib-port
python3 scripts/check_all.py
lake env lean tests/RepresentationFacts.lean
python3 scripts/check_equivalence.py
```

These commands use the FloatLib project's own toolchain and executable. `check_all.py` builds universal equivalence proofs and runs source-independence/trust audits, paper cases, recorded-vector replay, and non-monotonicity boundaries. The direct comparator snapshots the current parent source and compares both implementations' observations and decoding results. [The folder guide](../floatlib-port/FOLDER_GUIDE.md) explains each field and comparator.

A complete source ZIP works without the Git history. Reference preparation uses the bundled [pinned manifest](../floatlib-port/reference-manifest.json). Edge checks prepare a fresh source copy with no Git available, accept comment/whitespace edits, and reject arithmetic, string-literal, import, manifest, and dependency mutations. Git remains necessary for Lake's initial dependency downloads.

## Adding a regression

Put a maintained case in `tests/TensorCoreTests/TC/` or `EFT/`, import the relevant production module, and give its assertion a name in the regression namespace:

```lean
import TensorCore.TC.Block

open TensorCore
namespace TensorCore.Regression

def walkthroughCase : BlockInput v100F16F32 :=
  ⟨List.replicate 4 (0x3c00, 0x3c00), 0⟩

theorem walkthrough_case_bits :
    ((evalBlock walkthroughCase).toOption.map fun t => t.output.bits) = some 0x40800000 := by
  decide +kernel

end TensorCore.Regression
```

Add the module to `tests/TensorCoreTests.lean` so the full audit imports it. Run `lake build TensorCoreTests` and check the individual file. Update the results summary (`TensorCore/THEOREMS.md`) when adding a public result. The layout check rejects a module omitted from the full audit.

For an exploratory calculation, use a scratch Lean file and `lake env lean /path/to/scratch.lean`. For a larger family, prefer applying a symbolic production theorem or extending an independent executable comparison; finite examples alone do not prove a universal arithmetic claim.
