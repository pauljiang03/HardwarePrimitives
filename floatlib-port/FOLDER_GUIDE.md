# Guide to the FloatLib implementation

`floatlib-port/` is an independent Lean project inside `MMAlgebra`. It implements the paper's FP32-output Tensor Core block model and reference TC-EFT using FloatLib, and proves that its checked interfaces agree with the first-principles implementation. Its equivalence layer verifies the parent arithmetic and proof bodies against the pinned reference manifest.

This guide explains the folder and the strength of its evidence. The [README](README.md) gives the detailed numerical behavior and executable commands. The [comparison document](COMPARISON.md) maps the arithmetic stages and paper statements to their Lean theorems.

## Verification claims

Lean checks universal theorems about the formal implementations, including their equivalence and the EFT's correctly rounded result under the stated conditions. Executable comparisons check those implementations against independent exact-arithmetic oracles and recorded hardware outputs.

Three different claims should be kept separate:

| Claim | Evidence |
|---|---|
| The FloatLib and first-principles implementations compute the same modeled behavior. | A universal equivalence theorem, including output bits, EFT branches and validation errors. |
| The formal EFT recovers the exact sum and produces correctly rounded FP32 results under its conditions. | Exact-recovery and rounding proofs; the scalar branch retains its grid, coefficient and representability conditions. |
| The behavior model describes physical Tensor Cores. | Agreement with recorded hardware measurements on the tested cases. This is not a proof covering every hardware execution. |

Equivalence cannot rule out an assumption shared by both models being wrong about hardware. Likewise, Lean checks the written theorem and its hypotheses; relating those definitions to the manuscript and hardware remains part of the specification review.

## Scope of interface equivalence

The main theorem is [`TCFloat.Equivalence.floatlib_eq_reference`](TCFloat/Equivalence/Representations.lean). It covers FP16, BF16 and packed TF32 operands with FP32 output, keeping `F = 23 + padding` mantissa bits after alignment. The FMA size, the number `padding` of padding bits and the optional minimum alignment exponent are parameters.

For every encoded block and every supplied FP32 word D, the two checked interfaces return the same TC bits and the same EFT branch/bits, or corresponding validation errors. D does not have to be the TC model's output. Nonfinite encodings and wrong product counts are included as rejected cases.

`inputEquiv` supplies a two-way mapping between the encoded input types. `floatlib_eq_reference_inverse` states the result starting from a FloatLib input. Separate equivalences cover words, canonical decoded terms, errors and tagged EFT outcomes. [`round32_eq`](TCFloat/Equivalence/RoundingStage.lean) connects the converters for every rational input in toward-zero (RTZ) and nearest-even (RNE) modes.

These claims concern checked interfaces and representations whose metadata and values are consistent. Arbitrary unchecked `Term` and `Trace` records can contain inconsistent metadata or output fields, so the representation equivalences cover their valid subsets. [RepresentationFacts.lean](tests/RepresentationFacts.lean) checks these distinctions.

## How theorem transport works

Some proofs follow this argument:

1. A theorem establishes a property of the first-principles implementation.
2. A proved equivalence connects the relevant first-principles and FloatLib computations.
3. Rewriting through those equalities establishes the property for the FloatLib implementation.

For example, [`floatlib_error_bound`](TCFloat/Equivalence/PortedTheorems.lean) applies `TensorCore.evalPrepared_error_bound`, then translates the exact input sum, accumulator, output and grid quantities through the proved correspondence. Lean checks that translation and all required hypotheses.

The transported proof depends on the first-principles theorem and the proved equivalence. Separate FloatLib theory modules prove recovery, scalar correction and rounding directly from FloatLib operations.

The executable uses FloatLib decoding, exact dyadic multiplication and rounding to FP32. A dependency audit checks its independence from the first-principles `TensorCore` functions. The audit also checks that EFT correction does not call the TC evaluator or the ideal-sum function to obtain its answer.

## Folder map

| File | Purpose |
|---|---|
| [TCFloat/Model.lean](TCFloat/Model.lean) | Executable TC stages, extraction, scalar guard and reference EFT branches. |
| [TCFloat/Interface.lean](TCFloat/Interface.lean) | Encoded paper interfaces, bounded inputs and typed validation errors. |
| [TCFloat/Theory.lean](TCFloat/Theory.lean), [Rounding.lean](TCFloat/Rounding.lean), [EFT.lean](TCFloat/EFT.lean) | Recovery, FloatLib rounding semantics and EFT correctness proofs. |
| [Behavior.lean](TCFloat/Behavior.lean), [DirectedRounding.lean](TCFloat/DirectedRounding.lean), [Monotonicity.lean](TCFloat/Monotonicity.lean) | Alignment, flowback, directed rounding and general non-monotonicity results. |
| [TCFloat/Equivalence/](TCFloat/Equivalence/) | Decoder/rounding/stage bridges, universal equivalence, inverse maps and paper theorems. |
| [Main.lean](Main.lean) | Batch executable adapter used by the regression scripts. |
| [TCFloat.lean](TCFloat.lean) | Root import that includes the equivalence and paper proof modules in the build. |
| [tests/](tests/) | Axiom/dependency audit, representation checks and decoder comparison programs. |
| [scripts/](scripts/) | Source preparation, regression runners and direct comparison with the first-principles executable. |
| [reference-manifest.json](reference-manifest.json) | Pinned source hashes, code-token hashes and imports for parent proof dependencies. |
| `reference-compat/` | Generated, ignored compatibility copy of verified parent proof dependencies. |
| `test-results/` | Generated, ignored inputs, logs, comparison outputs and reports. |
| `.lake/` | Downloaded dependencies and compiled artifacts. |
| `test-results/summary.json`, `test-results/equivalence/report.json` | Recorded verification results, revisions and source hashes. |

The paper proof modules establish the full output error bound, arbitrary-summand flowback, the general perturbation range, overlap identities, any-order exact summation and the paper's chosen-grid scalar conditions. The [comparison table](COMPARISON.md#correspondence-to-the-papers-fp32-statements) lists the individual theorem names.

The two implementations use the same executable scalar guard, based on the lowest bit actually set in the low parts. The paper theorems also handle a suitably chosen common grid with separate coefficient and absolute-range conditions. A failed executable guard does not prove scalar summation is impossible; the reference EFT can use exact consolidation followed by one FP32 rounding.

## How to build and verify

Use a complete repository clone or source ZIP, since the scripts read the parent project's source and saved test data. the Git history is unnecessary. Install elan/Lean, Git and Python 3; Lake uses Git to fetch pinned dependencies. Initial dependency setup needs network access and several GB of storage. MATLAB, CUDA and a GPU are unnecessary for replaying the saved measurements.

From the repository root:

```sh
cd floatlib-port
python3 scripts/check_all.py
python3 scripts/check_equivalence.py
```

The first command prepares the source compatibility copy, builds the executable and proofs, runs the axiom/dependency audit and representation checks, then runs the model, hardware replay, EFT, edge and monotonicity suites. The second builds the first-principles executable separately and compares both implementations on identical inputs. Run them in that order because the direct comparison consumes generated test inputs.

For a build and proof audit without rerunning the regression suites:

```sh
python3 scripts/prepare_reference.py
lake build
lake env lean tests/Audit.lean
```

The FloatLib project uses Lean 4.34.0 and dependency revision `0d91825727839f597fd06b22fdd038ea21480f0c`. The first-principles project uses Lean 4.33.1. The [reference manifest](reference-manifest.json) pins the arithmetic and proof dependencies used by the equivalence layer.

The preparation script checks the bundled manifest's SHA-256, resolves each parent dependency to its manifest entry, and verifies mathematical code tokens, string literals, and imports. Token hashes use UTF-8 JSON arrays and ignore comments and whitespace. Verified modules are copied into `reference-compat/`, with Nat/Int/Rat notation scoped to `TensorCore` using the same expansions to avoid mathlib parser collisions. The generated manifest records source hashes and dependency metadata. A protected-code or dependency mismatch causes preparation to fail. Edge checks exercise complete source archives and deliberate mutations of each protected input.

## Running Lean and the models against the test cases

Run all commands below from `floatlib-port/`. There are two activities: Lean checks the universal proofs when building the library; the regression scripts execute compiled Lean code on concrete test inputs and compare its outputs with expected results. The Python scripts are test harnesses, not substitutes for executing the Lean model.

### 1. Compile the proofs and executable

```sh
python3 scripts/prepare_reference.py
lake build
```

`lake build` includes the root `TCFloat` library, its equivalence and paper theorems, and the `tc_floatlib` executable. A successful build produces `.lake/build/bin/tc_floatlib`. Run `lake env lean tests/Audit.lean` to check the proof dependencies and executable independence, and `lake env lean tests/RepresentationFacts.lean` for the representation checks.

For a specific proof module after preparation, use Lake so that its dependencies are built too:

```sh
lake build TCFloat.Equivalence.Representations
lake build TCFloat.Equivalence.ScalarCorrection
```

### 2. Execute each saved/generated test suite

| Command | What executes and is compared | Main report under `test-results/` |
|---|---|---|
| `python3 scripts/check_features.py` | Compiled Lean TC model on synthetic FP16 cases and recorded V100/A100/H100 FP16 rows; compares bits and exact stage values. | `feature-report.json` |
| `python3 scripts/check_replay.py` | Compiled Lean model on recorded A100/H100 BF16/TF32 rows, plus model/EFT execution on the saved scalar-coverage corpus. | `replay-report.json` |
| `python3 scripts/check_tc_eft_paper.py` | Pinned paper generators produce inputs and expected results; compiled Lean executes the blocks, perturbation families and rounding cases. | `eft-paper-report.json` |
| `python3 scripts/check_edges.py` | Compiled Lean on supplied-D, rounding and invalid-input edge cases; also checks that deliberately contaminated dependency audits fail. | `edges-report.json` |
| `python3 scripts/check_monotonicity.py` | Compiled Lean on 360 boundary cases around the proved non-monotonicity threshold. | `monotonicity-report.json` |

Run the full suite in the required build context with:

```sh
python3 scripts/check_all.py
```

Success ends with `All FloatLib-port checks passed.` and writes `test-results/summary.json`. Commands exit with a nonzero status on failure. Inspect the assertion or Lean error and the `test-results/check-*.log` files for that run. Expected invalid-input rejections pass when they match the expected rejection.

### 3. Compare directly against the first-principles implementation

After `check_all.py` has generated the corpus:

```sh
python3 scripts/check_equivalence.py
```

This snapshots the parent sources and builds `tc_eft_reference` under `test-results/reference-source/`, sends the same commands to it and `.lake/build/bin/tc_floatlib`, and compares complete JSON records. It also executes both decoder comparison programs. The result is `test-results/equivalence/report.json`; paired outputs are saved as `observations-original.jsonl`, `observations-floatlib.jsonl`, `decoding-original.jsonl` and `decoding-floatlib.jsonl` in that directory.

### 4. Run a small input file yourself

```sh
mkdir -p test-results
cat > test-results/example-inputs.txt <<'EOF'
block fp16 1 0 none 3072 3072 1065353216 1065353216
round 16777217 16777216
family 0 4 1
EOF
.lake/build/bin/tc_floatlib test-results/example-inputs.txt > test-results/example-outputs.jsonl
cat test-results/example-outputs.jsonl
```

There is one JSON output record per input line. The `block` command runs the TC model and EFT with an explicit supplied D. Its arguments are `FORMAT K PADDING EALIGNMIN a0 b0 ... c D`: the FMA size, the number of padding bits, and the minimum alignment exponent, then interleaved operand pairs and decimal encoded words. `none` means no minimum alignment exponent. Decoded, the first example uses FP16 operands `0.000244140625 = 2^-12`, C = `1.0` and D = `1.0`; its exact ideal is `1 + 2^-24`, and the correctly rounded FP32 answer is `1.0`. `round` tests the exact rational numerator/denominator in RTZ and RNE. `family` executes a member of the encoded non-monotonicity family.

The `block` command expects packed 19-bit TF32 words when FORMAT is `tf32`. The separate feature command named `tf32` expects 32-bit register words with their low 13 bits zero. See the [README's executable interface](README.md#executable-interface) for the command forms.

To rerun the generated paper inputs directly after `check_tc_eft_paper.py`:

```sh
.lake/build/bin/tc_floatlib test-results/eft-paper/inputs.txt > test-results/paper-rerun.jsonl
```

This last command executes the model and writes observations. Use `check_tc_eft_paper.py` to also perform the expected-result comparisons. The same distinction applies to custom input files: producing JSON alone does not check an expected answer.

## Precisely how the executable checks work

### Execution and data flow

For the model/EFT suites, the data flow is:

```text
saved vectors or deterministic case generator
    -> Python serializes encoded operands into command lines
    -> subprocess runs .lake/build/bin/tc_floatlib INPUT_FILE
    -> Main.lean parses each nonblank line
    -> TCFloat.Model computes using FloatLib and exact arithmetic
    -> one JSON record is printed for each accepted command
    -> Python parses the records and asserts the expected comparisons
```

The harness launches the compiled Lean executable, waits for its exit status, and checks that the output has the expected number of records. Invalid JSON, a failed subprocess, an unexpected record count or a failed comparison stops the check. Rational fields are emitted as `numerator/denominator` strings and checked using Python `fractions.Fraction`, so these comparisons use exact equality, with no floating-point tolerance. Encoded FP32 outputs are compared as integers, preserving bit distinctions such as signed zero. JSON `null` represents a missing optional result.

The executable computes results using the FloatLib implementation's arithmetic definitions. Python generates cases, computes expected results and checks comparisons. Use ordinary `python3` without `-O` and without `PYTHONOPTIMIZE`, because the harnesses rely on Python assertions.

For a `block` command, [Main.lean](Main.lean) prepares the operands once, then produces two separate observations. `model` evaluates the TC block and constructs diagnostics using that computed output. `correction` runs the encoded EFT using the explicitly supplied D. The top-level `ideal` is a diagnostic exact sum. Printing that diagnostic does not make it an input to the correction algorithm. The dependency audit checks the correction functions separately.

### Exactly what each comparison checks

**Synthetic FP16 feature cases — [check_features.py](scripts/check_features.py).** The Python reference decodes operands using integer fields and exact rationals, preserves the input exponents, forms exact products in denormalized form, selects the alignment grid, truncates signed terms and adds them. It finds the toward-zero FP32 result by binary search over nonnegative finite FP32 encodings, then applies the sign. For accepted cases, the harness checks `bits`, `ideal`, `accumulated`, `value` and `residual`. For rejected synthetic cases, it checks that an `error` field exists; this particular check does not require the exact error constructor. Selected configurations with many padding bits also assert that alignment loss vanishes. Inputs include fixed boundaries and pseudorandom cases from seed `20260905`.

**Recorded hardware rows — [check_features.py](scripts/check_features.py) and [check_replay.py](scripts/check_replay.py).** Before replay, the scripts verify the vendor file hashes. Each row supplies encoded A/B operands, FP32 C and a recorded FP32 output D. FP16 operands stored in FP32 form are converted exactly to FP16 words. BF16 operands must have 16 zero low bits and are shifted into BF16 words. TF32 register operands must have 13 zero low bits; the feature adapter converts them to packed TF32. For each architecture and input format, the harness executes the model and compares its `bits` directly with recorded D. The hardware replay checks output bits; it does not claim that the intermediate diagnostics were measured on hardware. There are 5,000 rows for each of seven variants: V100/A100/H100 FP16 and A100/H100 BF16/TF32.

**Saved scalar/EFT corpus — [check_replay.py](scripts/check_replay.py).** The script reads `../data/regressions/eft-coverage-cases.json` and sends `block` commands to Lean. Its cases use no minimum alignment exponent. For ordinary records it checks TC bits, the exact scalar-guard Boolean, scalar result bits or rejection, each low component, full reference-EFT bits and the correction using supplied D. For records marked as errors it compares the model error string exactly and skips the ordinary-field checks. These records contain saved regression expectations.

**Paper oracle suite — [check_tc_eft_paper.py](scripts/check_tc_eft_paper.py).** Hash-checked generator files from `../vendor/tc-eft-validation/` are copied into an isolated scratch directory and run. The harness captures their inputs and stage values, including draws excluded from the generator's finite accepted set. It computes the expected ideal independently from the encoded inputs, obtains model expectations from the integer block oracle, and obtains FP32 rounding expectations from the oracle's neighboring-value procedure. It supplies the expected TC word as D when available, otherwise zero.

For ordinary block cases, the comparison checks the exact ideal, TC bits or the exact accumulator-out-of-range error, accumulator value, the selected largest exponent of a nonzero term and corrected bits. Where the generator supplies intermediate stages, it also checks the quantum, original terms, aligned terms, alignment residuals, low parts, output residual and overlap. The generator stores C last; the harness rotates those lists to the port's C-first order before comparing. It verifies that the scalar guard agrees with whether a scalar result exists, and that any accepted scalar result equals the expected correctly rounded answer.

The paper suite requires the `allZero` branch for all-zero terms and `outOfRange` when the exact sum lies outside the finite output domain. Otherwise it accepts either `scalar` or `exactReference`, provided the bits are correct. The pinned Python generator's scalar test can use a different grid from the Lean implementation, so `scalar_predicate_differences` records guard disagreements without treating them as incorrect numerical results. This suite checks numerical agreement with the Python oracle. The direct comparison below checks exact branch agreement with the first-principles Lean implementation.

The same script executes 49,005 encoded `family p K j` commands for `p=0..4`, `K=1..99` and `j=1..99`. It checks each exact accumulator and RTZ result against the family formula. Another 100 commands check RTZ/RNE around adjacent FP32 values, including endpoints, midpoints, signs and the subnormal/normal boundary. Endpoint and support checks inside the pinned Python generators are reported separately from the Lean executions.

**Targeted edges — [check_edges.py](scripts/check_edges.py).** Nine deliberately varied finite D words are supplied for a block whose ideal is the FP32 midpoint `1 + 2^-24`; the correction must return the even endpoint, 1, for every D. Eight exact rational inputs check signed zero, tiny values, underflow ties, finite extremes and values just outside the finite range in both rounding modes. Three domain cases check nonfinite D, a nonfinite operand and invalid TF32 register padding. The script also runs the dependency negative controls described below.

**Monotonicity boundaries — [check_monotonicity.py](scripts/check_monotonicity.py).** The script constructs encoded FP16 products with values `2^-12` and `2^(-12-p)`, varies `p=0..8`, and chooses K below, at and above `3*2^p`, plus zero/small cases. For three settings of the minimum alignment exponent and C equal to either 1 or `1-2^-24`, it checks the exact accumulator formula, selected exponent and output comparison with 1. For the lowered-C case, an output greater than 1 must occur exactly when `K >= 3*2^p`. This is a 360-case regression of the theorem's boundary behavior.

### Direct comparison of the two implementations

[check_equivalence.py](scripts/check_equivalence.py) snapshots the current parent implementation and builds its `tc_eft_reference` executable with the parent toolchain. It combines the generated paper inputs, scalar corpus and feature/hardware fixtures, then adds 2,000 deterministic random encoded blocks and 2,000 deterministic random rational-rounding commands using seed `20260923`. Feature rows are converted to the shared packed-word `block` interface, with D set to zero to exercise supplied-D independence. One malformed feature row is skipped because that shared interface rejects its shape during parsing.

Both executables receive the identical input file. `compare_outputs` uses `zip_longest` over the input and both output files, so a missing or extra record fails. It parses both JSON records and requires complete object equality. Dictionary key order and JSON whitespace do not matter; every emitted field value does, including branch labels, errors, exact rational strings and output words. The saved run matched all 115,029 command records. It also recorded identical output-file SHA-256 hashes; structural JSON equality is the comparator's acceptance rule, while the hashes preserve the observed artifacts.

Decoder checks use separate Lean programs through `lake env lean --run`, rather than the batch model executable. They compare every FP16 word (65,536), every BF16 word (65,536), every packed TF32 word (524,288), and 13,584 FP32 boundary/random samples: 668,944 rows in total. Successful decoding must agree on signed integer significand, exponent, mantissa width and exact rational value; rejected special values produce `null`. The comparison omits FloatLib's dyadic zero-sign field because `TensorCore.Decoded` represents numerical zero with a single sign. The FP32 samples and block cases are finite test sets.

### Errors, negative controls and proof checks

A rejected model input is different from a malformed command. A valid command can return an error JSON record, such as `TensorCore.ModelError.nonfiniteInput`, with a successful process exit. An invalid command shape, word width, denominator or unsupported `family` parameter makes `Main.lean` throw an IO error and exit unsuccessfully. The harness checks the expected behavior for each case.

The checks deliberately introduce mistakes to verify that the checking machinery detects them:

- The paper suite flips one bit in a model result and in an EFT result; both comparisons must fail. It also requires five malformed commands to exit unsuccessfully.
- The direct comparison creates differing one-bit output records and requires `compare_outputs` to reject them.
- The edge suite creates a definition that calls `TCFloat.evalWords`; the correction-dependency check must reject it. It creates another that calls `TensorCore.round32`; the source-independence check must reject that too.

[Audit.lean](tests/Audit.lean) checks proof and executable dependencies. It collects transitive axioms for the imported public `TCFloat` theorems and five representation-equivalence definitions, permitting only `propext`, `Classical.choice` and `Quot.sound`. It traces dependencies from four correction entry points to reject TC evaluation and ideal-sum calls, and from ten executable entry points to reject first-principles `TensorCore` dependencies. These checks inspect Lean declarations.

[check_all.py](scripts/check_all.py) checks process exit statuses, audit markers and required theorem names; scans the FloatLib sources for unfinished proofs and forbidden shortcuts; restricts parent-source imports to the equivalence folder; and aggregates reports and hashes. Only deprecation warnings from generated compatibility sources are accepted during the build. Numerical regression tests execute compiled Lean programs. Lean's kernel checks universal claims during proof elaboration; the numerical comparisons provide additional evidence on the tested inputs.

## Recorded verification

The saved successful run records:

- 270 audited proof roots, using only `propext`, `Classical.choice` and `Quot.sound`; the checks reject unfinished proofs and forbidden proof shortcuts.
- 115,029 direct command comparisons and 668,944 decoder comparisons, with zero mismatches.
- 35,000 unique recorded hardware rows, plus synthetic, EFT and monotonicity cases documented in the README. Suite counts overlap and should not be added as if all were distinct hardware experiments.
- Negative controls that reject mutated outputs and forbidden executable dependencies.

Reports identify source files and verification scripts by SHA-256. Run the commands above to generate reports for the source snapshot under review. The equivalence proof uses verified parent dependencies; differential validation builds a snapshot of the parent implementation.
