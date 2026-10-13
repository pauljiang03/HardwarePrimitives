# FP32-output tensor-core arithmetic with FloatLib

This is an independent Lean project inside `MMAlgebra`. It implements the FP32-output TC block model and the reference TC-EFT algorithm using FloatLib. Its executable runtime imports no `TensorCore` modules. A separate proof layer imports hash-checked copies of the parent definitions to prove universal equivalence. The project uses its own toolchain, Lake configuration, and build artifacts.

Start with the [folder guide](FOLDER_GUIDE.md) for the project layout, what the correctness claims mean, how transferred proofs work, and the verification commands.

The [reference manifest](reference-manifest.json) pins the parent arithmetic and proof bodies used by the equivalence layer.
FloatLib dependency: `https://github.com/lean-dojo/FloatLib`, pinned to `0d91825727839f597fd06b22fdd038ea21480f0c`.
Lean: **4.34.0**; the parent project uses its own separate toolchain. The committed `lake-manifest.json` pins transitive dependencies.

## Build and run

Install [elan](https://github.com/leanprover/elan), Git, and Python 3. A complete source ZIP or clone works; the Git history is unnecessary. Git is used by Lake to fetch pinned dependencies. No third-party Python packages, MATLAB, CUDA, or GPU are required for these checks. The first build needs network access to fetch Lean, FloatLib, mathlib, and their dependencies. Expect several GB of dependency/build storage.

From the repository root:

```sh
cd floatlib-port
python3 scripts/check_all.py
```

`check_all.py` prepares the hash-checked parent-source dependencies, then builds both the independent executable and all equivalence proofs. For a manual build, run `python3 scripts/prepare_reference.py` followed by `lake build`. The pinned manifest supplies the dependency revisions. The compatibility copy is generated under ignored `reference-compat/`; test outputs stay under ignored `test-results/`.

Individual checks:

```sh
lake env lean tests/Audit.lean
python3 scripts/check_features.py
python3 scripts/check_replay.py
python3 scripts/check_tc_eft_paper.py
python3 scripts/check_edges.py
python3 scripts/check_monotonicity.py
```

`check_all.py` builds, runs those checks, rejects unfinished proofs and forbidden proof shortcuts in the port, and writes `test-results/summary.json`. The Lean audit checks the transitive axioms of the port's public theorems; only `propext`, `Classical.choice`, and `Quot.sound` are allowed. It also checks that executable correction does not depend on TC model evaluation or the original-input ideal. A negative control deliberately violates that rule and must be rejected.

## Validation reports

Reproduce validation with `scripts/check_all.py`. Current reports and source hashes are generated under `test-results/summary.json`; the direct comparison writes `test-results/equivalence/report.json`.

`prepare_reference.py` verifies the parent dependency graph against the bundled [reference manifest](reference-manifest.json). The script checks the manifest's SHA-256, resolves modules to their manifest entries, and verifies mathematical code tokens, string literals, and imports. Comments and whitespace do not affect token verification. Parent declarations renamed since the pinned revision are recorded in [renamed-identifiers.json](renamed-identifiers.json) as exact token positions; restoring them must reproduce the pinned hash, so the check still proves the parent code changed only by those renames. After renaming parent declarations, regenerate the record with `python3 scripts/record_renames.py`. After a reviewed change to the parent's behavior, move the pin with `python3 scripts/pin_reference.py REVISION`, which rewrites the manifest from that revision and clears the rename record. It copies the verified parent sources into `reference-compat/` and records their hashes and dependency metadata in the generated manifest. Edge checks exercise source archives and reject mutations of protected code, imports, manifests, and dependencies.

## Equivalence with the first-principles implementation

[COMPARISON.md](COMPARISON.md) maps the definitions and paper statements to their Lean theorems. **`TCFloat.Equivalence.floatlib_eq_reference` is a universal Lean theorem**: the two encoded interfaces agree on TC bits, EFT bits and branches, and validation errors for every encoded input of the paper's FP16/BF16/TF32 models and every supplied D. `inputEquiv` and `floatlib_eq_reference_inverse` supply the two-way input correspondence. `round32_eq` proves converter equality for every rational input in toward-zero (RTZ) and nearest-even (RNE) modes.

The theorem concerns checked encoded inputs and consistent/canonical numerical representations; it does not identify arbitrary unchecked `Term` or `Trace` records. See the comparison for the precise scope and inverse laws. Direct differential tests additionally compare command observations and exhaustive FP16/BF16/TF32 decoder cases against a snapshot of the current parent sources. Reproduce with `python3 scripts/check_equivalence.py` after `check_all.py`.

## What FloatLib supplies

* `FloatFormat.binary16`, `bfloat16`, `tf32`, and `binary32` describe the actual encodings.
* `Model.toDyadic?` rejects nonfinite values and decodes finite words exactly.
* `Numerics.Dyadic.mul` forms exact products, with its rational-semantics theorem used in the proof.
* `Model.roundRatWithRounding` implements FP32 truncation (FloatLib's IEEE round-toward-zero mode) and nearest-even rounding. Every scalar addition uses FloatLib nearest-even rounding and FloatLib decoding.
* FloatLib's real-valued `roundAt` and format-grid theorems prove that the executable EFT result has mathematical nearest-even semantics, including ties. This is a proof connection, not only an output comparison with a second program.

This project defines TC-specific alignment, extraction, scalar conditions, and flowback using FloatLib's numerical operations.

## Model and numerical scope

A block contains K exact products and an FP32 accumulator input C. Each dyadic value is an integer times a power of two; the model tracks input exponents separately from that value. A product is kept in denormalized form: its exponent is the sum of its input scales, even if the product value could be normalized differently. Zero inputs use neutral metadata `(scale, mantissaBits) = (0, 0)`; zero terms do not select the alignment maximum.

The largest exponent of a nonzero term, raised to the minimum alignment exponent where the architecture has one, selects the alignment quantum `2^(eta - 23 - neab)`, where `neab` is the number of extra alignment bits. Each term's magnitude is truncated on that grid, keeping its sign; the retained terms are added exactly; the accumulator is then truncated to FP32. This port implements that final truncation with FloatLib's IEEE round-toward-zero mode, which on the parent's finite domain gives the same bits (`round32_eq`). There is no integer accumulator wraparound. Inputs and the accumulated result must satisfy the parent's finite-domain rules. In particular, `|accumulator| > maxFinite32` is rejected before rounding, even though native IEEE toward-zero overflow would saturate.

The named FP16 models, written as (FMA size, extra alignment bits, minimum alignment exponent), are V100 `(4, 0, none)`, A100 `(8, 1, -132)`, and H100 `(16, 2, -133)`. The same constructor supports BF16 and packed 19-bit TF32. Tests also cover A100 TF32 with K=4, H100 WMMA TF32 with K=4, and the paper's H100 MMA TF32 with K=8. Arbitrary FMA sizes, numbers of extra alignment bits, and minimum alignment exponents can be evaluated.

The feature-test interface accepts TF32 in 32-bit registers and requires the low 13 bits to be zero. The EFT `block` interface accepts **packed 19-bit TF32**. These are different representations, not an implicit input-rounding operation.

Exact zero is canonicalized to +0, as in the parent reference; negative underflow can produce -0. NaNs and infinities are rejected. This project does not model exception flags, instruction scheduling, matrix tiling, undocumented hardware variants, or FP16 outputs.

## EFT and proofs

The extraction grid is the coarser of the alignment grid and supplied D's FP32 grid. Each input term splits into a retained part and a low part. The overlap is `D - sum(retained parts)`. Consequently, `D - overlap + sum(low parts)` recovers the exact input sum. The proof works for **any supplied finite D**, even one unrelated to the TC model output.

The scalar guard checks that the low bits of all terms fit together within 24 bits, counted from the lowest bit actually set (zeros ignored); that this lowest bit lies between `2^-149` and `2^104`; that D, the overlap and the retained sum each fit in FP32's 24 significant bits; and that the reconstructed sum is within finite FP32 range. This is the same rule as the TC-EFT paper's generator and the parent's 576-bit implementation. The equivalence theorem proves that both implementations make the same branch decisions. Separate paper theorems cover the chosen-grid coefficient and absolute-range conditions.

The guarded scalar branch sequentially adds the low parts in FP32, computes `D - overlap` in FP32, then performs the final FP32 addition. `naiveSumFrom_exact` proves every accepted prefix sum is exact. `scalar_correct` proves the result equals FloatLib nearest-even rounding of the exact input sum. `scalar_success_iff` proves this branch succeeds exactly when its guard holds.

When the scalar guard fails, Algorithm 1 consolidates the components using exact rational arithmetic and one FloatLib rounding. This implements the reference algorithm's fallback. The bounded 576-bit backend has its own refinement proofs in the parent project. `algorithm_correct` proves both reference branches return the correctly rounded exact sum; `algorithm_range` characterizes success by the finite FP32 range. `encodedAlgorithm_correct` includes the all-zero shortcut. `encodedAlgorithm_nearest` connects the returned word to mathematical nearest-even rounding over the reals.

| File | Main contents |
|---|---|
| `TCFloat/Model.lean` | Executable formats, decode, TC stages, extraction, scalar guard and both EFT branches |
| `TCFloat/Theory.lean` | Product denotation, exact loss accounting, overlap recovery, signed-truncation error and monotonicity |
| `TCFloat/Rounding.lean` | FloatLib executable-to-real rounding bridge and FP32 grid representability |
| `TCFloat/EFT.lean` | Prefix-sum exactness, scalar correctness, full Algorithm 1 correctness and range |
| `TCFloat/Behavior.lean` | C-perturbation flowback identity, exact internal-increase criterion, fixed-grid monotonicity, alignment error bounds, kernel-checked nonmonotonic outputs for V100/A100/H100 |
| `TCFloat/DirectedRounding.lean` | Proved connection from FloatLib RTZ rounding to signed-grid truncation for positive normal binary intervals |
| `TCFloat/Monotonicity.lean` | General K/p non-monotonicity threshold, actual encoded FP16 version, and formal failure of accumulator monotonicity |
| `Main.lean` | Batch executable adapter |

**Paper theorem coverage:** the bridge layer proves the full output-ULP error bound, arbitrary-summand output-level flowback criteria, the general K/p/j non-monotonicity range, overlap identities, any-order exact summation, the input bit-span/coefficient preconditions, and exact scalar correction on an arbitrary valid common grid. [COMPARISON.md](COMPARISON.md) gives the theorem-by-theorem correspondence. These proofs use actual FloatLib operations; some transport first-principles results through the proved equivalence. They do not establish universal GPU conformance.

| File | Purpose |
|---|---|
| `TCFloat/Interface.lean` | Independent encoded interfaces, including typed validation results |
| `TCFloat/Equivalence/RoundingStage.lean` | Universal RTZ/RNE rounding bit equality |
| `TCFloat/Equivalence/Encoded.lean` | Universal TC/EFT encoded-interface equivalence |
| `TCFloat/Equivalence/Representations.lean` | Two-way input/result mappings and exact-error equivalence |
| `TCFloat/Equivalence/PortedTheorems.lean` | Error, flowback, perturbation-range and overlap statements |
| `TCFloat/Equivalence/ScalarCorrection.lean` | Paper scalar-summation and chosen-grid conditions |

## What the tests do

1. **`check_features.py`:** 2,033 synthetic FP16 model cases plus 15,000 recorded FP16 GPU vectors. It checks output bits, exact ideal, accumulator, output value, and total residual. Synthetic cases include arbitrary FMA sizes, numbers of extra alignment bits, minimum alignment exponents, cancellation, zeros, subnormals, overflow, and nonfinite inputs. The independent Python oracle uses exact rational arithmetic and binary search over FP32 encodings.
2. **`check_replay.py`:** 20,000 recorded BF16/TF32 GPU rows (5,000 per A100/H100 format pair). It also replays 21,966 saved scalar-coverage records, checking model bits, low parts, the exact guard decision, scalar bits, and full-EFT bits. Two records are nonfinite-input rejections. The source coverage suite deliberately uses no minimum alignment exponent; the hardware replay uses each architecture's minimum alignment exponent.
3. **`check_tc_eft_paper.py`:** runs the hash-pinned Python generators in an isolated scratch directory. It sends 52,031 cases to the compiled FloatLib executable: 59 named blocks, 800 deterministic blocks, 1,600 full-range blocks, retained out-of-domain draws, 8 boundary/composition blocks, 49,005 encoded perturbation-family cases, and 100 rounding cases. It compares intermediate extraction values as well as final bits. Mutating model/correction bits must make the comparator fail; malformed commands must be rejected.
4. **`check_edges.py`:** unrelated finite supplied D values, signed zeros, underflow ties, finite endpoints and rejection beyond them, nonfinite D, nonfinite operands, invalid TF32 padding, and a negative executable-dependency control.

5. **`check_monotonicity.py`:** boundary cases immediately below, at, and above the proven `3·2^p` threshold, as well as zero/small K, p=0 through 8, and three configurations of the minimum alignment exponent. Both alignment-grid selection and accumulator formulas are checked, together with the final FP32 output inequality. The universal theorem is established by Lean, not by this finite enumeration.

The feature and paper suites use exact-arithmetic oracles and deterministic case generation. The 21,966-record scalar corpus contains saved regression expectations. Counts across suites overlap: in particular, scalar coverage includes the same 15,000 FP16 hardware rows. There are **35,000 unique recorded hardware rows** across the suites.

### Where the MATLAB data fits

Recorded inputs and GPU outputs live in the parent's `vendor/matlab-tensor-core-v0.5/model_validation/`. Each row is one block FMA as defined by the source. FP16/BF16/TF32 operands in those files are stored using FP32 word representations; the harness converts them to the corresponding input encoding without numerical rounding. The c/d files contain binary FP32 words. Vendor hashes are checked before replay.

The tests run entirely in software and compare outputs with the recorded GPU measurements. Their hardware evidence covers the recorded inputs. H100 TF32 K=8 is covered by the paper's software cases; the bundled hardware corpus does not include that variant.

## Executable interface

Write commands to a text file, one per line, and run:

```sh
.lake/build/bin/tc_floatlib input.txt
```

Examples (the executable requires decimal bit encodings):

```text
block fp16 1 0 none 3072 3072 1065353216 1065353216
round 16777217 16777216
family 0 4 1
canonical 1 0 none 15360 15360 0
```

Decoded as floating-point values, the `block` example uses A = B = `0.000244140625 = 2^-12` and C = D = `1.0`. Its exact sum is `1 + 2^-24`, and its corrected FP32 result is `1.0`. The `round` example rounds the same exact sum to `1.0` in both RNE and RTZ. The `canonical` example uses A = B = `1.0` and C = `0.0`.

`block FORMAT K NEAB EALIGNMIN a0 b0 ... c D` returns the independent ideal, model-stage diagnostics, and correction using supplied D. FORMAT is `fp16`, `bf16`, or packed `tf32`; NEAB is the number of extra alignment bits, and EALIGNMIN, the minimum alignment exponent, is an integer or `none`. `round N D` compares FloatLib RNE/RTZ on the exact rational N/D under the source finite-range restriction. `family p K j` evaluates the encoded FP16 perturbation family. `canonical`/`bf16`/`tf32` feature commands omit supplied D; feature `tf32` uses register words.

The reference algorithms use arbitrary-precision exact arithmetic plus specified FP32 roundings. This is an executable formal model, not a native GPU implementation or a performance benchmark.
