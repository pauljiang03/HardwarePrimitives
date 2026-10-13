# Paper-scope equivalence: first-principles and FloatLib implementations

**Kernel-checked universal equivalence** connects the first-principles and FloatLib implementations of the FP32-output TC model and reference EFT, including output bits, EFT branch choices, and distinct validation errors.

The scope is the FP16, BF16 and packed TF32 inputs in the paper, FP32 output, and models that keep `F = 23 + p` fractional bits after alignment, where `p`, the number of extra alignment bits, is any natural number. The FMA size and the minimum alignment exponent are parameters. Other repository applications and backends are not part of this comparison.

## Main theorem and the two-way correspondence

See [`floatlib_eq_reference`](TCFloat/Equivalence/Representations.lean) and `floatlib_eq_reference_inverse`. For every model in that scope, every encoded block, and every supplied FP32 word D:

- The FloatLib TC interface returns the same output word or the same validation error as `TensorCore.evalBlock`.
- The FloatLib EFT interface returns the same branch and word, or the same validation error, as `TensorCore.tcEftEncoded`.
- D need not be the model's output. Invalid product counts and nonfinite operands/D are included in the comparison.

The statement uses the independent `Interface.tcChecked` and `Interface.eftChecked` functions. The `universal_equivalence` theorem in [`Encoded.lean`](TCFloat/Equivalence/Encoded.lean) proves the same numerical/branch behavior for the Option interfaces, which represent validation errors as `none`. The checked theorem also preserves the error constructors.

The correspondence includes explicit representation proofs:

| Representation | Proved correspondence |
|---|---|
| Encoded words | `wordEquiv`: `BitVec w ≃ Fin (2^w)`, preserving every bit |
| Complete encoded blocks | `inputEquiv`, with both inverse laws; includes arbitrary product-list lengths |
| Decoded numerical terms | `termEquiv`: `TensorCore.Decoded` is equivalent to canonical, metadata-consistent FloatLib terms |
| Validation errors | `errorEquiv`: all four constructors correspond |
| Tagged EFT outcomes | `eftResultEquiv`: a bijection onto legitimate `(optional bits, branch)` outcomes; `encodedResult_injective` proves no two source outcomes are merged |

This does not identify unrestricted unchecked implementation types. An unchecked FloatLib-side `Term` can contain inconsistent metadata, and an unchecked `Trace` can contain inconsistent bits/value fields. The encoded constructors establish the required invariants. The term equivalence canonicalizes zero sign, matching the source's numerical representation; the word equivalence retains signed-zero bits. [RepresentationFacts.lean](tests/RepresentationFacts.lean) checks these distinctions.

## Every arithmetic stage is connected

The following equalities are proved under the stated representation invariants. RTZ denotes FloatLib's IEEE round-toward-zero mode, which this port uses to implement the parent's final truncation; on the parent's finite domain the two give the same bits. RNE denotes rounding to nearest with ties to even.

| Stage | Bridge theorem(s) |
|---|---|
| Format fields, finite decoding and metadata | `decode_project`, `decode_value`, `value32_eq` |
| Exact multiplication and original-input sum | `denormalizedTerm_mul`, `mul_valid`, `terms_eq`, `ideal_eq` |
| Largest exponent of the nonzero terms, minimum alignment exponent and alignment grid | `alignment_eq`, `eta_eq`, `q_eq` |
| Signed truncation, retained accumulator and alignment residuals | `truncCoeff_eq`, `truncGrid_eq`, `accumulator_eq`, `residuals_eq` |
| Actual RTZ/RNE rounding, including ties, subnormals, signed underflow and finite-range rejection | `round32_eq` for **every rational input** and both modes |
| FP32 representability, addition and sequential summation | `representable_eq`, `add_eq`, `naiveSum_eq` |
| Extraction grid, coarse/low parts, retained sum and overlap | `extraction_eq`, `coarse_eq`, `lows_eq`, `retained_eq`, `overlap_eq` |
| Lowest-set-bit grid, low bits and exact executable guard | `lowestBitExp_eq`, `support_eq`, `lowCoefficients_eq`, `guard_eq` |
| Scalar correction, exact fallback, branch and zero shortcut | `scalarUnchecked_eq`, `scalar_eq`, `consolidation_eq`, `algorithm_eq`, `encoded_trace_eq` |
| Encoded preparation and full entry points | `prepare_eq`, `prepare_valid`, `tc_checked_eq`, `eft_checked_eq` |

Files are under [`TCFloat/Equivalence/`](TCFloat/Equivalence/). The rounding bridge proves equality between the first-principles rational converter and FloatLib's quotient and packing operations.

## Correspondence to the paper's FP32 statements

The table follows the manuscript's section and theorem numbering. Port identifiers containing `inputGrid` concern the paper's input-based precondition (17), as do the parent's theorems that begin with `inputGrid_`.

| Paper statement | FloatLib-side theorem(s) |
|---|---|
| II-B: block behavior model | `floatlib_eq_reference`, plus the individual stage equalities above |
| III.1: total output error bound | `floatlib_error_bound`, including the final FP32 output quantum |
| III.2–III.3: monotonicity and flowback | `truncGrid_mono`, `floatlib_output_increase_iff`, `general_flowback_necessary`, `general_flowback_sufficient` |
| III.4: hardware non-monotonicity family | `nonmonotone_perturbation`, `nonmonotone_encoded`, `construction_not_monotone` |
| III.5: general perturbation range and size | `floatlib_nonmonotone_range` for arbitrary admissible K, p and j |
| IV.1: extraction identity and low-component bound | `retained_add_low`, `floatlib_lowPart_bound` |
| IV.2: overlap width | `floatlib_overlap_width` |
| IV.3–IV.4: overlapping bits and signed correction | `floatlib_accumulator_eq_retained`, `floatlib_overlap_eq_retained_sub_outputResidual` |
| IV.5: exact recovery for any finite supplied D | `overlap_recovery` |
| IV.6–IV.7: sequential FP32 addition and exact representable sums | `naiveSumFrom`, `representable_add_exact`, `grid_representable` |
| IV.8: coefficient bound, any order, and bit-span condition (16) | `floatlib_naiveSum_exact`, `floatlib_naiveSum_any_order`, `floatlib_bitSpan_exact` |
| IV.9: common input grid and input-based condition (17) | `floatlib_lowParts_on_grid`, `floatlib_inputGrid_coefficient_bound`, `floatlib_scalar_correct_of_inputGrid` |
| IV.10: exact FP32 overlap subtraction | `floatlib_overlap_subtraction_exact` |
| IV.11: scalar correction and one final RNE rounding | `floatlib_scalar_correct_on_grid`, `scalar_correct`, `encodedAlgorithm_nearest` |
| Reference full EFT, including the exact alternative described in IV-B | `algorithm_correct`, `algorithm_range`, `floatlib_eq_reference` |

The flowback criteria cover an **arbitrary chosen summand** and the rounded outputs before and after its perturbation. The two alignment grids are parameters and may differ. The sufficient condition includes representability assumptions. C-specialized criteria are proved in [Behavior.lean](TCFloat/Behavior.lean).

The paper scalar theorems justify the instruction sequence under chosen-grid, coefficient-bound and absolute-range conditions. The executable guard uses the lowest bit actually set in the low parts as its common grid, with the restriction `-149 ≤ λ ≤ 104`, matching the TC-EFT paper's generator. The manuscript allows choosing a suitable common grid and states sufficient conditions without prescribing a unique grid-search algorithm. The equivalence theorem proves equality of executable branch decisions; the chosen-grid theorems establish the paper's mathematical conditions. Failure of the executable guard does not assert that scalar summation is impossible.

Some bridge proofs transport first-principles theorems through proved equalities. The FloatLib executable and its recovery, scalar-correction, and rounding proofs are defined in separate modules.

## Reproducible proof boundary

The [reference manifest](reference-manifest.json) pins the parent arithmetic and proof dependencies. FloatLib is pinned to `0d91825727839f597fd06b22fdd038ea21480f0c`.

The parent project uses Lean 4.33.1; the FloatLib project uses Lean 4.34.0. `scripts/prepare_reference.py` checks the reference manifest's SHA-256 and verifies parent dependencies against its code-token, string-literal, and import entries. Module names are resolved through the compatibility map; comments and whitespace do not affect token verification. The verified parent modules are copied into ignored `reference-compat/`. Its Nat, Int and Rat notation is scoped to `TensorCore` with the same expansions to avoid mathlib parser collisions. The generated manifest records source hashes and dependency metadata. Preparation works from a complete source archive.

The equivalence modules import verified parent definitions. `Main.lean`, `TCFloat/Model.lean` and `TCFloat/Interface.lean` execute the FloatLib implementation. A dependency audit checks runtime independence from the parent functions and verifies that EFT correction does not call TC evaluation or the function that computes the exact input sum. Negative controls require rejection when forbidden dependencies are deliberately introduced.

From the repository root:

```sh
cd floatlib-port
python3 scripts/check_all.py
python3 scripts/check_equivalence.py
```

The first command prepares the compatibility copy, builds all proofs and the executable, audits allowed axioms, checks representations, and runs the regression suites. It rejects unfinished proofs and kernel-bypassing proof shortcuts. The only permitted axioms are `propext`, `Classical.choice` and `Quot.sound`. Only deprecation warnings from generated compatibility sources are accepted; warnings from `TCFloat` sources fail the check.

The second command builds a snapshot of the parent executable with its own toolchain and compares 115,029 command observations and 668,944 decoder cases. Those finite comparisons supplement the universal proof. Hardware comparisons replay recorded GPU rows. Equivalence proves the two formal implementations agree; hardware correspondence is supported by measurements on those recorded inputs.

The generated manifests identify the parent source snapshots used by the equivalence proofs and differential tests with SHA-256 hashes.
