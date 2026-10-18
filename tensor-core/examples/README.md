# Examples

Each file checks its own results. Run one with `lake env lean examples/NAME.lean`
after `lake build`.

| File | Contents |
| --- | --- |
| [GettingStarted.lean](GettingStarted.lean) | A block calculation, TC-EFT correction, a symbolic recovery theorem |
| [NonMonotonicity.lean](NonMonotonicity.lean) | A smaller `C` giving a larger output, and the general family theorem |
| [CanonicalInvocation.lean](CanonicalInvocation.lean) | A Hopper invocation and arbitrary-width model refinement |
| [BinaryFoundation.lean](BinaryFoundation.lean) | Signed encodings and binary rounding contracts |
| [EncodedEFT.lean](EncodedEFT.lean) | Correction of a supplied `D` and encoded correctness |
| [ScalarEFT.lean](ScalarEFT.lean) | Correction precision and any-order exact summation |
| [BoundedEFT.lean](BoundedEFT.lean) | BF16 cancellation and the bounded success contract |
| [IndependentSpecification.lean](IndependentSpecification.lean) | Model equality with the independent specification |
| [EFTCoverage.lean](EFTCoverage.lean) | Batch adapter for the scalar-coverage harness (`lake env lean --run`) |
| [InstructionGroups.lean](InstructionGroups.lean) | Batch adapter for the instruction-variant comparison (`lake env lean --run`) |

`scripts/check_clean_build.py` checks every file here.
