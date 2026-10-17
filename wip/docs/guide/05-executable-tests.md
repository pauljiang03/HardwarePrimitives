# How the executable Lean tests work

Start with the detailed [tests walkthrough](../../tests/README.md). It gives the commands, expected observations, test-module map, failure behavior, and instructions for adding a case.

Four mechanisms appear in this repository:

| Mechanism | Command / syntax | What succeeds |
| --- | --- | --- |
| Kernel witness or symbolic theorem | `example ... := by decide +kernel`, or a proof applying a universal theorem | Lean checks the proposition and proof |
| Printed calculation | `#eval ...` inside a Lean file | The calculation executes and its observation prints |
| Lean IO adapter | `lake env lean --run FILE INPUT` | `main` parses and processes the supplied batch |
| Native adapter plus independent comparator | `.lake/build/bin/tc_*` called by a Python harness | Every compared observation meets the harness's independent expectation |

A printed value alone does not assert an expected answer. The worked examples pair useful calculations with kernel-checked equalities or symbolic theorem applications. Larger comparison suites run the same Lean functions through adapters and assert exact output bits and rational diagnostics outside Lean.

```sh
lake build
lake env lean examples/GettingStarted.lean
lake env lean examples/NonMonotonicity.lean
lake env lean tests/TensorCoreTests/EFT/EFT.lean
python3 scripts/check_eft.py
```

The test import root is `tests/TensorCoreTests.lean`. Default `lake build` builds it; `lake build TensorCore` builds production only. The complete validation command, `python3 scripts/check_clean_build.py`, also checks all `examples/*.lean` and every Lean code block in the maintained documentation.

For the independent implementation:

```sh
cd floatlib-port
python3 scripts/check_all.py
lake env lean tests/RepresentationFacts.lean
python3 scripts/check_equivalence.py
```

The FloatLib test project uses its own toolchain. Its [folder guide](../../floatlib-port/FOLDER_GUIDE.md) explains the exact observation fields and source-independence audits.
