# TCFloat

A second implementation of the FP32-output Tensor Core block model and the
reference TC-EFT algorithm, built on [FloatLib](https://github.com/lean-dojo/FloatLib)
instead of `TensorCore`'s own numerics. Its executable imports no `TensorCore`
module; a separate proof layer imports hash-checked copies of the parent
definitions and proves the two implementations equal.

- Lean 4.34.0, with its own toolchain and Lake configuration.
- FloatLib pinned to `0d91825727839f597fd06b22fdd038ea21480f0c`; the committed
  `lake-manifest.json` pins the transitive dependencies.
- The parent sources are pinned by code tokens in
  [`reference-manifest.json`](reference-manifest.json).

## Build and check

```sh
cd floatlib-port
python3 scripts/check_all.py           # prepare the pinned parent sources, build, run every check
python3 scripts/check_equivalence.py   # compare with a snapshot of the current parent sources
```

The first build needs network access to fetch Lean, FloatLib and mathlib.
`check_all.py` writes `test-results/summary.json`. For a manual build, run
`python3 scripts/prepare_reference.py`, then `lake build`.

## What is proved

`TCFloat.Equivalence.floatlib_eq_reference`: for every encoded input of the
FP16, BF16 and TF32 models and every supplied `D`, the two implementations
agree on the block output bits, the TC-EFT bits and branch, and the
validation errors. The port also proves, on its own definitions, the error
bound, the non-monotonicity threshold `3·2^p`, overlap recovery, and the
correctness of both branches of TC-EFT. Only `propext`, `Classical.choice`
and `Quot.sound` are used.

| Module | Contents |
| --- | --- |
| `TCFloat/Model.lean` | Formats, decoding, block stages, extraction, both TC-EFT branches |
| `TCFloat/Theory.lean`, `Behavior.lean`, `Monotonicity.lean` | Loss accounting, error bounds, flowback, non-monotonicity |
| `TCFloat/Rounding.lean`, `DirectedRounding.lean` | The bridge from FloatLib's rounding to the model's |
| `TCFloat/EFT.lean` | Exact prefix sums and TC-EFT correctness |
| `TCFloat/Equivalence/` | The universal equivalence with the parent implementation |
| `Main.lean` | Batch executable `tc_floatlib` |

## Tests

| Script | Checks |
| --- | --- |
| `check_features.py` | 2,033 synthetic FP16 cases and 15,000 recorded FP16 GPU rows |
| `check_replay.py` | 20,000 recorded BF16/TF32 GPU rows and 21,966 scalar-coverage records |
| `check_tc_eft_paper.py` | 52,031 cases from the TC-EFT paper's pinned generators |
| `check_edges.py` | Unrelated `D`, signed zeros, underflow ties, range endpoints, nonfinite inputs |
| `check_monotonicity.py` | Cases below, at and above the `3·2^p` threshold |

## Scope

The FP8 models of the parent are not ported. NaNs and infinities are
rejected; exception flags, tiling, scheduling and FP16 outputs are not
modeled.
