# Tests

`TensorCoreTests` is the regression library of `TensorCore`: kernel-checked
witnesses, negative controls and trust audits. [`TensorCoreTests.lean`](TensorCoreTests.lean)
imports every module, so the axiom audit sees the whole environment.

```sh
lake build TensorCoreTests
```

| Directory | Contents |
| --- | --- |
| [`TensorCoreTests/TC/`](TensorCoreTests/TC) | Model regressions, non-monotonicity witnesses, chains, FP8 `mma.sync` corrections |
| [`TensorCoreTests/EFT/`](TensorCoreTests/EFT) | TC-EFT regressions and bounded-execution checks |
| [`TensorCoreTests/Specification/`](TensorCoreTests/Specification) | Independent-specification audit and negative controls |

## Checks

Run from `tensor-core/` with plain `python3`; the scripts refuse to run
under `-O`.

| Script | Checks |
| --- | --- |
| `scripts/check_clean_build.py` | Everything below, on a fresh copy with no build cache |
| `scripts/check_axioms.py` | Axioms of every public theorem; proof shortcuts in the sources |
| `scripts/validate.py`, `check_features.py` | Model traces and rounding against exact-arithmetic oracles |
| `scripts/check_device.py`, `check_device_formats.py`, `check_device_replay.py` | Replay of the recorded GPU outputs in `vendor/` |
| `scripts/check_eft.py`, `check_lean_eft.py` | TC-EFT coverage, instruction variants, bounded EFT, native folds |
| `scripts/check_independent_spec.py` | The independent specification and its independence controls |
| `scripts/check_docs.py`, `check_layout.py` | Documentation links and Lean blocks; module layering |
| `scripts/check_mmasim.py` | Cross-check against MMA-Sim (needs a local checkout and `torch`) |

Reports go to `data/regressions/`.

## Adding a regression

Put the case in `TensorCoreTests/TC/` or `EFT/`, name its assertion in the
`TensorCore.Regression` namespace, and import the module from
`TensorCoreTests.lean`:

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

The layout check rejects a module that the regression root does not import.
