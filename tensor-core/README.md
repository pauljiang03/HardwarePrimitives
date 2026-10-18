# TensorCore

Executable Lean 4 models of the matrix multipliers of NVIDIA Tensor Cores,
from Volta to Blackwell, with machine-checked properties. The models follow
Khattak and Mikaitis, *Accurate Models of NVIDIA Tensor Cores*
([arXiv:2512.07004](https://arxiv.org/abs/2512.07004)).

A standalone Lake project. Documentation: [the Tensor Core
model](https://pauljiang03.github.io/HardwarePrimitives/tensor-core/).

## Coverage

| Hardware | Input formats |
| --- | --- |
| NVIDIA V100, A100, Ada (L40S), H100, H200, B200 | FP16, BF16, TF32 |
| Ada, Hopper, B200 | FP8 E4M3/E5M2 block FMAs |
| H100, H200, B200, RTX PRO 6000 | FP8 `mma.sync` |

Outputs are FP32. Each model supports the formats of its hardware; V100 has
FP16 only.

## Build

```sh
cd tensor-core
lake build                    # TensorCore, its tests and the native adapters
```

## Usage

```lean
import TensorCore.TC

open TensorCore

def ones : BlockInput v100F16F32 :=
  ⟨List.replicate 4 (0x3c00, 0x3c00), 0⟩

#eval (evalBlock ones).map fun t => t.output.bits.toNat

example : ((evalBlock ones).toOption.map fun t => t.output.bits) =
    some 0x40800000 := by decide +kernel
```

Four FP16 products `1 × 1` on the V100 model give the FP32 word of `4.0`; the
`example` checks the bits in the kernel. More in [`examples/`](examples/README.md).

## Proven properties

- Equality with an independent transcription of the published model, for
  every input; error bounds; exact accepted domains.
- An exact characterization of a family of non-monotonic inputs.
- TC-EFT, which recovers the correctly rounded sum of a block FMA, with a
  576-bit exact fallback.
- A bitvector datapath proven equal to the model.

Details: [error bounds](https://pauljiang03.github.io/HardwarePrimitives/tensor-core/properties/error-bounds/),
[non-monotonicity](https://pauljiang03.github.io/HardwarePrimitives/tensor-core/properties/non-monotonicity/),
[TC-EFT](https://pauljiang03.github.io/HardwarePrimitives/tensor-core/properties/eft/).

Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Validation

```sh
python3 scripts/check_clean_build.py   # fresh build, axiom audit, examples, oracles, GPU replay
```

- The models reproduce every recorded GPU output of the *Accurate Models*
  toolbox bit for bit (35,000 rows at v0.5, 125,000 at commit 79143bd, 20,000
  at v0.1).
- No mismatch with Microsoft's MMA-Sim on 850,000 cases.
- A second implementation on FloatLib, proven to give the same observation for
  every input ([`floatlib-port/`](floatlib-port/README.md)).

## Layout

| Path | Contents |
| --- | --- |
| [`TensorCore/`](TensorCore.lean) | Models, properties, TC-EFT, bitvector kernels |
| [`tests/`](tests/README.md) | `TensorCoreTests` regression library |
| [`examples/`](examples/README.md) | Checked worked examples |
| `Main/`, `tc` | Native adapters and a command-line launcher |
| `scripts/` | Validation runners and exact-arithmetic oracles |
| `data/`, `vendor/` | Inputs, reports, and pinned GPU recordings ([sources](vendor/SOURCES.json)) |
| [`floatlib-port/`](floatlib-port/README.md) | Second implementation on FloatLib (separate Lake project with mathlib) |

## Vendored materials

Vendored materials keep their own notices, including the BSD 2-Clause license
of the *Accurate Models* toolbox data
([v0.5](vendor/matlab-tensor-core-v0.5/LICENCE),
[79143bd](vendor/matlab-tensor-core-79143bd/LICENCE),
[v0.1](vendor/matlab-tensor-core-v0.1/LICENCE)). MMA-Sim (MIT, Microsoft) is
not vendored; its cross-check uses a local checkout of the commit pinned in
[`vendor/mmasim/SOURCES.json`](vendor/mmasim/SOURCES.json).
