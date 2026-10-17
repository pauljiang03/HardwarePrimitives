# Hardware Primitives

Executable Lean 4 models of GPU matrix multipliers, with machine-checked
properties. The same definitions run as bit-accurate simulators and serve as
the objects of the proofs.

[Website](https://pauljiang03.github.io/HardwarePrimitives/) ·
[What is proven](https://pauljiang03.github.io/HardwarePrimitives/proofs/theorems/) ·
[Status](https://pauljiang03.github.io/HardwarePrimitives/status/)

## Coverage

| Library | Hardware | Input formats |
| --- | --- | --- |
| `TensorCore` | NVIDIA V100, A100, Ada (L40S), H100, H200, B200 | FP16, BF16, TF32; FP8 E4M3/E5M2 block FMAs on Ada, Hopper, B200; FP8 `mma.sync` on H100, H200, B200, RTX PRO 6000 |
| `MatrixCore` | AMD CDNA 1 (MI100), CDNA 2 (MI210, MI250), CDNA 3 (MI300A, MI300X) | FP32, FP16, BF16, XF32, FP8 E4M3/E5M2 FNUZ |

The models follow Khattak and Mikaitis, *Accurate Models of NVIDIA Tensor
Cores* ([arXiv:2512.07004](https://arxiv.org/abs/2512.07004)), and Khattak,
Mikaitis and Graziani, *Accurate Models of AMD Matrix Cores*
([arXiv:2609.14845](https://arxiv.org/abs/2609.14845)). Outputs are binary32.

## Proved properties

- **Both libraries:** equality with an independent transcription of the
  published model, for every input; error bounds; exact accepted domains; a
  second implementation on FloatLib proved equivalent.
- **Tensor Cores:** a characterization of non-monotonicity, and TC-EFT, which
  recovers the correctly rounded sum of a block FMA (with a 576-bit exact
  fallback); a bitvector datapath proved equal to the model.
- **Matrix cores, per generation:** correct rounding on CDNA 1; on CDNA 2,
  non-monotonicity in the products only through flushing; on CDNA 3, an exact
  characterization of non-monotonicity in the products (a family with an exact
  threshold, and necessary and sufficient conditions), correct rounding when
  alignment loses nothing, and fixed-width accumulation. Every generation is
  monotone in `c`.

Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Requirements

[elan](https://github.com/leanprover/elan) (each project pins its toolchain in
`lean-toolchain`) and Python 3. No GPU, CUDA or MATLAB is needed.

## Build

```sh
lake build                    # TensorCore, its tests and the native adapters
cd amd && lake build          # MatrixCore and its tests
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

## Validation

```sh
python3 scripts/check_clean_build.py   # fresh build, axiom audit, examples, oracles, GPU replay
cd amd && python3 scripts/check.py     # MatrixCore build, examples, documentation blocks
```

The Tensor Core models reproduce every recorded GPU output of the *Accurate
Models* toolbox bit for bit (35,000 rows at v0.5, 125,000 at commit 79143bd,
20,000 at v0.1) and show no mismatch with Microsoft's MMA-Sim on 850,000
cases. The AMD model reproduces the paper's
test vectors and agrees with the authors' MATLAB models and with MMA-Sim's
CDNA 3 FP8 semantics. See [What is
tested](https://pauljiang03.github.io/HardwarePrimitives/proofs/tested/).

## Repository layout

| Path | Contents |
| --- | --- |
| [`TensorCore/`](TensorCore.lean) | NVIDIA Tensor Core models, properties, TC-EFT, bitvector kernels |
| [`amd/`](amd/README.md) | AMD matrix-core library `MatrixCore` (standalone Lake project) |
| [`floatlib-port/`](floatlib-port/README.md) | Second implementation of the Tensor Core model on FloatLib |
| [`tests/`](tests/README.md) | `TensorCoreTests` regression library |
| [`examples/`](examples/README.md) | Checked worked examples |
| `Main/`, `tc` | Native adapters and a command-line launcher |
| `scripts/` | Validation runners and exact-arithmetic oracles |
| `data/`, `vendor/` | Inputs, reports, and pinned GPU recordings ([sources](vendor/SOURCES.json)) |
| `site/` | Website sources |
| [`wip/`](wip/README.md) | Work in progress, not part of the libraries |

## License

MIT ([LICENSE](LICENSE)). Vendored materials keep their own notices, including
the BSD 2-Clause license of the *Accurate Models* toolbox data
([v0.5](vendor/matlab-tensor-core-v0.5/LICENCE),
[79143bd](vendor/matlab-tensor-core-79143bd/LICENCE),
[v0.1](vendor/matlab-tensor-core-v0.1/LICENCE)). MMA-Sim (MIT, Microsoft) is
not vendored; its cross-check uses a local checkout of the commit pinned in
[`vendor/mmasim/SOURCES.json`](vendor/mmasim/SOURCES.json).
