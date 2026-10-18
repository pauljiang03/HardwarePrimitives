# Hardware Primitives

Executable Lean 4 models of GPU matrix multipliers, with machine-checked
properties. The same definitions run as bit-accurate simulators and serve as
the objects of the proofs.

[Website](https://pauljiang03.github.io/HardwarePrimitives/) ·
[What is proven](https://pauljiang03.github.io/HardwarePrimitives/proofs/theorems/) ·
[Status](https://pauljiang03.github.io/HardwarePrimitives/status/)

## Hardware primitives

Each primitive has its own folder: a standalone Lake project with its library,
tests, examples, validation scripts and a second implementation on FloatLib.

| Folder | Library | Hardware | Input formats |
| --- | --- | --- | --- |
| [`tensor-core/`](tensor-core/README.md) | `TensorCore` | NVIDIA V100, A100, Ada (L40S), H100, H200, B200 | FP16, BF16, TF32; FP8 E4M3/E5M2 block FMAs on Ada, Hopper, B200; FP8 `mma.sync` on H100, H200, B200, RTX PRO 6000 |
| [`matrix-core/`](matrix-core/README.md) | `MatrixCore` | AMD CDNA 1 (MI100), CDNA 2 (MI210, MI250), CDNA 3 (MI300A, MI300X) | FP32, FP16, BF16, XF32, FP8 E4M3/E5M2 FNUZ |

The two libraries are independent: `MatrixCore` does not import `TensorCore`.
The models follow Khattak and Mikaitis, *Accurate Models of NVIDIA Tensor
Cores* ([arXiv:2512.07004](https://arxiv.org/abs/2512.07004)), and Khattak,
Mikaitis and Graziani, *Accurate Models of AMD Matrix Cores*
([arXiv:2609.14845](https://arxiv.org/abs/2609.14845)). Outputs are FP32.

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
  monotone in `c`, and MC-EFT, the matrix core counterpart of TC-EFT, recovers
  the correctly rounded sum of a block from its output.

Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Requirements

[elan](https://github.com/leanprover/elan) (each project pins its toolchain in
`lean-toolchain`) and Python 3. No GPU, CUDA or MATLAB is needed.

## Build and validate

```sh
cd tensor-core
lake build                             # TensorCore, its tests and the native adapters
python3 scripts/check_clean_build.py   # fresh build, axiom audit, examples, oracles, GPU replay

cd ../matrix-core
lake build                             # MatrixCore, the paper's test vectors, the axiom audit
python3 scripts/check.py               # clean build, examples, documentation blocks
```

Usage examples are in each folder's README. The Tensor Core models reproduce
every recorded GPU output of the *Accurate Models* toolbox bit for bit and
show no mismatch with Microsoft's MMA-Sim on 850,000 cases. The AMD model
reproduces the paper's test vectors and agrees with the authors' MATLAB models
and with MMA-Sim's CDNA 3 FP8 semantics. See [What is
tested](https://pauljiang03.github.io/HardwarePrimitives/proofs/tested/).

## Repository layout

| Path | Contents |
| --- | --- |
| [`tensor-core/`](tensor-core/README.md) | NVIDIA Tensor Cores: models, properties, TC-EFT, bitvector kernels, tests, examples, FloatLib implementation, GPU recordings |
| [`matrix-core/`](matrix-core/README.md) | AMD matrix cores: models, properties, MC-EFT, tests, examples, FloatLib implementation |
| `site/` | Website sources |
| [`wip/`](wip/README.md) | Work in progress, not part of the libraries |

## License

MIT ([LICENSE](LICENSE)). Vendored materials keep their own notices; see
[`tensor-core/README.md`](tensor-core/README.md#vendored-materials).
