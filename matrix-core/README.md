# MatrixCore

Executable Lean 4 models of the MFMA instructions of AMD CDNA 1, CDNA 2 and
CDNA 3 GPUs, with machine-checked properties. The models follow Khattak,
Mikaitis and Graziani, *Accurate Models of AMD Matrix Cores*
([arXiv:2609.14845](https://arxiv.org/abs/2609.14845)), in the paper's
notation.

A standalone Lake project with its own numerics; it does not depend on
`TensorCore`, and the two can be imported into one file
([`cross-vendor/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/cross-vendor)). Documentation: [the AMD model at a
glance](https://pauljiang03.github.io/HardwarePrimitives/matrix-core/).

## Coverage

| Architecture | Inputs | Configuration | `N_FMA` |
| --- | --- | --- | --- |
| CDNA 1, 2, 3 | FP32 | SFMA (`correct_rounding`, one product per step) | 1 |
| CDNA 1 (MI100) | FP16 / BF16 | `correct_rounding` | 4 / 2 |
| CDNA 2 (MI210, MI250) | FP16 / BF16 / BF16 `_1k` | `pair_wise_sum` | 4 / 2 / 4 |
| CDNA 3 (MI300A, MI300X) | FP16 / BF16 / XF32 | `global_alignment` (Algorithm 1) | 8 / 8 / 4 |
| CDNA 3 | FP8 E4M3 / E5M2 FNUZ, any mix | `odd_even_grouping` (Algorithm 2) | 16 |

`c` and `d` are FP32. Inner products of any length and `D = AB + C` chain
blocks through `c`; `blockOutcome` and `dotOutcome` give the observed result
for any input words, infinities and NaN included.

## Build

```sh
cd matrix-core
lake build                    # MatrixCore, the paper's test vectors, the axiom audit
python3 scripts/check.py      # clean build, examples, documentation blocks
EXPORTER=… CHECKER=… bash scripts/conleche.sh   # re-check every declaration with con-leche
```

## Usage

```lean
import MatrixCore

open MatrixCore

def ones : BlockInput cdna1F16 := ⟨List.replicate 4 0x3C00, List.replicate 4 0x3C00, 0⟩

#eval blockBits ones

example : blockBits ones = .ok 0x40800000 := by decide +kernel
```

## Proven properties

| Generation | Proven |
| --- | --- |
| All | Equality with an independent transcription of the paper's algorithms; exact accepted domain; error bounds, also from the inputs alone; monotonicity in `c`; loss accounting for inner products and `D = AB + C`; the MC-EFT correction, which returns the correctly rounded sum of a block or an inner product from any finite output word, with its fast path from the inputs alone and a 576-bit register version |
| CDNA 1 and SFMA | Correct rounding; error at most half an ulp; monotone in every product; independent of product order |
| CDNA 2 | Non-monotone in the products only through flushing; correctly rounded when every intermediate rounding is exact; order dependent |
| CDNA 3 | Monotone in the products while the alignment exponents are unchanged; necessary and sufficient conditions for an output decrease; a family with an exact threshold; correctly rounded when alignment loses nothing; fixed-width registers of 29 to 31 bits; Algorithm 1 independent of product order; the FP8 parity law: an FP8 block depends on its slots only through the unordered pair {odd slots, even slots} |

Details per generation: [CDNA 1](https://pauljiang03.github.io/HardwarePrimitives/matrix-core/properties/cdna1/),
[CDNA 2](https://pauljiang03.github.io/HardwarePrimitives/matrix-core/properties/cdna2/),
[CDNA 3](https://pauljiang03.github.io/HardwarePrimitives/matrix-core/properties/cdna3/),
[MC-EFT](https://pauljiang03.github.io/HardwarePrimitives/matrix-core/properties/eft/).

Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Validation

- Every test vector of the paper's Section 4 is a kernel-checked regression
  reproducing the output the paper reports for the hardware
  ([paper notes](docs/paper-notes.md)).
- Differential testing against the authors' MATLAB models (600,000 random
  inner products, 20,000 targeted FP8) and MMA-Sim's CDNA 3 FP8 semantics
  (90,000), with no unexplained difference ([method and counts](docs/differential.md)).
- A second implementation on FloatLib, proven to give the same observation for
  every input ([`floatlib-port/`](floatlib-port/README.md)).

No recorded AMD hardware outputs are published; the model rests on the
paper's vectors and these comparisons.

## Layout

| Path | Contents |
| --- | --- |
| [`MatrixCore/Numerics/`](MatrixCore/Numerics.lean) | Formats, decoding, grids, FP32 rounding and its correctness |
| [`MatrixCore/MC/`](MatrixCore/MC.lean) | Models, block stages, evaluation, special values, chaining, theorems |
| [`MatrixCore/Specification/`](MatrixCore/Specification.lean) | Independent transcription of the paper and the equality proofs |
| [`MatrixCore/EFT/`](MatrixCore/EFT.lean) | The MC-EFT correction for every generation, inner products, the fast path from the inputs, and the 576-bit register version |
| [`tests/`](tests/README.md) | The paper's test vectors, regressions and the audit |
| `examples/`, `Main/` | Worked examples; `mc_eval`, which evaluates inner products from words |
| `scripts/` | Validation runner and differential tests |
| [`floatlib-port/`](floatlib-port/README.md) | Second implementation on FloatLib (separate Lake project with mathlib) |
| [`docs/`](docs/paper-notes.md) | Notes on the paper's vectors and on the differential tests |
