# CrossVendor

Single theorems that compare the NVIDIA Tensor Core model (`TensorCore`) with
the AMD Matrix Core model (`MatrixCore`). Each library keeps its own numerics.
This project imports both and proves the comparisons in one statement each.

Documentation: [Tensor Cores and Matrix Cores compared](https://pauljiang03.github.io/HardwarePrimitives/proofs/cross-vendor/).

## What is proven

| Theorem | Statement |
| --- | --- |
| `value32_eq`, `fp16_value_eq`, `bf16_value_eq` | Both libraries decode every FP32, FP16 and BF16 word to the same value, or both reject it |
| `round32_eq_rne32` | Both round every rational to nearest even to the same FP32 word, up to the largest finite magnitude |
| `corrections_agree` | For blocks with the same exact sum in the FP32 range, TC-EFT and MC-EFT return the same word |
| `fp16_ampere_cdna3`, `fp16_volta_cdna1`, `bf16_ampere_cdna3` | The same for the same operand words on A100 and CDNA 3 (FP16, BF16) and on V100 and CDNA 1 (FP16) |
| `final_rounding` | On the same FP16 words, A100 truncates and CDNA 3 rounds to nearest; both corrections return the same word |
| `accumulator_monotonicity` | Lowering `C` can raise an H100 output; on every Matrix Core configuration a larger `c` never lowers the output |
| `product_monotonicity` | Raising a product can lower the output on V100, CDNA 2 and CDNA 3, never on CDNA 1 or the SFMA |
| `product_order` | A Tensor Core block depends on its products as a multiset, as CDNA 1 and CDNA 3 Algorithm 1 do; CDNA 2 and CDNA 3 FP8 depend on positions |

Above the largest finite FP32 magnitude the libraries differ:
`TensorCore.round32` returns no word, while `MatrixCore.rne32` rounds values
below `2^128 − 2^103` down to the largest finite word.

## Build

```sh
cd cross-vendor
lake build                    # CrossVendor and the axiom audit
python3 scripts/check.py      # build, audit, documentation blocks
EXPORTER=… CHECKER=… bash scripts/conleche.sh   # re-check every declaration with con-leche
```

## Usage

`TensorCore` and `MatrixCore` scope their `ℕ`/`ℤ`/`ℚ` notation to their
namespaces, so one file can import both.

```lean
import CrossVendor

#eval (TensorCore.evalBlock CrossVendor.roundingTC).map (·.output.bits)
#eval MatrixCore.blockBits CrossVendor.roundingMC
#check @CrossVendor.corrections_agree
```
