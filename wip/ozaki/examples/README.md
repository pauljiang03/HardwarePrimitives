# Examples

Each file is a standalone worked example; run it from `ozaki/` with `lake env lean <file>`. The
`example`s are checked by kernel evaluation of the same definitions the theorems use.

| File | What it shows |
| --- | --- |
| [TensorCore.lean](TensorCore.lean) | Slicing a row, the binary32 σ-trick, one slice product on a V100 block, Ozaki-I and Ozaki-II on V100, CRT reconstruction, ADP on the INT8 matrix multiplier, correct rounding (including an exact halfway case), and the main theorems. |
| [MatrixCore.lean](MatrixCore.lean) | The same on the AMD CDNA models, with correct rounding on CDNA 3 fp16. |

`TensorCore` and `MatrixCore` cannot be imported together, so each file imports one of `OzakiTC`
and `OzakiMC`.
