# MCFloat

A second implementation of the `MatrixCore` model, written against
[FloatLib](https://github.com/lean-dojo/FloatLib) instead of `MatrixCore`'s own
numerics, for every variant of CDNA 1, 2 and 3. Lean proves that it gives the
same observed result as `MatrixCore` for every input.

A separate Lake project (Lean 4.34.0, FloatLib `0d91825`, which brings in
mathlib), so `MatrixCore` itself stays free of mathlib.

## Build and check

```sh
cd matrix-core/floatlib-port
python3 scripts/check.py        # pin check, build, proofs, audit, comparison with mc_eval
echo "cdna1F16 3c00,3c00,3c00,3c00 3c00,3c00,3c00,3c00 0" | .lake/build/bin/mc_floatlib
```

`mc_floatlib` reads the same lines as `mc_eval` (`<model> <a> <b> <c>`, words
in hexadecimal) and prints `F <word>`, `I+`, `I-` or `N`; the example prints
`F 40800000`. `lake build` first needs `reference-compat/`, which
`scripts/prepare_reference.py` creates from the sources pinned in
[`reference-manifest.json`](reference-manifest.json). A change to
`MatrixCore`'s code fails the pin check until it is pinned again with `--pin`.

## What is proven

| Statement | Lean |
| --- | --- |
| One block gives the same observation (finite word, `±∞`, NaN) as `blockOutcome` | `block_agree` |
| An inner product of any length gives the same observation as `dotOutcome` | `dot_agree` |
| FloatLib's FP32 rounding agrees with `rne32` and `fl32` on every rational | `round32_bits`, `fl_bits` |
| FloatLib's classification agrees with `MatrixCore`'s decoder on every word of every format | `fp32_agree`, …, `operand_xf32` |
| The per-model contracts, error bounds and monotonicity results hold for the FloatLib implementation | `floatlib_contract`, `floatlib_c_monotone`, `floatlib_nonmonotone`, … |

The audit ([`tests/Audit.lean`](tests/Audit.lean)) checks that every theorem
uses only `propext`, `Classical.choice` and `Quot.sound`, and that the
executable reaches no `MatrixCore` declaration, with a negative control.
`scripts/compare.py` also compares the compiled `mc_floatlib` with `mc_eval`
on random inner products for all twelve models.

## Layout

| Path | Contents |
| --- | --- |
| `MCFloat/Model.lean` | The FloatLib implementation |
| `MCFloat/Equivalence/`, `MCFloat/Equivalence.lean` | The equivalence proofs |
| `MCFloat/Contracts.lean` | Contracts and chaining for the FloatLib implementation |
| `Main.lean` | The executable `mc_floatlib` |
| `tests/`, `scripts/` | Audit, examples, reference preparation and comparison |
