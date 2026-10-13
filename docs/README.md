# Guide to tensor-core arithmetic

The guide connects executable calculations to the definitions and proofs that justify them. `python3 scripts/check_docs.py` checks each Lean code block; complete worked examples live in `examples/`.

1. [Getting started](guide/01-getting-started.md): choose imports, run a calculation, and find the source.
2. [The tensor-core model](guide/02-tensor-core-model.md): follow exact products in denormalized form, alignment, accumulation, and normalization with final rounding.
3. [Non-monotonicity](guide/03-non-monotonicity.md): execute a witness and connect it to the general threshold and range theorems.
4. [TC-EFT](guide/04-eft.md): follow the overlap identity, scalar preconditions, and the two execution backends.
5. [Executable Lean tests](guide/05-executable-tests.md): run kernel witnesses, IO programs, native adapters, and independent comparisons.

Use [What is proven](../TensorCore/THEOREMS.md) to locate results and their Lean source. The [reference](reference.md) lists command formats and precise contracts.

The independent FloatLib implementation has a [folder guide](../floatlib-port/FOLDER_GUIDE.md) and a [theorem correspondence](../floatlib-port/COMPARISON.md). Its toolchain and runtime implementation are separate from the first-principles project.
