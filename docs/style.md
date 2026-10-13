# Style and foundations

Source modules are grouped by mathematical role, with small public import modules,
explicit hypotheses, and properties beside the definitions they concern. The numerical
foundation uses Lean's standard-library arithmetic. Regression modules have a separate
source root under `tests/`.

- Put reusable arithmetic, representations, encoding, rounding, and inverse laws in `Numerics`.
- Put tensor-core assumptions in explicit `Model` or `InvocationSpec` fields and theorem premises.
- Put extraction and consolidation in `EFT`. Keep TC model properties and non-monotonicity in `TC`.
- Define representations before their operations. Keep a definition and its elementary properties together;
  split substantial correctness, bijection, and round-trip developments into named files.
- Use `ℕ`, `ℤ`, and `ℚ` for mathematical types, with `Nat`, `Int`, and `Rat` in qualified library names.
  The notation in `Numerics/Notation.lean` introduces syntax only. Use `BitVec` for encoded words.
- Use a short module introduction and declaration comments that explain a definition, its hypotheses,
  or its relationship to a numbered paper result. Explain proof steps when they add mathematical context.
- Use two-space indentation and descriptive theorem names within the relevant subject namespace.
  Import the module that owns a result, without obtaining basic lemmas through unrelated applications.
- Keep regression witnesses out of subject aggregate imports. `TensorCoreTests` and the default Lake build
  include all maintained regression modules; `scripts/check_layout.py` enforces their boundaries and audit coverage.

## Trusted foundation

The project introduces no additional arithmetic postulates. Its basic types and
operations come from Lean's standard library; correctness results are proved in Lean.
The axiom audit permits only `propext`, `Classical.choice`, and `Quot.sound` and checks
every compiled public theorem in the full development. Foundational definitions and
building blocks belong to `Numerics`; application assumptions are explicit arguments,
not global axioms. See [`axioms.txt`](axioms.txt) for the generated dependency audit.

The independent TC specification uses separate mathematical definitions.
They share standard-library arithmetic and the notation syntax, but their compiled
mathematical dependencies cannot use implementation declarations. The specification
audit checks this boundary, including dependencies inside propositions and proofs.

## Documentation

Keep the guide, executable-test walkthrough, and results summary (`TensorCore/THEOREMS.md`) current. Link directly
to Lean declarations instead of copying complete proof bodies into Markdown.
Write maintained documentation and source comments as a self-contained description of
this repository. State definitions, hypotheses, interfaces, and verification scope directly.
Describe numerical inputs and results with decoded floating-point values in prose and
output summaries. Use exact powers of two or full decimal values when the distinction
matters. Encoded literals in runnable commands and bitwise proof assertions should have
their decoded values explained nearby.

Run `python3 scripts/check_docs.py` to check maintained local links and elaborate every
Lean code block in the README, guide, test walkthrough, and results summary. Keep those
blocks standalone so a reader can copy one into a file and check it directly.
