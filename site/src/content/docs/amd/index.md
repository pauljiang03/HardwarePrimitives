---
title: The model at a glance
description: How the AMD matrix-core model turns encoded MFMA inputs into an FP32 output word in Lean, end to end.
---

This section explains how the arithmetic of AMD matrix cores, the MFMA
instructions of the CDNA 1, CDNA 2 and CDNA 3 GPUs, is represented in Lean. It
covers the data types, every stage of `evalBlock`, the numerical features of
each architecture, and how the model is tied to an independent specification
and to the published hardware observations.

The library, Matrix-Core, follows Khattak, Mikaitis and Graziani,
*[Accurate Models of AMD Matrix Cores](https://arxiv.org/abs/2609.14845)*
(arXiv 2609.14845), and uses that paper's notation throughout. It lives in the
[`amd/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/amd)
folder as a standalone Lake project, with its own numerical foundation: it
does not depend on the Tensor Core library, and the two cannot be imported
into the same file.

## The hardware behavior being modeled

One MFMA *block FMA* computes

```text
d = a₁·b₁ + a₂·b₂ + … + a_N·b_N + c
```

where `aℓ, bℓ` are FP32, FP16, BF16, XF32 or FP8 words, `c` and `d` are
FP32 words, and the FMA size `N = N_FMA` (1, 2, 4, 8 or 16) depends on
the architecture and the input format. Longer inner products chain blocks,
each block's `d` becoming the next block's `c`. Khattak, Mikaitis and Graziani
found that the three architectures form the sum in different ways, but every
block does the following:

1. Forms each product **exactly**, without normalizing the significand.
2. Accumulates the products and `c` in one of four **configurations**:
   - **CDNA 1** (`correct_rounding`) adds them exactly;
   - **CDNA 2** (`pair_wise_sum`) converts each product to FP32 and adds
     them in a balanced tree of FP32 additions, with subnormals flushed;
   - **CDNA 3** (`global_alignment`) **aligns** the products to their
     largest exponent, **truncates** the bits below a fixed-point grid, adds
     them exactly, and adds `c` **late**, after the products;
   - **CDNA 3 FP8** (`odd_even_grouping`) does the same for the odd- and
     the even-indexed products separately before combining them.
3. **Normalizes** the accumulated value `S_acc` and **rounds it to nearest
   even** in FP32: `d = fl{S_acc}`.

| Architecture | Inputs | Configuration | `N_FMA` |
| --- | --- | --- | --- |
| CDNA 1, 2, 3 | FP32 | SFMA: `correct_rounding`, one product per step | 1 |
| CDNA 1 (MI100) | FP16 / BF16 | `correct_rounding`: exact sum, one round to nearest even | 4 / 2 |
| CDNA 2 (MI210, MI250) | FP16 / BF16 / BF16 `_1k` | `pair_wise_sum`, subnormals flushed | 4 / 2 / 4 |
| CDNA 3 (MI300A, MI300X) | FP16 / BF16 / XF32 | `global_alignment` with late `c` (Algorithm 1) | 8 / 8 / 4 |
| CDNA 3 | FP8 E4M3 / E5M2 FNUZ, any mix | `odd_even_grouping` (Algorithm 2) | 16 |

The Lean model implements these steps directly.

## How it differs from a Tensor Core

| | NVIDIA Tensor Core | AMD matrix core |
| --- | --- | --- |
| Final rounding | truncation to FP32 | round to nearest even (`fl{·}`) |
| Alignment | every term, `C` included, to the largest exponent | CDNA 3: the products to their largest exponent; `c` added late |
| Monotone in `C` / `c` | no: a smaller `C` can move the grid and raise the output | yes, on every configuration |
| Monotone in the products | no | SFMA and CDNA 1 yes; CDNA 2 and CDNA 3 no |
| Product order | — | CDNA 1 and CDNA 3 Algorithm 1 depend only on the multiset; CDNA 2 and CDNA 3 FP8 depend on positions |
| EFT correction | TC-EFT: cut-off at the alignment grid or the last bit of `D` | MC-EFT: the same algorithm; the cut-off of each generation |

Each generation's properties page ([CDNA 1](/HardwarePrimitives/amd/properties/cdna1/),
[CDNA 2](/HardwarePrimitives/amd/properties/cdna2/),
[CDNA 3](/HardwarePrimitives/amd/properties/cdna3/)) states and proves its
entries. [MC-EFT](/HardwarePrimitives/amd/properties/eft/) returns the
correctly rounded sum of a block of any generation from its output.

## The pipeline in Lean

<div class="pipeline">
  <a href="/HardwarePrimitives/amd/formats/"><span class="n">01 · prepare</span><span class="t">Decode</span><span class="d"><code>BlockInput P</code> → <code>Prepared</code></span></a>
  <a href="/HardwarePrimitives/amd/products/"><span class="n">02 · Unpacked.mul</span><span class="t">Multiply</span><span class="d">exact, denormalized</span></a>
  <a href="/HardwarePrimitives/amd/cdna1/"><span class="n">03 · CDNA 1</span><span class="t">Exact sum</span><span class="d"><code>S_acc = Σ p + c</code></span></a>
  <a href="/HardwarePrimitives/amd/cdna2/"><span class="n">03 · CDNA 2</span><span class="t">Pairwise sums</span><span class="d">FP32 tree, <code>c</code> last</span></a>
  <a href="/HardwarePrimitives/amd/cdna3/"><span class="n">03 · CDNA 3</span><span class="t">Align, late <code>c</code></span><span class="d">grid <code>2^(e_max − 24)</code></span></a>
  <a href="/HardwarePrimitives/amd/normalization/"><span class="n">04 · fl32</span><span class="t">Normalize &amp; round</span><span class="d">nearest even → <code>F32</code></span></a>
</div>

The block is defined in
[`amd/MatrixCore/MC/Eval.lean`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Eval.lean)
from the stages in
[`Stages.lean`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/Stages.lean).
These are its definitions, unchanged apart from omitted comments:

```lean
structure Model where
  a : InputFormat                 -- input format of a
  b : InputFormat                 -- input format of b (c and d are FP32)
  nfma : ℕ                        -- N_FMA, the FMA size
  accumulation : Accumulation     -- correctRounding, pairWiseSum, globalAlignment, oddEvenGrouping
  padding : ℕ := 1                -- products keep 23 + padding mantissa bits after alignment
  cZeroExp : Option ℤ := some (-126)  -- e_{c=0}, the exponent given to c = 0
  late : LateAlignment := {}      -- align(c, S_{p_i,sum}) = (24, 32, RD)
  subnormals : Bool := true       -- false on CDNA 2: subnormals flushed
  productOverflow : Bool := false -- true on CDNA 3: |p_ℓ| ≥ 2^128 overflows

structure BlockInput (P : Model) where
  a : List P.a.Word
  b : List P.b.Word
  c : F32

def Prepared.p (x : Prepared) : List Unpacked := List.zipWith Unpacked.mul x.a x.b

def accumulate (P : Model) (x : Prepared) : Except ModelError ℚ :=
  if P.productOverflow && x.productOverflows then .error .productOverflow
  else
    match P.accumulation with
    | .correctRounding => .ok x.exact
    | .pairWiseSum =>
      match pairwiseSum P x with
      | none => .error .intermediateOverflow
      | some s => .ok s
    | .globalAlignment | .oddEvenGrouping => .ok (alignedAccumulation P x)

def evalBlock {P : Model} (x : BlockInput P) : Except ModelError (BlockTrace P) :=
  if x.a.length ≠ P.nfma ∨ x.b.length ≠ P.nfma then .error .wrongLength
  else
    match prepare x with
    | none => .error .nonfiniteInput
    | some px =>
      match accumulate P px with
      | .error e => .error e
      | .ok s =>
        match fl32 (!P.subnormals) s with
        | none => .error .outputOverflow
        | some d => .ok ⟨px, s, d⟩
```

### Names used in the code

| Paper | Meaning | Lean |
| --- | --- | --- |
| `a_ℓ`, `b_ℓ`, `c` | operands of one block | `BlockInput.a`, `.b`, `.c`; decoded: `Prepared` |
| `p_ℓ = a_ℓ b_ℓ` | full-precision product in denormalized form: `s_p = s_a s_b ∈ [0, 4)`, `e_p = e_a + e_b` | `Unpacked.mul`, `Prepared.p` |
| `Σ p_ℓ + c` exactly | | `Prepared.exact` |
| `N_FMA` | FMA size: the number of products in a single multi-term addition | `Model.nfma` |
| `n_eab` | the padding bits: products keep `23 + padding` mantissa bits | `Model.padding` |
| `e_max` | largest exponent of the nonzero products | `maxExp` |
| `S_{p_i,sum}` | sum of the aligned products | `productSum`, `alignedSum` |
| `e_c` | exponent of `c` (`−126` for subnormal `c`) | `cExp` |
| `e_{c=0}` | exponent given to `c = 0` (`−126`, or `−∞`) | `Model.cZeroExp` |
| `s′_c` | `s_c` shifted right by `e_max − e_c`, rounded down to 24 mantissa bits | `shiftedC` |
| `S′_{p_i,sum}` | `S_{p_i,sum}` shifted right by `e_c − e_max`, rounded down to 32 mantissa bits | `shiftedSum` |
| `S_acc` | the accumulated value presented to the final rounding | `BlockTrace.sAcc`, `alignedAccumulation` |
| `fl{·}` | normalize and round to FP32 with round to nearest even | `rne32`, `fl32` (with flush to zero), `flValue` |
| RD | round toward `−∞` on a fixed-point grid | `rdGrid`, `rdMantissa` |
| truncation | magnitude truncation on a fixed-point grid | `truncGrid`, `truncMantissa` |
| SFMA | `(…((c + p₁) + p₂) + …)` | `sfmaF32` with `dotBits` |

Three design choices run through the model, as on the Tensor Core side:

- **Exact arithmetic everywhere.** Values are `ℤ` and `ℚ`. Bits are discarded
  only where the paper names a truncation, a round down or an `fl{·}`.
- **Bits in, bits out.** Inputs are `BitVec` words of the input formats and the
  output is an `F32 = BitVec 32`.
- **Failure is explicit.** `evalBlock` returns `Except ModelError (BlockTrace P)`,
  and [`MatrixCore.evalBlock_success_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/AcceptedDomain.lean#L36)
  gives the exact accepted domain. `blockOutcome` gives the infinity or NaN
  the hardware returns where the finite model rejects an input
  ([normalization and final rounding](/HardwarePrimitives/amd/normalization/#special-values)).

## The feature table

The paper's feature comparison table has one row per numerical feature. Each
row is a field or a derived property of `Model`:

| Row | Lean | CDNA 3 value |
| --- | --- | --- |
| Input formats | `Model.a`, `Model.b` | FP16, BF16, XF32, FP8 |
| Product alignment `(2, 24)` | `Model.productAlignment` | `(2, 24)` |
| `N_FMA` | `Model.nfma` | 8 (16 for FP8, 4 for XF32) |
| `e_{c=0}` | `Model.cZeroExp` | `−126` |
| `c` late or early | `Model.lateC` | late |
| `align(c, S_{p_i-sum})` `(24, 32, RD)` | `LateAlignment.cMantissaBits`, `.sumMantissaBits` | 24, 32 |
| Output rounding | `fl{·}` is round to nearest even on every CDNA variant | round to nearest even |
| `\|p_i\|` overflow | `Model.productOverflow` | `2^128` |

The four configurations are the constructors of `Accumulation`:

| Paper | Lean | Used by |
| --- | --- | --- |
| `correct_rounding` | `.correctRounding` | [CDNA 1](/HardwarePrimitives/amd/cdna1/), the SFMA |
| `pair_wise_sum` | `.pairWiseSum` | [CDNA 2](/HardwarePrimitives/amd/cdna2/) |
| `global_alignment` with `late_partial_sum` | `.globalAlignment` | [CDNA 3](/HardwarePrimitives/amd/cdna3/) FP16, BF16, XF32 |
| `odd_even_grouping` | `.oddEvenGrouping` | [CDNA 3](/HardwarePrimitives/amd/cdna3/#odd-and-even-groups-fp8-algorithm-2) FP8 |

`Architecture.model` maps an architecture (from a device name such as
`MI300X`) and an input kind to its model, where the architecture supports it.

## A worked trace

Here is CDNA 3 FP16 (`N_FMA = 8`, `padding = 1`) with `c = 0`, seven products
`2^-12 × 2^-12 = 2^-24`, and one product of value `2.25`, written two ways:
as `1.5 × 1.5` and as `2.25 × 1`.

| Stage | `1.5 × 1.5` (`0x3E00`, `0x3E00`) | `2.25 × 1` (`0x4080`, `0x3C00`) |
| --- | --- | --- |
| Large product | value `2.25`, `s_p = 2.25`, `e_p = 0 + 0 = 0` | value `2.25`, `s_p = 1.125`, `e_p = 1 + 0 = 1` |
| Each small product | value `2^-24`, `e_p = −24` | same |
| `e_max` | `0` | `1` |
| Grid `2^(e_max − 24)` | `2^-24` | `2^-23` |
| Each small product's bit at `2^-24` | on the grid: kept | below the grid: dropped |
| `S_acc` (`c = 0` adds nothing) | `2.25 + 7·2^-24` | `2.25` |
| `fl{S_acc}` | `2.25 + 2^-21` (`0x40100002`) | `2.25` (`0x40100000`) |

The products have the same values, but the exponent the alignment sees is the
sum of the input exponents, so the second block aligns on a coarser grid. Both
rows are checked in Lean
([`MatrixCore.cdna3F16_products_not_determined`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/amd/MatrixCore/MC/ProductMonotonicity.lean#L176)):

```lean
import MatrixCore

open MatrixCore

example :
    blockBits (P := cdna3F16)
        ⟨0x3E00 :: List.replicate 7 0x0C00, 0x3E00 :: List.replicate 7 0x0C00, 0⟩ = .ok 0x40100002 ∧
    blockBits (P := cdna3F16)
        ⟨0x4080 :: List.replicate 7 0x0C00, 0x3C00 :: List.replicate 7 0x0C00, 0⟩ = .ok 0x40100000 := by
  decide +kernel
```

## Reading on

The shared stages and each generation have their own page:

1. [Formats and decoding](/HardwarePrimitives/amd/formats/): IEEE and FNUZ classification, exponents, subnormals, XF32.
2. [Exact products in denormalized form](/HardwarePrimitives/amd/products/): why the exponent of a product is the sum of the input exponents.
3. [CDNA 1: correct rounding](/HardwarePrimitives/amd/cdna1/): the exact sum, and the SFMA of the FP32 instructions.
4. [CDNA 2: pairwise sums](/HardwarePrimitives/amd/cdna2/): flushing, product conversion and the FP32 tree.
5. [CDNA 3: global alignment](/HardwarePrimitives/amd/cdna3/): `e_max`, truncation, the FP8 groups, the late addition of `c`, fixed-width registers.
6. [Normalization and final rounding](/HardwarePrimitives/amd/normalization/): `fl{·}`, range, flushing, signed zero and special values.
7. [Instructions and chaining](/HardwarePrimitives/amd/instructions/): inner products of any length and `D = AB + C`.
8. [Independent specification](/HardwarePrimitives/amd/specification/): a second transcription of the paper, proved equal to the model.
9. [Hardware validation](/HardwarePrimitives/amd/validation/): the paper's vectors, the MATLAB models, MMA-Sim and a FloatLib implementation.

The NVIDIA Tensor Cores have a model of their own, with truncation and `C`
inside the alignment: see [the model at a glance](/HardwarePrimitives/model/).
