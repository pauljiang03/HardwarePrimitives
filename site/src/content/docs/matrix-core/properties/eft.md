---
title: MC-EFT correction
description: MC-EFT, the error-free transformation for AMD Matrix Cores - the correctly rounded sum of a CDNA 1, 2 or 3 block or inner product from its output, the fast path from the inputs alone, and the 576-bit register version.
---

MC-EFT is the error-free transformation for AMD Matrix Cores. It carries the
algorithm of [TC-EFT](/HardwarePrimitives/tensor-core/properties/eft/), which corrects a
Tensor Core block with the bits the hardware dropped, over to CDNA 1, 2 and 3.
It takes the encoded inputs of one block and a finite
FP32 word `D`, normally the Matrix Core's output, and returns the exact sum
`S = c + Σ a_ℓ b_ℓ` rounded to the nearest FP32 value (ties to even). It also
corrects [inner products of any length](#inner-products-of-any-length), and it
runs entirely [in a 576-bit register](#in-a-576-bit-register).

## Does it work?

**Yes, on every CDNA model.** Lean proves that whenever the correction returns
a word, that word is the exact sum `S` correctly rounded to FP32. It returns a
word exactly when `|S| < 2^128 − 2^103`, that is, when the rounded sum is a
finite FP32 number. This holds for **any** finite `D`. `D` only decides which
of two routes produces the answer.

```lean
def mcEft {P : Model} (x : BlockInput P) (D : F32) : Except EftError EftResult

theorem mcEft_correct (h : mcEft x D = .ok r) (hb : r.bits = some b) :
    ∃ px, prepare x = some px ∧ RoundsNearestEven32 px.exact b
theorem mcEft_isSome_iff (h : mcEft x D = .ok r) (hp : prepare x = some px) :
    r.bits.isSome = true ↔ absQ px.exact < overflowThreshold32
```

([`MatrixCore.mcEft`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Encoded.lean#L64),
[`MatrixCore.mcEft_correct`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Encoded.lean#L108),
[`MatrixCore.mcEft_isSome_iff`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Encoded.lean#L115).)
The result is `.fast b` (the FP32 path), `.exact b` (the exact fallback) or
`.outOfRange`. An infinity or NaN among the inputs or in `D`, or vectors of the
wrong length, give an error instead.

## The algorithm

1. **Pick a cut-off bit `2^q`** (next section).
2. **Split every term at the cut-off** into a high part, a multiple of `2^q`,
   and a low part below it. Products are split by truncating the magnitude, as
   alignment does. On CDNA 3, `c` is split by rounding down wherever the matrix
   core rounds it down.
3. **Sum the high parts** to get `H`. The overlap is `εₒ = D − H`.
4. **Add the low parts back:** `S = D − εₒ + Σ low parts`, and round once to
   FP32
   ([`MatrixCore.EftSplit.recovery`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Core.lean#L139)).

## The cut-off of each generation

| Generation | Cut-off `2^q` | Why |
| --- | --- | --- |
| CDNA 1 and the SFMA | the last bit of `D` | the output is already correctly rounded |
| CDNA 2 | the last bit of `D` | there is no alignment grid: each `fl{·}` rounds at its own result |
| CDNA 3 (FP16, BF16, XF32, FP8) | the higher of the last bit of `D` and the alignment grid | as on Tensor Cores |

On CDNA 3 the alignment grid is `2^(e_max − 24)` when `e_c ≤ e_max`, and the
coarser of that and `2^(e_c − 32)` when `e_c > e_max`.
On FP8 the cut-off is at or above the common grid of the two groups, so each
group's round down acts only on low parts. When the FP8 cutoff drops `c`,
the whole of `c` is a low part.

## Two ways to finish

### The fast path: plain FP32 additions

The low parts are summed in FP32, `D − εₒ` is formed in FP32, and one rounded
FP32 addition gives the result. The fast path is used only when a check
passes:

- the lowest bit set in the low parts is no lower than `2^-149`;
- above that bit, the low parts need fewer than 24 bits in total, and stay
  below `2^128`;
- the overlap `εₒ` and `H` are FP32 values.

When the check passes, every FP32 step before the last one is exact, so the
fast path returns the correctly rounded sum
([`MatrixCore.EftSplit.fastPath_sound`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Core.lean#L155)).
The key lemma is that FP32 summation is exact when all the bits lie on one grid
within one span of 24 bits inside the FP32 range
([`MatrixCore.naiveSum32_exact_of_bitSpan`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Sum32.lean#L119)).

### The exact fallback

If the check fails, `D − εₒ + Σ low parts` is formed in exact arithmetic and
rounded once. This always gives the right answer.

## What the Matrix Core's output buys

Correctness never depends on `D`. What `D` buys, when it is the Matrix Core's
own output, is a small overlap, which keeps the work on the fast path. Each
generation has its own exact statement.

### CDNA 1 and the SFMA: the correction returns `D`

The output is already the correctly rounded sum, so the correction from the
output returns the output
([`MatrixCore.correctRounding_eft`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/CDNA1.lean#L11);
`cdna1F16_eft`, `cdna1BF16_eft`, `sfmaF32_eft`).

### CDNA 2: the overlap is every rounding error

With the cut-off at the last bit of `D`, the overlap is exactly the low parts,
plus every rounding error of the Matrix Core (each product conversion, each
pairwise addition and the final rounding), minus what flushing to zero removed:

```lean
structure PairwiseOverlap (t : BlockTrace P) : Prop where
  cutoff : t.split.q = ulpExp32 (wordValue t.d)
  onGrid : OnGrid (t.split.overlap (wordValue t.d)) t.split.q
  overlap : t.split.overlap (wordValue t.d) = sumQ t.split.lows + (wordValue t.d - t.sAcc) +
    sumQ (pairwiseRoundingErrors P t.prepared) - flushLoss P t.prepared
  overlap_le : absQ (t.split.overlap (wordValue t.d)) ≤ ((P.nfma : ℚ) + 1) * pow2 t.split.q +
    pairwiseBound P t.prepared + flBound (!P.subnormals) t.sAcc

theorem pairwise_eft (hacc : P.accumulation = .pairWiseSum) (h : evalBlock x = .ok t) :
    PairwiseOverlap t
```

([`MatrixCore.pairwise_eft`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/CDNA2.lean#L109);
`cdna2F16_eft`, `cdna2BF16_eft`, `cdna2BF16_1k_eft`.) The bound goes through
the [CDNA 2 error bound](/HardwarePrimitives/matrix-core/properties/cdna2/#error-bounds),
which can be large under cancellation, so nothing here says the CDNA 2 overlap
is small in general.

### CDNA 3: the overlap is what alignment kept, plus the final rounding

With `D` the block's output, `S_acc` is exactly `H` plus the part of the low
parts that the alignment kept. The overlap is that kept part plus the final
rounding error, which is at most half a unit in the last place of `D`:

```lean
structure AlignedOverlap (t : BlockTrace P) : Prop where
  kept : t.sAcc = t.split.H + keptLow P t.prepared t.split.q
  kept_lt : absQ (keptLow P t.prepared t.split.q) < ((P.nfma : ℚ) + 5) * pow2 t.split.q
  final : absQ (wordValue t.d - t.sAcc) ≤ pow2 (ulpExp32 (wordValue t.d) - 1)
  overlap : t.split.overlap (wordValue t.d) =
    keptLow P t.prepared t.split.q + (wordValue t.d - t.sAcc)
  overlap_lt : absQ (t.split.overlap (wordValue t.d)) < ((P.nfma : ℚ) + 6) * pow2 t.split.q
  loss : t.prepared.exact - t.sAcc = sumQ t.split.lows - keptLow P t.prepared t.split.q
```

([`MatrixCore.aligned_eft`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/CDNA3.lean#L632);
`cdna3F16_eft`, `cdna3BF16_eft`, `cdna3XF32_eft`, `cdna3FP8_eft`.) What
alignment dropped is the low parts minus the kept part. The kept part is
usually not zero: the cut-off is normally the last bit of `D`, above the
alignment grid.

After cancellation, the last bit of `D` can lie at or below the alignment grid.
If also `e_c ≤ e_max`, the final rounding is exact (`D = S_acc`). With global
alignment (FP16, BF16, XF32) it follows that `H = D`, the overlap is `0`, and
the low parts are exactly what alignment dropped: `S = D + Σ low parts`
([`MatrixCore.globalAlignment_exact_rounding`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/CDNA3.lean#L706)).

## From the inputs alone

The check of the fast path looks at `D`. A condition on the inputs alone
predicts it. It uses the exact sum `S` of the decoded inputs and a bound `E` on
the error of `D`; each generation's a priori error bound is such a bound, also
computed from the inputs. [`MatrixCore.InputFast`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Inputs.lean#L254) holds when, for every `D`
within `E` of `S`:

- the lowest bit of the nonzero terms is at least `2^-149`;
- the low parts fit 24 bits above it at the highest cut-off such a `D` can give;
- the overlap and `H` fit FP32 at the lowest cut-off such a `D` can give.

Lean proves that the check then passes for every finite `D` within `E` of `S`
([`MatrixCore.guard_of_inputs`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Inputs.lean#L280)). With each generation's a priori bound, the
correction of the Matrix Core's own output takes the fast path:

```lean
theorem aligned_fast (hL : LateModel P)
    (hacc : P.accumulation = .globalAlignment ∨ P.accumulation = .oddEvenGrouping)
    (hsub : P.subnormals = true) (h : evalBlock x = .ok t)
    (hc : InputFast P t.prepared (alignedApriori P t.prepared))
    (hS : absQ t.prepared.exact < overflowThreshold32) : ∃ b, mcEft x t.d = .ok (.fast b)
```

([`MatrixCore.aligned_fast`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Inputs.lean#L422) for CDNA 3, [`MatrixCore.pairwise_fast`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Inputs.lean#L415) for
CDNA 2, [`MatrixCore.correctRounding_fast`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Inputs.lean#L407) for CDNA 1 and the SFMA.) All six
conditions of the check follow from the inputs. On Tensor Cores, the TC-EFT
paper's inequality (17) gives five of nine and leaves four as assumptions. The
price is that the condition uses the exact sum and the error bound, not only the
exponents.

The condition is sufficient, not necessary. Near a power of two, a `D` just
below it lowers the cut-off, so the condition can fail for a block that takes
the fast path. In the kernel-checked tests it holds for the first CDNA 3 row
below, the CDNA 1 row and a CDNA 2 block with lead product `1.5`, and fails for
the fallback row, as it must, and for the CDNA 2 order example, whose sum is
near `1`.

## Inner products of any length

[`MatrixCore.mcEftDot`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Dot.lean#L15) corrects an inner product of any length from its final
output word `D`: `c` and every product are split at the last bit of `D`. Any
returned word is the exact `c + Σ a_ℓ b_ℓ` rounded to the nearest FP32 value,
for any finite `D` ([`MatrixCore.mcEftDot_correct`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Dot.lean#L80)). From the Matrix Core's
output, the overlap is the error of `D` plus the low parts, and the error is at
most the sum of the blocks' error bounds ([`MatrixCore.dot_overlap`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Dot.lean#L108)). With any
bound on that error, the condition of the previous section gives the fast path
([`MatrixCore.mcEftDot_fast`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Inputs.lean#L454)).

| Inner product | Matrix Core `D` | Correctly rounded `S` | Correction |
| --- | --- | --- | --- |
| CDNA 3 FP16, two blocks of the first row below | `0x40900000` | `0x40900002` | fast, `0x40900002` |
| CDNA 1 FP16, two blocks, each `1 + 2^-24` | `0x3F800000` | `0x3F800001` | fast, `0x3F800001` |

In the CDNA 1 inner product, each block is correctly rounded: it rounds the tie
`1 + 2^-24` to `1`. The chain still loses `2^-23`, and the correction puts it
back.

## In a 576-bit register

[`MatrixCore.mcEftFixed`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Fixed.lean#L992) runs the whole correction on 576-bit two's-complement
registers in units of `2^-298`, the lowest bit of a product of two FP32 values:

- the terms are registers, split at the cut-off by masks;
- `H` and the low parts are register additions;
- the check is a trailing-zero count, masks and comparisons;
- the fast path is FP32 rounding of register sums, and the exact fallback is one
  rounding of the register sum, by a leading-zero count, shifts and
  comparisons.

Exponents and shift counts are small naturals. Lean proves that no addition
wraps and that the result is that of `mcEft`, on every model whose products lie
on `2^-298` with exponents at most `258` and that has fewer than `2^12`
products:

```lean
theorem mcEftFixed_eq (hP : P.FitsRun) (x : BlockInput P) (D : F32) :
    mcEftFixed x D = mcEft x D
```

([`MatrixCore.mcEftFixed_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Fixed.lean#L1018); the register rounding is [`MatrixCore.roundReg_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Register.lean#L232).)
Every model of the paper fits ([`MatrixCore.paper_models_fitRun`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Fixed.lean#L1071)).
[`MatrixCore.mcEftDotFixed_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/MatrixCore/EFT/Fixed.lean#L1046) gives the same for inner products of fewer than
`2^12` products.

## Worked examples

Every row is a kernel-checked test
([`EFT.lean`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/matrix-core/tests/MatrixCoreTests/EFT.lean)).
"Correction" is the result from the Matrix Core's own `D`.

| Block | Inputs | Matrix Core `D` | Correctly rounded `S` | Correction |
| --- | --- | --- | --- | --- |
| CDNA 3 FP16 | `c = 0`, `2.25 × 1`, seven `2^-12 × 2^-12` | `0x40100000` | `0x40100002` | fast, `0x40100002` |
| CDNA 3 FP16 | `1 × 1`, `1.5·2^-12 × 2^-11` | `0x3F800002` | `0x3F800002` | fast, `0x3F800002` |
| CDNA 3 FP16 | `1 × 1`, `−(1 − 2^-11) × 1`, `2^-13 × 2^-12` | `0x3A000000` | `0x3A000200` | fast, `0x3A000200` |
| CDNA 3 FP16 | `c = 2^-60`, `1 × 1`, `2^-12 × 2^-12` | `0x3F800000` | `0x3F800001` | exact, `0x3F800001` |
| CDNA 3 FP16, `e_c > e_max` | `c = 1`, `2^-12 × 2^-12`, `2^-20 × 2^-20` | `0x3F800000` | `0x3F800001` | fast, `0x3F800001` |
| CDNA 3 FP8 E5M2 | `−1` and `−1.5·2^-12 × 2^-12`, both odd-indexed | `0xBF800000` | `0xBF800001` | fast, `0xBF800001` |
| CDNA 2 FP16 | products `1, s, s, 0`, `s = 2^-23 + 2^-24` | `0x3F800004` | `0x3F800003` | fast, `0x3F800003` |
| CDNA 1 FP16 | products `1, s, s, 0` | `0x3F800003` | `0x3F800003` | fast, `0x3F800003` (`D` itself) |

- **The first row** is the block of [the worked trace](/HardwarePrimitives/matrix-core/#a-worked-trace)
  whose seven small products are truncated away. Here `q = −22`, `H = D = 2.25`,
  the overlap is `0` and the low parts are `7·2^-24`. The same block from
  `D = 0` or `D = 0xC0100000` also takes the fast path, and from
  `D = 0x7F7FFFFF` the exact one. All three return `0x40100002`.
- **The second row** shows a kept part. The Matrix Core keeps `2^-24` of the
  low part, and the overlap `2^-23` is that part plus `D − S_acc = 2^-24`.
- **The third row** is cancellation. The last bit of `D = 2^-11` is below the
  grid, so `H = D`, the overlap is `0`, and the low part `2^-25` is what
  alignment dropped.
- **In the fourth row** the low parts `2^-24` and `2^-60` span 37 bits, so the
  check fails. Plain FP32 additions would also lose `2^-60` and return `1`; the
  exact fallback returns `1 + 2^-23`.
- **The CDNA 2 row** is the [order example](/HardwarePrimitives/matrix-core/cdna2/#example).
  The overlap `2^-22` is the low parts `2^-23` plus two pairwise rounding errors
  of `2^-24`.

## The caveats, plainly

**1. The result doesn't depend on `D` being the Matrix Core's output.** The
proofs work for any finite `D`, so the correction does not rely on the model
matching the hardware. A good `D` buys speed, not correctness.

**2. The condition on the inputs is sufficient, not necessary.** It can fail
near a power of two for a block that takes the fast path. There are no
fast-path statistics on AMD inputs, and a low part below `2^-149` always forces
the fallback.

**3. Finite inputs only.** Infinities and NaNs give an error, and a sum beyond
the FP32 range gives `.outOfRange` rather than infinity. An exactly zero sum
returns `+0`.

**4. What `S` is.** On XF32, `S` is the exact sum of the operands as the matrix
core reads them, truncated to ten mantissa bits; the input truncation is not
corrected. On CDNA 2, `S` uses the inputs before flushing, and the result is
rounded with subnormals, not flushed.

**5. Inner products.** The correction is correct for any length, and the
register version covers fewer than `2^12` products. For an inner product, the
condition on the inputs takes a given bound on the error of `D`, such as the sum
of the blocks' bounds, rather than one computed from the inputs alone.

**6. Re-checked independently.** On 2026-10-18 con-leche, an independent Lean
checker, accepted every declaration of `MatrixCore` and its tests, MC-EFT
included ([What is tested](/HardwarePrimitives/proofs/tested/#proven-in-lean)).
