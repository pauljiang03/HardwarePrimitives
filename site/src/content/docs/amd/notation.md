---
title: 2. Notation and formats
description: The notation of Accurate Models of AMD Matrix Cores mapped to Matrix-Core's Lean names, the feature table, the four configurations, and the input formats.
---

Matrix-Core uses the notation of *Accurate Models of AMD Matrix Cores*
throughout. This page maps each symbol to its Lean name.

## Inner products

An MFMA instruction computes `D = AB + C`. Each element is the inner product

```text
d = Σ_{ℓ=1}^{k} a_ℓ b_ℓ + c = Σ_{ℓ=1}^{k} p_ℓ + c,
```

evaluated in blocks of `N_FMA` products. A finite value is written
`x = s · 2^e`, with significand `s` and exponent `e`. In Lean an `Unpacked`
value keeps the significand as an integer `m` with `t` fractional bits
(`s = m / 2^t`), and gives subnormals and zero the minimum normal exponent.

| Paper | Meaning | Lean |
| --- | --- | --- |
| `a_ℓ`, `b_ℓ`, `c` | operands of one block | `BlockInput.a`, `.b`, `.c`; decoded: `Prepared` |
| `p_ℓ = a_ℓ b_ℓ` | full-precision, denormalized product: `s_p = s_a s_b ∈ [0, 4)`, `e_p = e_a + e_b` | `Unpacked.mul`, `Prepared.p` |
| `Σ p_ℓ + c` exactly | | `Prepared.exact` |
| `N_FMA` | products per multi-term addition | `Profile.nfma` |
| `n_eab` | extra alignment bits: products keep `23 + n_eab` fractional bits | `Profile.neab` |
| `e_max` | largest exponent of the nonzero products | `maxExp` |
| `S_{p_i,sum}` | sum of the aligned products | `productSum`, `alignedSum` |
| `e_c` | exponent of `c` (`−126` for subnormal `c`) | `cExp` |
| `e_{c=0}` | exponent given to `c = 0` (`−126`, or `−∞`) | `Profile.cZeroExp` |
| `s′_c` | `s_c` shifted right by `e_max − e_c`, rounded down to 24 fractional bits | `shiftedC` |
| `S′_{p_i,sum}` | `S_{p_i,sum}` shifted right by `e_c − e_max`, rounded down to 32 fractional bits | `shiftedSum` |
| `S_acc` | the accumulated significand presented to the final rounding | `BlockTrace.sAcc`, `alignedAccumulation` |
| `fl{·}` | normalize and round to binary32 with round to nearest even | `rne32`, `fl32` (with flush to zero), `flValue` |
| RD | round toward `−∞` on a fixed-point grid | `rdGrid`, `rdFrac` |
| truncation | magnitude truncation on a fixed-point grid | `truncGrid`, `truncFrac` |
| SFMA | `(…((c + p₁) + p₂) + …)` | `sfmaF32` with `dotBits` |

## The feature table

The paper's feature comparison table has one row per numerical feature. Each
row is a field or a derived property of `Profile`:

| Row | Lean | CDNA 3 value |
| --- | --- | --- |
| Input formats | `Profile.a`, `Profile.b` | fp16, bf16, XF32, fp8 |
| Product alignment `(2, 24)` | `Profile.productAlignment` | `(2, 24)` |
| `N_FMA` | `Profile.nfma` | 8 (16 for binary8, 4 for XF32) |
| `e_{c=0}` | `Profile.cZeroExp` | `−126` |
| `c` late or early | `Profile.lateC` | late |
| `align(c, S_{p_i-sum})` `(24, 32, RD)` | `LateAlignment.cFracBits`, `.sumFracBits` | 24, 32 |
| Output rounding | `fl{·}` is round to nearest even on every CDNA path | round to nearest even |
| `\|p_i\|` overflow | `Profile.productOverflow` | `2^128` |

## The four configurations

| Paper | Lean | Used by |
| --- | --- | --- |
| `correct_rounding` | `.correctRounding` | CDNA 1, SFMA |
| `pair_wise_sum` | `.pairWiseSum` | CDNA 2 |
| `global_alignment` with `late_partial_sum` | `.globalAlignment` | CDNA 3 fp16, bf16, XF32 |
| `odd_even_grouping` | `.oddEvenGrouping` | CDNA 3 binary8 |

## Formats

| Paper | Lean | Precision | Minimum normal | Maximum |
| --- | --- | --- | --- | --- |
| binary32 (fp32) | `binary32` | 24 | `2^-126` | `(2 − 2^-23)·2^127` |
| tf19 (XF32) | `tf19`, `InputFormat.xf32` | 11 | `2^-126` | `(2 − 2^-10)·2^127` |
| bfloat16 (bf16) | `bfloat16` | 8 | `2^-126` | `(2 − 2^-7)·2^127` |
| binary16 (fp16) | `binary16` | 11 | `2^-14` | `65504` |
| fp8-E4M3 FNUZ | `e4m3fnuz` | 4 | `2^-7` | `240` |
| fp8-E5M2 FNUZ | `e5m2fnuz` | 3 | `2^-15` | `57344` |

FNUZ formats have no infinities and no negative zero; the negative-zero word
is NaN. XF32 reads a binary32 word and truncates its significand to ten
fraction bits.
