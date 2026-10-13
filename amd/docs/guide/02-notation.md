# The paper's notation in Lean

## Inner products

An MFMA instruction computes `D = AB + C`. Each element is the inner product of Eq. (1),

```
d = Σ_{ℓ=1}^{k} a_ℓ b_ℓ + c = Σ_{ℓ=1}^{k} p_ℓ + c,
```

evaluated in blocks of `N_FMA` products. A finite value is written `x = s · 2^e`, with
significand `s` and exponent `e`. In Lean, an `Unpacked` value keeps the significand as an integer
`m` with `t` fractional bits (`s = m / 2^t`), and gives subnormals and zero the minimum normal
exponent.

| Paper | Meaning | Lean |
| --- | --- | --- |
| `a_ℓ`, `b_ℓ`, `c` | operands of one block | `BlockInput.a`, `.b`, `.c`; decoded: `Prepared` |
| `p_ℓ = a_ℓ b_ℓ` | full-precision product in denormalized form: `s_p = s_a s_b ∈ [0, 4)`, `e_p = e_a + e_b` | `Unpacked.mul`, `Prepared.p` |
| Eq. (1) exactly | `Σ p_ℓ + c` | `Prepared.exact` |
| `N_FMA` | products per multi-term addition | `Model.nfma` |
| `n_eab` | extra alignment bits: products keep `23 + n_eab` fractional bits | `Model.neab` |
| `e_max` | largest exponent of the nonzero products | `maxExp`, `(productSum P ps).1` |
| `s_{p_i}` aligned to `e_max`, truncated to 24 fractional bits | | `truncFrac p.value e (23 + n_eab)` |
| `S_{p_i,sum}` | sum of the aligned products | `(productSum P ps).2` (a value), `alignedSum` |
| `e_{max-odd}`, `e_{max-even}`, `S_{p_i,sum-odd}`, `S_{p_i,sum-even}` | binary8 groups | `alignedSum P.neab (oddIndexed ps)`, `… (evenIndexed ps)` |
| `e_c` | exponent of `c` (`−126` for subnormal `c`) | `cExp` |
| `e_{c=0}` | exponent given to `c = 0` (`−126`, or `−∞`) | `Model.cZeroExp` (`none` is `−∞`) |
| `s′_c` | `s_c` shifted right by `e_max − e_c`, RD to 24 fractional bits | `shiftedC` |
| `S′_{p_i,sum}` | `S_{p_i,sum}` shifted right by `e_c − e_max`, RD to 32 fractional bits | `rdFrac pSum eC 32` in `shiftedSum` |
| `S_acc` | the accumulated significand presented to the final rounding | `BlockTrace.sAcc`, `alignedAccumulation` |
| subnormal-aware normalization | leading bit to the binary point, not below exponent `−126` | `normExp` |
| RD to 31 fractional bits after normalization | | `normalizeRD 31` |
| `fl{·}` | normalize and round to binary32 with RNE | `rne32`, `fl32` (with flush to zero), `flValue` |
| RD | round toward `−∞` on a fixed-point grid | `rdGrid`, `rdFrac` |
| truncation | magnitude truncation on a fixed-point grid | `truncGrid`, `truncFrac` |
| "fractional bits" `k` after alignment to `e` | grid `2^(e − k)` | `rdFrac x e k = rdGrid x (e − k)` |
| SFMA | `(…((c + p₁) + p₂) + …)` | `sfmaF32` with `dotBits` |

## The feature table

The paper's feature comparison table has one row per numerical feature. Each row is a field or a
derived property of `Model`:

| Row | Lean | CDNA 3 value |
| --- | --- | --- |
| Input formats | `Model.a`, `Model.b` (`InputFormat`) | fp16, bf16, XF32, fp8 |
| Prd. Align. `(2, 24)` | `Model.productAlignment` (`2` integer bits, `23 + n_eab` fractional bits) | `(2, 24)` |
| `N_FMA` | `Model.nfma` | 8 (16 for binary8, 4 for XF32) |
| `e_{c=0}` | `Model.cZeroExp` | `−126` |
| `c` late/early | `Model.lateC` | late |
| `align(c, S_{p_i-sum})` `(24, 32, RD)` | `LateAlignment.cFracBits`, `.sumFracBits` | 24, 32 |
| out. round. | `fl{·}` is RNE on every CDNA variant | RNE |
| `e^lim_min` | implied by `e_{c=0} = −126`: `S_acc` is never aligned below `−126` | `−126` |
| `|p_i|`-overflow | `Model.productOverflow` | `2^128` |

## The four configurations

The paper's generalized model has four configurations, the constructors of `Accumulation`:

| Paper | Lean | Used by |
| --- | --- | --- |
| `correct_rounding` | `.correctRounding` | CDNA 1, SFMA |
| `pair_wise_sum` | `.pairWiseSum` | CDNA 2 |
| `global_alignment` with `late_partial_sum` | `.globalAlignment` | CDNA 3 fp16, bf16, XF32 |
| `odd_even_grouping` | `.oddEvenGrouping` | CDNA 3 binary8 |

## Formats (Table 1)

| Paper | Lean | Precision | Minimum normal | Maximum |
| --- | --- | --- | --- | --- |
| binary32 (fp32) | `binary32` | 24 | `2^-126` | `(2 − 2^-23)·2^127` |
| tf19 (XF32) | `tf19`, `InputFormat.xf32` | 11 | `2^-126` | `(2 − 2^-10)·2^127` |
| bfloat16 (bf16) | `bfloat16` | 8 | `2^-126` | `(2 − 2^-7)·2^127` |
| binary16 (fp16) | `binary16` | 11 | `2^-14` | `65504` |
| fp8-E4M3 FNUZ | `e4m3fnuz` | 4 | `2^-7` | `240` |
| fp8-E5M2 FNUZ | `e5m2fnuz` | 3 | `2^-15` | `57344` |

FNUZ formats have no infinities and no negative zero; the negative-zero word is NaN. XF32 reads a
binary32 word and truncates its significand to ten fraction bits.
