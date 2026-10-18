---
title: Ozaki-II, proven end to end
description: The complete Lean proof of Ozaki-II on the Tensor Core and AMD matrix-core models, from scaling and residues to Chinese-remainder reconstruction and the final rounding, and its correctly rounded variant.
---

Ozaki-II (Ozaki, Uchino and Imamura, 2025) computes `x · y` with one call to
the matrix multiplier per modulus instead of one per slice pair. It scales the
inputs to integers, computes their product modulo a few small moduli on the
matrix multiplier,
where the residues are small enough to multiply exactly, rebuilds the integer
product with the Chinese remainder theorem (CRT), and rounds once. The only
approximation is the first step. Every step below is a Lean theorem in
[`ozaki/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/wip/ozaki), checked
with only Lean's standard axioms.

## The algorithm for one output entry

1. **Scale and truncate** `x` to integers `a` of at most `P` bits, scaling by
   `2^sₓ` so that the largest entry is near `2^P`; the same for `y` and `c`.
2. **Residues.** For each modulus `m`, reduce `a` and `c` to symmetric residues
   in `(−m/2, m/2]` and compute their dot product on the matrix multiplier.
3. **Reconstruct** `a · c` from its residues with the CRT. This is exact when
   `2 k 2^(2P) < M`, the product of the moduli.
4. **Round once:** `fl(2^(−sₓ−s_y) (a · c))`.

The Z3 models use `k = 4`, the moduli `{4096, 4095, 4093, 4091}` (`M ≈ 2^48`)
and `P = 22`: four calls to the matrix multiplier per entry.

## Step 1: scaling and truncation

| Fact | Lean |
| --- | --- |
| The scaled row maximum lies in `(2^(P−1), 2^P]`, and every truncated integer has magnitude at most `2^P`. | [`scaleShift_spec`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Checks.lean#L45), [`scaleTrunc_bound`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Ozaki2.lean#L51) |
| The truncation error: `\|x · y − 2^(−sₓ−s_y)(a · c)\| ≤ Σᵢ (2^(−sₓ)\|yᵢ\| + 2^(−sₓ−s_y)\|aᵢ\|)`, at most `8 k max\|x\| max\|y\| 2^(−P)`. Sharper: `2^(−s)Σ\|yᵢ\| + 2^(−t)Σ\|xᵢ\|` for any shifts, Uchino et al.'s bound without its cross term, since truncation is toward zero, and `4 k max\|x\| max\|y\| 2^(−P)` normwise ([`truncProduct_error_mixed`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SharpBounds.lean#L534), [`truncProduct_error_normwise4`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SharpBounds.lean#L573)). | [`truncProduct_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Ozaki2.lean#L127), [`truncProduct_error_normwise`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Ozaki2.lean#L159) |

## Step 2: residues on the matrix multiplier

| Fact | Lean |
| --- | --- |
| Symmetric residues lie in `(−m/2, m/2]`, and the product of the residues is congruent to the product modulo `m`. | [`symMod_bounds`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/CRT.lean#L32), [`dvd_dotZ_symMod`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Ozaki2.lean#L240) |
| A residue product has magnitude at most `k ⌊m/2⌋²`, at most `2^24` for the Z3 moduli. | [`natAbs_residueProduct_le`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Checks.lean#L69), [`z3_residue_exactnessBound`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Checks.lean#L83) |
| The matrix multiplier computes each residue product exactly: residues of moduli at most `2^(b+1)` are `b`-bit integers, and the Tensor Core and matrix-core matrix multipliers are exact on those. | [`tcMultiplier_exactOn`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/MatrixMultiplier.lean#L195), [`mcMultiplier_exactOn`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiMC/MatrixMultiplier.lean#L326) |

## Step 3: Chinese-remainder reconstruction

```lean
theorem crt_eq {B : CRTBasis} (hB : B.Valid) {rs : List ℤ} (hlen : rs.length = B.moduli.length)
    {c : ℤ} (hres : ∀ j : Fin B.moduli.length, (B.moduli[j] : ℤ) ∣ rs.getD j 0 - c)
    (h1 : -(B.modulus : ℤ) < 2 * c) (h2 : 2 * c ≤ B.modulus) : crt B rs = c
```

For any valid basis (pairwise coprime moduli with the CRT weights), the
reconstruction returns every `c` with `−M < 2c ≤ M` from residues congruent to
it ([`crt_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/CRT.lean#L156)), and it matches every residue ([`crt_dvd_sub`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Checks.lean#L94)). For the Z3
moduli the weights form a valid basis ([`z3Basis_valid`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Parameters.lean#L48)) and `P = 22` is the
largest precision with `2 k 2^(2P) < M` ([`z3_bits`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Parameters.lean#L58)). At `P = 23` the product
can reach `M` itself, whose residues are all zero, so it reconstructs as `0`
([`crt_fails_at_23`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Parameters.lean#L65)).

## Step 4: the whole scheme

| Fact | Lean |
| --- | --- |
| With an exact matrix multiplier, Ozaki-II is one rounding of the truncated product. | [`ozaki2_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Ozaki2.lean#L281) |
| Its error: one rounding plus the truncation bound. | [`ozaki2_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Ozaki2.lean#L333), [`tcOzaki2_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Schemes.lean#L82) |
| It returns a value (never Inf or NaN) when the product is within range. | [`ozaki2_isSome`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Success.lean#L161) |
| The Z3 configuration runs exactly on V100. | [`v100_ozaki2_z3`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Schemes.lean#L114) |

On the Z3 models' test matrices the Lean pipeline returns the same binary32
words as the Z3 model on every fp16 and tf32 variant and on the AMD variants.

## Dot products of any length, and FP64

The reconstruction range grows with `k`, so a longer dot product needs more
moduli or a smaller `P`; the matrix-multiplier side is handled by split-K, which runs
each residue product in chunks and adds the chunk results exactly
([`chunked_exactOn`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SplitK.lean#L131)). With binary64 inputs and enough moduli, Ozaki-II
emulates FP64 on fp16, bf16 and tf32 Tensor Cores and on AMD matrix cores; the
tests use twelve moduli at most `4096` (`P = 69` for `k = 8`).

## Correctly rounded Ozaki-II

Ozaki-II rounds once, but it rounds the product of the *truncated* inputs. On
the Z3 test matrices that is never the correctly rounded `x · y`: with
`P = 22`, two bits short of binary32's `24`, results are off by up to 68
binary32 steps.

The correctly rounded version uses the same rounding test as Ozaki-I. Before its last
rounding, Ozaki-II holds `H`, the reconstructed product, exactly, and the
truncation bound gives `B ≥ |x · y − H|` ([`dot_approx_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Correct.lean#L174)). If `H − B`
and `H + B` round to the same value, so does `x · y`; otherwise more moduli
are tried, and finally an exact fallback ([`ozaki2CR_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Correct.lean#L297)). The exact fallback can
run on the matrix multiplier too, as Ozaki-I with all slice products
([`ozaki2CRE_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Correct.lean#L542)), so every product on the matrix multiplier, residue or slice,
runs on the hardware model:

- binary32, any length: [`tcOzaki2CRL_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/LongDot.lean#L158), [`mcOzaki2CRL_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiMC/LongDot.lean#L74);
- FP64, any length: [`tcOzaki2CRD_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/LongDot.lean#L218), [`mcOzaki2CRD_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiMC/LongDot.lean#L128).

The whole correctly rounded Ozaki-II also runs as one integer function from
`(significand, exponent)` inputs: integer scaling, residues and CRT
reconstruction, an integer rounding test whose bound is built from the scaled
integers the matrix multiplier already multiplies, and the exact fallback in
fixed-width registers ([`ozaki2CRJ_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/BoundedOzaki2J.lean#L112), [`ozaki2CRJS_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/BoundedOzaki2J.lean#L174) with signed zeros). The
[correct rounding](/HardwarePrimitives/ozaki/correct-rounding/) page has the register
widths and the IEEE special values.

Correct rounding costs Ozaki-II more than Ozaki-I, because it has no margin at
`P = 22`. On the Z3 test matrices the rounding test succeeds on no entry with
four moduli, on 21 of 32 with five, and on all of them with six.

## What the proof assumes

- **The hardware models**, validated against GPUs by measurement, not proven.
- **The conditions**: valid moduli at most `2^(b+1)`, `2 k 2^(2P) < M`, and the
  exactness bound of the matrix multiplier per call (or split-K).
- **An exact reconstruction**, or one accumulated within a proven `ε`: with
  the CRT sum accumulated in FP64, the reduction still recovers the product
  when `2k 2^(2P) + 2ε < M`, and the error grows by about `ε 2^-s`
  ([`ozaki2Approx_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SharpBounds2.lean#L637), [`ozaki2FP64_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SharpBounds2.lean#L813)). Uchino et al.'s binary64
  reconstruction algorithm, with split weights, a rounded reciprocal and
  fused multiply-adds, is proven to recover the quotient and meet an explicit
  bound ([`uchinoRecon_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/UchinoCRT.lean#L276), [`ozaki2Uchino_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/UchinoCRT.lean#L473)). Their closed-form
  constant is proven in their setting, and their scaling end to end, with
  their exhaustively checked slack as a hypothesis ([`uchino_R64`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/UchinoConst.lean#L303),
  [`ozaki2Uchino_scaled_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/UchinoScaling.lean#L779)).
- **Exact arithmetic off the matrix multiplier**: the scaling, the
  reconstruction and the rounding test are exact integer and rational
  arithmetic in the proofs. The
  integer form of the whole pipeline, from `(significand, exponent)`
  inputs, is proven equal to it, with one theorem bounding every register
  ([correct rounding](/HardwarePrimitives/ozaki/correct-rounding/)).
