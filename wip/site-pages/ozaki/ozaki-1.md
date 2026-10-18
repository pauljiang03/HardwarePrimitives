---
title: Ozaki-I, proven end to end
description: The complete Lean proof of Ozaki-I on the Tensor Core and AMD Matrix Core models, from exact slicing to the binary32 or binary64 result, for dot products of any length, and a variant that is always correctly rounded.
---

Ozaki-I (Ozaki, Ogita, Oishi and Rump, 2012) computes a high-precision matrix
product on a low-precision matrix multiplier. It cuts every input into a few
slices of small integers, multiplies slices on the matrix multiplier, where
products of small integers are exact, and adds the scaled products. This page follows the
whole proof, from the slicing of the inputs to the value the hardware returns.
Every step is a Lean theorem in the [`ozaki/`](https://github.com/pauljiang03/HardwarePrimitives/tree/main/wip/ozaki)
project, which depends on the Tensor Core model of this repository and on the
AMD Matrix Core model in `amd/`. Lean checks all of it with only its standard
axioms.

The project follows a set of bit-precise Z3 models of the schemes. A Z3 runtime
assertion checks one fact on its test matrices; the Lean theorem states it for
every input. Each Z3 label (`[S1.13]`, `[M.3]`, …) maps to a Lean theorem or a
kernel-checked test in
[`ozaki/THEOREMS.md`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/THEOREMS.md),
which also lists what is not proven.

## The algorithm for one output entry

Every entry of `C = AB` is a dot product `x · y` of a row of `A` and a column
of `B`, with `k` terms, and Ozaki-I treats each entry separately. It has two
parameters: `b`, the bits per slice, and `s`, the number of slices.

1. **Split** `x` into `s` slices on decreasing power-of-two grids,
   `x = Σₜ 2^gₜ qₜ + r`, where every `qₜ` is a vector of integers of magnitude
   at most `2^b` and `r` is what is left. Split `y` the same way into `2^hᵤ pᵤ`.
2. **Multiply** the `s (s + 1) / 2` slice pairs with `t + u < s` on the matrix multiplier:
   the integer dot products `qₜ · pᵤ`.
3. **Add** the products, each scaled by `2^(gₜ + hᵤ)`, in binary32 (or binary64
   for FP64 emulation), smallest first.

The Z3 models use `k = 4`, `b = 11` and `s = 4`: ten products on the matrix
multiplier per entry.

## Step 1: the slicing is exact

Slice `t` rounds what the previous slices left to the nearest multiple of
`2^gₜ`, where `gₜ = ⌈log₂ max|·|⌉ − b`. Four facts carry the rest of the proof:

| Fact | Lean |
| --- | --- |
| The slices and the residual add up to `x` exactly, as a statement about every dot product `x · y`. | [`split_dot`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Split.lean#L250) |
| Every slice coefficient is an integer of magnitude at most `2^b`. | [`split_coeff_bound`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Split.lean#L254) |
| Slice `t` lies at least `t (b + 1)` bits below the first: every slice gains `b + 1` bits. | [`split_grid_le`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Split.lean#L257) |
| The residual after `s` slices is at most `2^(E − s(b+1))`, with `E = ⌈log₂ max\|x\|⌉`. | [`split_residual_le`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Split.lean#L264), [`splitExp_spec`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Split.lean#L238) |

```lean
theorem split_dot (b s : ℕ) (x y : List ℚ) :
    dot x y = ((split b s x).1.map fun sl => 2 ^ sl.grid * dot (ofInts sl.coeffs) y).sum +
      dot (split b s x).2 y
```

The proofs slice in exact arithmetic. On binary32 hardware the rounding to a
grid is the σ-trick `hi = fl(fl(a + σ) − σ)` with `σ = 3 · 2^(g+22)`, and the
remainder `fl(a − hi)`. Lean proves that this computes exactly the slice above
for every binary32 `a` with `|a| ≤ 2^(g+b)`, `b ≤ 21` and every grid
`−149 ≤ g ≤ 104` ([`sigma_split`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Split32.lean#L176)); that the remainder needs no range condition
at all ([`finiteValue32_sub_round`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Split32.lean#L91)); and that a whole split computed with
binary32 operations is the split of the proof when every grid is in that range
([`splitFrom32_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Split32.lean#L268)). The Z3 lemma covers `|a| ≤ 1`.

Outside that range σ overflows (above about `2^115`) or the grid falls below
binary32's, as in the long exact fallbacks. Slicing with integer operations covers
every grid: on significands and exponents it shifts, divides with
round-half-even and compares, and it equals the split of the proof for every
vector and grid ([`splitInt_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SliceInt.lean#L582)). Its coefficients have at most `b + 1` bits,
its significands never grow, and no division needs more than `p + 2` bits,
whatever the exponents ([`splitInt_width`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SliceInt.lean#L605), [`split_binary32_int`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SliceInt.lean#L630),
[`split_binary64_int`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SliceInt.lean#L638)).

## Step 2: every slice product is exact on the hardware

A `MatrixMultiplier` is a function from two integer vectors to the value the
hardware returns. `MatrixMultiplier.ExactOn b bound` says that it returns
`Σ xᵢyᵢ` exactly when every entry has magnitude at most `2^b` and the
products total at most `bound`, the exactness bound.

On the Tensor Core model, the matrix multiplier encodes the integers as fp16,
bf16 or tf32 words, pads them with zeros to whole block FMAs, and chains the
block FMAs through `C`, starting from zero. Integer operands lose nothing in alignment when `2b ≤ F` (`F = 23`
on V100, `24` on A100, `25` on H100), and the binary32 output holds every
integer up to `2^24`:

| Fact | Lean |
| --- | --- |
| A block of integer operands with `\|c\| + Σ\|aᵢbᵢ\| ≤ 2^24` returns `c + Σ aᵢbᵢ` exactly. | [`Ozaki.TC.evalBlock_int`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Exactness.lean#L188) |
| So does a chain of blocks. | [`Ozaki.TC.runBlocks_int`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Exactness.lean#L339) |
| The matrix multiplier is exact on `b`-bit vectors whose products total at most `2^24`, on any variant with `F ≥ 23`, `2b ≤ F` and a binary32 block output whose input format holds `b`-bit integers. | [`tcMultiplier_exactOn`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/MatrixMultiplier.lean#L195) |
| This holds on all eight GPU variants, with `b = 11` for fp16 and tf32 and `b = 8` for bf16. | [`v100_exactOn`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Models.lean#L31) and seven more |

```lean
theorem tcMultiplier_exactOn {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (hK : 0 < p.nfma) : (tcMultiplier p).ExactOn b (2 ^ 24)
```

The same holds on the AMD model for the binary32 SFMA, CDNA 1, 2 and 3 fp16,
CDNA 3 XF32 and the bf16 variants ([`mcMultiplier_exactOn`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiMC/MatrixMultiplier.lean#L326)).

**What the hardware models add.** That a slice product must fit the binary32
output is the familiar slice-width rule of the Ozaki literature. The models
prove it on each variant, show that the output rather than the accumulator
sets it, and show where it breaks: a full block FMA of `11`-bit products on
A100 or H100 already loses a bit ([`a100_full_blockFMA`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Limits.lean#L51)). The
[hardware semantics](/HardwarePrimitives/ozaki/hardware/) page has the exact condition,
the two-pass recovery and the choice of slices per GPU.

## Step 3: what the slicing leaves out, exactly

With exact slice products, the only error before the additions is the slice
pairs Ozaki-I skips and the residuals. Lean proves an exact identity for it:
pairing slice `t` of `x` with the residual of `y` after `s − t` slices accounts
for all the skipped pairs together ([`dot_eq_exactTerms_add`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Ozaki1.lean#L199)):

```text
x · y − Σ_{t+u<s} 2^(gₜ+hᵤ) (qₜ · pᵤ) = r · y + Σₜ 2^gₜ (qₜ · r'ₛ₋ₜ)
```

Bounding each piece with Step 1 gives the slicing error
([`exactTerms_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Ozaki1.lean#L235), [`exactTerms_error_normwise`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Ozaki1.lean#L302)):

```text
|x · y − Σ terms| ≤ (s + 1) k 2^(E + F − s(b+1)) ≤ 4 (s + 1) k max|x| max|y| 2^(−s(b+1))
```

An entrywise form is sharper: every slice and leftover part of an entry is at
most twice the entry, so the slicing error is at most
`(s + 1) Σᵢ min(2|xᵢyᵢ|, 2^(E + F − s(b+1)))`, never more than the bound above
and `0` when every product is zero ([`exactTerms_error_sharp`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SharpBounds.lean#L315)). It has the
shape of Abdelfattah et al.'s bound for their splitting
([`exactTerms_error_kappa`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SharpBounds.lean#L414)). With different
slice counts for `x` and `y` the same identity and bound hold
([`exactTermsRect_error_uniform`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SharpBounds2.lean#L189)).

## Step 4: the additions

The scaled products are added left to right. Binary32 round to nearest returns
`q` up to `2^-24 |q| + 2^-150` ([`Ozaki.TC.round32Value_within`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Rounding.lean#L112)), and `n` such
additions lose at most `((1 + u)^n − 1) Σ|tⱼ| + n (1 + u)^n η`
([`sumWith_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Summation.lean#L116)). With round to nearest the sharper Jeannerod–Rump bound
`(n − 1) u Σ|tⱼ|` holds, with no condition on `n u` and no underflow term
when the terms are representable ([`sumWith_error_jr`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SharpBounds.lean#L756),
[`ozaki1_error_jr`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SharpBounds.lean#L1192)). It holds for any
summation order, not only left to right ([`sumTree_error_jr`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SharpBounds2.lean#L484)). Every scaled slice product is itself a binary32 value when
its exponent is in range, so the scaling is exact
([`Ozaki.TC.scaled_slice_product_exact`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Scaling.lean#L56)).

## Step 5: the whole scheme

| Fact | Lean |
| --- | --- |
| Ozaki-I adds exactly the scaled exact slice products. | [`ozaki1_eq_sumWith`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Ozaki1.lean#L173), [`tcOzaki1_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Schemes.lean#L49) |
| The result is within the addition bound plus the slicing bound of `x · y`. | [`ozaki1_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Ozaki1.lean#L372), [`tcOzaki1_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Schemes.lean#L56), [`mcOzaki1_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiMC/Schemes.lean#L56) |
| The result is never Inf or NaN when the inputs are within a stated range. | [`ozaki1_isSome`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Success.lean#L113), [`tcOzaki1_isSome`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Success.lean#L35) |
| The Z3 configuration runs exactly on V100. | [`v100_ozaki1_z3`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/Schemes.lean#L106) |

```lean
theorem tcOzaki1_error {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (hK : 0 < p.nfma) (s : ℕ) {x y : List ℚ} (hlen : x.length = y.length)
    (hk : x.length * (2 ^ b * 2 ^ b) ≤ 2 ^ 24) {v : ℚ} (hv : tcOzaki1 p b s x y = some v) :
    Rat.abs (v - dot x y) ≤
      ((1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length - 1) *
          ((trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y))) +
        (trianglePairs s).length * (1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length *
          2 ^ (-150 : ℤ) +
        ((s + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp b x + splitExp b y - s * (b + 1))
```

## Dot products of any length, and FP64

The condition `k · 2^(2b) ≤ 2^24` above allows only four terms of `11`-bit
slices. Split-K removes it: cut the inner dimension into chunks of
`2^(24 − 2b)` terms, run each chunk on the matrix multiplier, and add the integer chunk
results exactly. This is exact for every length ([`chunked_exactOn`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/SplitK.lean#L131),
[`tcSplitK_exactOn`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/LongDot.lean#L42)), and on the Tensor Core model the chunk results can be
added in `TensorCore`'s fixed-width register, exact while the products total less
than `2^63` in a 64-bit register ([`tcSplitKReg_exactOn`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/LongDot.lean#L74)). On A100 and H100 a
second TC-EFT technique recovers a full block FMA of `11`-bit products exactly: run
it once from `c = 0`, then again from `c = −D1`; because `c` takes part in
alignment, the second pass returns exactly what the first truncated
([`twoPass_exact`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/TwoPass.lean#L256)). The two-pass matrix multiplier is exact for every length on
all eight variants, with full block FMAs of `11`-bit slices on fp16 and tf32
and `8`-bit slices on bf16 ([`h100F16_exactOn2`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/TwoPass.lean#L474), [`h100TF32Mma_exactOn2`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/TwoPass.lean#L510),
[`h100BF16_exactOn2`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/TwoPass.lean#L492) and five more). With split-K:

- Ozaki-I's error bound holds for every `k` ([`tcOzaki1L_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/LongDot.lean#L114)).
- **FP64 emulation.** With binary64 recombination the same bound holds with
  `u = 2^-53` ([`tcOzaki1D_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/LongDot.lean#L183), [`mcOzaki1D_error`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiMC/LongDot.lean#L96)), on fp16, bf16 and
  tf32 Tensor Cores and on AMD Matrix Cores.

## Correctly rounded Ozaki-I

Ozaki-I as above guarantees an error bound, not correct rounding. Its
correctly rounded version keeps the slice products exact and applies Ziv's
rounding test: it checks whether both ends of `H ± B` round to the same float,
tries more slices if not, and otherwise takes an exact fallback that also runs
on the matrix multiplier: Ozaki-I with all `s²` slice products once nothing is
left over ([`ozaki1Full_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/Ozaki/Correct.lean#L473)).

```lean
theorem tcOzaki1CRD_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a)
    (hlen : x.length = y.length) :
    tcOzaki1CRD p b ss smax x y = rne64 (dot x y)
```

This is correctly rounded FP64 GEMM on fp16, bf16 or tf32 Tensor Cores for
binary64 inputs of any length ([`tcOzaki1CRD_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/LongDot.lean#L209)), and the same holds on AMD
Matrix Cores ([`mcOzaki1CRD_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiMC/LongDot.lean#L120)) and for binary32 ([`tcOzaki1CRL_eq`](https://github.com/pauljiang03/HardwarePrimitives/blob/main/wip/ozaki/OzakiTC/LongDot.lean#L150)). The
whole pipeline also runs in fixed-width integer registers, with one theorem
bounding every register, and with IEEE special values. All of it is on the
[correct rounding](/HardwarePrimitives/ozaki/correct-rounding/) page.

## What is checked

- **Against the Z3 models.** On their two test cases the Lean pipelines return
  the same binary32 words as the unmodified Z3 models on the V100, A100 and
  H100 fp16 and all tf32 variants, and on the AMD SFMA, CDNA 1, 2 and 3 fp16
  and CDNA 3 XF32 variants, by kernel evaluation.
- **Against exact arithmetic.** The correctly rounded variants return the words
  an independent Python script computes with exact fractions: on the Z3
  matrices, a product with heavy cancellation, a product exactly halfway
  between two binary32 values, and random binary64 products with `k = 8`
  (FP64 emulation with split-K) on V100 and CDNA 3.
- **Accuracy.** Four slices are at least as accurate as one on the Z3 matrices
  (`[M.2]`), and every error the Z3 models print is reproduced.
- **Axioms.** An audit confirms every theorem uses only `propext`,
  `Classical.choice` and `Quot.sound`.

## What the proof assumes

- **The hardware models.** The theorems are about the Tensor Core and
  Matrix Core models; that GPUs behave like them rests on the models'
  [validation](/HardwarePrimitives/tensor-core/validation/).
- **The matrix multiplier's conditions.** Slices fit the input format (`b ≤ 11` for fp16
  and tf32, `b ≤ 8` for bf16) and `2b ≤ F`; with split-K, chunks of
  `2^(24 − 2b)` terms.
- **Off the matrix multiplier.** The slicing, the rounding test, the exact
  fallback and the final rounding are one integer function, with one theorem bounding every
  register ([correct rounding](/HardwarePrimitives/ozaki/correct-rounding/)). The binary32
  σ-trick is proven only for grids in `[2^-149, 2^104]`; the integer slicing
  covers every grid.
- **TensorCore's rounding.** The schemes and the σ-trick round with IEEE's
  round to nearest even. TensorCore's own rounding agrees with it up to the
  largest finite value and returns nothing above it; no result depends on
  that.
- **Not covered.** FP8 variants, NaN payloads, and the dispatch heuristics of
  production libraries.
