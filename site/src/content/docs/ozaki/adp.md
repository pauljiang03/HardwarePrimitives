---
title: ADP and ESC
description: NVIDIA's Automatic Dynamic Precision for FP64 emulation on INT8 matrix multipliers, formalized in Lean - its slice encoding, the exponent span capacity, the Grade-A guarantee for the whole routine, a subnormal counterexample and a guardrail that fixes it, and a correctly rounded version.
---

ADP (Schwarz et al., NVIDIA, arXiv:2511.13778) is the scheme behind FP64
emulation in cuBLAS. It runs Ozaki-I on INT8 matrix multipliers and adds guardrails: it
estimates from the inputs' exponents how many slices full FP64 accuracy needs
(the exponent span capacity, ESC), and falls back to native FP64 when the
inputs contain Inf or NaN or emulation would not pay off. The Lean development
follows a Z3 model of the routine step by step. Every result below uses only
Lean's standard axioms.

## The routine

1. **Scan** for Inf and NaN; if any, use native FP64 ([`adp_nonfinite_iff`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADP.lean#L487)).
2. **ESC.** From the exponents, estimate the span between the largest possible
   product and the largest actual one; a coarsened, blockwise estimate keeps it
   cheap. If it is unbounded, use native FP64.
3. **Width and slices.** Fixed-point width `W = 53 + ESC + 1`, and the fewest
   byte slices that hold `W` bits ([`Ozaki.TC.adpWidth`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADP.lean#L251),
   [`Ozaki.TC.slicesNeeded_spec`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADP.lean#L298)).
4. **Speed heuristic.** If `s²` INT8 products would cost more than native
   FP64, use native FP64.
5. **Emulate.** Convert each row and column to `W`-bit fixed point, cut the
   integers into signed bytes, multiply all `s²` slice pairs on the INT8
   matrix multiplier, recombine exactly, and round once to binary64.

## The encoding and the matrix multiplier

| Fact | Lean |
| --- | --- |
| Fixed point: `0 ≤ a 2^s − N < 1` and `N ∈ [−2^W, 2^W)`. | [`fixed_floor`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADPError.lean#L103), [`fixed_range`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADPError.lean#L110) |
| The unsigned-slice remap reconstructs every integer, and its slices are signed bytes exactly on its range; a remapped digit keeps the unsigned digit's bit pattern. | [`remap_value`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADP.lean#L109), [`remap_s8`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADP.lean#L156), [`remap_bit_pattern`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADP.lean#L167) |
| `53`-bit integers need `8` naive signed slices but `7` remapped ones; the remap range is slightly smaller than the prototype's. | [`slices_53`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADP.lean#L190), [`remap_range_smaller`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADP.lean#L171) |
| INT8 × INT8 → INT32 is exact on byte operands; a 16-bit register wraps. | [`int8Dot_bytes`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/Int8.lean#L48), [`int8Dot_16_wraps`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/Int8.lean#L53) |
| The `s²` slice products, weighted by `256^(t+u)`, add up to the fixed-point product, so the emulated result is one binary64 rounding of it. | [`slice_recombination`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADP.lean#L490), [`int8Ozaki_eq`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/Int8.lean#L103) |

The INT8 matrix multiplier here is a 32-bit wrapping register (`TensorCore`'s fixed-width
accumulator) over exact integer products, not a model of an INT8 Tensor Core
instruction.

## ESC and accuracy

| Fact | Lean |
| --- | --- |
| The coarsened estimate never exceeds the exact one when zeros have exponent `−∞`, for any block size; skipping zeros, or giving them the subnormal exponent, can break it. | [`coarseEst_le`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADP.lean#L364), [`skipZeros_unsafe`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADP.lean#L387), [`field0_unsafe`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADP.lean#L394) |
| The coarsened ESC is at least the exact ESC, and the matrix ESC at least every entry's. | [`escCoarse_ge`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADPError.lean#L387), [`Ozaki.TC.matrixEsc_ge`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADP.lean#L338) |
| Full fidelity: with `W = 53 + ESC + 1`, both factors of the largest product convert exactly. | [`full_fidelity`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADP.lean#L402) |
| Each product's fixed-point error is at most `2^(F−52)`, where `F` is the exponent of the largest product. | [`term_bound`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADPError.lean#L197) |
| The fixed-point product is within `k 2^(F−52)` of `x · y`. | [`fixedPoint_error`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADPError.lean#L289) |

From these, Lean proves the paper's Grade-A guarantee, a componentwise bound
`f(k) u |A||B|` with `f` linear, which the paper establishes by experiment; the
constant `f(k) = 4k + 1` is the Z3 model's ([`emulated_gradeA`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADPError.lean#L562)):

```lean
theorem emulated_gradeA {rnd : ℚ → Option ℚ} {η : ℚ} (hr : RoundWithin rnd (2 ^ (-53 : ℤ)) η)
    {n : ℕ} {x y : List ℚ} (hlen : x.length = y.length)
    (hx : ∀ a ∈ x, OnGrid64 a) (hy : ∀ b ∈ y, OnGrid64 b)
    (hnx : ∀ a ∈ x, Normal64 a) (hny : ∀ b ∈ y, Normal64 b) {c W : ℤ}
    (hc : escCoarse n x y = some c) (hW : 54 + c ≤ W) (hk : 2 * (x.length : ℚ) * 2 ^ (-53 : ℤ) ≤ 1)
    {C : ℚ} (hC : rnd (fixedProduct W x y) = some C) :
    Rat.abs (C - dot x y) ≤
      (4 * x.length + 1) * 2 ^ (-53 : ℤ) * ((List.zipWith (· * ·) x y).map Rat.abs).sum + η
```

For the whole routine: whenever it returns values on normal or zero entries
of matching shapes with `k · 2^14 < 2^31`, every entry meets Grade A on the
emulated path and the classical `γₖ` bound on the native path
([`adp_accuracy`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADP.lean#L574), [`nativeEntry_error`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADP.lean#L434)).

## Findings

- **From the Z3 model**, now proved in general: zeros must have exponent `−∞`
  in the coarsened ESC; the remap range is slightly smaller than the unsigned
  range; the `+1` in `W` buys one bit in the funnel; the Inf/NaN scan must come
  before ESC. The coarsening theorem holds for every block size, and the funnel
  bound does not need the Z3 query's assumption `e_a + e_b ≤ F`.
- **Grade A needs no `u²` term:** full fidelity makes the largest product
  exact, so each product's error is half what the Z3 check allows.
- **Subnormal inputs break Grade A.** With `x = [2^-1074, 2^-1023 × 7]` and
  `y = [1, −2^-60 × 7]`, the routine emulates and returns `−2^-1074` for a
  positive exact product. The exponent clamp at `−1022` lets `2^F` exceed the
  largest product by up to `2^52`. The Z3 model of ADP fails its own
  final-rounding check on the same input, and no guardrail catches it. This
  concerns the routine as the paper describes it, which the paper and the
  cuBLAS documentation say is accurate for subnormal values too. Shipping
  cuBLAS is not modeled: it passes Demmel et al.'s underflow test (2026),
  detecting the wide range and using its FP64 path, much as the guardrail
  below does.
- **One more guardrail fixes it.** `adpSafe` sends inputs with a nonzero
  entry below `2^-1022` to native FP64. With it, Grade A holds with no
  normality hypothesis ([`adpSafe_accuracy`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPFix.lean#L95)); on the counterexample it returns
  the correctly rounded `2^-1074`, and on the five recorded Z3 cases it returns
  what `adp` returns.
- **The routine returns values.** For finite inputs of matching shapes whose
  products are within range, `adp` (on normal or zero entries) and `adpSafe`
  (on any) return values, never Inf or NaN ([`adp_isSome`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPFix.lean#L374),
  [`adpSafe_isSome`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPFix.lean#L408)).
- **The zero policy matters for the whole routine, not only the estimate.**
  The Z3 model stops its unsafe zero policies with an assertion. Without it,
  "skip zeros" fails for every block size of at least `2` and every length
  in range: a row `(2^a, 1, 0, …)` against a column `(0, 2^d, 0, …)` emulates
  with an estimate below the exact one and returns `0` for the product `2^d`
  ([`adpPolicy_skip_wrong`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPZeroPolicyGeneral.lean#L465)); giving zeros exponent `−1022` fails likewise
  ([`adpPolicy_field0_wrong`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPZeroPolicyGeneral.lean#L486)). With block size `1` skipping is safe
  ([`escCoarsePolicy_skip_one`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPZeroPolicyGeneral.lean#L260)), and the `−∞` policy is `adp` itself
  ([`adpPolicy_negInf`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPZeroPolicy.lean#L77)). The failure holds for every matrix shape: zero
  rows and columns never change the estimate, so padding the counterexample
  keeps it ([`adpPolicy_skip_wrong_shape`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPZeroPolicyShapes.lean#L260)). Other rows hide it only by raising
  the matrix estimate. An entry meets Grade A when the estimate covers its own
  exponent span ([`adpPolicy_entry_gradeA`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPZeroPolicyIff.lean#L123)), and fails for some input with
  the same exponents when a factor loses more than about `log₂((8k + 4)k)`
  bits ([`adpPolicy_unmasked_fails_left`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPZeroPolicyIff.lean#L810)); with sharper conditions,
  every input of an exponent pattern meets Grade A when each factor loses at
  most about `log₂(2k)` bits ([`adpPolicy_entry_gradeA_loss`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPZeroPolicyGap.lean#L297)), some input
  breaks it from about `log₂(2k + 2)` bits ([`adpPolicy_unmasked_fails_full_left`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPZeroPolicyGap.lean#L638)),
  and one pattern can admit both outcomes ([`adpPolicy_pattern_undecided_left`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPZeroPolicyGap.lean#L703)). An unsafe run whose estimate is at least the
  safe one meets Grade A ([`adpPolicy_masked_gradeA`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPZeroPolicyShapes.lean#L296)).

## Correctly rounded

ADP rounds once, but it rounds the fixed-point product, which differs from
`x · y` where the conversion drops bits. The rounding test of the other
schemes applies: `H` is the exactly recombined fixed-point product, `B` the
fixed-point bound, and if `H ± B` round to the same value, so does `x · y`;
otherwise a wider configuration, then the exact product ([`adpCR_eq`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/Correct.lean#L255)). On two
random binary64 test cases the rounding test succeeds on every entry at the
slice count
ADP's own ESC rule picks (`8` and `11` slices), so correct rounding costs no
extra INT8 products there. This version takes the `(s, W)` configurations as
given; it is not the ESC-driven routine with its guardrails, and its last
resort is exact rational arithmetic, not the matrix multiplier.

`adpCRE` runs every product on the INT8 matrix multiplier. The matrix
multiplier is split into chunks so that INT32 never wraps, which makes it exact on `6`-bit slices for
every length ([`int8SplitK_exactOn`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPFix.lean#L141)). The fixed-point enclosures run on it,
and so does the exact fallback: Ozaki-I with all slice products of `6`-bit
slices, which leaves nothing over after `300` slices for binary64 inputs. The
result is the IEEE binary64 round to nearest of `x · y` for binary64 inputs
of any length ([`adpCRE_eq`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPFix.lean#L226)). On the subnormal counterexample the enclosure
of `8` slices does not decide it, and the exact fallback returns `2^-1074`.

The whole correctly rounded version also runs as one integer function from
`(significand, exponent)` inputs: integer fixed-point conversion, byte slices
on the INT8 matrix multiplier, an integer rounding test and the exact
fallback in fixed-width registers, with one theorem bounding every register ([`adpCRJ_eq`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPIntJ.lean#L34),
[`adpCRJS_eq`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPIntJ.lean#L60) with signed zeros, [`adpCRJC_eq`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPChecked.lean#L434); see
[correct rounding](/MMAlgebra/ozaki/correct-rounding/)).

## What is checked

On five cases recorded from the Z3 model (uniform and signed inputs, Test 2
with `b = 2` and `b = 64`, and an input with an infinity), the Lean routine
takes the same path and returns the same values, with the same ESC, `W` and
slice count on the emulated cases.

Every test-level check of the Z3 model that concerns ADP itself is a theorem
or a kernel-checked test on the model's own inputs:
- decoding, including both zeros;
- the paper's remap example ([`Ozaki.ADP.paper_remap_example`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADPEncodings.lean#L312));
- the three slice encodings agreeing ([`encodings_agree`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPLabels.lean#L126));
- ESC with block size `1` ([`escCoarse_one`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADPEncodings.lean#L353));
- the valid paths ([`adp_finite_path`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPLabels.lean#L283));
- emergent overflow ([`emulEntry_none_iff`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPLabels.lean#L298));
- subnormal inputs;
- the zero policies ([`zeros_case_caught`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADPEncodings.lean#L383)).

The naive signed-byte encoding is proved too ([`naiveDigits_s8`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/Ozaki/ADPEncodings.lean#L110)). The two
remaining checks test the Z3 model's own harness.

**Infinities and NaN.** `adp` returns no values where a result is not finite.
`adpIEEE` runs the same routine on IEEE data. Words decode exactly as IEEE
classifies them ([`decodeF64_inf_iff`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPIEEE.lean#L92), [`decodeF64_nan_iff`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPIEEE.lean#L77)). The
non-finite path is native FP64 with IEEE operations
([`adpIEEE_nonfinite`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPIEEE.lean#L285)), and an emulated result that overflows is `±Inf`.
Wherever `adp` returns values, it returns the same ones ([`adpIEEE_agrees`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/ADPIEEE.lean#L300)).
On the Z3 model's cases with an infinity, a NaN and an emulated overflow, it
returns the Z3 model's words.

## What the proof assumes

- **INT8 hardware semantics are out of scope for now**, on both vendors
  ([issue #2](https://github.com/pauljiang03/MMAlgebra/issues/2)). The INT8
  matrix multiplier is the arithmetic of a wrapping INT32 register over exact integer
  products. Its result is the exact sum modulo `2^32` in every accumulation
  order, and a saturating register agrees with it on ADP's operands
  ([`int8Dot_any_order`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/Int8Semantics.lean#L76), [`int8_wrap_sat_exact`](https://github.com/pauljiang03/MMAlgebra/blob/main/ozaki/OzakiTC/Int8Semantics.lean#L135)). Neither hardware model
  has an INT8 instruction, and nothing is validated against INT8 hardware.
- The routine follows the Z3 model of the paper, not cuBLAS's implementation.
- Grade A is proved for `adp` on normal or zero entries and for `adpSafe` on
  all entries, with an underflow term; cuBLAS's own handling of subnormal
  inputs is not modeled.
