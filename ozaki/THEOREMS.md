# What is proven

This page lists the main results that Lean has checked, in plain language, with the label of the
matching check in the Z3 models where there is one
(`[Z.n]` for a Z3 proof, other labels for runtime assertions). Labels refer to `ozaki1/` in the
Ozaki-I sections, `ozaki2/` in the Ozaki-II sections, and `ozaki-NVIDIA/` in the ADP section; in
the hardware sections they carry a prefix `I:`, `II:` or `ADP:`. The linked file has the exact
statement and every assumption. Every theorem depends only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`); both test libraries audit this. Every named declaration,
with `TensorCore`, `MatrixCore` and the tests, is also re-checked by the external checker
[con-leche](https://github.com/leanprover/con-leche) in `--verified` mode
([`scripts/conleche.sh`](scripts/conleche.sh); the README has the counts).

A Z3 runtime assertion checks one fact on the test matrices; the Lean theorem states it for every
input. A Z3 lemma is proved for one format or exponent range; the Lean theorem is stated for the
general case where that costs nothing.

Several sections go beyond the Z3 models: [correct rounding](#correct-rounding), with its
[fixed-width integer arithmetic](#fixed-width-integer-arithmetic) and
[IEEE special values](#ieee-rounding-special-values-and-signed-zeros);
[long dot products, FP64 and error bounds](#long-dot-products-fp64-and-error-bounds); and the
[ADP pipeline](#the-adp-pipeline-on-the-int8-matrix-multiplier) with its Grade-A guarantee. The
[last section](#not-proved) lists what is not proved.

## The schemes, independent of the hardware

### Ozaki-I: slicing

| What it says | Z3 | Lean name | File |
| --- | --- | --- | --- |
| The slices and the residual add up to the vector exactly, against every `y`. | `[S1.13]` | `Ozaki.split_dot` | [Ozaki/Split.lean](Ozaki/Split.lean) |
| Every slice coefficient is an integer of magnitude at most `2^b`. | `[S1.9]`, `[S1.10]` | `Ozaki.split_coeff_bound` | [Ozaki/Split.lean](Ozaki/Split.lean) |
| Slice `t` lies on a grid at least `t (b + 1)` bits below the first; the residual after `s` slices is at most `2^(E − s(b+1))`. | `[S1.12]` | `Ozaki.split_grid_le`, `Ozaki.split_residual_le` | [Ozaki/Split.lean](Ozaki/Split.lean) |
| `E = ⌈log₂ max\|x\|⌉`, so `2^(E−1) < max\|x\| ≤ 2^E`. | `[H.3]` | `Ozaki.splitExp_spec` | [Ozaki/Split.lean](Ozaki/Split.lean) |

### Ozaki-I: products and recombination

| What it says | Z3 | Lean name | File |
| --- | --- | --- | --- |
| With `s` slices there are `s (s + 1) / 2` slice products. | `[S3.1]` | `Ozaki.trianglePairs_length` | [Ozaki/Ozaki1.lean](Ozaki/Ozaki1.lean) |
| With a matrix multiplier exact on `b`-bit slices, Ozaki-I adds exactly the scaled exact slice products. | `[S2.1]` | `Ozaki.ozaki1_eq_sumWith` | [Ozaki/Ozaki1.lean](Ozaki/Ozaki1.lean) |
| A slice product has magnitude at most `k 2^(2b)`, which is `2^24` in the Z3 configuration. | `[S2.2]` | `Ozaki.slice_product_bound`, `Ozaki.z3_slice_product_bound` | [Ozaki/Checks.lean](Ozaki/Checks.lean) |
| Error identity: `x · y − Σ terms = r · y + Σₜ 2^gₜ (qₜ · r'ₛ₋ₜ)`, where `r'ₖ` is the residual of `y` after `k` slices. | `[S3.4]` | `Ozaki.dot_eq_exactTerms_add` | [Ozaki/Ozaki1.lean](Ozaki/Ozaki1.lean) |
| The slicing error is at most `(s + 1) k 2^(E + F − s(b+1))`, and at most `4 (s + 1) k max\|x\| max\|y\| 2^(−s(b+1))`. | | `Ozaki.exactTerms_error`, `Ozaki.exactTerms_error_normwise` | [Ozaki/Ozaki1.lean](Ozaki/Ozaki1.lean) |
| `n` additions with relative error `u` and absolute error `η` lose at most `((1 + u)^n − 1) Σ\|tⱼ\| + n (1 + u)^n η`. | `[S3.3]` | `Ozaki.sumWith_error` | [Ozaki/Summation.lean](Ozaki/Summation.lean) |
| The whole of Ozaki-I: the result is within the recombination bound plus the slicing bound of `x · y`. | | `Ozaki.ozaki1_error` | [Ozaki/Ozaki1.lean](Ozaki/Ozaki1.lean) |
| Ozaki-I returns a value (never Inf or NaN) when the sum of the scaled products and its rounding errors stays within the format's range. | `[H.1]` | `Ozaki.ozaki1_isSome`, `Ozaki.sumWith_isSome` | [Ozaki/Success.lean](Ozaki/Success.lean) |
| Native GEMM (products rounded, then added left to right) is within `γₖ Σ\|xᵢyᵢ\|` plus a subnormal term, `γₖ = k u / (1 − k u)`. | `[M.1]`, `ADP:[N.1]` | `Ozaki.nativeDot_error`, `Ozaki.nativeDot_error_gamma` | [Ozaki/Native.lean](Ozaki/Native.lean) |

### Ozaki-II

| What it says | Z3 | Lean name | File |
| --- | --- | --- | --- |
| The scaled, truncated integers have magnitude at most `2^P`. | `[S1.3]`, `[S1.4]` | `Ozaki.scaleTrunc_bound` | [Ozaki/Ozaki2.lean](Ozaki/Ozaki2.lean) |
| The scaled row maximum lies in `(2^(P−1), 2^P]`. | `[S1.1]`, `[H.4]` | `Ozaki.scaleShift_spec`, `Ozaki.ceilLog2_spec` | [Ozaki/Checks.lean](Ozaki/Checks.lean), [Ozaki/Rounding.lean](Ozaki/Rounding.lean) |
| Truncation loses less than one and never increases the magnitude; the truncated product is at most `k 2^(2P)`. | `[S1.5]`, `[S1.6]` | `Ozaki.truncInt_spec`, `Ozaki.natAbs_truncProduct_le` | [Ozaki/Rounding.lean](Ozaki/Rounding.lean), [Ozaki/Checks.lean](Ozaki/Checks.lean) |
| A residue product is at most `k ⌊m/2⌋²`. | `[S3.2]` | `Ozaki.natAbs_residueProduct_le` | [Ozaki/Checks.lean](Ozaki/Checks.lean) |
| Symmetric residues lie in `(−m/2, m/2]`, and products of residues are congruent to the product. | `[H.5]`, `[S3.3]` | `Ozaki.symMod_bounds`, `Ozaki.dvd_dotZ_symMod` | [Ozaki/CRT.lean](Ozaki/CRT.lean), [Ozaki/Ozaki2.lean](Ozaki/Ozaki2.lean) |
| CRT reconstruction with any valid basis returns every `c` with `−M < 2c ≤ M` from residues congruent to it. | `[Z.4]`, `[S4.3]` | `Ozaki.crt_eq` | [Ozaki/CRT.lean](Ozaki/CRT.lean) |
| The reconstruction matches every residue: `mⱼ ∣ crt B rs − rⱼ`. | `[S4.2]` | `Ozaki.crt_dvd_sub` | [Ozaki/Checks.lean](Ozaki/Checks.lean) |
| With a matrix multiplier exact on `b`-bit residues and `2 k 2^(2P) < M`, Ozaki-II is one rounding of the truncated product. | `[S4.3]` | `Ozaki.ozaki2_eq` | [Ozaki/Ozaki2.lean](Ozaki/Ozaki2.lean) |
| Truncation error `\|x · y − 2^(−sₓ−s_y) (a · c)\| ≤ Σᵢ (2^(−sₓ)\|yᵢ\| + 2^(−sₓ−s_y)\|aᵢ\|)`, at most `8 k max\|x\| max\|y\| 2^(−P)`. | `[S5.1]` | `Ozaki.truncProduct_error`, `Ozaki.truncProduct_error_normwise` | [Ozaki/Ozaki2.lean](Ozaki/Ozaki2.lean) |
| The whole of Ozaki-II: one rounding plus the truncation bound. | | `Ozaki.ozaki2_error` | [Ozaki/Ozaki2.lean](Ozaki/Ozaki2.lean) |
| Ozaki-II returns a value when `k 2^((P−sₓ)+(P−s_y))` is within range. | `[H.1]` | `Ozaki.ozaki2_isSome` | [Ozaki/Success.lean](Ozaki/Success.lean) |

### The Z3 models' parameters

| What it says | Z3 | Lean name | File |
| --- | --- | --- | --- |
| Four products of `11`-bit integers total at most `2^24`. | `[M.0]` | `Ozaki.z3_slice_exactnessBound` | [Ozaki/Parameters.lean](Ozaki/Parameters.lean) |
| The computed weights for `{4096, 4095, 4093, 4091}` form a valid CRT basis. | `[S0.1]`, `[S0.2]`, `[S4.1]` | `Ozaki.z3Basis_valid` | [Ozaki/Parameters.lean](Ozaki/Parameters.lean) |
| `P = 22` is the largest precision with `2 k 2^(2P) < M`. | `[S0.3]`, `[S0.4]` | `Ozaki.z3_bits` | [Ozaki/Parameters.lean](Ozaki/Parameters.lean) |
| `k ⌊m/2⌋² ≤ 2^24` for the Z3 moduli. | `[S0.5]` | `Ozaki.z3_residue_exactnessBound` | [Ozaki/Checks.lean](Ozaki/Checks.lean) |
| At `P = 23`, `c = M` is within reach and reconstructs as `0`. | `[Z.5]` | `Ozaki.crt_fails_at_23` | [Ozaki/Parameters.lean](Ozaki/Parameters.lean) |

### ADP and ESC (INT8 matrix multipliers)

| What it says | Z3 | Lean name | File |
| --- | --- | --- | --- |
| The unsigned-slice remap reconstructs every integer. | `[U.5]` | `Ozaki.ADP.remap_value` | [Ozaki/ADP.lean](Ozaki/ADP.lean) |
| Remapped slices are signed bytes exactly on `[−128 (256^s − 1)/255, 127 (256^s − 1)/255]`. | `[Z.3]` | `Ozaki.ADP.remap_s8` | [Ozaki/ADP.lean](Ozaki/ADP.lean) |
| A remapped digit keeps the unsigned digit's bit pattern. | `[Z.5]` | `Ozaki.ADP.remap_bit_pattern` | [Ozaki/ADP.lean](Ozaki/ADP.lean) |
| The remap range is smaller than the prototype's: `2^23 − 129` fits three floor/u8 slices but not three remapped ones. | `[Z.4]` | `Ozaki.ADP.remap_range_smaller` | [Ozaki/ADP.lean](Ozaki/ADP.lean) |
| `53`-bit integers need `8` naive signed slices and `7` remapped ones. | `[T.3]` | `Ozaki.ADP.slices_53` | [Ozaki/ADP.lean](Ozaki/ADP.lean) |
| The naive signed-byte encoding: for `\|N\| < 128^s` its digits lie in `[−127, 127]` and `Σ dₜ 128^t = N`; a width that fits naive slices fits remapped ones. | `[U.6]`, `[T.3]` | `Ozaki.ADP.naiveDigits_s8`, `Ozaki.ADP.naiveFits_remapFits` | [Ozaki/ADPEncodings.lean](Ozaki/ADPEncodings.lean) |
| The three encodings (remap, floor/u8, naive s8): each has `s` digits of magnitude at most `255` and reconstructs every integer in its range, and the slice products of any of them, weighted by its base, add up to the fixed-point product. | `[T.4]` | `Ozaki.ADP.SliceEncoding.digits_value`, `Ozaki.ADP.SliceEncoding.digits_natAbs_le`, `Ozaki.ADP.slice_recombination_with` | [Ozaki/ADPEncodings.lean](Ozaki/ADPEncodings.lean) |
| The paper's remap example: floor digits `[200, 123]` become `[−56, 124]`, and `−56` has the bit pattern of `200`. | `[T.2]` | `Ozaki.ADP.paper_remap_example` | [Ozaki/ADPEncodings.lean](Ozaki/ADPEncodings.lean) |
| With block size `1` the coarsened estimate is the exact one, so the coarsened ESC is the exact ESC. | `[T.5]` | `Ozaki.ADP.coarseEst_one`, `Ozaki.ADP.escCoarse_one` | [Ozaki/ADPEncodings.lean](Ozaki/ADPEncodings.lean) |
| On the Z3 model's own zero-policy rows, skipping zeros or giving them exponent `−1022` violates `[X.4]`, and the `−∞` policy does not. | `[T.12]` | `Ozaki.ADP.zeros_case_caught`, `Ozaki.ADP.field0_case_caught` | [Ozaki/ADPEncodings.lean](Ozaki/ADPEncodings.lean) |
| The coarsened estimate never exceeds the exact `exp(z_r)` when zeros have exponent `−∞`, for any block size. | `[Z.6]` | `Ozaki.ADP.coarseEst_le` | [Ozaki/ADP.lean](Ozaki/ADP.lean) |
| Skipping zeros, or giving them exponent `−1022`, can overestimate it. | `[Z.7]`, `[Z.8]` | `Ozaki.ADP.skipZeros_unsafe`, `Ozaki.ADP.field0_unsafe` | [Ozaki/ADP.lean](Ozaki/ADP.lean) |
| Full fidelity with `W = 53 + ESC + 1`, and also without the `+1`. | `[Z.9]`, `[Z.9b]` | `Ozaki.ADP.full_fidelity`, `Ozaki.ADP.full_fidelity_without_plus_one` | [Ozaki/ADP.lean](Ozaki/ADP.lean) |
| `\|ab − ãb̃\| ≤ δa\|b\| + \|ã\|δb`; with the `+1` each half is at most `2^(F−52)`, and without it that fails. | `[Z.10]`–`[Z.12]` | `Ozaki.ADP.term_error`, `Ozaki.ADP.funnel`, `Ozaki.ADP.funnel_needs_plus_one` | [Ozaki/ADP.lean](Ozaki/ADP.lean) |
| The `s²` slice products, weighted by `256^(t+u)`, add up to the fixed-point product. | `[R.1]` | `Ozaki.ADP.slice_recombination` | [Ozaki/ADP.lean](Ozaki/ADP.lean) |
| Floor digits: the low digits are unsigned bytes, the lead digit a signed byte, and they reconstruct `N`. | `[U.1]`, `[U.2]` | `Ozaki.ADP.floorDigits_bytes`, `Ozaki.ADP.floorDigits_value` | [Ozaki/ADPError.lean](Ozaki/ADPError.lean) |
| A nonzero binary64 value lies in `[2^e, 2^(e+1))` for its exponent `e` (normals). | `[D.2]` | `Ozaki.ADP.abs_lt_exp64`, `Ozaki.ADP.exp64_le_abs` | [Ozaki/ADPError.lean](Ozaki/ADPError.lean) |
| Fixed point: `0 ≤ a 2^s − N < 1`, `N ∈ [−2^W, 2^W)`, and on-grid entries convert exactly. | `[F.1]`, `[F.2]` | `Ozaki.ADP.fixed_floor`, `Ozaki.ADP.fixed_range`, `Ozaki.ADP.fixed_exact` | [Ozaki/ADPError.lean](Ozaki/ADPError.lean) |
| Both factors of a dominant product convert exactly (full fidelity on the data). | `[F.3]` | `Ozaki.ADP.dominant_exact` | [Ozaki/ADPError.lean](Ozaki/ADPError.lean) |
| Each product's fixed-point error is at most `2^(F−52)` (the Z3 check allows `2^(F−51)`). | `[F.4]` | `Ozaki.ADP.term_bound` | [Ozaki/ADPError.lean](Ozaki/ADPError.lean) |
| The exact ESC is attained, is at least `0`, and the coarsened ESC is at least the exact one. | `[X.1]`, `[X.2]`, `[X.5]` | `Ozaki.ADP.fExact_attained`, `Ozaki.ADP.fExact_le`, `Ozaki.ADP.escCoarse_ge` | [Ozaki/ADPError.lean](Ozaki/ADPError.lean) |
| Block representatives bound every member. | `[X.3]` | `Ozaki.ADP.blockRep_bounds` | [Ozaki/ADPError.lean](Ozaki/ADPError.lean) |
| The fixed-point product is within `k 2^(F−52)` of `x · y`, on ADP's own shifts and coarsened ESC. | `[P.1]` | `Ozaki.ADP.fixedPoint_error`, `Ozaki.ADP.fixedProduct_error` | [Ozaki/ADPError.lean](Ozaki/ADPError.lean) |
| **Grade A.** After one rounding, `\|C − x · y\| ≤ (4k + 1) 2^-53 Σ\|xᵢyᵢ\| + η`, for normal or zero entries and `2ku ≤ 1`. Subnormal entries can violate it (see the README's findings). | `[P.2]` | `Ozaki.ADP.emulated_gradeA` | [Ozaki/ADPError.lean](Ozaki/ADPError.lean) |

## Correct rounding

Each scheme holds an exact value `H` before its last rounding and a proved bound `B ≥ |x · y − H|`.
If `H − B` and `H + B` round to the same value, so does `x · y`; otherwise more slices or moduli are
tried, then an exact fallback. This is Ziv's rounding test. No Z3 model has a counterpart. `ozaki1CR`
and `ozaki2CR` fall back to the exact rational `x · y`, so their theorems would hold without the
matrix multiplier; the `CRE` versions take the exact fallback on the matrix multiplier. The monotonicity of rounding to nearest is classical (Flocq's
`Rnd_N_pt_monotone`); it is proved here for the framework.

### The rounding test and the exact fallback

| What it says | Lean name | File |
| --- | --- | --- |
| Rounding to nearest is monotone; this needs only that results are nearest values, not the tie rule. | `Ozaki.round_monotone` | [Ozaki/Correct.lean](Ozaki/Correct.lean) |
| If `\|v − H\| ≤ B` and both `H ± B` round to `w`, then `v` rounds to `w`. | `Ozaki.round_eq_of_enclosure` | [Ozaki/Correct.lean](Ozaki/Correct.lean) |
| Trying enclosures in turn and then the exact value returns the rounding of the exact value. | `Ozaki.roundingTest_eq` | [Ozaki/Correct.lean](Ozaki/Correct.lean) |
| `\|x · y − x' · y'\| ≤ max\|x − x'\| Σ\|y\| + max\|y − y'\| Σ\|x'\|`. | `Ozaki.dot_approx_error` | [Ozaki/Correct.lean](Ozaki/Correct.lean) |
| Ozaki-I and Ozaki-II, correctly rounded, on any matrix multiplier exact on their slices or residues. | `Ozaki.ozaki1CR_eq`, `Ozaki.ozaki2CR_eq` | [Ozaki/Correct.lean](Ozaki/Correct.lean) |
| Inputs on a grid `2^m` leave nothing over once the slicing bound is below `2^m`; with nothing left over, Ozaki-I with all `s²` slice products is exact. | `Ozaki.split_residual_zero`, `Ozaki.ozaki1Full_eq` | [Ozaki/Correct.lean](Ozaki/Correct.lean) |
| Correctly rounded Ozaki-I and Ozaki-II whose exact fallback also runs on the matrix multiplier (Ozaki-I with all `s²` slice products). | `Ozaki.ozaki1CRE_eq`, `Ozaki.ozaki2CRE_eq` | [Ozaki/Correct.lean](Ozaki/Correct.lean) |
| **What the rounding test achieves:** on an enclosure the test succeeds whenever `x · y − 2B` and `x · y + 2B` round to the same value, in particular whenever `x · y` is more than `2B` from every rounding boundary (at exactly `2B` an endpoint can be a tie that rounds the other way); for Ozaki-I with its slicing bound. | `Ozaki.roundEnclosure_of_margin`, `Ozaki.ozaki1Enclosure_succeeds` | [Ozaki/Correct.lean](Ozaki/Correct.lean) |
| **Slice counts that grow with `k`.** The first test at the slice count for precision `t + ⌈log₂ k⌉` has a bound at most `max\|x\| max\|y\| 2^-t`, with no factor `k`; the schemes using this rule are correctly rounded, with exact sums, truncated sums and integers, on both vendors. | `Ozaki.slicesForCR`, `Ozaki.ozaki1Bound_le_cr`, `Ozaki.ozaki1Bound_le_cr_rel`, `Ozaki.ozaki1CRK_eq`, `Ozaki.ozaki1CRIK_eq`, `Ozaki.TC.tcOzaki1CRDKA_eq`, `Ozaki.MC.mcOzaki1CRDKA_eq` | [Ozaki/SliceRuleCR.lean](Ozaki/SliceRuleCR.lean), [OzakiTC/CRRules.lean](OzakiTC/CRRules.lean), [OzakiMC/CRRules.lean](OzakiMC/CRRules.lean) |
| **The exact fallback first, when cheaper.** With the slice count of the exact fallback known after slicing (computed by integer operations too), the scheme takes the exact fallback directly when its `s²` products cost no more than the first test; it is correctly rounded, never costs more than the plain scheme, and costs only the exact fallback when the shortcut applies. | `Ozaki.exactCountI_eq`, `Ozaki.ozaki1CRA_eq`, `Ozaki.ozaki1CRIA_eq`, `Ozaki.ozaki1CRKA_eq`, `Ozaki.ozaki1CRA_cost_le`, `Ozaki.ozaki1CRA_cost_shortcut`, `Ozaki.creCost_first_succeeds` | [Ozaki/Adaptive.lean](Ozaki/Adaptive.lean) |
| **The rounding test succeeds at once on exact zeros.** The slicing bound counts only the positions where both entries are nonzero, never more than the normwise bound; the count is `0` exactly when every product is zero, and it is one exact dot product of 0/1 vectors on the matrix multiplier. With it, on an entry whose products are all zero the first test succeeds with `0` (and IEEE's zero sign), whatever the later tests or the fallback would return; versions with exact sums, truncated sums and fixed-width integers, on both vendors. | `Ozaki.exactTerms_error_overlap`, `Ozaki.supportOverlap_eq_zero_iff`, `Ozaki.overlapMultiplier_eq`, `Ozaki.truncatedSum_error_nonzero`, `Ozaki.ozaki1CREZ_eq`, `Ozaki.ozaki1CRWZ_eq`, `Ozaki.ozaki1TestBZ_eq`, `Ozaki.ozaki1CREZ_zero`, `Ozaki.ozaki1CRWSZ_eq`, `Ozaki.ozaki1CRWSZ_zero`, `Ozaki.TC.tcOzaki1CRDZ_eq`, `Ozaki.TC.tcOzaki1CRBDZ_eq`, `Ozaki.TC.tcOzaki1CRDSZ_eq`, `Ozaki.MC.mcOzaki1CRDZ_eq` | [Ozaki/ZeroCheck.lean](Ozaki/ZeroCheck.lean), [OzakiTC/ZeroCheck.lean](OzakiTC/ZeroCheck.lean), [OzakiMC/ZeroCheck.lean](OzakiMC/ZeroCheck.lean) |

### Fixed-width integer arithmetic

Everything after the matrix multiplier also runs in integer registers whose widths do not depend on the
inputs' exponents, and each integer form is proved equal to its rational counterpart.

| What it says | Lean name | File |
| --- | --- | --- |
| **Slicing with integer operations, for every grid.** A binary vector given as significands and exponents `(m, e)` is sliced with integer shifts, a round-half-even division and exponent arithmetic, and the result equals the scheme's split for every vector, slice count and grid. Every coefficient is at most `2^b`, the remaining significands never grow (below `2^24` for binary32, `2^53` for binary64), and a division never needs more than `p + 2` bits: the widths depend on the format and `b`, never on the exponents. | `Ozaki.rneShift_eq`, `Ozaki.gridInt_eq`, `Ozaki.coeffInt_eq`, `Ozaki.splitInt_eq`, `Ozaki.splitInt_width`, `Ozaki.shiftPow_le`, `Ozaki.split_binary32_int`, `Ozaki.split_binary64_int` | [Ozaki/SliceInt.lean](Ozaki/SliceInt.lean) |
| **The exact sum's register** (needed only by an exact fallback that adds the slice products exactly; the bounded one below does not): for inputs on a grid `2^m` the exact slice sum is `N · 2^(2(m−b))` with `\|N\| ≤ (s(s+1)/2) k 2^(E+F−2(m−b))`; for binary32 and `11`-bit slices about `580` bits. | `Ozaki.exactTerms_sum_register`, `Ozaki.exactTerms_sum_register32` | [Ozaki/Width.lean](Ozaki/Width.lean), [Ozaki/Exact64.lean](Ozaki/Exact64.lean) |
| **A two-word truncated sum suffices for the rounding test.** Each scaled slice product rounded down to `W` bits below the largest possible product and added exactly: within `n 2^q` of the exact sum, an integer multiple of `2^q` with `\|N\| ≤ (s(s+1)/2)(k 2^W + 1)`; correct rounding holds with it, on both vendors, for binary32 and FP64. | `Ozaki.truncatedSum_error`, `Ozaki.ozaki1CRW_eq`, `Ozaki.ozaki1Truncated_register`, `Ozaki.ozaki1TruncatedEnclosure_succeeds`, `Ozaki.TC.tcOzaki1CRDW_eq`, `Ozaki.TC.tcOzaki1CRLW_eq`, `Ozaki.TC.v100_fp64CRW`, `Ozaki.MC.mcOzaki1CRDW_eq`, `Ozaki.MC.mcOzaki1CRLW_eq` | [Ozaki/TruncatedSum.lean](Ozaki/TruncatedSum.lean), [OzakiTC/LongDot.lean](OzakiTC/LongDot.lean), [OzakiMC/LongDot.lean](OzakiMC/LongDot.lean) |
| **Bounded registers.** A `w`-bit two's-complement register adds a list exactly when the magnitudes total less than `2^(w−1)`. Round to nearest even of `N 2^q` by a few integer comparisons, for every `N` and `q`. The sign and the round to nearest even of a sum of terms `v 2^e` by a top-down summation over ranges of `W` bits, with ties, underflow and overflow, whenever `W > bitlen(n + 1) + p + 3`; the top-down summation visits at most `E − m + 1` ranges. | `Ozaki.fixedSum_eq`, `Ozaki.fixedSum_natAbs_le`, `Ozaki.roundExact_eq`, `Ozaki.roundByCmp_spec`, `Ozaki.signSum_eq`, `Ozaki.roundSum_eq`, `Ozaki.topDownSum_sound`, `Ozaki.topDownSum_parts_lt`, `Ozaki.query_natAbs_lt`, `Ozaki.topDownSumAll_fuel_le` | [Ozaki/Bounded.lean](Ozaki/Bounded.lean), [Ozaki/SignOracle.lean](Ozaki/SignOracle.lean) |
| **Correctly rounded Ozaki-I in bounded integer arithmetic.** The rounding test on a truncated sum in a register of `W + bitlen(n(k+2)) + 1` bits that never wraps, the exact fallback by the top-down summation with ranges of `bitlen(s² + 1) + p + 4` bits over terms at most the exactness bound of the matrix multiplier, and the final rounding by comparisons. Each equals its rational counterpart, so the scheme is correctly rounded, on both vendors, for binary32 and FP64 inputs of any length. | `Ozaki.ozaki1TestB_eq`, `Ozaki.ozaki1TestB_register`, `Ozaki.ozaki1ExactFallbackB_eq`, `Ozaki.ozaki1ExactFallbackB_terms`, `Ozaki.ozaki1CRB_eq_CRW`, `Ozaki.ozaki1CRB_eq`, `Ozaki.ozaki1CRB64_eq`, `Ozaki.ozaki1CRB32_eq`, `Ozaki.TC.tcOzaki1CRBD_eq`, `Ozaki.TC.tcOzaki1CRBL_eq`, `Ozaki.TC.v100_fp64CRB`, `Ozaki.MC.mcOzaki1CRBD_eq`, `Ozaki.MC.mcOzaki1CRBL_eq` | [Ozaki/BoundedOzaki.lean](Ozaki/BoundedOzaki.lean), [OzakiTC/Bounded.lean](OzakiTC/Bounded.lean), [OzakiMC/Bounded.lean](OzakiMC/Bounded.lean) |
| **A top-down summation that jumps empty gaps.** The top-down summation of the exact fallback starts each range at the top of the largest remaining term, decides the sign and the round to nearest even of the sum as before, and visits at most `n · bitlen(max \|v\|) + 1` ranges, whatever the exponents. | `Ozaki.topDownSumJ_sound`, `Ozaki.signSumJ_eq`, `Ozaki.roundSumJ_eq`, `Ozaki.rangesJ_le`, `Ozaki.exactFallback_ranges` | [Ozaki/TopDownSummation.lean](Ozaki/TopDownSummation.lean), [Ozaki/BoundedOzaki2J.lean](Ozaki/BoundedOzaki2J.lean) |
| **Correctly rounded Ozaki-I as one integer function**, from `(significand, exponent)` inputs: integer slicing, the matrix multiplier, the integer rounding test, the jumping exact fallback and the final rounding; equal to the bounded scheme, correctly rounded for binary32 and binary64 inputs, with IEEE signed zeros, on both vendors. | `Ozaki.ozaki1CRI_eq_CRB`, `Ozaki.ozaki1CRI_eq`, `Ozaki.ozaki1CRI64_eq`, `Ozaki.ozaki1CRI32_eq`, `Ozaki.ozaki1CRIS_eq`, `Ozaki.TC.tcOzaki1CRID_eq`, `Ozaki.TC.v100_fp64CRI`, `Ozaki.MC.mcOzaki1CRID_eq` | [Ozaki/BoundedInt.lean](Ozaki/BoundedInt.lean), [OzakiTC/Bounded.lean](OzakiTC/Bounded.lean), [OzakiMC/Bounded.lean](OzakiMC/Bounded.lean) |
| **Integer rounding tests for Ozaki-II and ADP.** The enclosure as `(N, q, K, q)`: `N` the CRT result or the recombined fixed-point product, and `K` a bound built from the scaled integers the matrix multiplier already multiplies; the integer test equals the rational one, and the schemes with it are correctly rounded. Widths: `2\|N\| ≤ M` and `K ≤ k(2^(P+1) + 1)` (Ozaki-II), `\|N\| ≤ k 2^(2W)` and `K ≤ k(2^(W+1) + 1)` (ADP). | `Ozaki.enclosureTestB_eq`, `Ozaki.roundingTestB_eq`, `Ozaki.ozaki2EnclosureB_sound`, `Ozaki.ozaki2CRB_eq`, `Ozaki.ozaki2EnclosureB_width`, `Ozaki.TC.adpEnclosureB_sound`, `Ozaki.TC.adpCRB_eq`, `Ozaki.TC.adpEnclosureB_width` | [Ozaki/BoundedOzaki2.lean](Ozaki/BoundedOzaki2.lean), [OzakiTC/ADPBounded.lean](OzakiTC/ADPBounded.lean) |
| **Integer input conversion.** Ozaki-II's scaling and truncation and ADP's fixed point as shifts of the significands, with the shift amounts from bit lengths; each equals the rational definition. | `Ozaki.truncShiftZ_eq`, `Ozaki.floorShiftZ_eq`, `Ozaki.scaleShiftZ_eq`, `Ozaki.toFixedZ_eq` | [Ozaki/BoundedOzaki2Int.lean](Ozaki/BoundedOzaki2Int.lean) |
| **Correctly rounded Ozaki-II and ADP-style slicing as integer functions**, from `(significand, exponent)` inputs, with the jumping exact fallback; correctly rounded, with IEEE signed zeros; Ozaki-II on both vendors, ADP on the Tensor Core side. | `Ozaki.ozaki2CRZ_eq`, `Ozaki.ozaki2CRJ_eq_CRZ`, `Ozaki.ozaki2CRJ_eq`, `Ozaki.ozaki2CRJ64_eq`, `Ozaki.ozaki2CRJS_eq`, `Ozaki.TC.adpCRZ_eq`, `Ozaki.TC.adpCRJ_eq_CRZ`, `Ozaki.TC.adpCRJ_eq`, `Ozaki.TC.adpCRJS_eq`, `Ozaki.TC.tcOzaki2CRJS_eq`, `Ozaki.MC.mcOzaki2CRJS_eq` | [Ozaki/BoundedOzaki2Int.lean](Ozaki/BoundedOzaki2Int.lean), [Ozaki/BoundedOzaki2J.lean](Ozaki/BoundedOzaki2J.lean), [OzakiTC/ADPIntJ.lean](OzakiTC/ADPIntJ.lean), [OzakiMC/Ozaki2IntJ.lean](OzakiMC/Ozaki2IntJ.lean) |
| **One theorem bounding every register.** A version of each integer pipeline with overflow checks guards every integer it computes, data against `2^R` and exponents and counters against `2^X`; under explicit formulas the checked version returns exactly the unchecked result. Ozaki-I: `R = 263`, `X = 17` for FP64 (`11`-bit slices, up to `175`, `k ≤ 2^20`), `207` and `15` for binary32. Ozaki-II: `263` and `17` for FP64 (twelve moduli up to `4096`, `P ≤ 69`), `161` and `15` for binary32. ADP-style: `259` and `17` for FP64 (up to `11` slices of width up to `81`). The guards include the internals of the matrix multipliers: split-K's chunk results and partial sums, the 32-bit register of the INT8 matrix multiplier (proved never to wrap) and the CRT constants; the signed-zero pipelines have checked versions too. Kernel tests show the guards fail at narrower widths. | `Ozaki.ozaki1CRIC_eq`, `Ozaki.ozaki1CRISC_eq`, `Ozaki.ozaki1CRIC_binary64_eq`, `Ozaki.ozaki2CRJC_eq`, `Ozaki.ozaki2CRJC_binary64_eq`, `Ozaki.TC.adpCRJC_eq`, `Ozaki.TC.adpCRJC_binary64_eq`, `Ozaki.TC.v100_fp64CRI_widths`, `Ozaki.TC.v100_fp64CRJ_widths`, `Ozaki.MC.cdna3F16_fp64CRI_widths`, `Ozaki.MC.cdna3F16_fp64CRJ_widths`, `Ozaki.ozaki1CRIC_binary64_tight`, `Ozaki.ozaki2CRJC_binary64_tight`, `Ozaki.TC.adpCRJC_binary64_tight`, `Ozaki.chunkedC_exactOn`, `Ozaki.TC.int8DotC_eq`, `Ozaki.ozaki2CRJSC_eq`, `Ozaki.TC.adpCRJSC_eq`, `Ozaki.TC.v100_fp64CRI_checked`, `Ozaki.MC.cdna3F16_fp64CRI_checked`, `Ozaki.ozaki1CRISC_binary32_tight`, `Ozaki.ozaki2CRJSC_binary32_tight` | [Ozaki/BoundedChecked.lean](Ozaki/BoundedChecked.lean), [Ozaki/BoundedChecked2.lean](Ozaki/BoundedChecked2.lean), [Ozaki/CheckedTight.lean](Ozaki/CheckedTight.lean), [Ozaki/CheckedMultipliers.lean](Ozaki/CheckedMultipliers.lean), [Ozaki/BoundedCheckedSigned.lean](Ozaki/BoundedCheckedSigned.lean), [OzakiTC/ADPChecked.lean](OzakiTC/ADPChecked.lean), [OzakiTC/Int8Checked.lean](OzakiTC/Int8Checked.lean), [OzakiMC/Ozaki2Checked.lean](OzakiMC/Ozaki2Checked.lean) |

### IEEE rounding, special values and signed zeros

| What it says | Lean name | File |
| --- | --- | --- |
| A hardware-independent IEEE round to nearest even for any binary format, with IEEE overflow: nearest, succeeds on intervals, error `2^-p\|q\| + 2^(emin−p)`. Instances `rne32Q` and `rne64`. | `Ozaki.roundRNE_nearest`, `Ozaki.roundRNE_intervals`, `Ozaki.roundRNE_within`, `Ozaki.rne64_nearest`, `Ozaki.rne32Q_nearest` | [Ozaki/Binary.lean](Ozaki/Binary.lean) |
| TensorCore's and MatrixCore's binary32 values, and TensorCore's binary64 values, are those of `Ozaki.Binary`. | `Ozaki.TC.finiteValue32_binary32`, `Ozaki.TC.fp64_binary64`, `Ozaki.MC.finiteValue32_binary32` | [OzakiTC/Rounding.lean](OzakiTC/Rounding.lean), [OzakiTC/LongDot.lean](OzakiTC/LongDot.lean), [OzakiMC/LongDot.lean](OzakiMC/LongDot.lean) |
| **One rounding on both vendors.** Every scheme rounds with IEEE's round to nearest even. TensorCore's binary32 and binary64 roundings compute the same value (the same exponent, grid and ties-to-even step) and differ only in overflow: they return no result above the largest finite value, where IEEE rounds values within half an ulp of it down to it. So they agree with IEEE's up to the largest finite value, and every result they return is IEEE's. MatrixCore's binary32 rounding is IEEE's on every input. | `Ozaki.TC.signedRounded_eq_rneU`, `Ozaki.TC.round32ValueTC_eq`, `Ozaki.TC.add32_of_fp32Add`, `Ozaki.TC.binarySignedRounded_eq_rneU`, `Ozaki.TC.fp64RoundTC_eq`, `Ozaki.TC.fp64Round_of_TC`, `Ozaki.MC.rneValue_eq_rneU`, `Ozaki.MC.round32Value_eq_rne32Q` | [OzakiTC/Rounding.lean](OzakiTC/Rounding.lean), [OzakiTC/IEEE.lean](OzakiTC/IEEE.lean), [OzakiMC/IEEE.lean](OzakiMC/IEEE.lean) |
| **IEEE values and operations.** Data are finite values with a sign bit, `±Inf` or NaN. Round to nearest even is total: `±Inf` exactly when the rounded magnitude exceeds the largest finite value, a zero result keeps the sign of the exact value; multiplication and addition follow IEEE's table (`Inf · 0` and `Inf + (−Inf)` are NaN, NaN propagates, `x + (−x) = +0`, `(−0) + (−0) = −0`) and agree with `roundRNE` on finite results. | `Ozaki.roundF_of_some`, `Ozaki.roundF_eq_inf_iff`, `Ozaki.roundF_inFormat`, `Ozaki.mulF_inf_zero`, `Ozaki.addF_inf_neg`, `Ozaki.addF_neg_self`, `Ozaki.addF_negZero`, `Ozaki.addF_fin_val`, `Ozaki.mulF_fin_val` | [Ozaki/IEEEValue.lean](Ozaki/IEEEValue.lean) |
| **The IEEE correctly rounded dot product.** NaN if an input is NaN, a product is `Inf · 0`, or the products include `+Inf` and `−Inf`; else `±Inf` if a product is infinite; else the exact sum rounded once, `±Inf` on overflow, with IEEE's zero sign. IEEE 754 leaves a dot product's order and precision to the implementation; this is the "exact, then round once" reading. A wrapper that handles the special inputs and gets the sign of an overflowing sum from the integer terms of the exact fallback turns any correctly rounded scheme into one that meets this specification for every input. | `Ozaki.dotIEEE`, `Ozaki.dotIEEE_fin`, `Ozaki.crIEEE_eq`, `Ozaki.crIEEE_exactSign`, `Ozaki.exactSignB_eq` | [Ozaki/IEEEDot.lean](Ozaki/IEEEDot.lean) |
| **Every correctly rounded scheme with special values**, on both vendors, binary32 and FP64, exact sum or truncated sum, Ozaki-I, Ozaki-II and ADP-style slicing. | `Ozaki.TC.tcOzaki1CRDI_eq`, `Ozaki.TC.tcOzaki1CRLI_eq`, `Ozaki.TC.tcOzaki1CRDWI_eq`, `Ozaki.TC.tcOzaki1CRLWI_eq`, `Ozaki.TC.tcOzaki2CRDI_eq`, `Ozaki.TC.tcOzaki2CRLI_eq`, `Ozaki.TC.adpCREI_eq`, `Ozaki.MC.mcOzaki1CRDI_eq`, `Ozaki.MC.mcOzaki1CRLI_eq`, `Ozaki.MC.mcOzaki1CRDWI_eq`, `Ozaki.MC.mcOzaki1CRLWI_eq`, `Ozaki.MC.mcOzaki2CRDI_eq`, `Ozaki.MC.mcOzaki2CRLI_eq` | [OzakiTC/IEEESchemes.lean](OzakiTC/IEEESchemes.lean), [OzakiMC/IEEESchemes.lean](OzakiMC/IEEESchemes.lean) |
| **Native GEMM, plain Ozaki-I and Ozaki-II with special values**: IEEE operations, `±Inf` on overflow, IEEE zero signs; on finite inputs they return the rational schemes' results whenever those are finite, so the error bounds apply. | `Ozaki.nativeDotIEEE_fin`, `Ozaki.ozaki1IEEE_fin`, `Ozaki.ozaki2IEEE_fin`, `Ozaki.TC.tcOzaki1I_fin`, `Ozaki.TC.tcOzaki2I_fin`, `Ozaki.TC.tcOzaki1DI_fin`, `Ozaki.MC.mcOzaki1I_fin`, `Ozaki.MC.mcOzaki2I_fin`, `Ozaki.MC.mcOzaki1DI_fin` | [Ozaki/IEEEDot.lean](Ozaki/IEEEDot.lean), [OzakiTC/IEEESchemes.lean](OzakiTC/IEEESchemes.lean), [OzakiMC/IEEESchemes.lean](OzakiMC/IEEESchemes.lean) |
| **Signed zeros.** The specification is IEEE's: the correctly rounded sum, `−0` when a nonzero exact sum rounds to zero from below, and for an exact zero `−0` only when every product is `−0`. The signed rounding test decides the sign from the enclosure when it lies on one side of zero, and otherwise from the exact fallback; correctly rounded Ozaki-I with a truncated sum returns the specified signed value on both vendors, for binary32 and FP64. | `Ozaki.roundingTestSigned_eq`, `Ozaki.ozaki1CRWS_eq`, `Ozaki.TC.tcOzaki1CRDS_eq`, `Ozaki.TC.tcOzaki1CRLS_eq`, `Ozaki.MC.mcOzaki1CRDS_eq`, `Ozaki.MC.mcOzaki1CRLS_eq` | [Ozaki/SignedZero.lean](Ozaki/SignedZero.lean), [OzakiTC/Signed.lean](OzakiTC/Signed.lean), [OzakiMC/Signed.lean](OzakiMC/Signed.lean) |
| **Signed zeros for Ozaki-II and ADP-style slicing**, rational and with integer rounding tests, proved equal to the specification. | `Ozaki.ozaki2CRS_eq`, `Ozaki.ozaki2CRBS_eq`, `Ozaki.TC.adpCRES_eq`, `Ozaki.TC.adpCRBS_eq`, `Ozaki.TC.tcOzaki2CRDS_eq`, `Ozaki.MC.mcOzaki2CRDS_eq` | [Ozaki/BoundedOzaki2.lean](Ozaki/BoundedOzaki2.lean), [OzakiTC/ADPBounded.lean](OzakiTC/ADPBounded.lean) |
| **Special values from the stored words, in integer arithmetic.** Decoding a binary word into sign, exponent and significand fields, and detecting zeros, subnormals, infinities and NaN, by integer operations; it agrees with TensorCore's classification for any format, and the wrapper built on it meets the specification on stored words. | `Ozaki.decodeWord_inFormat`, `Ozaki.dotSpecialI_eq`, `Ozaki.crIEEEIW_eq`, `Ozaki.crIEEEWord_eq`, `Ozaki.TC.decodeWord_classifyNat`, `Ozaki.TC.decodeWord_binary64`, `Ozaki.TC.tcOzaki1CRIDW_eq`, `Ozaki.MC.decodeWord_decodeNat`, `Ozaki.MC.mcOzaki1CRILW_eq` | [Ozaki/IEEEWords.lean](Ozaki/IEEEWords.lean), [OzakiTC/IEEEWords.lean](OzakiTC/IEEEWords.lean), [OzakiMC/IEEEWords.lean](OzakiMC/IEEEWords.lean) |
| **Special values for the integer pipelines.** Stored inputs (significand, exponent and sign, `±Inf`, NaN) and a wrapper whose overflow sign comes from the integer sign oracle; every integer and fixed-width version meets the specification for every input. | `Ozaki.crIEEEI_eq`, `Ozaki.crIEEEI_exactSign`, `Ozaki.TC.tcOzaki1CRIDI_eq`, `Ozaki.TC.tcOzaki2CRJI_eq`, `Ozaki.TC.adpCRJI_eq`, `Ozaki.TC.tcOzaki2CRBI_eq`, `Ozaki.TC.adpCRBI_eq`, `Ozaki.TC.tcOzaki1CRBDZI_eq`, `Ozaki.MC.mcOzaki1CRIDI_eq`, `Ozaki.MC.mcOzaki2CRJI_eq` | [Ozaki/IEEEInt.lean](Ozaki/IEEEInt.lean), [OzakiTC/IEEEBounded.lean](OzakiTC/IEEEBounded.lean), [OzakiMC/IEEEBounded.lean](OzakiMC/IEEEBounded.lean) |

## Long dot products, FP64 and error bounds

| What it says | Lean name | File |
| --- | --- | --- |
| **Split-K.** Chunks of `m` terms, each an exact call to the matrix multiplier, added exactly: exact on vectors of every length when `m · 2^(2b)` is within the exactness bound. | `Ozaki.chunked_exactOn`, `Ozaki.chunksAux_pairs`, `Ozaki.chunkLen_exactnessBound` | [Ozaki/SplitK.lean](Ozaki/SplitK.lean) |
| Binary32 and binary64 values are multiples of `2^-149` and `2^-1074`; inputs leave nothing over after `smax` slices with `smax (b+1) > 277` (binary32) or `> 2098` (binary64). | `Ozaki.binary64Value_gridMultiple`, `Ozaki.vanish32Q`, `Ozaki.vanish64` | [Ozaki/Binary.lean](Ozaki/Binary.lean), [Ozaki/Exact64.lean](Ozaki/Exact64.lean) |
| Split-K on Tensor Core blocks, exact for every length; with the chunk results in a `w`-bit register, exact while the products total less than `2^(w−1)`. | `Ozaki.TC.tcSplitK_exactOn`, `Ozaki.TC.tcSplitKReg_exactOn` | [OzakiTC/LongDot.lean](OzakiTC/LongDot.lean) |
| Ozaki-I's binary32 error bound for every `k`; FP64 emulation by Ozaki-I with binary64 recombination (`u = 2^-53`). | `Ozaki.TC.tcOzaki1L_error`, `Ozaki.TC.tcOzaki1D_error`, `Ozaki.MC.mcOzaki1L_error`, `Ozaki.MC.mcOzaki1D_error` | [OzakiTC/LongDot.lean](OzakiTC/LongDot.lean), [OzakiMC/LongDot.lean](OzakiMC/LongDot.lean) |
| **Correctly rounded binary32 GEMM of any inner dimension**, Ozaki-I and Ozaki-II, every product on the matrix multiplier of the hardware model, the IEEE `rne32Q` on both vendors. | `Ozaki.TC.tcOzaki1CRL_eq`, `Ozaki.TC.tcOzaki2CRL_eq`, `Ozaki.MC.mcOzaki1CRL_eq`, `Ozaki.MC.mcOzaki2CRL_eq` | [OzakiTC/LongDot.lean](OzakiTC/LongDot.lean), [OzakiMC/LongDot.lean](OzakiMC/LongDot.lean) |
| **Correctly rounded FP64 GEMM** on fp16, bf16 and tf32 Tensor Cores and AMD matrix cores, binary64 inputs of any length, the IEEE `rne64` on both vendors. | `Ozaki.TC.tcOzaki1CRD_eq`, `Ozaki.TC.tcOzaki2CRD_eq`, `Ozaki.TC.v100_fp64CR`, `Ozaki.TC.a100BF16_fp64CR`, `Ozaki.MC.mcOzaki1CRD_eq`, `Ozaki.MC.mcOzaki2CRD_eq`, `Ozaki.MC.cdna3F16_fp64CR`, `Ozaki.MC.cdna3BF16_fp64CR` | [OzakiTC/LongDot.lean](OzakiTC/LongDot.lean), [OzakiMC/LongDot.lean](OzakiMC/LongDot.lean) |
| **Ozaki-I, entrywise.** Every slice and leftover part of an entry is at most twice the entry, so the slicing error is at most `(s + 1) Σᵢ min(2\|xᵢyᵢ\|, 2^(E+F−s(b+1)))`, never more than the normwise bound, and the slice terms sum to `x · y` exactly when every product is zero; in the shape of Abdelfattah et al.'s bound, `(s + 1) 2^(−s(b+1)) κₓ κ_y Σ\|xᵢyᵢ\|`. | `Ozaki.exactTerms_error_sharp`, `Ozaki.exactTerms_error_sharp_le`, `Ozaki.exactTerms_eq_of_products_zero`, `Ozaki.exactTerms_error_kappa`, `Ozaki.ozaki1_error_sharp` | [Ozaki/SharpBounds.lean](Ozaki/SharpBounds.lean) |
| **Ozaki-II truncation, mixed.** For any shifts, `2^(−s)Σ\|yᵢ\| + 2^(−t)Σ\|xᵢ\|`: Uchino et al.'s bound without its cross term, since truncation is toward zero; `4k max\|x\| max\|y\| 2^(−P)` normwise, half the previous `8k`. | `Ozaki.truncProduct_error_mixed`, `Ozaki.truncProduct_error_mixed_max`, `Ozaki.truncProduct_error_normwise4`, `Ozaki.ozaki2_error_mixed` | [Ozaki/SharpBounds.lean](Ozaki/SharpBounds.lean) |
| **Uchino et al.'s closed-form constant (R64) and scaling (Lemma 1).** R64 is proved in their setting, where the first fused multiply-add is exact, with an explicit underflow term; their `log2f`-based scaling satisfies their Lemma 1; end to end, Ozaki-II with their scaling and reconstruction is within the truncation bound plus R64, with their exhaustively checked scaling slack as a hypothesis. | `Ozaki.fma_exact_of_grid`, `Ozaki.uchinoRecon_error_fma`, `Ozaki.uchino_R64`, `Ozaki.uchino_shift_le`, `Ozaki.uchino_lemma1`, `Ozaki.uchino_lemma1_slack`, `Ozaki.ozaki2Uchino_R64`, `Ozaki.ozaki2Uchino_scaled_error` | [Ozaki/UchinoConst.lean](Ozaki/UchinoConst.lean), [Ozaki/UchinoScaling.lean](Ozaki/UchinoScaling.lean) |
| **Jeannerod–Rump in any order.** For any binary summation tree over any permutation of the terms, the error is at most `(n − 1) u Σ\|tᵢ\|`, and a dot product's at most `k u Σ\|xᵢyᵢ\|`, underflow allowed for the sums. | `Ozaki.sumTree_error_jr`, `Ozaki.dotTree_error_jr`, `Ozaki.sumTree_error_jr_rne`, `Ozaki.dotTree_error_jr_rne` | [Ozaki/SharpBounds2.lean](Ozaki/SharpBounds2.lean) |
| **Different slice counts per matrix.** With `sx` slices of `x`, `sy` of `y` and the pairs `t + u < m`, an exact error identity and the bound `(sx + 1) k 2^(E+F−min(sx, sy, m)(b+1))`; with `sx = sy = m` it is Ozaki-I's triangle. | `Ozaki.dot_eq_exactTermsRect_add`, `Ozaki.exactTermsRect_error_uniform`, `Ozaki.exactTermsRect_triangle` | [Ozaki/SharpBounds2.lean](Ozaki/SharpBounds2.lean) |
| **Ozaki-II with an inexact reconstruction.** If the CRT sum is accumulated within `ε` (for example left to right in FP64, `ε = n 2^-53 2^(b+1) Σ\|wⱼ\|`) and `2k 2^(2P) + 2ε < M`, the reduction still recovers the product within `ε`, and the scheme's error grows by `u ε 2^-s + ε 2^-s`. | `Ozaki.reduceApprox_eq`, `Ozaki.ozaki2Approx_error`, `Ozaki.crtAccFP64_error`, `Ozaki.ozaki2FP64_error` | [Ozaki/SharpBounds2.lean](Ozaki/SharpBounds2.lean) |
| **Accumulation by levels (Abdelfattah et al., §4.4).** Scaled slice products grouped into levels whose terms share a grid and fit the precision sum exactly in any order; the level sums added in floating point lose at most `(ψ − 1) u Σ\|Lⱼ\|`, so Ozaki-I with this accumulation is within that plus the slicing bound. For regular slicing, which blocks of diagonals form exact levels: three per level for their INT8 setting in binary64, two for `11`-bit fp16 slices. Their spare-carry recursion is replaced by a sum-of-magnitudes condition, with a run-time check where grids are irregular. | `Ozaki.sumTree_exact`, `Ozaki.levelAcc_error`, `Ozaki.ozaki1Levels_error`, `Ozaki.level_exact_of_diagonals`, `Ozaki.levelOKB_spec`, `Ozaki.fits_int8_binary64`, `Ozaki.not_fits_int8_binary64_four`, `Ozaki.fits_fp16_binary64` | [Ozaki/AbdelfattahAcc.lean](Ozaki/AbdelfattahAcc.lean) |
| **Abdelfattah et al.'s spare-carry recursion (4.20)–(4.22).** Formalized with a level's size read as a count of diagonals: every level it accepts is exact, for every slice width; it never accepts more diagonals than the condition proved here, fewer at the first level and at late levels for slices of at least `2` bits, and the two can coincide in between. | `Ozaki.afAccept_diagFits_pos`, `Ozaki.afAccept_levelExact_pos`, `Ozaki.af_strict_zero`, `Ozaki.af_strict_late`, `Ozaki.af_int8_coincide`, `Ozaki.af_int8_vs_diagFits` | [Ozaki/AbdelfattahCarry.lean](Ozaki/AbdelfattahCarry.lean), [Ozaki/AbdelfattahCarry2.lean](Ozaki/AbdelfattahCarry2.lean) |
| **Uchino et al.'s binary64 CRT reconstruction (Algorithm 3).** Split weights, the two partial sums in binary64 (the first exact), the quotient by a rounded reciprocal and two fused multiply-adds: when the margin holds, the quotient is the true one (their Lemma 4) and the result is within an explicit bound of the reconstructed product (their Lemmas 3 and 5); end to end, Ozaki-II with this reconstruction is within the truncation bound plus that bound, through one rounding. The nested roundings are bounded relative to their own arguments, so their closed-form constant is not checked; their approximate `log2f` scaling enters as arbitrary shifts with the CRT range as a hypothesis. | `Ozaki.sumWith_exact`, `Ozaki.split_acc_error`, `Ozaki.uchinoRecon_error`, `Ozaki.crt_dvd`, `Ozaki.ozaki2Uchino_error` | [Ozaki/UchinoCRT.lean](Ozaki/UchinoCRT.lean) |
| **Jeannerod–Rump.** With round to nearest, summing left to right loses at most `(n − 1) u Σ\|tᵢ\|`, underflow allowed, and a dot product at most `k u Σ\|xᵢyᵢ\|` when no product underflows (`ku + (k−1)u²` and an underflow term otherwise), with no condition on `k u`; IEEE round to nearest even has the properties the proof needs. Ozaki-I's recombination adds at most `(n − 1) u Σ\|tⱼ\|`. | `Ozaki.sumWith_error_jr`, `Ozaki.nativeDot_error_jr`, `Ozaki.nativeDot_error_jr_underflow`, `Ozaki.roundRNE_jrAdd`, `Ozaki.ozaki1_error_jr`, `Ozaki.TC.native32_error_jr`, `Ozaki.TC.nativeDot64_error_jr`, `Ozaki.TC.tcOzaki1_error_jr`, `Ozaki.MC.native32_error_jr`, `Ozaki.MC.mcOzaki1_error_jr` | [Ozaki/SharpBounds.lean](Ozaki/SharpBounds.lean), [OzakiTC/SharpBounds.lean](OzakiTC/SharpBounds.lean), [OzakiMC/SharpBounds.lean](OzakiMC/SharpBounds.lean) |

## On the NVIDIA Tensor Core model

| What it says | Z3 | Lean name | File |
| --- | --- | --- | --- |
| Alignment loses nothing when every nonzero term is a multiple of `2^g` with exponent at most `g + F`. | | `Ozaki.TC.accumulator_eq_exactDot_of_grid` | [OzakiTC/Exactness.lean](OzakiTC/Exactness.lean) |
| A block of `b`-bit integers (`2b ≤ F`, `F ≥ 23`) with an integer `c` and `\|c\| + Σ\|aᵢbᵢ\| ≤ 2^24` returns `c + Σ aᵢbᵢ` exactly. | `I:[Z.4]`, `I:[E.4]` | `Ozaki.TC.evalBlock_int` | [OzakiTC/Exactness.lean](OzakiTC/Exactness.lean) |
| The same for a chain of blocks through their binary32 outputs. | | `Ozaki.TC.runBlocks_int` | [OzakiTC/Exactness.lean](OzakiTC/Exactness.lean) |
| Every integer of magnitude at most `2^(m+1)` is encoded exactly in a format with `m` stored bits. | `I:[Z.2]`, `I:[S1.11]` | `Ozaki.TC.encodeInt_spec` | [OzakiTC/MatrixMultiplier.lean](OzakiTC/MatrixMultiplier.lean) |
| The Tensor Core matrix multiplier is exact on `b`-bit vectors whose products total at most `2^24`. | `I:[S2.1]`, `II:[S3.1]` | `Ozaki.TC.tcMultiplier_exactOn` | [OzakiTC/MatrixMultiplier.lean](OzakiTC/MatrixMultiplier.lean) |
| Every `\|z\| ≤ 2^11` (and every symmetric residue modulo `m ≤ 4096`) encodes to an fp16 word and back; products of fp16 values are binary32, so their multiplication is exact; binary32 addition of integers whose sum is at most `2^24` is exact. | `I:[E.1]`–`I:[E.4]`, `I:[Z.2]`–`I:[Z.4]`, `II:[E.1]`–`II:[E.4]`, `II:[Z.1]`–`II:[Z.3]`, `II:[S2.1]` | `Ozaki.TC.fp16_encodes_int`, `Ozaki.TC.fp16_encodes_residue`, `Ozaki.TC.fp16_product_exact`, `Ozaki.TC.fp32Add_int_exact` | [OzakiTC/Checks.lean](OzakiTC/Checks.lean) |
| The same on all eight GPU variants, with `b = 11` (fp16, tf32) or `b = 8` (bf16). | | `Ozaki.TC.v100_exactOn`, … | [OzakiTC/Models.lean](OzakiTC/Models.lean) |
| Binary32 round to nearest (IEEE's, and TensorCore's): `\|fl(q) − q\| ≤ 2^-24 \|q\| + 2^-150`. | `I:[S3.3]`, `II:[H.2]` | `Ozaki.TC.round32Value_within`, `Ozaki.TC.add32_within`, `Ozaki.TC.fp32Add_within` | [OzakiTC/Rounding.lean](OzakiTC/Rounding.lean) |
| The σ-trick, with IEEE binary32 addition, computes `rne(a / 2^g) · 2^g` and an exact remainder for every binary32 `a` with `\|a\| ≤ 2^(g+b)`, grid `−149 ≤ g ≤ 104`, and `b ≤ 21`. | `I:[Z.1]`, `I:[S1.1]`–`I:[S1.8]` | `Ozaki.TC.sigma_split`, `Ozaki.TC.sigma_slice` | [OzakiTC/Split32.lean](OzakiTC/Split32.lean) |
| The remainder `a − rne(a/2^g) 2^g` is binary32 for every grid, so every residual of a binary32 vector is binary32. | `I:[S1.7]` | `Ozaki.TC.finiteValue32_sub_round`, `Ozaki.TC.splitFrom_binary32` | [OzakiTC/Split32.lean](OzakiTC/Split32.lean) |
| The whole split computed with binary32 σ-trick operations equals the scheme's split when every grid lies in `[−149, 104]`. | `I:[S1.13]` | `Ozaki.TC.splitFrom32_eq` | [OzakiTC/Split32.lean](OzakiTC/Split32.lean) |
| `2^e` is binary32 for `−149 ≤ e ≤ 127`; a scaled slice product and the Ozaki-II input scaling are binary32 when in range, so these multiplications are exact. | `I:[H.2]`, `I:[S3.2]`, `II:[H.3]`, `II:[S1.2]` | `Ozaki.TC.pow2_finiteValue32`, `Ozaki.TC.scaled_slice_product_exact`, `Ozaki.TC.exactTerm_finiteValue32`, `Ozaki.TC.scaleShift_exact32` | [OzakiTC/Scaling.lean](OzakiTC/Scaling.lean) |
| Ozaki-I and Ozaki-II on any variant: exact Tensor Core calls, and the error bounds. | | `Ozaki.TC.tcOzaki1_eq`, `Ozaki.TC.tcOzaki1_error`, `Ozaki.TC.tcOzaki2_eq`, `Ozaki.TC.tcOzaki2_error` | [OzakiTC/Schemes.lean](OzakiTC/Schemes.lean) |
| The Z3 models' configuration on V100. | | `Ozaki.TC.v100_ozaki1_z3`, `Ozaki.TC.v100_ozaki2_z3` | [OzakiTC/Schemes.lean](OzakiTC/Schemes.lean) |
| Both schemes return a value: on any variant whose matrix multiplier is exact under a magnitude bound, and in the Z3 configuration for entries up to `2^60`. | `I:[H.1]`, `II:[H.1]` | `Ozaki.TC.tcOzaki1_isSome`, `Ozaki.TC.tcOzaki2_isSome`, `Ozaki.TC.v100_ozaki1_z3_isSome`, `Ozaki.TC.v100_ozaki2_z3_isSome` | [OzakiTC/Success.lean](OzakiTC/Success.lean) |
| Native binary32 GEMM meets the classical bound `γₖ Σ\|xᵢyᵢ\|` (plus a subnormal term). | `I:[M.1]` | `Ozaki.TC.native32_error` | [OzakiTC/Native.lean](OzakiTC/Native.lean) |
| Binary32 and binary64 round to nearest return a nearest representable value and succeed on intervals. | | `Ozaki.TC.round32Value_nearest`, `Ozaki.TC.round32Value_intervals`, `Ozaki.TC.fp64Round_nearest`, `Ozaki.TC.fp64Round_intervals` | [OzakiTC/Correct.lean](OzakiTC/Correct.lean) |
| **Correctly rounded** Ozaki-I and Ozaki-II on any variant whose matrix multiplier is exact; Ozaki-I with its exact fallback on Tensor Core block FMAs too, for binary32 inputs (`24` slices of `11` bits suffice). | | `Ozaki.TC.tcOzaki1CR_eq`, `Ozaki.TC.tcOzaki2CR_eq`, `Ozaki.TC.tcOzaki1CRE_eq`, `Ozaki.TC.v100_ozaki1CRE` | [OzakiTC/Correct.lean](OzakiTC/Correct.lean) |
| **Two passes recover a full block FMA exactly**: pass 1 from `c = 0` gives `D1`, pass 2 from `c = −D1` gives `D2`, and `D1 + D2 = Σ aᵢbᵢ` whenever `K · 2^(2b) ≤ 2^(F+1)`; the matrix multiplier built on it is exact for every length, with full block FMAs on all eight variants (`11`-bit slices on fp16 and tf32, `8`-bit on bf16); Ozaki-I on it meets its error bound for every `k`. | | `Ozaki.TC.twoPass_exact`, `Ozaki.TC.tcMultiplier2_exactOn`, `Ozaki.TC.v100F16_exactOn2`, `Ozaki.TC.a100F16_exactOn2`, `Ozaki.TC.h100F16_exactOn2`, `Ozaki.TC.a100BF16_exactOn2`, `Ozaki.TC.h100BF16_exactOn2`, `Ozaki.TC.a100TF32_exactOn2`, `Ozaki.TC.h100TF32Wmma_exactOn2`, `Ozaki.TC.h100TF32Mma_exactOn2`, `Ozaki.TC.h100_ozaki1TP_error` | [OzakiTC/TwoPass.lean](OzakiTC/TwoPass.lean) |
| fp16 holds `2048` but not `4095`; `12`-bit magnitudes exceed the exactness bound on V100; a full A100 block FMA of `11`-bit products can exceed it; an A100 block is exact where binary32 additions are not. | `I:[Z.5]` | `Ozaki.TC.fp16_not_4095`, `Ozaki.TC.v100_twelve_bit_magnitudes`, `Ozaki.TC.a100_full_blockFMA`, `Ozaki.TC.a100_exact_where_binary32_is_not` | [OzakiTC/Limits.lean](OzakiTC/Limits.lean) |
| INT8 × INT8 → INT32 in a 32-bit wrapping register (TC-EFT's `machineAccumulate`) over exact integer products is exact on byte operands; a 16-bit register wraps. | `ADP:[Z.1]`, `ADP:[Z.2]` | `Ozaki.TC.int8Dot_bytes`, `Ozaki.TC.int8Dot_16_wraps` | [OzakiTC/Int8.lean](OzakiTC/Int8.lean) |
| **INT8 accumulation semantics.** The wrapping register returns the exact dot product reduced to signed `w`-bit two's complement, so every accumulation order (any tree of wrapping additions over any permutation of the products) gives the same result; a saturating register, clamping after every addition in any grouping, is exact while the magnitudes stay in range. On ADP's operands wrapping, saturating and exact all agree. | | `Ozaki.TC.int8Dot_eq_wrap`, `Ozaki.TC.int8Dot_any_order`, `Ozaki.TC.satAccumulate_exact`, `Ozaki.TC.AddTree.satSum_exact`, `Ozaki.TC.int8_wrap_sat_exact` | [OzakiTC/Int8Semantics.lean](OzakiTC/Int8Semantics.lean) |
| Ozaki-I on the INT8 matrix multiplier: the slice products recombine exactly to the fixed-point product, so the result is one binary64 rounding of it. | `ADP:[E.3]`, `ADP:[R.1]` | `Ozaki.TC.int8Recombine_eq`, `Ozaki.TC.int8Ozaki_eq` | [OzakiTC/Int8.lean](OzakiTC/Int8.lean) |
| **Exactness with cancellation.** A block of `b`-bit integers with `2b ≤ F` and an integer `\|c\| < 2^(F+1)` returns the exact sum whenever that sum is a binary32 value, with no bound on `Σ\|aᵢbᵢ\|`; the condition on the sum is necessary. Chains and the matrix multiplier likewise, when the prefixes at block boundaries stay within `2^24`. Eight products `±2^22` on A100 and a full H100 block FMA of sixteen return `0`. | | `Ozaki.TC.evalBlock_cancel`, `Ozaki.TC.evalBlock_exact_needs_binary32`, `Ozaki.TC.runBlocks_cancel`, `Ozaki.TC.tcMultiplier_exactWhen`, `Ozaki.TC.a100_cancel_zero`, `Ozaki.TC.h100_cancel_zero` | [OzakiTC/Cancellation.lean](OzakiTC/Cancellation.lean) |
| **The choice of slices, chunks and passes.** Every candidate configuration on every variant is exact for every length; the cost in block FMAs of Ozaki-I at a stated slice rule picks the cheapest. `10`-bit slices that fill the block FMA win wherever a block FMA holds more than four products (H100 fp16, FP64, `k = 1024`: 1344 blocks, against 3840 for `11`-bit chunks of four and 1920 for two passes); the chosen configurations are correctly rounded. | | `Ozaki.slicesFor`, `Ozaki.slicing_term_le_maxAbs`, `Ozaki.TC.candidates_exact`, `Ozaki.TC.h100F16_best`, `Ozaki.TC.v100F16_best`, `Ozaki.TC.h100F16_exactOn10`, `Ozaki.TC.h100F16_fp64CR10`, `Ozaki.TC.h100F16_exactFallback` | [Ozaki/SliceRule.lean](Ozaki/SliceRule.lean), [OzakiTC/SplitChoice.lean](OzakiTC/SplitChoice.lean) |
| **Ozaki-I against Ozaki-II with correct rounding's margin.** Ozaki-II's moduli chosen for precision `t + ⌈log₂ k⌉` (truncation at most `max\|x\| max\|y\| 2^-t`), Ozaki-I's slices likewise: for FP64 Ozaki-II is `1.75×` to `2.25×` cheaper on every variant except the SFMA (`1.1×`); for binary32 `1.25×` to `1.5×`, except on the SFMA, where two-pass Ozaki-I wins. Any positive, pairwise-coprime moduli give a valid CRT basis. | | `Ozaki.moduliForCR_spec`, `Ozaki.truncation_le_cr`, `Ozaki.crtBasis_valid`, `Ozaki.moduliBasis_valid_all`, `Ozaki.TC.h100F16_bestCR`, `Ozaki.TC.h100F16_fp64CR2_margin`, `Ozaki.MC.cdna3F16_bestCR`, `Ozaki.MC.cdna3F16_fp64CR2_margin` | [Ozaki/CRTValid.lean](Ozaki/CRTValid.lean), [Ozaki/SliceRuleCR.lean](Ozaki/SliceRuleCR.lean), [OzakiTC/Ozaki2ChoiceCR.lean](OzakiTC/Ozaki2ChoiceCR.lean), [OzakiMC/CRRules.lean](OzakiMC/CRRules.lean) |
| **The choice for Ozaki-II and ADP.** The fewest pairwise-coprime moduli up to `2^(b+1)` that meet the same accuracy target, every candidate exact; for FP64, Ozaki-II needs `1.4×` to `2×` fewer block FMAs than Ozaki-I on every variant (H100 fp16, `k = 1024`: 768 against 1344). For ADP-style slicing the remap encoding is never worse than naive signed bytes, but the floor encoding saves a slice when the width is `7` mod `8`. The chosen configurations are correctly rounded. | | `Ozaki.moduliList_pairwise`, `Ozaki.moduliFor_spec`, `Ozaki.TC.ozaki2Candidates_ok`, `Ozaki.TC.h100F16_best2`, `Ozaki.TC.h100F16_fp64CR2`, `Ozaki.TC.adpCandidate_exact`, `Ozaki.TC.adpCost_remap_le_naive`, `Ozaki.TC.adp_best`, `Ozaki.TC.adp_fp64CR_esc0` | [Ozaki/ModuliRule.lean](Ozaki/ModuliRule.lean), [OzakiTC/Ozaki2Choice.lean](OzakiTC/Ozaki2Choice.lean), [OzakiTC/ADPChoice.lean](OzakiTC/ADPChoice.lean) |

### The ADP pipeline on the INT8 matrix multiplier

`Ozaki.TC.adp` is the routine of the Z3 model `adp.py`, in its order: scan for non-finite inputs,
matrix ESC (unbounded sends the product to native binary64), `W = 53 + ESC + 1`, the slice count,
the heuristic `s² ≤ ratio`, then emulation on TC-EFT's INT8 matrix multiplier, or native binary64 otherwise. On
the five cases recorded from the unmodified Z3 model (three emulated, one sent to native binary64 by
its ESC, one non-finite) it returns the same path and values ([tests](tests/README.md)).

| What it says | Z3 | Lean name |
| --- | --- | --- |
| A binary64 word is `m 2^(e−52)` with `\|m\| < 2^53`, and `\|v\| < 2^(e+1)`. | `ADP:[D.1]`–`ADP:[D.3]` | `Ozaki.TC.value64_onGrid`, `Ozaki.TC.value64_bound` |
| Binary64 round to nearest (IEEE's): `\|fl(q) − q\| ≤ 2^-53 \|q\| + 2^-1075`; it fails exactly when the rounded magnitude exceeds the largest finite value, as in IEEE. | `ADP:[R.2]` | `Ozaki.TC.fp64Round_within`, `Ozaki.TC.fp64Round_none_iff` |
| `W = 53 + ESC + 1`, and the slice count is the least that holds `W` bits. | `ADP:[B.1]`, `ADP:[B.2]` | `Ozaki.TC.adpWidth`, `Ozaki.TC.slicesNeeded_spec` |
| The matrix ESC is at least every entry's ESC. | `ADP:[X.6]` | `Ozaki.TC.matrixEsc_ge` |
| A slice is an 8-bit pattern; one emulated entry is the binary64 rounding of the fixed-point product. | `ADP:[E.1]`, `ADP:[E.3]`, `ADP:[R.1]` | `Ozaki.TC.int8_pattern`, `Ozaki.TC.emulEntry_eq` |
| An emulated entry meets P.1 and Grade A; a native entry meets the `γₖ` bound. | `ADP:[P.1]`, `ADP:[P.2]`, `ADP:[N.1]` | `Ozaki.TC.emulEntry_P1`, `Ozaki.TC.emulEntry_gradeA`, `Ozaki.TC.nativeEntry_error` |
| The guardrails: non-finite inputs go to the native path, and emulation runs only on finite inputs with a finite ESC and `s² ≤ ratio`. | `ADP:[G.1]`–`ADP:[G.3]` | `Ozaki.TC.adp_nonfinite_iff`, `Ozaki.TC.adp_emulated` |
| **The whole routine.** Whenever `adp` returns values, on normal or zero entries of matching shapes with `k · 2^14 < 2^31`, every entry meets Grade A on the emulated path and the `γₖ` bound on the native path. | `ADP:[P.2]`, `ADP:[N.1]` | `Ozaki.TC.adp_accuracy` |
| Both zeros decode to `0` with exponent `−∞`. | `ADP:[T.1]` | `Ozaki.TC.decode_zeros` |
| **The encodings agree.** The routine with any of the three slice encodings, each with its own minimal slice count, returns one binary64 rounding of the same fixed-point product, so two encodings that both emulate return the same values (with `k · 2^16 < 2^31`, the Z3 model's static bound). | `ADP:[T.4]`, `ADP:[B.2]` | `Ozaki.TC.emulEntryWith_eq`, `Ozaki.TC.encodings_agree`, `Ozaki.TC.adpWith_remap`, `Ozaki.TC.adpWith_encodings_agree`, `Ozaki.TC.slicesNeededWith_spec`, `Ozaki.TC.slicesNeeded_le_naive` |
| Finite inputs take the emulated or the native-slow path; with a subnormal entry `adpSafe` takes the native path. | `ADP:[T.7]`, `ADP:[T.11]` | `Ozaki.TC.adp_finite_path`, `Ozaki.TC.adpSafe_subnormal` |
| **Emergent overflow.** An emulated entry fails exactly when the rounded fixed-point product exceeds the largest finite binary64 value; where the Z3 model returns `±Inf`, `adp` returns no values and `adpIEEE` returns `±Inf`. | `ADP:[T.10]` | `Ozaki.TC.emulEntry_none_iff` |
| **ADP with special values.** Words decode to IEEE data exactly as IEEE classifies them; `adpIEEE` takes `adp`'s path and returns its values wherever `adp` returns values, its non-finite path is native FP64 with IEEE operations, and on the Z3 model's cases with an infinity, a NaN and an emulated overflow it returns the Z3 model's words, class for class. | `ADP:[T.9]`, `ADP:[T.10]` | `Ozaki.TC.decodeF64_inf_iff`, `Ozaki.TC.decodeF64_nan_iff`, `Ozaki.TC.adpIEEE_agrees`, `Ozaki.TC.adpIEEE_nonfinite`, `Ozaki.TC.adpSafeIEEE_agrees` |
| **A guardrail for subnormal inputs.** `adpSafe` sends inputs with a nonzero entry below `2^-1022` to the native path; whenever it emulates, every entry is normal or zero, and whenever it returns values, every entry meets Grade A on the emulated path and the `γₖ` bound on the native path, with no normality hypothesis. On the five recorded Z3 cases it returns what `adp` returns. | `ADP:[P.2]`, `ADP:[N.1]` | `Ozaki.TC.adpSafe_emulated_normal`, `Ozaki.TC.nativeGemm64_accuracy`, `Ozaki.TC.adpSafe_accuracy` |
| **The routine with the Z3 model's zero policies.** With the `−∞` policy it is `adp`. Without the model's `[X.4]` assertion, "skip zeros" fails for every block size of at least `2` and every `2 ≤ k < 2^17`: a row `(2^a, 1, 0, …)` against a column `(0, 2^d, 0, …)` emulates with an estimate below the exact ESC and returns `0` for the product `2^d`, breaking Grade A; with block size `1` skipping is safe. Giving zeros exponent `−1022` fails likewise for every block size, with `−1022 ≤ d ≤ −998`. The failure holds for every matrix shape: zero rows and columns never change the estimate, so padding the counterexample keeps it. Other rows mask it only by raising the matrix estimate. Sufficient, per entry: an entry meets Grade A whenever the run's ESC is at least its own exact ESC. Necessary: if some factor of one of its products loses more than about `log₂((8k + 4)k)` bits in conversion, inputs with the same exponents, hence the same ESC, width and slice count, break Grade A. Sharper: Grade A holds for every input of a pattern when each factor's conversion loses at most `D` bits with about `2^(D+1) + 2 ≤ 4k`, and fails for some input when one factor loses `D` bits with about `2^(D+1) ≥ 4k + 4`; about one value of `D` is left between them. Where the necessary condition applies, the same pattern (same ESC, width and path) admits an input that meets Grade A and one that breaks it, so the pattern alone does not decide an input. | `ADP:[X.4]`, `ADP:[T.12]` | `Ozaki.TC.adpPolicy_negInf`, `Ozaki.TC.adpPolicy_skip_wrong`, `Ozaki.TC.adpPolicy_field0_wrong`, `Ozaki.TC.escCoarsePolicy_skip_one`, `Ozaki.TC.adpPolicy_skip_wrong_shape`, `Ozaki.TC.adpPolicy_field0_wrong_shape`, `Ozaki.TC.adpPolicy_masked_gradeA`, `Ozaki.TC.adpPolicy_entry_gradeA`, `Ozaki.TC.adpPolicy_unmasked_fails_left`, `Ozaki.TC.adpPolicy_unmasked_fails_right`, `Ozaki.TC.adpPolicy_entry_gradeA_loss`, `Ozaki.TC.adpPolicy_unmasked_fails_full_left`, `Ozaki.TC.adpPolicy_pattern_undecided_left`, `Ozaki.TC.adpPolicy_pow2_gradeA` |
| **The routine returns values** for finite inputs of matching shapes with `k · 2^14 < 2^31` and every `Σ\|xᵢyᵢ\| ≤ 2^1000` (a sufficient bound, not a sharp one); `adp` needs normal or zero entries, `adpSafe` does not. | | `Ozaki.TC.adp_isSome`, `Ozaki.TC.adpSafe_isSome` |
| **Correctly rounded fixed-point Ozaki-I as in ADP**: with given `(s, W)` that fit and `k · 2^14 < 2^31`, `adpCR` returns the binary64 round to nearest of `x · y` for every input; it falls back to the exact rational product, and it is not the ESC-driven routine. | | `Ozaki.TC.adpCR_eq` |
| **The same with every product on the INT8 matrix multiplier, any length.** The INT8 matrix multiplier with split-K is exact on `6`-bit slices for every length; the fixed-point enclosures run on it with split-K too; and the exact fallback is Ozaki-I with all slice products of `6`-bit slices on it, at most `smax` slices with `7 smax > 2098`. | | `Ozaki.TC.int8SplitK_exactOn`, `Ozaki.TC.int8DotK_exact`, `Ozaki.TC.adpEnclosureK_sound`, `Ozaki.TC.adpCRE_eq` |

All of these are in [OzakiTC/ADP.lean](OzakiTC/ADP.lean), except `adpCR_eq` in
[OzakiTC/Correct.lean](OzakiTC/Correct.lean), the guardrail, success and `adpCRE` results in
[OzakiTC/ADPFix.lean](OzakiTC/ADPFix.lean), the zero policies in
[OzakiTC/ADPZeroPolicy.lean](OzakiTC/ADPZeroPolicy.lean),
[OzakiTC/ADPZeroPolicyGeneral.lean](OzakiTC/ADPZeroPolicyGeneral.lean) and
[OzakiTC/ADPZeroPolicyShapes.lean](OzakiTC/ADPZeroPolicyShapes.lean) and
[OzakiTC/ADPZeroPolicyIff.lean](OzakiTC/ADPZeroPolicyIff.lean) and
[OzakiTC/ADPZeroPolicyGap.lean](OzakiTC/ADPZeroPolicyGap.lean), and the test-level labels (`[T.1]`, `[T.4]`, `[T.7]`,
`[T.10]`, `[T.11]`) in [OzakiTC/ADPLabels.lean](OzakiTC/ADPLabels.lean). The Z3 model's inputs for
`[T.1]`, `[T.4]`, `[T.7]`, `[T.8]`, `[T.10]`, `[T.11]` and `[T.12]` are also checked by kernel
evaluation ([tests](tests/README.md)). `[T.13]` (fault injection) and `[T.14]` (label coverage)
check the Z3 model's own harness; their counterpart here is this page, where every label has a
theorem or a kernel-checked test.

## On the AMD matrix-core model

| What it says | Z3 | Lean name | File |
| --- | --- | --- | --- |
| Binary32 round to nearest returns every binary32 value, and every integer of magnitude at most `2^24`, unchanged, with or without flushing subnormals. | | `Ozaki.MC.rneValue_of_finite`, `Ozaki.MC.flValue_int` | [OzakiMC/Exactness.lean](OzakiMC/Exactness.lean) |
| CDNA 2's pairwise sums on integers within `2^24` are their exact sum. | | `Ozaki.MC.pairwiseGroupSum_int` | [OzakiMC/Exactness.lean](OzakiMC/Exactness.lean) |
| On `correct_rounding`, `pair_wise_sum` and `global_alignment`, `S_acc` of integer operands is the exact sum. | | `Ozaki.MC.accumulate_int` | [OzakiMC/Exactness.lean](OzakiMC/Exactness.lean) |
| A block, a chain of blocks, and an inner product of any length return `c + Σ aᵢbᵢ` exactly when `\|c\| + Σ\|aᵢbᵢ\| ≤ 2^24`. | `I:[Z.4]`, `I:[E.4]` | `Ozaki.MC.evalBlock_int`, `Ozaki.MC.runBlocks_int`, `Ozaki.MC.dotBits_int` | [OzakiMC/Exactness.lean](OzakiMC/Exactness.lean) |
| `encodeExact` encodes every integer of magnitude at most `2^(p+1)`; XF32 keeps every integer up to `2^11`. | `I:[Z.2]`, `I:[S1.11]` | `Ozaki.MC.encodeExact_int`, `Ozaki.MC.xf32_encodesInts` | [OzakiMC/MatrixMultiplier.lean](OzakiMC/MatrixMultiplier.lean) |
| The matrix-core matrix multiplier is exact on `b`-bit vectors whose products total at most `2^24`. | `I:[S2.1]`, `II:[S3.1]` | `Ozaki.MC.mcMultiplier_exactOn` | [OzakiMC/MatrixMultiplier.lean](OzakiMC/MatrixMultiplier.lean) |
| The same on SFMA (`b ≤ 24`), CDNA 1, 2 and 3 fp16 and CDNA 3 XF32 (`b ≤ 11`), and the bf16 variants (`b ≤ 8`). | | `Ozaki.MC.cdna3F16_exactMultiplier`, … | [OzakiMC/Models.lean](OzakiMC/Models.lean) |
| Binary32 round to nearest: `\|fl(q) − q\| ≤ 2^-24 \|q\| + 2^-150`. | `I:[S3.3]`, `II:[H.2]` | `Ozaki.MC.round32Value_within`, `Ozaki.MC.fp32Add_within` | [OzakiMC/Rounding.lean](OzakiMC/Rounding.lean) |
| Scaled slice products and the Ozaki-II input scaling are exact in range. | `I:[S3.2]`, `II:[S1.2]` | `Ozaki.MC.scaled_slice_product_exact`, `Ozaki.MC.scaleShift_exact32` | [OzakiMC/Scaling.lean](OzakiMC/Scaling.lean) |
| Both schemes return a value under a magnitude bound, and in the Z3 configuration on CDNA 3 fp16. | `I:[H.1]`, `II:[H.1]` | `Ozaki.MC.mcOzaki1_isSome`, `Ozaki.MC.mcOzaki2_isSome`, `Ozaki.MC.cdna3F16_ozaki1_z3_isSome` | [OzakiMC/Success.lean](OzakiMC/Success.lean) |
| Native binary32 GEMM meets the classical bound. | `I:[M.1]` | `Ozaki.MC.native32_error` | [OzakiMC/Native.lean](OzakiMC/Native.lean) |
| **Correctly rounded** Ozaki-I and Ozaki-II on any variant whose matrix multiplier is exact, and Ozaki-I with its exact fallback on matrix-core block FMAs for binary32 inputs. MatrixCore's rounding is IEEE's, the rounding the Tensor Core side uses (`Ozaki.MC.round32Value_eq_rne32Q`). | | `Ozaki.MC.round32Value_nearest`, `Ozaki.MC.mcOzaki1CR_eq`, `Ozaki.MC.mcOzaki2CR_eq`, `Ozaki.MC.mcOzaki1CRE_eq` | [OzakiMC/Correct.lean](OzakiMC/Correct.lean) |
| Ozaki-I and Ozaki-II on any variant whose matrix multiplier is exact, and the Z3 models' configuration on CDNA 1, 2 and 3 fp16. | | `Ozaki.MC.mcOzaki1_eq`, `Ozaki.MC.mcOzaki1_error`, `Ozaki.MC.mcOzaki2_eq`, `Ozaki.MC.mcOzaki2_error`, `Ozaki.MC.cdna3F16_ozaki1_z3`, … | [OzakiMC/Schemes.lean](OzakiMC/Schemes.lean) |
| bf16 holds `256` but not `2047`; a full CDNA 3 block FMA of `11`-bit products can exceed the exactness bound; the fp16 variants are exact where the SFMA is not. | | `Ozaki.MC.bfloat16_holds_256`, `Ozaki.MC.cdna3F16_full_blockFMA`, `Ozaki.MC.fp16_exact_where_sfma_is_not` | [OzakiMC/Limits.lean](OzakiMC/Limits.lean) |
| **Exactness with cancellation**, per architecture: CDNA 1 and CDNA 3 return the exact sum whenever every product, `c` and the sum are within `2^24`; CDNA 2 also needs every pairwise sum within `2^24` (implied by the exactness bound). | | `Ozaki.MC.accumulate_cancel`, `Ozaki.MC.evalBlock_cancel`, `Ozaki.MC.pairwiseGroupSum_cancel`, `Ozaki.MC.pairwiseSumsBounded_of_bound`, `Ozaki.MC.cdna3_cancel_zero`, `Ozaki.MC.cdna12_cancel_c` | [OzakiMC/Cancellation.lean](OzakiMC/Cancellation.lean) |
| **The choice of slices and chunks** on every AMD variant, each candidate exact for every length; on CDNA 3 fp16, `10`-bit slices are cheapest (FP64, `k = 1024`: 2688 blocks against 3840). | | `Ozaki.MC.mcCandidates_exact`, `Ozaki.MC.cdna3F16_best`, `Ozaki.MC.cdna3F16_fp64CR10`, `Ozaki.MC.sfma_fp64CR12` | [OzakiMC/SplitChoice.lean](OzakiMC/SplitChoice.lean) |
| **Two passes on AMD.** On the SFMA and CDNA 1 the second pass from `c = −D1` recovers the exact sum (on the SFMA it is TwoProdFMA); on CDNA 3 too, since global alignment is exact for larger `c`; the two-pass matrix multiplier is exact for every length. On CDNA 2 it fails in general: the pairwise sums are rounded before `c` is added. A second pass is needed only on CDNA 3 fp16 and the SFMA. | | `Ozaki.MC.sfma_twoProd`, `Ozaki.MC.mcTwoPass_exact_cr`, `Ozaki.MC.alignedAccumulation_wide`, `Ozaki.MC.mcTwoPass_exact_ga`, `Ozaki.MC.mcMultiplier2_exactOn`, `Ozaki.MC.cdna3F16_twoPass_full_blockFMA`, `Ozaki.MC.cdna2_twoPass_fails`, `Ozaki.MC.full_blockFMAs_fit` | [OzakiMC/TwoPass.lean](OzakiMC/TwoPass.lean) |
| **Ozaki-I against Ozaki-II on AMD**: Ozaki-II is cheaper for FP64 on every variant; two passes win only on the SFMA, for Ozaki-I. | | `Ozaki.MC.mcRunCandidates_exact`, `Ozaki.MC.cdna3F16_best12`, `Ozaki.MC.cdna3F16_fp64CR2`, `Ozaki.MC.sfma_fp64CR2pass` | [OzakiMC/Ozaki2Choice.lean](OzakiMC/Ozaki2Choice.lean) |

## Not proved

- That real GPUs behave like the models; see TC-EFT's and Matrix-Core's validation.
- FP8 variants: CDNA 3's `odd_even_grouping`, and no FP8 Tensor Core variant exists in `TensorCore`.
- INT8 hardware semantics are out of scope for now, on both vendors
  ([issue #2](https://github.com/pauljiang03/TC-EFT/issues/2)). ADP runs on an idealized INT8
  matrix multiplier, the arithmetic of a wrapping (or saturating) INT32 register over exact integer products;
  its result does not depend on the accumulation order, but neither `TensorCore` nor `MatrixCore`
  models an INT8 instruction, and nothing is validated against INT8 hardware.
- The Z3 models' measured comparisons (`I:[M.2]`, `I:[M.3]`, `II:[M.2]`, `II:[M.3]`) are checked
  on their test matrices ([tests](tests/README.md)), not proved: they are not true for every input.
- ADP: when other rows mask an unsafe zero policy's failure is characterized up to about one value
  of the bit loss `D`; an exact characterization would need the worst error over all significands
  of each pattern. Losses split across both factors of one product have no matching necessary
  construction, and subnormal entries are excluded. Grade A fails for some subnormal inputs of `adp` as the paper describes it; the extra
  guardrail of `adpSafe` restores it. cuBLAS's own implementation is not modeled; it passes an
  independent underflow test (Demmel et al., 2026).
- TensorCore's own binary32 and binary64 roundings fail above the largest finite value, where
  IEEE rounds values below `2^128 − 2^103` (binary64: `2^1024 − 2^970`) down to it. No result here
  depends on that: the schemes, the σ-trick and `int8Ozaki` all use IEEE's rounding.
- The width theorems do not guard comparisons, signs, absolute values, bit lengths, list lengths,
  or powers of two used as shift amounts, which create no new magnitude. ADP's integer pipeline
  exists on the Tensor Core side only, and the AMD word-level special values cover binary32 words
  (MatrixCore has no binary64 decoding).
- How often the fallback runs is measured by simulation
  ([`scripts/fallback_sim.py`](scripts/fallback_sim.py)), not proved; the cost theorems compare
  schemes, they do not predict a fallback rate.
- The binary32 σ-trick is proved only for grids in `[2^-149, 2^104]`; the integer slicing covers
  every grid.
- The cancellation condition is the exact boundary, not a scheduling rule: the running sums are
  known only after computing them. The slice-choice costs count block FMAs, not time.
- IEEE special values are modeled without NaN payloads or signaling NaNs. The rational functions
  (`Option ℚ`, `none` on overflow) remain the core of every proof; their IEEE counterparts are the
  `…I` functions above.

These blocks keep every name above connected to the actual API. `TensorCore` and `MatrixCore`
cannot be imported together, so there is one block for each model:

```lean
import OzakiTC

open Ozaki Ozaki.TC Ozaki.ADP

#check @split_dot
#check @split_coeff_bound
#check @split_grid_le
#check @split_residual_le
#check @splitExp_spec
#check @trianglePairs_length
#check @ozaki1_eq_sumWith
#check @dot_eq_exactTerms_add
#check @exactTerms_error
#check @exactTerms_error_normwise
#check @sumWith_error
#check @ozaki1_error
#check @scaleTrunc_bound
#check @symMod_bounds
#check @dvd_dotZ_symMod
#check @crt_eq
#check @ozaki2_eq
#check @truncProduct_error
#check @truncProduct_error_normwise
#check @ozaki2_error
#check @z3_slice_exactnessBound
#check @z3Basis_valid
#check @z3_bits
#check @crt_fails_at_23
#check @remap_value
#check @remap_s8
#check @remap_bit_pattern
#check @remap_range_smaller
#check @slices_53
#check @coarseEst_le
#check @skipZeros_unsafe
#check @field0_unsafe
#check @full_fidelity
#check @full_fidelity_without_plus_one
#check @term_error
#check @funnel
#check @funnel_needs_plus_one
#check @slice_recombination
#check @accumulator_eq_exactDot_of_grid
#check @evalBlock_int
#check @runBlocks_int
#check @encodeInt_spec
#check @tcMultiplier_exactOn
#check @v100_exactOn
#check @round32Value_within
#check @fp32Add_within
#check @sigma_split
#check @sigma_slice
#check @finiteValue32_sub_round
#check @splitFrom_binary32
#check @splitFrom32_eq
#check @tcOzaki1_eq
#check @tcOzaki1_error
#check @tcOzaki2_eq
#check @tcOzaki2_error
#check @v100_ozaki1_z3
#check @v100_ozaki2_z3
#check @fp16_not_4095
#check @v100_twelve_bit_magnitudes
#check @a100_full_blockFMA
#check @a100_exact_where_binary32_is_not
#check @int8Dot_bytes
#check @int8Dot_16_wraps
#check @int8Ozaki_eq
#check @slice_product_bound
#check @scaleShift_spec
#check @natAbs_truncProduct_le
#check @natAbs_residueProduct_le
#check @z3_residue_exactnessBound
#check @crt_dvd_sub
#check @ozaki1_isSome
#check @ozaki2_isSome
#check @nativeDot_error
#check @nativeDot_error_gamma
#check @Ozaki.ADP.floorDigits_bytes
#check @Ozaki.ADP.fixed_range
#check @Ozaki.ADP.dominant_exact
#check @Ozaki.ADP.term_bound
#check @Ozaki.ADP.escCoarse_ge
#check @Ozaki.ADP.blockRep_bounds
#check @Ozaki.ADP.fixedPoint_error
#check @Ozaki.ADP.emulated_gradeA
#check @round_monotone
#check @round_eq_of_enclosure
#check @roundingTest_eq
#check @dot_approx_error
#check @ozaki1CR_eq
#check @ozaki2CR_eq
#check @split_residual_zero
#check @ozaki1Full_eq
#check @ozaki1CRE_eq
#check @fp16_encodes_int
#check @fp16_product_exact
#check @fp32Add_int_exact
#check @scaled_slice_product_exact
#check @scaleShift_exact32
#check @tcOzaki1_isSome
#check @v100_ozaki1_z3_isSome
#check @native32_error
#check @round32Value_nearest
#check @fp64Round_nearest
#check @tcOzaki1CR_eq
#check @tcOzaki2CR_eq
#check @tcOzaki1CRE_eq
#check @v100_ozaki1CRE
#check @Ozaki.TC.value64_onGrid
#check @Ozaki.TC.fp64Round_within
#check @Ozaki.TC.slicesNeeded_spec
#check @Ozaki.TC.matrixEsc_ge
#check @Ozaki.TC.emulEntry_gradeA
#check @Ozaki.TC.nativeEntry_error
#check @Ozaki.TC.adp_emulated
#check @Ozaki.TC.adp_accuracy
#check @Ozaki.ADP.naiveDigits_s8
#check @Ozaki.ADP.slice_recombination_with
#check @Ozaki.ADP.paper_remap_example
#check @Ozaki.ADP.escCoarse_one
#check @Ozaki.ADP.zeros_case_caught
#check @Ozaki.TC.decode_zeros
#check @Ozaki.TC.encodings_agree
#check @Ozaki.TC.adpWith_encodings_agree
#check @Ozaki.TC.adp_finite_path
#check @Ozaki.TC.emulEntry_none_iff
#check @Ozaki.TC.adpSafe_subnormal
#check @Ozaki.TC.int8Dot_eq_wrap
#check @Ozaki.TC.int8Dot_any_order
#check @Ozaki.TC.int8_wrap_sat_exact
#check @adpCR_eq
#check @chunked_exactOn
#check @roundEnclosure_of_margin
#check @ozaki1Enclosure_succeeds
#check @ozaki2CRE_eq
#check @roundRNE_nearest
#check @rne64_nearest
#check @rne32Q_nearest
#check @vanish32Q
#check @vanish64
#check @exactTerms_sum_register
#check @exactTerms_sum_register32
#check @tcSplitK_exactOn
#check @tcSplitKReg_exactOn
#check @tcOzaki1L_error
#check @tcOzaki1D_error
#check @tcOzaki1CRL_eq
#check @tcOzaki2CRL_eq
#check @tcOzaki1CRD_eq
#check @tcOzaki2CRD_eq
#check @v100_fp64CR
#check @a100BF16_fp64CR
#check @finiteValue32_binary32
#check @fp64_binary64
#check @twoPass_exact
#check @tcMultiplier2_exactOn
#check @a100F16_exactOn2
#check @h100F16_exactOn2
#check @h100_ozaki1TP_error
#check @truncatedSum_error
#check @ozaki1CRW_eq
#check @ozaki1Truncated_register
#check @ozaki1TruncatedEnclosure_succeeds
#check @tcOzaki1CRDW_eq
#check @tcOzaki1CRLW_eq
#check @v100_fp64CRW
#check @round32ValueTC_eq
#check @add32_of_fp32Add
#check @fp64RoundTC_eq
#check @fp64Round_of_TC
#check @fp64Round_none_iff
#check @v100F16_exactOn2
#check @h100TF32Mma_exactOn2
#check @int8Recombine_eq
#check @adpSafe_accuracy
#check @adp_isSome
#check @adpSafe_isSome
#check @int8SplitK_exactOn
#check @adpCRE_eq
#check @splitInt_eq
#check @splitInt_width
#check @split_binary32_int
#check @split_binary64_int
#check @roundingTestSigned_eq
#check @ozaki1CRWS_eq
#check @tcOzaki1CRDS_eq
#check @tcOzaki1CRLS_eq
#check @roundF_eq_inf_iff
#check @addF_neg_self
#check @dotIEEE_fin
#check @crIEEE_eq
#check @crIEEE_exactSign
#check @nativeDotIEEE_fin
#check @tcOzaki1CRDI_eq
#check @tcOzaki2CRDI_eq
#check @adpCREI_eq
#check @tcOzaki1I_fin
#check @decodeF64_inf_iff
#check @decodeF64_nan_iff
#check @adpIEEE_agrees
#check @adpIEEE_nonfinite
#check @fixedSum_eq
#check @roundExact_eq
#check @signSum_eq
#check @roundSum_eq
#check @topDownSumAll_fuel_le
#check @ozaki1TestB_eq
#check @ozaki1TestB_register
#check @ozaki1ExactFallbackB_eq
#check @ozaki1CRB_eq_CRW
#check @ozaki1CRB_eq
#check @ozaki1CRB64_eq
#check @ozaki1CRB32_eq
#check @tcOzaki1CRBD_eq
#check @tcOzaki1CRBL_eq
#check @v100_fp64CRB
#check @overlapMultiplier_eq
#check @ozaki1CREZ_zero
#check @tcOzaki1CRDZ_eq
#check @rangesJ_le
#check @roundSumJ_eq
#check @ozaki1CRI_eq
#check @ozaki1CRIS_eq
#check @Ozaki.ozaki1CRIC_eq
#check @Ozaki.ozaki1CRIC_binary64_eq
#check @Ozaki.ozaki2CRJC_eq
#check @adpCRJC_eq
#check @enclosureTestB_eq
#check @ozaki2CRB_eq
#check @adpCRB_eq
#check @truncShiftZ_eq
#check @toFixedZ_eq
#check @ozaki2CRJ_eq
#check @adpCRJ_eq
#check @ozaki2CRJS_eq
#check @adpCRJS_eq
#check @ozaki2CRS_eq
#check @adpCRES_eq
#check @crIEEEI_eq
#check @tcOzaki1CRIDI_eq
#check @tcOzaki2CRJI_eq
#check @adpCRJI_eq
#check @exactTerms_error_sharp
#check @exactTerms_error_kappa
#check @truncProduct_error_mixed
#check @truncProduct_error_normwise4
#check @sumWith_error_jr
#check @nativeDot_error_jr
#check @tcOzaki1_error_jr
#check @Ozaki.TC.evalBlock_cancel
#check @evalBlock_exact_needs_binary32
#check @tcMultiplier_exactWhen
#check @candidates_exact
#check @h100F16_best
#check @h100F16_fp64CR10
#check @adpPolicy_negInf
#check @ozaki1CRIC_binary64_tight
#check @chunkedC_exactOn
#check @int8DotC_eq
#check @ozaki2CRJSC_eq
#check @adpCRJSC_eq
#check @dotSpecialI_eq
#check @crIEEEWord_eq
#check @decodeWord_classifyNat
#check @moduliFor_spec
#check @ozaki2Candidates_ok
#check @h100F16_best2
#check @adp_best
#check @adpPolicy_skip_wrong
#check @adpPolicy_field0_wrong
#check @adpPolicy_skip_wrong_shape
#check @adpPolicy_masked_gradeA
#check @adpPolicy_entry_gradeA
#check @adpPolicy_unmasked_fails_left
#check @adpPolicy_entry_gradeA_loss
#check @adpPolicy_pattern_undecided_left
#check @ozaki1CRISC_binary32_tight
#check @ozaki1Bound_le_cr
#check @ozaki1CRK_eq
#check @ozaki1CRA_eq
#check @ozaki1CRA_cost_le
#check @ozaki1CRA_cost_shortcut
#check @crtBasis_valid
#check @moduliForCR_spec
#check @h100F16_bestCR
#check @sumTree_error_jr
#check @dotTree_error_jr
#check @dot_eq_exactTermsRect_add
#check @exactTermsRect_error_uniform
#check @ozaki2Approx_error
#check @ozaki2FP64_error
#check @levelAcc_error
#check @ozaki1Levels_error
#check @level_exact_of_diagonals
#check @uchinoRecon_error
#check @afAccept_levelExact
#check @afAccept_levelExact_pos
#check @af_strict_late
#check @af_int8_vs_diagFits
#check @ozaki2Uchino_error
#check @uchino_R64
#check @uchino_lemma1_slack
#check @ozaki2Uchino_scaled_error
```

```lean
import OzakiMC

open Ozaki Ozaki.MC

#check @rneValue_of_finite
#check @flValue_int
#check @pairwiseGroupSum_int
#check @accumulate_int
#check @evalBlock_int
#check @runBlocks_int
#check @dotBits_int
#check @encodeExact_int
#check @xf32_encodesInts
#check @mcMultiplier_exactOn
#check @cdna3F16_exactMultiplier
#check @round32Value_within
#check @fp32Add_within
#check @mcOzaki1_eq
#check @mcOzaki1_error
#check @mcOzaki2_eq
#check @mcOzaki2_error
#check @cdna3F16_ozaki1_z3
#check @bfloat16_holds_256
#check @cdna3F16_full_blockFMA
#check @fp16_exact_where_sfma_is_not
#check @scaled_slice_product_exact
#check @mcOzaki1_isSome
#check @native32_error
#check @round32Value_nearest
#check @mcOzaki1CR_eq
#check @mcOzaki2CR_eq
#check @mcOzaki1CRE_eq
#check @mcSplitK_exactOn
#check @mcOzaki1L_error
#check @mcOzaki1D_error
#check @mcOzaki1CRL_eq
#check @mcOzaki2CRL_eq
#check @mcOzaki1CRD_eq
#check @mcOzaki2CRD_eq
#check @cdna3F16_fp64CR
#check @cdna3BF16_fp64CR
#check @mcOzaki1CRDW_eq
#check @mcOzaki1CRLW_eq
#check @round32Value_eq_rne32Q
#check @mcOzaki1CRDS_eq
#check @mcOzaki1CRLS_eq
#check @mcOzaki1CRDI_eq
#check @mcOzaki2CRDI_eq
#check @mcOzaki1I_fin
#check @mcOzaki2I_fin
#check @mcOzaki1CRBD_eq
#check @mcOzaki1CRBL_eq
#check @mcOzaki1CRID_eq
#check @mcOzaki2CRJS_eq
#check @mcOzaki1CRIDI_eq
#check @mcOzaki2CRJI_eq
#check @Ozaki.MC.evalBlock_cancel
#check @pairwiseGroupSum_cancel
#check @pairwiseSumsBounded_of_bound
#check @mcCandidates_exact
#check @cdna3F16_best
#check @cdna3F16_fp64CR10
#check @mcOzaki1_error_jr
#check @mcMultiplier2_exactOn
#check @cdna2_twoPass_fails
#check @cdna3F16_twoPass_full_blockFMA
#check @cdna3F16_best12
#check @decodeWord_decodeNat
#check @mcOzaki1CRILW_eq
```
