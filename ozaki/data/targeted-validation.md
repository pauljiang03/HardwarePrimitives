# Targeted hardware validation

`targeted-validation.json` lists 140 inputs to run on NVIDIA (V100, A100, H100) and AMD
(MI100, MI210/MI250, MI300) matrix units, with the output word the Lean models predict for each.
The inputs are the models' distinguishing counterexamples, plus boundary cases that the 35,000
NVIDIA measurements behind the TensorCore models do not exercise: minimum alignment exponents, zero
and negative-zero operands, subnormal operands, TF32's wide exponent range, and H100 TF32 MMA.

The predictions come from the models, not from hand computation:

* NVIDIA: `scripts/targeted/TensorCoreCases.lean`, `#eval` of `TensorCore.runBlocks`, run from
  the repository root;
* AMD: `scripts/targeted/MatrixCoreCases.lean`, `#eval` of `MatrixCore.dotBits`, run from `amd/`.

`scripts/targeted_validation.py` runs both scripts and writes the JSON. For the 56 cases that come
from kernel-checked theorems, it also checks that the `#eval` output equals the value each theorem
states (`agrees_with_theorem`).

```sh
# from ozaki/ (the root TensorCore and amd/ MatrixCore projects must be built)
python3 scripts/targeted_validation.py > data/targeted-validation.json
```

## Cases

| Category | Cases | Source |
| --- | ---: | --- |
| `full-block-exactness` | 8 | `a100_full_blockFMA`, `a100_exact_where_binary32_is_not`, the H100 block FMA example in `OzakiTC/TwoPass.lean`, `cdna3F16_full_blockFMA` (29331464 vs A100's 29331462), `fp16_exact_where_sfma_is_not` |
| `cancellation` | 6 | `a100_cancel_zero`, `a100_cancel_2047`, `h100_cancel_zero`, `cdna3_cancel_zero`, `cdna12_cancel_c` |
| `two-pass` | 12 (6 pairs) | A100/H100 examples in `OzakiTC/TwoPass.lean`, `cdna3F16_twoPass_full_blockFMA`, `sfma_twoProd`, `cdna2_twoPass_fails` (CDNA 2 fails, CDNA 1 recovers) |
| `non-monotonicity` | 30 | V100/A100/H100 `c`-families and `range_witnesses` (`tests/TensorCoreTests/TC/Monotonicity.lean`), the eight `cdna*_nonmonotonic` pairs (fp8 included), `cdna3F16_products_not_determined` |
| `min-alignment-exponent` | 8 (new) | A100/H100, BF16 and TF32: a kept/dropped pair that pins the minimum alignment exponent |
| `signed-zero` | 18 (new) | `−0` products and `c = −0` on the FP16 variants of every architecture |
| `subnormal` | 34 (new) | subnormal fp16/bf16/TF32 operands, subnormal outputs, subnormal `c` |
| `tf32-exponent-range` | 12 (new) | products from `2^-126` to `2^127`; partial sums above FP32's range |
| `h100-tf32-mma` | 8 (new) | full block FMA, two passes, cancellation, an FMA-size probe, an padding-bits probe, the `c`-family below its threshold |
| `padding-bits` | 4 (new) | the padding-bits probe on the BF16 and TF32 variants |

Sixteen cases use the H100 TF32 MMA model `hopperTF32MmaF32` across these categories.

Each case records:

* `inputs`: `c` and the vectors `a`, `b` in `k` order, as hex words; TF32 cases also give the
  32-bit register words;
* `predicted.d`: the model's output word;
* `exact_sum`: the exact `c + Σ aᵢbᵢ`;
* `instruction`: a suggested instruction;
* `lean_source`: the theorem or construction the case comes from;
* `mismatch_means`: what a different output would mean.

Cases marked `(new)` were constructed for this suite. Where it helps localise a mismatch,
`alternatives` gives the model's output for the same input under a nearby hypothesis: a minimum
alignment exponent one higher or one lower, none at all, `p ± 1` padding bits, or block
FMAs of size 4 instead of 8.

Some cases are probes, built so that the measured word identifies a model parameter:

* **Minimum-alignment-exponent pair (`*-min-align-exp-kept`, `*-min-align-exp-dropped`).** A
  product of `2^-140` puts the maximum exponent below the minimum alignment exponent
  `e_align^min`, so alignment is to `e_align^min`. A product `−2^-j` lies either exactly on the
  predicted grid `2^(e_align^min − F)` or one step below it. The model predicts `0x000001FF` for
  the kept case and `0x00000200` for the dropped one. Only the model's minimum alignment exponent
  gives that pair: with none (or a lower one) both are `0x1FF`; with a higher one both are
  `0x200`.
* **FMA-size probe (`nv-tf32-k8-fma-size-probe`).** The inputs are
  `2^23 + 2^23 + 1 | −2^23 − 2^23` with `k = 8`. One block FMA of size 8 returns `1.0`. Two
  chained block FMAs of size 4 lose the `1` in the FP32 output of the first and return `0`.
* **Padding-bits probe (`*-align-bits-probe`).** With `c = 1` and products of
  `1.5·2^-25`, the output word gives the number of padding bits `p`. On H100 TF32 MMA:
  `p = 1` gives `0x3F800000`, `p = 2` (the model) `0x3F800002`, and `p = 3` `0x3F800003`.

## Running on hardware (pseudo-steps)

1. For each case, build one output element `d = c + Σ aᵢbᵢ`:
   * put the vector `a` in row 0 of `A` and `b` in column 0 of `B`, both in `k` order;
   * set `C[0][0] = c`;
   * set every other entry of `A`, `B` and `C` to zero;
   * read `D[0][0]`.

   Use the suggested instruction or another with the same `k`. If an instruction has a larger
   `k`, put the vector first and fill the rest with zeros: a trailing block FMA whose products are
   all zero returns its `c` unchanged. Signed-zero cases need an instruction whose `k` equals the
   vector length.
2. Pass words bit-exactly. Do not convert them:
   * load fp16/bf16/fp8 words as raw 16- or 8-bit patterns;
   * for TF32, load `a_fp32_register`/`b_fp32_register` directly, with no `cvt.rna.tf32.f32`;
   * for XF32, load the binary32 words, whose low 13 bits are already zero.

   Compile without fast-math.
3. Compare `D[0][0]` with `predicted.d` bit for bit. For cases with `status: "outside model
   domain"` (TF32 `2^127 + 2^127`), record the output: the model makes no prediction there.
4. Two-pass pairs:
   * run `/pass1`, then `/pass2`, whose `c` is the model's `−D1`;
   * if pass 1 matched, that `c` is the device's own `−D1`;
   * otherwise rerun pass 2 with `c = −D1(device)`, rounded to nearest, and report both.
5. Report `id`, device, instruction, the observed `d` and whether it matches. When a case does
   not match, also report which `alternatives` entry it equals, if any.
6. Before the suite, run a harness self-check, because a wrong fragment layout looks like a model
   mismatch:
   * all-ones `a`, `b` with `c = 0.5` should give `k + 0.5`;
   * the `nv-a100-f16-cancel-2047` vector placed in a different row should leave `D[0][0] = c`.

Scope notes:

* The H100 FP16/BF16 models describe HMMA (`mma.sync`/WMMA). The models make no separate claim
  about `wgmma.mma_async`; running the H100 cases through `wgmma` (for example `m64n8k16`)
  tests whether WGMMA shares the model.
* A100 TF32 vectors of length 8 run as two chained block FMAs of size 4 (`m16n8k8`).
* FP8 appears only in the AMD non-monotonicity pairs.
* INT8 is out of scope.

## Kernel sketches (untested)

The sketches below are **untested** and have not been compiled. They show the shape of a
harness, not a validated one.

The fragment layouts follow the PTX ISA section "Matrix Fragments for `mma.m16n8k8`" (TF32).
Check them against the ISA before use.

```cuda
// UNTESTED. H100 TF32 MMA: one m16n8k8 instruction, one warp. A is 16x8 row-major, B is 8x8
// (k x n) column-major, C/D 16x8 row-major; all words already TF32 (low 13 bits zero).
__global__ void mma_tf32_m16n8k8(const uint32_t* A, const uint32_t* B, const float* C, float* D) {
  int lane = threadIdx.x, g = lane >> 2, t = lane & 3;
  uint32_t a0 = A[g * 8 + t], a1 = A[(g + 8) * 8 + t], a2 = A[g * 8 + t + 4], a3 = A[(g + 8) * 8 + t + 4];
  uint32_t b0 = B[g * 8 + t], b1 = B[g * 8 + t + 4];          // B column g, rows t and t + 4
  float c0 = C[g * 8 + 2 * t], c1 = C[g * 8 + 2 * t + 1], c2 = C[(g + 8) * 8 + 2 * t], c3 = C[(g + 8) * 8 + 2 * t + 1];
  float d0, d1, d2, d3;
  asm volatile("mma.sync.aligned.m16n8k8.row.col.f32.tf32.tf32.f32 "
               "{%0,%1,%2,%3}, {%4,%5,%6,%7}, {%8,%9}, {%10,%11,%12,%13};"
               : "=f"(d0), "=f"(d1), "=f"(d2), "=f"(d3)
               : "r"(a0), "r"(a1), "r"(a2), "r"(a3), "r"(b0), "r"(b1),
                 "f"(c0), "f"(c1), "f"(c2), "f"(c3));
  D[g * 8 + 2 * t] = d0; D[g * 8 + 2 * t + 1] = d1; D[(g + 8) * 8 + 2 * t] = d2; D[(g + 8) * 8 + 2 * t + 1] = d3;
}

// UNTESTED. FP16 (and analogously BF16, TF32 m16n16k8) through WMMA, which needs no layout:
// V100 lowers m16n16k16 to HMMA.844 (4 block FMAs of size 4), A100 to HMMA.1688 (2 x 8), H100
// to HMMA.16816 (1 x 16).
#include <mma.h>
using namespace nvcuda;
__global__ void wmma_f16(const __half* A, const __half* B, const float* C, float* D) {
  wmma::fragment<wmma::matrix_a, 16, 16, 16, __half, wmma::row_major> a;
  wmma::fragment<wmma::matrix_b, 16, 16, 16, __half, wmma::col_major> b;
  wmma::fragment<wmma::accumulator, 16, 16, 16, float> c;
  wmma::load_matrix_sync(a, A, 16); wmma::load_matrix_sync(b, B, 16);
  wmma::load_matrix_sync(c, C, 16, wmma::mem_row_major);
  wmma::mma_sync(c, a, b, c);
  wmma::store_matrix_sync(D, c, 16, wmma::mem_row_major);
}
```

For the AMD sketch, take operand and accumulator layouts from AMD's Matrix Instruction
Calculator (`amd_matrix_instruction_calculator`, for example `--architecture cdna3 --instruction
v_mfma_f32_32x32x8_f16 --detail-instruction`). Verify any layout with the self-check above.

```cpp
// UNTESTED. CDNA 3 fp16, one v_mfma_f32_32x32x8_f16 (k = 8, one block of 8), one wavefront of 64.
// Assumed layout (check with the calculator): lane l holds A[l % 32][4 * (l / 32) + j] and
// B[4 * (l / 32) + j][l % 32] for j = 0..3; D[0][0] is accumulator element 0 of lane 0.
typedef _Float16 half4 __attribute__((ext_vector_type(4)));
typedef float float16 __attribute__((ext_vector_type(16)));
__global__ void mfma_f16(const _Float16* A /*32x8*/, const _Float16* B /*8x32*/, float c00, float* d00) {
  int l = threadIdx.x, r = l % 32, k0 = 4 * (l / 32);
  half4 a, b;
  for (int j = 0; j < 4; ++j) { a[j] = A[r * 8 + k0 + j]; b[j] = B[(k0 + j) * 32 + r]; }
  float16 acc = {};
  if (l == 0) acc[0] = c00;      // C[0][0]; every other C entry is zero
  acc = __builtin_amdgcn_mfma_f32_32x32x8f16(a, b, acc, 0, 0, 0);
  if (l == 0) *d00 = acc[0];
}
```
