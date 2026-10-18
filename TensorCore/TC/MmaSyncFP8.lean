import TensorCore.TC.GPUs

/-! # FP8 through `mma.sync` on H100, H200, B200 and the RTX PRO 6000

Khattak and Mikaitis (*Accurate Models of NVIDIA Tensor Cores*, Sections 4.1.6 to 4.1.8,
Figure 5(c) and Table 4) report that on H100, H200 and B200 an FP8 `mma.sync` does not run on an FP8
Tensor Core: the operands are converted to FP16 and the instruction runs as FP16 `HMMA.16816`
instructions. The 32 products of an `m16n8k32` instruction are split by alternating pairs of
positions, `{1, 2, 5, 6, …, 29, 30}` and `{3, 4, 7, 8, …, 31, 32}`, each group is summed by one FP16
block FMA, and `c` is added after the products, in binary32 with round-to-nearest-even. The same
interleaving holds for `m16n8k16`, with eight products in each group.

The model of one instruction (`mmaSyncFP8`):

* every FP8 operand is converted to FP16 (exact: `e4m3ToF16_exact`, `e5m2ToF16_exact`);
* the first group is one Hopper FP16 block FMA (`N_FMA = 16`, the 23-bit mantissa plus 2 padding
  bits after alignment, `e_align^min = −133`) from a zero accumulator;
* the second group is one Hopper FP16 block FMA whose accumulator input is the first block's output;
* `c` is added to the second block's output in binary32, rounded to nearest even (late
  accumulation of `c`).

The paper does not state that the second block takes the first block's output, nor the order of
the groups. Its interleaving experiment excludes the order in which the second group comes first
(`interleave_test_e5m2`, `interleave_test_reversed`); a recorded B200 output excludes two
independent blocks whose outputs are added in binary32 (`separate_groups_excluded`). The replay of
the recorded rows is in `scripts/check_device_replay.py`.

The RTX PRO 6000 (Blackwell) runs an FP8 `mma.sync` as `QMMA.16832` with B200's FP8 features: 32
products, the 23-bit mantissa plus 2 padding bits after alignment, and `c` inside the block FMA
(`rtxPro6000E4M3F32`, `rtxPro6000E5M2F32`). -/

namespace TensorCore

/-! ## The model -/

/-- The products at positions `k` (from 0) with `k mod 4 < 2`: the first FP16 block FMA. -/
def groupA {α : Type} (xs : List α) : List α :=
  (xs.zipIdx.filter fun (_, k) => k % 4 < 2).map Prod.fst

/-- The products at positions `k` with `k mod 4 ≥ 2`: the second FP16 block FMA. -/
def groupB {α : Type} (xs : List α) : List α :=
  (xs.zipIdx.filter fun (_, k) => 2 ≤ k % 4).map Prod.fst

/-- Zero pairs appended up to `n` products. -/
def padTo (n : ℕ) (ps : List (F16 × F16)) : List (F16 × F16) :=
  ps ++ List.replicate (n - ps.length) (0, 0)

/-- One FP16 block FMA of the Hopper model (H100, H200; B200 shares Hopper's FP16 arithmetic). -/
def hmma (c : F32) (ps : List (F16 × F16)) : Option F32 :=
  (evalBlock (p := hopperF16F32) ⟨padTo 16 ps, c⟩).toOption.map (·.output.bits)

/-- One FP8 `mma.sync` (`m16n8k32`, or `m16n8k16` with eight products per group) on H100, H200
and B200, for one output: FP8 converted to FP16, the interleaved groups chained through two FP16
block FMAs from a zero accumulator, then `c` added in binary32 with round-to-nearest-even. -/
def mmaSyncFP8 (conv : BitVec 8 → F16) (c : F32) (ps : List (BitVec 8 × BitVec 8)) :
    Option F32 := do
  let ps16 := ps.map fun (a, b) => (conv a, conv b)
  let d1 ← hmma 0 (groupA ps16)
  let d2 ← hmma d1 (groupB ps16)
  addFp32 d2 c

/-- A long inner product through consecutive FP8 `mma.sync` instructions of `k` products each
(the last padded with zero pairs), each output the next instruction's `c`. -/
def mmaSyncFP8Dot (conv : BitVec 8 → F16) (k : ℕ) (c : F32) (ps : List (BitVec 8 × BitVec 8)) :
    Option F32 :=
  let n := (ps.length + k - 1) / k
  (chunks k n (ps ++ List.replicate (n * k - ps.length) (0, 0))).foldlM
    (fun c inst => mmaSyncFP8 conv c inst) c

/-- The RTX PRO 6000 (Blackwell) runs FP8 `mma.sync` as `QMMA.16832` with B200's FP8 features:
`N_FMA = 32`, 25 mantissa bits after alignment, `c` inside the block FMA. -/
@[implicit_reducible] def rtxPro6000E4M3F32 : Model := blackwellE4M3F32
@[implicit_reducible] def rtxPro6000E5M2F32 : Model := blackwellE5M2F32

/-! ## Kernel-checked consequences -/

/-- E5M2 words: `1`, `2^-12`. -/
def one8 : BitVec 8 := 0x3c
def tiny8 : BitVec 8 := 0x0c

/-- The paper's interleaving experiment in E5M2: `p₁ = 1`, `p₂ = 2^-24` and one more product
`2^-24` at position `k` (from 0), all others zero, `c = 0`. The output is `1 + 2^-23` exactly when
position `k` is in the first group (`k mod 4 < 2`), and `1` otherwise. -/
def interleaveInput (k : ℕ) : List (BitVec 8 × BitVec 8) :=
  (List.range 32).map fun i =>
    if i = 0 then (one8, one8) else if i = 1 ∨ i = k then (tiny8, tiny8) else (0, 0)

theorem interleave_test_e5m2 :
    ∀ k, k < 32 → 2 ≤ k →
      mmaSyncFP8 e5m2ToF16 0 (interleaveInput k) =
        some (if k % 4 < 2 then 0x3f800001 else 0x3f800000) := by
  decide +kernel

/-- The same experiment on the order with the second group first gives `1 + 2^-23` at every
position, so it does not reproduce the observed pattern. -/
def mmaSyncFP8BA (conv : BitVec 8 → F16) (c : F32) (ps : List (BitVec 8 × BitVec 8)) :
    Option F32 := do
  let ps16 := ps.map fun (a, b) => (conv a, conv b)
  let d1 ← hmma 0 (groupB ps16)
  let d2 ← hmma d1 (groupA ps16)
  addFp32 d2 c

theorem interleave_test_reversed :
    ∀ k, k < 32 → 2 ≤ k → mmaSyncFP8BA e5m2ToF16 0 (interleaveInput k) = some 0x3f800001 := by
  decide +kernel

/-- A single 32-product block (the B200 FP8 model from `c = 0`), followed by the same late
addition, does not show the pattern either: the experiment separates it from `mma.sync`. -/
theorem interleave_test_single_block :
    ∀ k, k < 32 → 2 ≤ k → blackwellE5M2F32.dotThenAdd 0 (interleaveInput k) = some 0x3f800001 := by
  decide +kernel

/-- Late accumulation of `c`: with `c = 1` and the products `2^-24 + 2^-24 + 2^-24`, all in the
first group, the `mma.sync` path rounds `1 + 3·2^-24` to nearest (`1 + 2^-22`), while a block FMA
that holds `c` (the RTX PRO 6000 and B200 FP8 block FMAs) truncates it (`1 + 2^-23`). -/
def lateInput : List (BitVec 8 × BitVec 8) :=
  (List.range 32).map fun i => if i = 0 ∨ i = 1 ∨ i = 4 then (tiny8, tiny8) else (0, 0)

theorem late_c_witness :
    mmaSyncFP8 e5m2ToF16 0x3f800000 lateInput = some 0x3f800002 ∧
    rtxPro6000E5M2F32.dot 0x3f800000 lateInput = some 0x3f800001 := by
  decide +kernel

/-- The alternative in which the two groups are summed by independent FP16 block FMAs from `+0`,
their outputs added in binary32, then `c` added in binary32. -/
def mmaSyncFP8Separate (conv : BitVec 8 → F16) (c : F32) (ps : List (BitVec 8 × BitVec 8)) :
    Option F32 := do
  let ps16 := ps.map fun (a, b) => (conv a, conv b)
  let d1 ← hmma 0 (groupA ps16)
  let d2 ← hmma 0 (groupB ps16)
  let s ← addFp32 d1 d2
  addFp32 s c

/-- The operands of row 3936 (line number) of the recorded B200 E5M2 vectors of the Accurate Models
toolbox, commit 79143bd (`vendor/matlab-tensor-core-79143bd/model_validation/B200/E5M2/`): `c` is
`0x3f01684f` and the recorded output `0xc10ddf7c`. -/
def b200E5M2Row3936 : List (BitVec 8 × BitVec 8) :=
  [(0xc0, 0x37), (0xb8, 0xbb), (0xb9, 0xb6), (0xb5, 0x35), (0xa7, 0x04), (0x2c, 0xb8),
   (0x3b, 0x30), (0xb6, 0xb7), (0x3d, 0x3b), (0x2c, 0xbc), (0x40, 0xbc), (0xba, 0xbc),
   (0xa9, 0xbe), (0x38, 0x3c), (0x39, 0xba), (0xbd, 0x38), (0xb6, 0xb4), (0x38, 0xc0),
   (0xbc, 0x35), (0x3c, 0xb7), (0x33, 0x3c), (0x38, 0xc0), (0xbe, 0x32), (0x3d, 0xb7),
   (0xb2, 0x34), (0x39, 0xaf), (0x39, 0xbb), (0x27, 0x3b), (0xbd, 0x3d), (0xbf, 0x3b),
   (0xbc, 0x39), (0xb9, 0x3e)]

/-- On that recorded row the `mma.sync` model gives the recorded output, and independent groups
give the next binary32 word. -/
theorem separate_groups_excluded :
    mmaSyncFP8 e5m2ToF16 0x3f01684f b200E5M2Row3936 = some 0xc10ddf7c ∧
    mmaSyncFP8Separate e5m2ToF16 0x3f01684f b200E5M2Row3936 = some 0xc10ddf7d := by
  decide +kernel

end TensorCore
