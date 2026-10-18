import TensorCore.TC.GPUs

/-! # FP8 through `mma.sync` on H100, H200, B200 and the RTX PRO 6000

On H100, H200 and B200 an FP8 `mma.sync` runs on the FP16 Tensor Core (Khattak and Mikaitis,
Sections 4.1.6 to 4.1.8); the model sums two interleaved groups of products with chained FP16 block
FMAs, then adds `c` in FP32 with round-to-nearest-even. The RTX PRO 6000 runs it as `QMMA.16832`
with B200's FP8 block FMA. -/

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

/-- One output of an FP8 `mma.sync` on H100, H200 and B200: two chained FP16 block FMAs, then `c`. -/
def mmaSyncFP8 (conv : BitVec 8 → F16) (c : F32) (ps : List (BitVec 8 × BitVec 8)) :
    Option F32 := do
  let ps16 := ps.map fun (a, b) => (conv a, conv b)
  let d1 ← hmma 0 (groupA ps16)
  let d2 ← hmma d1 (groupB ps16)
  addFp32 d2 c

/-- A long inner product through consecutive FP8 `mma.sync` instructions of `k` products each. -/
def mmaSyncFP8Dot (conv : BitVec 8 → F16) (k : ℕ) (c : F32) (ps : List (BitVec 8 × BitVec 8)) :
    Option F32 :=
  let n := (ps.length + k - 1) / k
  (chunks k n (ps ++ List.replicate (n * k - ps.length) (0, 0))).foldlM
    (fun c inst => mmaSyncFP8 conv c inst) c

/-- RTX PRO 6000 FP8 `mma.sync` (`QMMA.16832`): B200's FP8 block FMA, with `c` inside. -/
@[implicit_reducible] def rtxPro6000E4M3F32 : Model := blackwellE4M3F32
@[implicit_reducible] def rtxPro6000E5M2F32 : Model := blackwellE5M2F32

/-! ## Kernel-checked consequences -/

/-- E5M2 words: `1`, `2^-12`. -/
def one8 : BitVec 8 := 0x3c
def tiny8 : BitVec 8 := 0x0c

/-- The paper's interleaving experiment in E5M2, with the extra product at position `k`. -/
def interleaveInput (k : ℕ) : List (BitVec 8 × BitVec 8) :=
  (List.range 32).map fun i =>
    if i = 0 then (one8, one8) else if i = 1 ∨ i = k then (tiny8, tiny8) else (0, 0)

theorem interleave_test_e5m2 :
    ∀ k, k < 32 → 2 ≤ k →
      mmaSyncFP8 e5m2ToF16 0 (interleaveInput k) =
        some (if k % 4 < 2 then 0x3f800001 else 0x3f800000) := by
  decide +kernel

/-- The order with the second group first. -/
def mmaSyncFP8BA (conv : BitVec 8 → F16) (c : F32) (ps : List (BitVec 8 × BitVec 8)) :
    Option F32 := do
  let ps16 := ps.map fun (a, b) => (conv a, conv b)
  let d1 ← hmma 0 (groupB ps16)
  let d2 ← hmma d1 (groupA ps16)
  addFp32 d2 c

theorem interleave_test_reversed :
    ∀ k, k < 32 → 2 ≤ k → mmaSyncFP8BA e5m2ToF16 0 (interleaveInput k) = some 0x3f800001 := by
  decide +kernel

/-- A single 32-product block from `c = 0`, then the late addition of `c`. -/
theorem interleave_test_single_block :
    ∀ k, k < 32 → 2 ≤ k → blackwellE5M2F32.dotThenAdd 0 (interleaveInput k) = some 0x3f800001 := by
  decide +kernel

/-- Late accumulation of `c`: `c = 1` and three products `2^-24` in the first group. -/
def lateInput : List (BitVec 8 × BitVec 8) :=
  (List.range 32).map fun i => if i = 0 ∨ i = 1 ∨ i = 4 then (tiny8, tiny8) else (0, 0)

theorem late_c_witness :
    mmaSyncFP8 e5m2ToF16 0x3f800000 lateInput = some 0x3f800002 ∧
    rtxPro6000E5M2F32.dot 0x3f800000 lateInput = some 0x3f800001 := by
  decide +kernel

/-- Independent FP16 block FMAs for the two groups, their outputs and then `c` added in FP32. -/
def mmaSyncFP8Separate (conv : BitVec 8 → F16) (c : F32) (ps : List (BitVec 8 × BitVec 8)) :
    Option F32 := do
  let ps16 := ps.map fun (a, b) => (conv a, conv b)
  let d1 ← hmma 0 (groupA ps16)
  let d2 ← hmma 0 (groupB ps16)
  let s ← addFp32 d1 d2
  addFp32 s c

/-- Operands of row 3936 of the recorded B200 E5M2 vectors (Accurate Models toolbox, commit 79143bd). -/
def b200E5M2Row3936 : List (BitVec 8 × BitVec 8) :=
  [(0xc0, 0x37), (0xb8, 0xbb), (0xb9, 0xb6), (0xb5, 0x35), (0xa7, 0x04), (0x2c, 0xb8),
   (0x3b, 0x30), (0xb6, 0xb7), (0x3d, 0x3b), (0x2c, 0xbc), (0x40, 0xbc), (0xba, 0xbc),
   (0xa9, 0xbe), (0x38, 0x3c), (0x39, 0xba), (0xbd, 0x38), (0xb6, 0xb4), (0x38, 0xc0),
   (0xbc, 0x35), (0x3c, 0xb7), (0x33, 0x3c), (0x38, 0xc0), (0xbe, 0x32), (0x3d, 0xb7),
   (0xb2, 0x34), (0x39, 0xaf), (0x39, 0xbb), (0x27, 0x3b), (0xbd, 0x3d), (0xbf, 0x3b),
   (0xbc, 0x39), (0xb9, 0x3e)]

/-- The recorded B200 row 3936 excludes independent groups. -/
theorem separate_groups_excluded :
    mmaSyncFP8 e5m2ToF16 0x3f01684f b200E5M2Row3936 = some 0xc10ddf7c ∧
    mmaSyncFP8Separate e5m2ToF16 0x3f01684f b200E5M2Row3936 = some 0xc10ddf7d := by
  decide +kernel

end TensorCore
