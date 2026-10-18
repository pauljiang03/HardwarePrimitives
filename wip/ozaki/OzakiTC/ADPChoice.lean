import OzakiTC.ADPLabels
import OzakiTC.ADPFix

/-! # Choosing ADP's slice encoding and count on the INT8 matrix multiplier

ADP's emulation converts each row and column to `W`-bit fixed point, `W = t + ESC + 1` for a target
of `t` bits (`53 + ESC + 1` for FP64, `adpWidth`), cuts the integers into `s` byte slices, and
multiplies all `s²` slice pairs on the INT8 matrix multiplier. Its knobs are the slice encoding and
the slice count, which the encoding's range fixes (`slicesNeededWith`, `slicesNeededWith_spec`); the
exponent span `ESC` comes from the data.

* **Every candidate is exact** (`adpCandidate_exact`): with any of the three encodings and its
  slice count, an emulated entry is one binary64 rounding of the fixed-point product, for vectors
  with `k · 2^16 < 2^31` (`emulEntryWith_eq`); with the remap encoding the INT8 matrix multiplier
  with split-K makes this hold for every length (`adpCRE_eq`).
* **The cost** of an encoding is `s² · ⌈k / K₈⌉` INT8 blocks of `K₈` byte products. The INT8
  matrix multiplier of this development has no block FMA structure, since INT8 hardware semantics
  are out of scope (issue #2); `K₈ = 32`, the `k` of the `m16n8k32` integer MMA shape, is a modeling
  assumption. INT8 blocks are not comparable with the Tensor Core or Matrix Core blocks of the other
  choices without the instructions' relative throughput, which the models do not give.

**The remap encoding is never worse than the naive one** (`adpCost_remap_le_naive`), as the paper
says. It is not always the cheapest: its slices are all signed bytes, so `s` remapped slices hold
`W ≤ 8s − 2` bits, while the floor encoding (unsigned low bytes, a signed lead byte) holds
`W ≤ 8s − 1`. When `W ≡ 7 (mod 8)` (`ESC ≡ 1 (mod 8)` for FP64), remap needs one more slice:
`ESC = 1` costs `64` slice pairs remapped against `49` with floor digits (`adp_best`). The floor
encoding needs INT8 instructions that take unsigned operands.

## Results (inner dimension `k = 1024`, `K₈ = 32`, INT8 blocks)

| target | `ESC` | `W` | best encoding | slices | blocks | remap | naive |
| --- | --- | --- | --- | --- | --- | --- | --- |
| FP64 | 0 | 54 | remap | 7 | 1568 | 1568 | 2048 |
| FP64 | 1 | 55 | floor | 7 | 1568 | 2048 | 2048 |
| FP64 | 10 | 64 | remap | 9 | 2592 | 2592 | 3200 |
| binary32 | 0 | 25 | remap | 4 | 512 | 512 | 512 |
| binary32 | 10 | 35 | remap | 5 | 800 | 800 | 1152 |
-/

namespace Ozaki.TC

open scoped TensorCore

/-- The fixed-point width for `t` bits and exponent span `e`. -/
def adpW (t e : ℕ) : ℕ := t + e + 1

/-- INT8 blocks of `K₈` byte products for one slice-pair product of inner dimension `k`. -/
def int8Blocks (K8 k : ℕ) : ℕ := (k + K8 - 1) / K8

/-- **ADP's cost** with an encoding: all `s²` slice pairs, `s` the encoding's slice count. -/
def adpCost (enc : ADP.SliceEncoding) (K8 t e k : ℕ) : ℕ :=
  slicesNeededWith enc (adpW t e) * slicesNeededWith enc (adpW t e) * int8Blocks K8 k

/-- The three encodings, remap first. -/
def adpEncodings : List ADP.SliceEncoding := [.remap, .floorU8, .naiveS8]

/-- The cheapest encoding; the first on a tie. -/
def adpBest (K8 t e k : ℕ) : Option ADP.SliceEncoding :=
  adpEncodings.foldl (fun acc enc => match acc with
    | none => some enc
    | some a => if adpCost enc K8 t e k < adpCost a K8 t e k then some enc else some a) none

/-- **Every candidate is exact**: an emulated entry with any encoding and its slice count is one
binary64 rounding of the fixed-point product. -/
theorem adpCandidate_exact (enc : ADP.SliceEncoding) (t e : ℕ) {x y : List ℚ}
    (hk : x.length * 2 ^ 16 < 2 ^ 31) :
    emulEntryWith enc (adpW t e) (slicesNeededWith enc (adpW t e)) x y =
      fp64Round (ADP.fixedProduct (adpW t e) x y) :=
  emulEntryWith_eq (slicesNeededWith_spec enc _).1 (slicesNeededWith_spec enc _).2.1 hk

/-- **Remap is never worse than the naive signed bytes.** -/
theorem adpCost_remap_le_naive (K8 t e k : ℕ) :
    adpCost .remap K8 t e k ≤ adpCost .naiveS8 K8 t e k := by
  unfold adpCost
  have hn := slicesNeededWith_spec .naiveS8 (adpW t e)
  have hr : slicesNeededWith .remap (adpW t e) = slicesNeeded (adpW t e) := slicesNeededWith_remap _
  have hle : slicesNeeded (adpW t e) ≤ slicesNeededWith .naiveS8 (adpW t e) :=
    slicesNeeded_le_naive hn.1 hn.2.1
  rw [hr]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hle hle)

/-- **The cheapest encoding at `k = 1024`** (`K₈ = 32`): remap for FP64 at `ESC = 0` and `10` and
for binary32; floor digits at `ESC = 1`, where remap needs an eighth slice. -/
theorem adp_best :
    adpBest 32 53 0 1024 = some .remap ∧ adpCost .remap 32 53 0 1024 = 1568 ∧
      adpCost .naiveS8 32 53 0 1024 = 2048 ∧
    adpBest 32 53 1 1024 = some .floorU8 ∧ adpCost .floorU8 32 53 1 1024 = 1568 ∧
      adpCost .remap 32 53 1 1024 = 2048 ∧
    adpBest 32 53 10 1024 = some .remap ∧ adpCost .remap 32 53 10 1024 = 2592 ∧
      adpCost .naiveS8 32 53 10 1024 = 3200 ∧
    adpBest 32 24 0 1024 = some .remap ∧ adpCost .remap 32 24 0 1024 = 512 ∧
    adpBest 32 24 10 1024 = some .remap ∧ adpCost .remap 32 24 10 1024 = 800 ∧
      adpCost .naiveS8 32 24 10 1024 = 1152 := by
  decide +kernel

/-- **Correctly rounded FP64 with ADP's slicing at `ESC = 0`**: `7` remapped slices of a `54`-bit
fixed point, every product on the INT8 matrix multiplier, binary64 inputs of any length. -/
theorem adp_fp64CR_esc0 {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    adpCRE [(7, 54)] 300 x y = fp64Round (dot x y) := by
  refine adpCRE_eq ?_ (by decide) hx hy hlen
  intro c hc
  rw [List.mem_singleton.mp hc]
  exact ⟨by decide, by decide +kernel⟩

end Ozaki.TC
