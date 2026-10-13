import OzakiTCTests.FinalPipelines
import OzakiTC.CheckedTight
import OzakiTC.IEEEWords

/-! # Tighter widths, guarded matrix multipliers, signed checked pipelines, integer special detection

Small kernel-checked cases (`decide +kernel`) on the four binary64 entries of
`OzakiTCTests.FinalPipelines`:

* the checked Ozaki-I and Ozaki-II on V100 fp16 blocks through the guarded split-K matrix multiplier
  (`v100SplitKC`) at the tighter widths, `263` bits for data and `17` for exponents and counters,
  with the rounding test succeeding and through the exact fallback alone, against the binary64 round
  to nearest; and `none` with a `64`-bit data register or an `8`-bit exponent register;
* checked ADP-style slicing on the guarded INT8 matrix multipliers at `259` and `17` bits, with a
  configuration and through the exact fallback;
* the signed checked Ozaki-II and ADP on products that are all `−0` and that cancel;
* the guarded INT8 register refuses to wrap where TC-EFT's register wraps, and the guarded split-K
  matrix multiplier fails a guard when its chunk results exceed the data register. -/

open TensorCore Ozaki Ozaki.TC Ozaki.Checked OzakiTCTests.FinalPipelines

namespace OzakiTCTests.CheckedTight

example : ozaki1CRIC ⟨263, 17⟩ (v100SplitKC ⟨263, 17⟩) 53 (-1022) 1023 11 96 [5, 6] 175 xs ys =
      some (rne64 (dot (entryVals xs) (entryVals ys))) ∧
    ozaki1CRIC ⟨263, 17⟩ (v100SplitKC ⟨263, 17⟩) 53 (-1022) 1023 11 96 [] 175 xs ys =
      some (rne64 (dot (entryVals xs) (entryVals ys))) := by
  decide +kernel

/-- Too narrow: the integers of the truncated sum need more than a `64`-bit data register, and the
exponents more than an `8`-bit one. -/
example : ozaki1CRIC ⟨64, 17⟩ (v100SplitKC ⟨64, 17⟩) 53 (-1022) 1023 11 96 [5, 6] 175 xs ys = none ∧
    ozaki1CRIC ⟨263, 8⟩ (v100SplitKC ⟨263, 8⟩) 53 (-1022) 1023 11 96 [5, 6] 175 xs ys = none := by
  decide +kernel

example : ozaki2CRJC ⟨263, 17⟩ (v100SplitKC ⟨263, 17⟩) 53 (-1022) 1023 cfgs2 11 175 xs ys =
    some (rne64 (dot (entryVals xs) (entryVals ys))) := by
  decide +kernel

example : adpCRJC ⟨259, 17⟩ [(8, 56)] 300 xs ys = some (rne64 (dot (entryVals xs) (entryVals ys))) ∧
    adpCRJC ⟨259, 17⟩ [] 300 xs ys = some (rne64 (dot (entryVals xs) (entryVals ys))) := by
  decide +kernel

/-! ## Signed checked pipelines -/

example : ozaki2CRJSC ⟨263, 17⟩ (v100SplitKC ⟨263, 17⟩) 53 (-1022) 1023 cfgs2 11 175 negZ.1 negZ.2 =
      some (some ⟨0, true⟩) ∧
    ozaki2CRJSC ⟨263, 17⟩ (v100SplitKC ⟨263, 17⟩) 53 (-1022) 1023 cfgs2 11 175 cancel.1 cancel.2 =
      some (some ⟨0, false⟩) ∧
    adpCRJSC ⟨259, 17⟩ [(8, 56)] 300 negZ.1 negZ.2 = some (some ⟨0, true⟩) ∧
    adpCRJSC ⟨259, 17⟩ [(8, 56)] 300 cancel.1 cancel.2 = some (some ⟨0, false⟩) := by
  decide +kernel

/-! ## The guarded matrix multipliers -/

/-- Three products `2^30` total `3 · 2^30 > 2^31`: TC-EFT's 32-bit register wraps, the guarded one
refuses. -/
example : int8Dot 32 [2 ^ 15, 2 ^ 15, 2 ^ 15] [2 ^ 15, 2 ^ 15, 2 ^ 15] ≠ 3 * 2 ^ 30 ∧
    int8DotC ⟨64, 17⟩ [2 ^ 15, 2 ^ 15, 2 ^ 15] [2 ^ 15, 2 ^ 15, 2 ^ 15] = none := by
  decide +kernel

/-- Products of `11`-bit slices exceed a `20`-bit data register: the guarded split-K matrix
multiplier fails a guard; with `30` bits it returns the exact product. -/
example : v100SplitKC ⟨20, 17⟩ [2047, 2047, 2047, 2047] [2047, 2047, 2047, 2047] = none ∧
    v100SplitKC ⟨30, 17⟩ [2047, 2047, 2047, 2047] [2047, 2047, 2047, 2047] =
      some (4 * 2047 * 2047) := by
  decide +kernel

end OzakiTCTests.CheckedTight
