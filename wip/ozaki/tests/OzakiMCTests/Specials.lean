import OzakiMC.IEEESchemes

/-! # IEEE special values on the matrix-core model

The specification's special cases for correctly rounded FP64 by Ozaki-I on CDNA 3 fp16 blocks with
special values (`mcOzaki1CRDI`), each checked against `dotIEEE` by kernel evaluation: a NaN input,
`Inf · 0`, `+Inf` and `−Inf` products, an infinity with finite products, overflow to `±Inf`,
products that are all `−0`, exact cancellation, a negative product that underflows, and an ordinary
sum. The results are those of the Tensor Core test, as the theorems say they must be. -/

open MatrixCore Ozaki Ozaki.MC

namespace OzakiMCTests.Specials

def f (v : ℚ) : FVal := .fin ⟨v, decide (v < 0)⟩

def pz : FVal := .fin ⟨0, false⟩
def nz : FVal := .fin ⟨0, true⟩

def cr (xs ys : List FVal) : FVal := mcOzaki1CRDI cdna3F16 11 [5, 6] 175 xs ys
def spec (xs ys : List FVal) : FVal := dotIEEE 53 (-1022) 1023 xs ys

def big : ℚ := 2 ^ (1023 : ℤ)
def tiny : ℚ := 2 ^ (-540 : ℤ)

example : cr [f 1, .nan] [f 2, f 3] = .nan ∧ spec [f 1, .nan] [f 2, f 3] = .nan := by
  decide +kernel

example : cr [.inf false, f 1] [nz, f 2] = .nan ∧ spec [.inf false, f 1] [nz, f 2] = .nan := by
  decide +kernel

example : cr [.inf false, .inf true] [f 1, f 1] = .nan ∧
    spec [.inf false, .inf true] [f 1, f 1] = .nan := by
  decide +kernel

example : cr [f 3, .inf true] [f 2, f 5] = .inf true ∧ spec [f 3, .inf true] [f 2, f 5] = .inf true ∧
    cr [.inf false] [f (-2)] = .inf true := by
  decide +kernel

example : cr [f big, f big] [f 1, f 1] = .inf false ∧ spec [f big, f big] [f 1, f 1] = .inf false ∧
    cr [f big, f big] [f (-1), f (-1)] = .inf true := by
  decide +kernel

example : cr [nz, pz] [f 1, nz] = nz ∧ spec [nz, pz] [f 1, nz] = nz := by
  decide +kernel

example : cr [f 1, f (-1)] [f 1, f 1] = pz ∧ spec [f 1, f (-1)] [f 1, f 1] = pz := by
  decide +kernel

example : cr [f tiny] [f (-tiny)] = nz ∧ spec [f tiny] [f (-tiny)] = nz := by
  decide +kernel

example : cr [f 1, f 2] [f 3, f 4] = f 11 := by
  decide +kernel

end OzakiMCTests.Specials
