import OzakiTC.ADPIEEE

/-! # IEEE special values on the Tensor Core model

**The specification's special cases** for correctly rounded FP64 by Ozaki-I on V100 fp16 blocks
with special values (`tcOzaki1CRDI`), each checked against the specification `dotIEEE` by kernel
evaluation: a NaN input, `Inf · 0`, `+Inf` and `−Inf` products, an infinity with finite products,
overflow of a finite dot product to `±Inf`, products that are all `−0`, exact cancellation (`+0`),
a negative product that underflows (`−0`), and an ordinary sum.

**ADP against the Z3 model.** [`scripts/z3_specials_reference.py`](../../scripts/z3_specials_reference.py)
records the Z3 ADP model's outputs on three cases in
[`data/z3-specials-reference.json`](../../data/z3-specials-reference.json): an Inf in `A` (the
non-finite case of `z3-adp-reference.json`), a NaN in `A`, and finite inputs whose emulated products
overflow beside a row whose products cancel exactly. `adpIEEE` (and `adpSafeIEEE`) take the same
path and return the same words, decoded to IEEE data, so NaN is compared by class. -/

open TensorCore Ozaki Ozaki.TC

namespace OzakiTCTests.Specials

/-- A nonzero finite datum. -/
def f (v : ℚ) : FVal := .fin ⟨v, decide (v < 0)⟩

def pz : FVal := .fin ⟨0, false⟩
def nz : FVal := .fin ⟨0, true⟩

/-- Correctly rounded FP64 on V100 with special values, and the specification. -/
def cr (xs ys : List FVal) : FVal := tcOzaki1CRDI v100F16F32 11 [5, 6] 175 xs ys
def spec (xs ys : List FVal) : FVal := dotIEEE 53 (-1022) 1023 xs ys

def big : ℚ := 2 ^ (1023 : ℤ)
def tiny : ℚ := 2 ^ (-540 : ℤ)

/-- A NaN input. -/
example : cr [f 1, .nan] [f 2, f 3] = .nan ∧ spec [f 1, .nan] [f 2, f 3] = .nan := by
  decide +kernel

/-- `Inf · 0`. -/
example : cr [.inf false, f 1] [nz, f 2] = .nan ∧ spec [.inf false, f 1] [nz, f 2] = .nan := by
  decide +kernel

/-- `+Inf` and `−Inf` products. -/
example : cr [.inf false, .inf true] [f 1, f 1] = .nan ∧
    spec [.inf false, .inf true] [f 1, f 1] = .nan := by
  decide +kernel

/-- An infinite product among finite ones: `3 · 2 + (−Inf) · 5 = −Inf`, and `Inf · (−2) = −Inf`. -/
example : cr [f 3, .inf true] [f 2, f 5] = .inf true ∧ spec [f 3, .inf true] [f 2, f 5] = .inf true ∧
    cr [.inf false] [f (-2)] = .inf true := by
  decide +kernel

/-- Overflow of a finite dot product: `2^1023 + 2^1023` is `+Inf`, its negative `−Inf`. -/
example : cr [f big, f big] [f 1, f 1] = .inf false ∧ spec [f big, f big] [f 1, f 1] = .inf false ∧
    cr [f big, f big] [f (-1), f (-1)] = .inf true := by
  decide +kernel

/-- Products that are all `−0`: `(−0) · 1 + (+0) · (−0) = −0`. -/
example : cr [nz, pz] [f 1, nz] = nz ∧ spec [nz, pz] [f 1, nz] = nz := by
  decide +kernel

/-- Exact cancellation: `1 · 1 + (−1) · 1 = +0`. -/
example : cr [f 1, f (-1)] [f 1, f 1] = pz ∧ spec [f 1, f (-1)] [f 1, f 1] = pz := by
  decide +kernel

/-- A negative product that underflows: `2^-540 · (−2^-540)` rounds to `−0`. -/
example : cr [f tiny] [f (-tiny)] = nz ∧ spec [f tiny] [f (-tiny)] = nz := by
  decide +kernel

/-- An ordinary sum: `1 · 3 + 2 · 4 = 11`. -/
example : cr [f 1, f 2] [f 3, f 4] = f 11 := by
  decide +kernel

/-! ## ADP against the Z3 model -/

/-- `A`, case `nonfinite`. -/
def A_nonfinite : List (List (BitVec 64)) :=
  [[0xBFEF36D54C3E4DCC, 0xBFE8CE7501E36018, 0xBFCB6F02BB7E1D30, 0x3FD788DD50B13A00],
    [0xBFE71FB01065DA2A, 0xBFE8CDB983B7E2B2, 0x7FF0000000000000, 0x3FE07C65311DE238],
    [0xBFE690FA782572D8, 0x3FDECDCA2087A440, 0x3FD4C1E080F849D8, 0xBFE7424C262690C2],
    [0x3FB24241AEDF3640, 0xBFBAC063DE54E110, 0xBFC661CE997138C8, 0x3FEFC41854BEA17E]]

/-- `B`, case `nonfinite`. -/
def B_nonfinite : List (List (BitVec 64)) :=
  [[0xBFEB0B8580968872, 0xBFE2541A3ED7C454, 0xBFD9331734D38ACC, 0x3FE99D19D9E7010A],
    [0xBF7EB317E7183E00, 0x3FDC30D7D09DE6E4, 0xBFE995BE6566F902, 0x3F92485954913BC0],
    [0x3FE5F4E82874DD2A, 0x3FA758B3D8648240, 0x3FEC75FA27F0F80A, 0x3FE86F69D3C00AFC],
    [0xBFD0845C56616F40, 0xBFEFF3C6A3A9252C, 0x3FE0564C2E409558, 0xBFE7E8E95BCD7ED0]]

/-- `C`, case `nonfinite`. -/
def C_nonfinite : List (List (BitVec 64)) :=
  [[0x3FE2D2F436C00075, 0xBFC4717D9C3EA8B8, 0x3FF0040C1D15FDFB, 0xBFF3BA7EC7BC0478],
    [0x7FF0000000000000, 0x7FF0000000000000, 0x7FF0000000000000, 0x7FF0000000000000],
    [0x3FF00A4FB8446991, 0x3FF5B418FDE7A26D, 0xBFC84A67EDC657EA, 0x3FCE1080AA98BEA0],
    [0xBFDBE1F823CA744E, 0xBFF160811C790F04, 0x3FDA0822E585A07E, 0xBFEA3D94B2CF3DC9]]

/-- `A`, case `nan`. -/
def A_nan : List (List (BitVec 64)) :=
  [[0xBFCE756D955E6A28, 0x7FF8000000000000, 0xBFE55FA780C8B14C, 0x3FEA7C3F3B15C50A],
    [0x3FC3F3CFDCAF68F0, 0x3FD8564454890AFC, 0x3FBB2A9C91B6DD80, 0xBFCDD00E64BCB738],
    [0x3FDDA5DCAC364928, 0x3FC390C8604C6AA8, 0x3FE1FF5669FE18D4, 0x3FD4AEAF6FF72B34],
    [0x3FE5B70F08258C26, 0xBFBF07AEC346C9A0, 0xBFE613AB981B4F48, 0xBFE6691A38290500]]

/-- `B`, case `nan`. -/
def B_nan : List (List (BitVec 64)) :=
  [[0x3FD1D8BCC1C80314, 0xBFEE66394A114DFA, 0xBFDCCBD6DC14EC48, 0xBFE1B6EA4EE239F2],
    [0x3FDE44B051A3D1F8, 0x3FD69E16BBD9C668, 0x3FE91978545CE920, 0xBFEA6F981B46ABDE],
    [0xBFC3FCEE7EFBA2E8, 0xBFEE17CD67401CB6, 0xBFE201D5DE2382B0, 0x3F85EF6D343BCC80],
    [0xBFEE4D3C138291F4, 0xBFE3463E72459784, 0x3FD32F69CB38A088, 0x3FB70291DAD969A0]]

/-- `C`, case `nan`. -/
def C_nan : List (List (BitVec 64)) :=
  [[0x7FF8000000000000, 0x7FF8000000000000, 0x7FF8000000000000, 0x7FF8000000000000],
    [0x3FDB58B9CF8D5CEB, 0x3F9B71035DD456F4, 0x3FB93D66FCDDDABB, 0xBFDAE51FC40238AA],
    [0xBFC89F72284BAF72, 0xBFF1C0F3B2257C7D, 0xBFD3B8C9BE0BE994, 0xBFD63FEBF8DE0E5E],
    [0x3FECE3B7CD7DA88C, 0x3FD88520673D2FFD, 0xBFCC6E3F6597DD12, 0xBFD62289D5C079C1]]

/-- `A`, case `overflow`. -/
def A_overflow : List (List (BitVec 64)) :=
  [[0x7E37E43C8800759C, 0x7E37E43C8800759C],
    [0x3FF0000000000000, 0x4000000000000000]]

/-- `B`, case `overflow`. -/
def B_overflow : List (List (BitVec 64)) :=
  [[0x4202A05F20000000, 0x3FF0000000000000],
    [0x4202A05F20000000, 0xBFF0000000000000]]

/-- `C`, case `overflow`. -/
def C_overflow : List (List (BitVec 64)) :=
  [[0x7FF0000000000000, 0x0000000000000000],
    [0x421BF08EB0000000, 0xBFF0000000000000]]

example : adpIEEE {} A_nonfinite B_nonfinite =
    (.nativeNonfinite, C_nonfinite.map (·.map decodeF64)) := by
  decide +kernel

example : adpIEEE {} A_nan B_nan = (.nativeNonfinite, C_nan.map (·.map decodeF64)) := by
  decide +kernel

example : adpIEEE {} A_overflow B_overflow = (.emulated, C_overflow.map (·.map decodeF64)) := by
  decide +kernel

example : adpSafeIEEE {} A_nonfinite B_nonfinite =
      (.nativeNonfinite, C_nonfinite.map (·.map decodeF64)) ∧
    adpSafeIEEE {} A_overflow B_overflow = (.emulated, C_overflow.map (·.map decodeF64)) := by
  decide +kernel

/-- The decoded outputs contain `+Inf`, NaN and `+0`, so the comparisons above cover them. -/
example : decodeF64 0x7FF0000000000000 = .inf false ∧ decodeF64 0x7FF8000000000000 = .nan ∧
    decodeF64 0x0000000000000000 = pz ∧ decodeF64 0x8000000000000000 = nz := by
  decide +kernel

end OzakiTCTests.Specials
