import TensorCore.Numerics.Encoding

/-! Bounded binary searches for the bit support of a 576-bit magnitude. -/

namespace TensorCore.EFMachine

def scanBoundary (test : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if test mid then scanBoundary test fuel (mid + 1) hi
      else scanBoundary test fuel lo mid
    else lo

def leadingZeros (m : BitVec 576) : BitVec 576 :=
  576 - BitVec.ofNat 576 (scanBoundary (fun n => (m >>> n) != 0) 10 0 576)

def trailingZeros (m : BitVec 576) : BitVec 576 :=
  BitVec.ofNat 576 (scanBoundary (fun n => m.setWidth (n + 1) == 0) 10 0 576)

end TensorCore.EFMachine
