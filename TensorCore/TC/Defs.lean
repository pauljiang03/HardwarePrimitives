import TensorCore.Numerics.Encoding

/-! Models of Tensor Cores: the numerical features of one block FMA. -/

namespace TensorCore


/-- Numerical features of one Tensor Core block FMA. -/
structure Model where
  /-- Input format of `a` and `b` (FP16, BF16, packed TF32, E5M2, or widened E4M3). -/
  input : Format
  /-- K, the FMA size N_FMA: the number of products added in a single multi-term addition. -/
  nfma : ℕ
  /-- F = 23 + p: the fractional bits each term keeps after alignment, with p extra alignment bits. -/
  alignFracBits : ℤ
  /-- The minimum alignment exponent e_align^min, if the architecture has one. -/
  eAlignMin : Option ℤ
  /-- The fraction bits of the block output. 23, a full binary32 output, on every variant except the
  FP8 block FMAs of Ada and Hopper, which have `p = -10` extra alignment bits (*Accurate Models*,
  Table 3) and keep `23 + p = 13` output fraction bits, as the Accurate Models toolbox's `GEMM.m`
  sets for `p < 0`. Fewer than 23 bits truncate the binary32 output further. -/
  outputFracBits : ℕ := 23
  deriving Repr, DecidableEq

/-- V100 FP16 -> FP32: `K = 4`, `(2, 23, 0)` alignment, and no relevant minimum alignment exponent. -/
def v100F16F32 : Model := ⟨fp16, 4, 23, none, 23⟩

/-- The binary32 word with only its leading `m` fraction bits kept, the others cleared: truncation
toward zero to `m` fraction bits, for normal and subnormal words alike. Unchanged when `23 ≤ m`. -/
def truncateFraction32 (m : ℕ) (w : F32) : F32 :=
  BitVec.ofNat 32 (w.toNat / 2 ^ (23 - m) * 2 ^ (23 - m))

theorem truncateFraction32_of_le {m : ℕ} (h : 23 ≤ m) (w : F32) : truncateFraction32 m w = w := by
  have h0 : 23 - m = 0 := by omega
  apply BitVec.eq_of_toNat_eq
  simp [truncateFraction32, h0]

@[simp] theorem truncateFraction32_23 (w : F32) : truncateFraction32 23 w = w :=
  truncateFraction32_of_le (Nat.le_refl 23) w

theorem truncateFraction32_toNat (m : ℕ) (w : F32) :
    (truncateFraction32 m w).toNat = w.toNat / 2 ^ (23 - m) * 2 ^ (23 - m) := by
  have hlt := w.isLt
  have hle : w.toNat / 2 ^ (23 - m) * 2 ^ (23 - m) ≤ w.toNat := Nat.div_mul_le_self _ _
  simp only [truncateFraction32, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

/-- Truncating the fraction keeps the sign and exponent fields. -/
theorem truncateFraction32_div (m : ℕ) (w : F32) :
    (truncateFraction32 m w).toNat / 2 ^ 23 = w.toNat / 2 ^ 23 := by
  rw [truncateFraction32_toNat]
  have hk : 23 - m + (23 - (23 - m)) = 23 := by omega
  have hp : (2 : ℕ) ^ 23 = 2 ^ (23 - m) * 2 ^ (23 - (23 - m)) := by rw [← Nat.pow_add, hk]
  have hpos : 0 < 2 ^ (23 - m) := Nat.two_pow_pos _
  rw [hp, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ hpos]

/-- A finite binary32 word stays finite when its fraction is truncated. -/
theorem decode32_truncateFraction32 {m : ℕ} {w : F32} (h : (decode32 w).isSome) :
    (decode32 (truncateFraction32 m w)).isSome := by
  have hd := truncateFraction32_div m w
  revert h
  simp only [decode32, classify, classifyNat, fp32]
  have he : (truncateFraction32 m w).toNat / 2 ^ 23 % 2 ^ 8 = w.toNat / 2 ^ 23 % 2 ^ 8 := by rw [hd]
  rw [he]
  intro h
  split <;> rename_i h1
  · rw [if_pos h1] at h; split at h <;> simp [Classification.finite] at h
  · split <;> split <;> simp [Classification.finite]

/-- The minimum alignment exponent only raises a nonempty maximum; an all-zero block stays `none`. -/
def Model.applyEAlignMin (p : Model) : Option ℤ → Option ℤ
  | none => none
  | some e => some (match p.eAlignMin with | none => e | some f => max e f)

abbrev Model.Word (p : Model) := BitVec p.input.width

def Model.decode (p : Model) (x : p.Word) : Option Decoded := (classify p.input x).finite

end TensorCore
