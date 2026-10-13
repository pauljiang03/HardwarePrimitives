import OzakiTC.Exactness
import Ozaki.ADP
import Ozaki.Binary

/-! # Ozaki-I on an INT8 matrix multiplier (ADP)

NVIDIA's ADP emulates binary64 GEMM on INT8 tensor cores, which multiply bytes and accumulate in
an INT32 register. TC-EFT models a fixed-width register as `machineAccumulate w`, `w`-bit
two's-complement additions that wrap on overflow; `int8Dot w` is the INT8 matrix multiplier with
that register. This file proves:

* `int8Dot_exact`: the register holds the exact sum whenever `Σ|xᵢyᵢ| < 2^(w−1)`; for signed and
  unsigned bytes in a 32-bit register this is `int8Dot_bytes` (`[Z.1]`: `k = 4` products of
  `s8 · s8` or `s8 · u8`);
* `int8Dot_16_wraps`: a 16-bit register wraps on four byte products (`[Z.2]`);
* `int8Ozaki_eq`: Ozaki-I on the INT8 matrix multiplier (fixed point, remapped slices, all `s²`
  slice products, exact recombination, one binary64 rounding) returns the binary64 rounding of the
  exact fixed-point product, when every fixed-point integer fits the remap range and
  `k · 2^14 < 2^31`. -/

open TensorCore

namespace Ozaki.TC

/-- The INT8 matrix multiplier: products of byte operands accumulated in a `w`-bit wrapping
register. -/
def int8Dot (w : ℕ) (x y : List ℤ) : ℤ := (machineAccumulate w 0 (List.zipWith (· * ·) x y)).toInt

theorem magnitudeSum_zipWith : ∀ x y : List ℤ,
    magnitudeSum (List.zipWith (· * ·) x y) = dotAbs x y
  | [], _ => by simp [magnitudeSum]
  | _ :: _, [] => by simp [magnitudeSum]
  | a :: x, b :: y => by simp [magnitudeSum, magnitudeSum_zipWith x y]

theorem sumZ_zipWith : ∀ x y : List ℤ, sumZ (List.zipWith (· * ·) x y) = dotZ x y
  | [], _ => by simp [sumZ]
  | _ :: _, [] => by simp [sumZ]
  | a :: x, b :: y => by simp [sumZ, sumZ_zipWith x y]

/-- The register holds the exact dot product whenever `Σ|xᵢyᵢ| < 2^(w−1)`. -/
theorem int8Dot_exact {w : ℕ} (hw : 0 < w) {x y : List ℤ} (h : dotAbs x y < 2 ^ (w - 1)) :
    int8Dot w x y = dotZ x y := by
  unfold int8Dot
  rw [machineAccumulate_exact w _ hw (by rw [magnitudeSum_zipWith]; exact h), sumZ_zipWith]

/-- **INT8 × INT8 → INT32 is exact** (`[Z.1]`). Signed bytes against signed or unsigned bytes,
`k · 128 · 255 < 2^31` (any `k ≤ 16448`). -/
theorem int8Dot_bytes {x y : List ℤ} (hx : ∀ a ∈ x, a.natAbs ≤ 128) (hy : ∀ b ∈ y, b.natAbs ≤ 255)
    (hk : x.length * (128 * 255) < 2 ^ 31) : int8Dot 32 x y = dotZ x y :=
  int8Dot_exact (by decide) (Nat.lt_of_le_of_lt (dotAbs_le x y 128 255 hx hy) hk)

/-- **A 16-bit register wraps** (`[Z.2]`): four products `127 · 127` total `64516 > 2^15`. -/
theorem int8Dot_16_wraps :
    int8Dot 16 [127, 127, 127, 127] [127, 127, 127, 127] = -1020 ∧
      dotZ [127, 127, 127, 127] [127, 127, 127, 127] = 64516 := by decide

/-! ## Ozaki-I on the INT8 matrix multiplier -/

/-- Fixed point: `N = ⌊a · 2^shift⌋` (round toward `−∞`, as §3 states for the lead slice). -/
def toFixed (shift : ℤ) (x : List ℚ) : List ℤ := x.map fun a => (a * (2 : ℚ) ^ shift).floor

/-- The exactly recombined slice products on the INT8 matrix multiplier:
`Σ_{t,u} 256^(t+u) (Nₐ,ₜ · N_b,ᵤ)`. -/
def int8Recombine (s : ℕ) (Na Nb : List ℤ) : ℤ :=
  ((List.range s).map fun t => ((List.range s).map fun u =>
    256 ^ (t + u) * int8Dot 32 (ADP.sliceVec s t Na) (ADP.sliceVec s u Nb)).sum).sum

/-- **Ozaki-I on the INT8 matrix multiplier** for one output entry: fixed-point integers with the
given shifts, `s` remapped byte slices, all `s²` slice products, exact recombination, and one
binary64 round to nearest even (IEEE's, `Ozaki.rne64`). -/
def int8Ozaki (s : ℕ) (shiftA shiftB : ℤ) (x y : List ℚ) : Option ℚ :=
  rne64 ((int8Recombine s (toFixed shiftA x) (toFixed shiftB y) : ℚ) * pow2 (-(shiftA + shiftB)))

theorem sliceVec_s8 {s : ℕ} (hs : 0 < s) {N : List ℤ}
    (hN : ∀ z ∈ N, ADP.remapLo s ≤ z ∧ z ≤ ADP.remapHi s) (t : ℕ) :
    ∀ d ∈ ADP.sliceVec s t N, d.natAbs ≤ 128 := by
  intro d hd
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hd
  have h8 := (ADP.remap_s8 hs z).mpr (hN z hz)
  rw [List.getD_eq_getElem?_getD]
  cases hget : (ADP.remap s z)[t]? with
  | none => simp
  | some d => have := h8 d (List.mem_of_getElem? hget); simp; omega

/-- On the remap range the INT8 slice products are exact and recombine to the fixed-point product
(the core of `int8Ozaki_eq`). -/
theorem int8Recombine_eq {s : ℕ} (hs : 0 < s) {Na Nb : List ℤ}
    (hx : ∀ z ∈ Na, ADP.remapLo s ≤ z ∧ z ≤ ADP.remapHi s)
    (hy : ∀ z ∈ Nb, ADP.remapLo s ≤ z ∧ z ≤ ADP.remapHi s)
    (hk : Na.length * (128 * 128) < 2 ^ 31) : int8Recombine s Na Nb = dotZ Na Nb := by
  unfold int8Recombine
  rw [← ADP.slice_recombination hs]
  congr 1; apply List.map_congr_left; intro t _
  congr 1; apply List.map_congr_left; intro u _
  congr 1
  apply int8Dot_exact (by decide)
  refine Nat.lt_of_le_of_lt (dotAbs_le _ _ 128 128 (sliceVec_s8 hs hx t) (sliceVec_s8 hs hy u)) ?_
  simpa [ADP.sliceVec] using hk

/-- **Exact INT8 emulation.** If every fixed-point integer lies in the remap range of `s` slices and
`k · 2^14 < 2^31`, every INT8 slice product is exact and the recombination is the exact
fixed-point product, so the result is its single binary64 rounding (`[E.3]`, `[R.1]`). -/
theorem int8Ozaki_eq {s : ℕ} (hs : 0 < s) (shiftA shiftB : ℤ) {x y : List ℚ}
    (hx : ∀ z ∈ toFixed shiftA x, ADP.remapLo s ≤ z ∧ z ≤ ADP.remapHi s)
    (hy : ∀ z ∈ toFixed shiftB y, ADP.remapLo s ≤ z ∧ z ≤ ADP.remapHi s)
    (hk : x.length * (128 * 128) < 2 ^ 31) :
    int8Ozaki s shiftA shiftB x y =
      rne64 ((dotZ (toFixed shiftA x) (toFixed shiftB y) : ℚ) * pow2 (-(shiftA + shiftB))) := by
  unfold int8Ozaki
  rw [int8Recombine_eq hs hx hy (by simpa [toFixed] using hk)]

end Ozaki.TC
