import OzakiTC.Correct
import Ozaki.SplitK
import Ozaki.Exact64
import Ozaki.TruncatedSum

/-! # Long dot products and FP64 emulation on the Tensor Core model

The Tensor Core matrix multiplier is exact while the products of one call total at most `2^24`, so
with `11`-bit slices a dot product may have only four terms. Split-K lifts the limit: chunks of
`2^(24 − 2b)` terms (four for `11`-bit slices, `256` for `8`-bit) each run on Tensor Core blocks,
and the integer chunk results are added exactly. In hardware the chunk results are read out and
accumulated in an integer register; `tcSplitKReg` does that in `TensorCore`'s fixed-width two's-complement
register, which is exact while the products total less than `2^(w−1)` (`2^63` for `w = 64`).

With split-K every theorem of the schemes holds for every inner dimension:

* binary32 GEMM: `tcOzaki1L_error`, and the correctly rounded `tcOzaki1CRL_eq`, `tcOzaki2CRL_eq`;
* **FP64 emulation**: Ozaki-I with binary64 recombination (`tcOzaki1D_error`, error `2^-53` per
  addition), and correctly rounded binary64 results from Ozaki-I and Ozaki-II (`tcOzaki1CRD_eq`,
  `tcOzaki2CRD_eq`) for binary64 inputs of any length: binary64 values are multiples of `2^-1074`
  with magnitude below `2^1024`, so `smax` slices with `smax (b + 1) > 2098` leave nothing over
  (`175` slices of `11` bits) and the exact fallback's slice products run on Tensor Core blocks too.

The correctly rounded results are stated with the hardware-independent IEEE round to nearest even of
`Ozaki.Binary` (`rne32Q`, `rne64`), the same function as on the AMD model, so both vendors return
the same value. Every slice product runs on the Tensor Core model; the slicing,
the exact sum of the slice products and the rounding test are exact arithmetic (the sum fits a
register of about `580` bits for binary32 inputs, `exactTerms_sum_register32`). -/

open TensorCore

namespace Ozaki.TC

/-! ## Split-K on Tensor Core blocks -/

/-- **Split-K on Tensor Core blocks**: chunks of `2^(24−2b)` terms, each a Tensor Core dot product,
added exactly. -/
def tcSplitK (p : Model) (b : ℕ) : MatrixMultiplier := chunked (chunkLen b) (tcMultiplier p)

/-- On any variant where the Tensor Core matrix multiplier is exact on `b`-bit slices, split-K is
exact on `b`-bit vectors of every length. -/
theorem tcSplitK_exactOn {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (B : ℕ) : (tcSplitK p b).ExactOn b B :=
  chunked_exactOn hmult (chunkLen_pos b) (chunkLen_exactnessBound hb) B

/-! ## The chunk results in a fixed-width integer register -/

/-- Add integer-valued chunk results in `TensorCore`'s `w`-bit two's-complement register. -/
def regSum (w : ℕ) (vs : List ℚ) : Option ℚ := do
  let zs ← vs.mapM toInt?
  pure ((machineAccumulate w 0 zs).toInt : ℚ)

/-- Split-K with the chunk results accumulated in a `w`-bit integer register. -/
def tcSplitKReg (w : ℕ) (p : Model) (b : ℕ) : MatrixMultiplier := fun x y =>
  (((chunksOf (chunkLen b) x).zip (chunksOf (chunkLen b) y)).mapM fun q => tcMultiplier p q.1 q.2).bind
    (regSum w)

theorem sumZ_eq_sum : ∀ zs : List ℤ, sumZ zs = zs.sum
  | [] => rfl
  | z :: zs => by simp [sumZ, sumZ_eq_sum zs]

theorem magnitudeSum_map_le {l : List α} {f : α → ℤ} {g : α → ℕ} (h : ∀ a ∈ l, (f a).natAbs ≤ g a) :
    magnitudeSum (l.map f) ≤ (l.map g).sum := by
  induction l with
  | nil => simp [magnitudeSum]
  | cons a l ih =>
    simp only [List.map_cons, magnitudeSum, List.sum_cons]
    have := h a List.mem_cons_self
    have := ih fun c hc => h c (List.mem_cons_of_mem _ hc)
    omega

/-- **The register cannot overflow.** With a `w`-bit register, split-K is exact on `b`-bit vectors
whose products total less than `2^(w−1)`: below `2^63` in a 64-bit register. -/
theorem tcSplitKReg_exactOn {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) {w B : ℕ} (hw : 0 < w) (hB : B < 2 ^ (w - 1)) :
    (tcSplitKReg w p b).ExactOn b B := by
  intro x y hlen hx hy hbud
  unfold tcSplitKReg chunksOf
  rw [hlen]
  obtain ⟨hpairs, hsum⟩ := chunksAux_pairs (chunkLen_pos b) y.length x y hlen (by omega)
  have habs := chunksAux_dotAbs (chunkLen_pos b) y.length x y hlen (by omega)
  generalize hP : (chunksAux (chunkLen b) y.length x).zip (chunksAux (chunkLen b) y.length y) = P
    at hpairs hsum habs
  rw [mapM_eq_some_map (g := fun q : List ℤ × List ℤ => ((dotZ q.1 q.2 : ℤ) : ℚ))]
  · simp only [Option.bind_some, regSum]
    rw [mapM_eq_some_map (g := fun z : ℚ => (z.num : ℤ)) (l := P.map _)]
    · have hzs : ((P.map fun q => ((dotZ q.1 q.2 : ℤ) : ℚ)).map fun z : ℚ => (z.num : ℤ)) =
          P.map fun q => dotZ q.1 q.2 := by
        simp [Function.comp_def, Rat.num_intCast]
      rw [hzs]
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rw [machineAccumulate_exact w _ hw, sumZ_eq_sum, hsum]
      · refine Nat.lt_of_le_of_lt (magnitudeSum_map_le (g := fun q => dotAbs q.1 q.2)
          fun q _ => natAbs_dotZ_le _ _) ?_
        rw [habs]; omega
    · intro z hz
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hz
      rw [toInt?_intCast, Rat.num_intCast]
  · intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := hpairs q hq
    apply hmult _ _ h1 (fun a ha => hx a (h3 a ha)) (fun a ha => hy a (h4 a ha))
    refine Nat.le_trans (dotAbs_le _ _ _ _ (fun a ha => hx a (h3 a ha))
      (fun a ha => hy a (h4 a ha))) ?_
    exact Nat.le_trans (Nat.mul_le_mul_right _ h2) (chunkLen_exactnessBound hb)

/-! ## Binary32 GEMM of any inner dimension -/

/-- Ozaki-I on Tensor Core blocks with split-K, binary32 recombination. -/
def tcOzaki1L (p : Model) (b s : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1 (tcSplitK p b) add32 b s x y

/-- **Ozaki-I on the Tensor Core for any inner dimension**: the bound of `tcOzaki1_error` without
the condition `k · 2^(2b) ≤ 2^24`. -/
theorem tcOzaki1L_error {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (s : ℕ) {x y : List ℚ} (hlen : x.length = y.length) {v : ℚ}
    (hv : tcOzaki1L p b s x y = some v) :
    Rat.abs (v - dot x y) ≤
      ((1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length - 1) *
          ((trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y))) +
        (trianglePairs s).length * (1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length *
          2 ^ (-150 : ℤ) +
        ((s + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp b x + splitExp b y - s * (b + 1)) :=
  ozaki1_error (tcSplitK_exactOn hmult hb _) (Rat.le_of_lt (two_pow_pos _))
    (Rat.le_of_lt (two_pow_pos _)) add32_within hlen (Nat.le_refl _) hv

/-- TensorCore's binary64 values are the binary64 values of `Ozaki.Binary`. -/
theorem fp64_binary64 {v : ℚ} (h : fp64.FiniteValue v) : Binary64Value v := by
  obtain ⟨k, e, h1, h2, h3, rfl⟩ := h
  have e1 : fp64.emin = -1022 := by decide
  have e2 : fp64.emax = 1023 := by decide
  have e3 : fp64.mantissaBits = 52 := rfl
  rw [e1] at h1; rw [e2] at h2; rw [e3] at h3
  refine ⟨k, e, h1, h2, h3, ?_⟩
  rw [pow2_eq, e3]
  congr 2

/-- Correctly rounded binary32 Ozaki-I of any inner dimension; every slice product, including the
exact fallback's, on Tensor Core blocks. -/
def tcOzaki1CRL (p : Model) (b : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRE (tcSplitK p b) rne32Q b ss smax x y

/-- Correctly rounded binary32 Ozaki-II of any inner dimension; every residue and slice product on
Tensor Core blocks. -/
def tcOzaki2CRL (p : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) (x y : List ℚ) :
    Option ℚ :=
  ozaki2CRE (tcSplitK p b) rne32Q cfgs b smax x y

/-- **Correctly rounded binary32 Ozaki-I for any inner dimension**, on any exact variant: the IEEE
round to nearest even of `x · y`, the same function as on the AMD model. -/
theorem tcOzaki1CRL_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a) (hlen : x.length = y.length) :
    tcOzaki1CRL p b ss smax x y = rne32Q (dot x y) :=
  ozaki1CRE_eq rne32Q_nearest rne32Q_intervals (tcSplitK_exactOn hmult hb _) ss hlen
    (Nat.le_refl _) (vanish32Q (by omega) hsmax hx hy)

/-- **Correctly rounded binary32 Ozaki-II for any inner dimension**, on any exact variant. -/
theorem tcOzaki2CRL_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 277 < smax * (b + 1))
    {x y : List ℚ}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * x.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a) (hlen : x.length = y.length) :
    tcOzaki2CRL p cfgs b smax x y = rne32Q (dot x y) :=
  ozaki2CRE_eq rne32Q_nearest rne32Q_intervals (tcSplitK_exactOn hmult hb _) hcfg hlen
    (Nat.le_refl _) (vanish32Q (by omega) hsmax hx hy)

/-! ## FP64 emulation -/

/-- Binary64 addition: the exact sum rounded to nearest even. -/
def fp64Add (a b : ℚ) : Option ℚ := fp64Round (a + b)

theorem fp64Add_within : AddWithin fp64Add (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) :=
  addOfRound_within fp64Round_within

/-- **FP64 emulation, Ozaki-I**: slices on Tensor Core blocks with split-K, the scaled slice
products added in binary64. -/
def tcOzaki1D (p : Model) (b s : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1 (tcSplitK p b) fp64Add b s x y

/-- **The error of FP64 emulation by Ozaki-I** on Tensor Core blocks, for any inner dimension:
binary64 additions plus the slicing bound. -/
theorem tcOzaki1D_error {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (s : ℕ) {x y : List ℚ} (hlen : x.length = y.length) {v : ℚ}
    (hv : tcOzaki1D p b s x y = some v) :
    Rat.abs (v - dot x y) ≤
      ((1 + 2 ^ (-53 : ℤ)) ^ (trianglePairs s).length - 1) *
          ((trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y))) +
        (trianglePairs s).length * (1 + 2 ^ (-53 : ℤ)) ^ (trianglePairs s).length *
          2 ^ (-1075 : ℤ) +
        ((s + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp b x + splitExp b y - s * (b + 1)) :=
  ozaki1_error (tcSplitK_exactOn hmult hb _) (Rat.le_of_lt (two_pow_pos _))
    (Rat.le_of_lt (two_pow_pos _)) fp64Add_within hlen (Nat.le_refl _) hv

/-- **Correctly rounded FP64 emulation, Ozaki-I**: every slice product on Tensor Core blocks, the
binary64 round to nearest even of `x · y`. -/
def tcOzaki1CRD (p : Model) (b : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRE (tcSplitK p b) rne64 b ss smax x y

/-- **Correctly rounded FP64 emulation, Ozaki-II**: every residue and slice product on Tensor Core
blocks, the binary64 round to nearest even of `x · y`. -/
def tcOzaki2CRD (p : Model) (cfgs : List (CRTBasis × ℕ)) (b smax : ℕ) (x y : List ℚ) :
    Option ℚ :=
  ozaki2CRE (tcSplitK p b) rne64 cfgs b smax x y

/-- **FP64 GEMM on fp16, bf16 or tf32 Tensor Cores, correctly rounded.** For binary64 inputs of any
length, on any variant where the matrix multiplier is exact on `b`-bit slices, the result is the
IEEE binary64 round to nearest even of `x · y`. -/
theorem tcOzaki1CRD_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1)) {x y : List ℚ}
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a)
    (hlen : x.length = y.length) :
    tcOzaki1CRD p b ss smax x y = rne64 (dot x y) :=
  ozaki1CRE_eq rne64_nearest rne64_intervals (tcSplitK_exactOn hmult hb _) ss hlen
    (Nat.le_refl _) (vanish64 (by omega) hsmax hx hy)

/-- **FP64 GEMM by Ozaki-II on Tensor Cores, correctly rounded.** -/
theorem tcOzaki2CRD_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) {cfgs : List (CRTBasis × ℕ)} {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {x y : List ℚ}
    (hcfg : ∀ c ∈ cfgs, c.1.Valid ∧ (∀ m ∈ c.1.moduli, m ≤ 2 ^ (b + 1)) ∧
      2 * x.length * (2 ^ c.2 * 2 ^ c.2) < c.1.modulus)
    (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a)
    (hlen : x.length = y.length) :
    tcOzaki2CRD p cfgs b smax x y = rne64 (dot x y) :=
  ozaki2CRE_eq rne64_nearest rne64_intervals (tcSplitK_exactOn hmult hb _) hcfg hlen
    (Nat.le_refl _) (vanish64 (by omega) hsmax hx hy)

/-- The instances: FP64 emulation on V100 fp16 (`11`-bit slices, up to `175`) and A100 bf16
(`8`-bit slices, up to `234`), correctly rounded, for every length. -/
theorem v100_fp64CR (ss : List ℕ) {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    tcOzaki1CRD v100F16F32 11 ss 175 x y = rne64 (dot x y) :=
  tcOzaki1CRD_eq v100_exactOn (by decide) ss (by decide) hx hy hlen

theorem a100BF16_fp64CR (ss : List ℕ) {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    tcOzaki1CRD a100BF16F32 8 ss 234 x y = rne64 (dot x y) :=
  tcOzaki1CRD_eq a100BF16_exactOn (by decide) ss (by decide) hx hy hlen

/-! ## With a two-word accumulator -/

/-- Correctly rounded binary32 Ozaki-I of any inner dimension with a `W`-bit truncated sum for
the rounding test. -/
def tcOzaki1CRLW (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRW (tcSplitK p b) rne32Q b W ss smax x y

/-- Correctly rounded FP64 by Ozaki-I with a `W`-bit truncated sum for the rounding test. -/
def tcOzaki1CRDW (p : Model) (b W : ℕ) (ss : List ℕ) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1CRW (tcSplitK p b) rne64 b W ss smax x y

theorem tcOzaki1CRLW_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (W : ℕ) (ss : List ℕ) {smax : ℕ} (hsmax : 277 < smax * (b + 1))
    {x y : List ℚ} (hx : ∀ a ∈ x, Binary32Value a) (hy : ∀ a ∈ y, Binary32Value a)
    (hlen : x.length = y.length) :
    tcOzaki1CRLW p b W ss smax x y = rne32Q (dot x y) :=
  ozaki1CRW_eq rne32Q_nearest rne32Q_intervals (tcSplitK_exactOn hmult hb _) W ss hlen
    (Nat.le_refl _) (vanish32Q (by omega) hsmax hx hy)

/-- **Correctly rounded FP64 GEMM on Tensor Cores with a two-word accumulator.** -/
theorem tcOzaki1CRDW_eq {p : Model} {b : ℕ} (hmult : (tcMultiplier p).ExactOn b (2 ^ 24))
    (hb : 2 * b ≤ 24) (W : ℕ) (ss : List ℕ) {smax : ℕ} (hsmax : 2098 < smax * (b + 1))
    {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a) (hy : ∀ a ∈ y, Binary64Value a)
    (hlen : x.length = y.length) :
    tcOzaki1CRDW p b W ss smax x y = rne64 (dot x y) :=
  ozaki1CRW_eq rne64_nearest rne64_intervals (tcSplitK_exactOn hmult hb _) W ss hlen
    (Nat.le_refl _) (vanish64 (by omega) hsmax hx hy)

/-- FP64 on V100 fp16 with a `96`-bit truncated sum: correctly rounded for every length. With up to
seven `11`-bit slices the truncation loss `n 2^(E+F−96)` is far below the slicing bound. -/
theorem v100_fp64CRW (ss : List ℕ) {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    tcOzaki1CRDW v100F16F32 11 96 ss 175 x y = rne64 (dot x y) :=
  tcOzaki1CRDW_eq v100_exactOn (by decide) 96 ss (by decide) hx hy hlen

end Ozaki.TC
