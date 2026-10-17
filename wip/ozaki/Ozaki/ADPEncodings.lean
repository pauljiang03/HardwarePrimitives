import Ozaki.ADPError

/-! # ADP's three slice encodings, and the Z3 model's test-level checks on encodings and ESC

The Z3 model of ADP cuts a fixed-point integer `N` into `s` slices in one of three ways:

* `remap` (the paper's production encoding, `Ozaki.ADP.remap`): base-256 signed bytes with carries;
* `floor_u8` (the prototype, `Ozaki.ADP.floorDigits`): `s − 1` unsigned bytes and a signed lead;
* `naive_s8`: the sign of `N` times the base-128 digits of `|N|`, every slice a signed byte with
  seven magnitude bits (`naiveDigits`).

This file proves, for every `N`:

* **`[U.6]`** the naive digits lie in `[−127, 127]` and reconstruct `N` in base `128` whenever
  `|N| < 128^s` (`naiveDigits_s8`);
* for each encoding whose slice count holds `W` bits, every fixed-point integer in `[−2^W, 2^W)`
  has `s` digits of magnitude at most `255` that reconstruct it in the encoding's base
  (`SliceEncoding.digits_length`, `SliceEncoding.digits_value`, `SliceEncoding.digits_natAbs_le`),
  so the `s²` weighted slice products of any encoding add up to the fixed-point product
  (`slice_recombination_with`); this is the core of `[T.4]`, the three encodings agree;
* **`[T.3]`** wherever naive slices hold `W` bits, so do remapped ones (`naiveFits_remapFits`);
* **`[T.2]`** the paper's example: `123 · 256 + 200` is `[200, 123]` in floor digits and
  `[−56, 124]` remapped, with the same low bit pattern (`paper_remap_example`);
* **`[T.5]`** blocks of one entry make the coarsened estimate the exact one (`coarseEst_one`), so the
  coarsened ESC with block size `1` is the exact ESC (`escCoarse_one`);
* **`[T.12]`** on the Z3 model's two zero cases, skipping zeros or giving them the exponent `−1022`
  makes the estimate exceed the exact largest product exponent, which is what `[X.4]` checks, while
  zeros as `−∞` never do (`zeros_case_caught`, `field0_case_caught`). -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

namespace Ozaki.ADP

/-! ## Digits in any base -/

/-- Value of digits in base `B`, lowest first. -/
def baseValue (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | d :: ds => d + B * baseValue B ds

theorem baseValue_256 : ∀ ds : List ℤ, baseValue 256 ds = digitValue ds
  | [] => rfl
  | d :: ds => by simp only [baseValue, digitValue, baseValue_256 ds]

theorem baseValue_map_mul (B c : ℤ) : ∀ ds : List ℤ,
    baseValue B (ds.map fun d => c * d) = c * baseValue B ds
  | [] => by simp [baseValue]
  | d :: ds => by
    simp only [List.map_cons, baseValue, baseValue_map_mul B c ds, Int.mul_add]
    rw [Int.mul_left_comm]

theorem baseValue_eq_sum (B : ℤ) (ds : List ℤ) :
    baseValue B ds = ((List.range ds.length).map fun t => ds.getD t 0 * B ^ t).sum := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [List.length_cons, List.range_succ_eq_map]
    simp only [baseValue, List.map_cons, List.sum_cons, List.getD_cons_zero, List.map_map,
      Function.comp_def, List.getD_cons_succ, Int.pow_succ]
    rw [ih, Int.pow_zero, Int.mul_one, ← sumZ_map_mul_left]
    congr 2
    apply List.map_congr_left; intro t _; rw [Int.mul_comm B, Int.mul_assoc]

/-! ## The naive signed encoding (`[U.6]`) -/

/-- Base-128 digits of a natural number, lowest first: `s − 1` digits in `[0, 127]` and the rest
in the last. -/
def natDigits128 : ℕ → ℕ → List ℕ
  | 0, _ => []
  | 1, n => [n]
  | s + 2, n => (n % 128) :: natDigits128 (s + 1) (n / 128)

/-- **Naive signed slices** (`naive_s8`): the sign of `N` times the base-128 digits of `|N|`. -/
def naiveDigits (s : ℕ) (N : ℤ) : List ℤ :=
  (natDigits128 s N.natAbs).map fun d : ℕ => (if N < 0 then -1 else 1) * (d : ℤ)

theorem natDigits128_length : ∀ (s n : ℕ), (natDigits128 s n).length = s
  | 0, _ => rfl
  | 1, _ => rfl
  | s + 2, n => by simp [natDigits128, natDigits128_length (s + 1) (n / 128)]

theorem natDigits128_value : ∀ (s n : ℕ), 0 < s →
    baseValue 128 ((natDigits128 s n).map fun d : ℕ => (d : ℤ)) = n
  | 0, _, h => absurd h (by decide)
  | 1, n, _ => by simp [natDigits128, baseValue]
  | s + 2, n, _ => by
    simp only [natDigits128, List.map_cons, baseValue]
    rw [natDigits128_value (s + 1) (n / 128) (by omega)]
    omega

theorem natDigits128_le : ∀ (s n : ℕ), 0 < s → n < 128 ^ s → ∀ d ∈ natDigits128 s n, d ≤ 127
  | 0, _, h, _ => absurd h (by decide)
  | 1, n, _, hn => by simp [natDigits128] at hn ⊢; omega
  | s + 2, n, _, hn => by
    intro d hd
    simp only [natDigits128, List.mem_cons] at hd
    rcases hd with rfl | hd
    · omega
    · have hP : 128 ^ (s + 2) = 128 * 128 ^ (s + 1) := by rw [Nat.pow_succ]; omega
      exact natDigits128_le (s + 1) (n / 128) (by omega)
        (by rw [hP] at hn; exact Nat.div_lt_of_lt_mul hn) d hd

theorem naiveDigits_length (s : ℕ) (N : ℤ) : (naiveDigits s N).length = s := by
  simp [naiveDigits, natDigits128_length]

/-- **Naive signed slices** (`[U.6]`): for `|N| < 128^s`, the `s` digits lie in `[−127, 127]` and
`Σ dₜ 128^t = N`. -/
theorem naiveDigits_s8 {s : ℕ} (hs : 0 < s) {N : ℤ} (hN : N.natAbs < 128 ^ s) :
    (∀ d ∈ naiveDigits s N, -127 ≤ d ∧ d ≤ 127) ∧ baseValue 128 (naiveDigits s N) = N := by
  constructor
  · intro d hd
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    have := natDigits128_le s N.natAbs hs hN e he
    split <;> omega
  · unfold naiveDigits
    have h := natDigits128_value s N.natAbs hs
    have hm : ((natDigits128 s N.natAbs).map fun d : ℕ => (if N < 0 then -1 else 1) * (d : ℤ)) =
        ((natDigits128 s N.natAbs).map fun d : ℕ => (d : ℤ)).map
          fun d => (if N < 0 then -1 else 1) * d := by
      rw [List.map_map]; rfl
    rw [hm, baseValue_map_mul, h]
    split <;> omega

/-! ## The three encodings -/

/-- The slice encodings of the Z3 model. -/
inductive SliceEncoding where
  | remap
  | floorU8
  | naiveS8
  deriving DecidableEq, Repr

/-- The base the slices are weighted in: `128` for naive slices, `256` otherwise. -/
def SliceEncoding.base : SliceEncoding → ℤ
  | .naiveS8 => 128
  | _ => 256

/-- The `s` slices of `N`, lowest first. -/
def SliceEncoding.digits : SliceEncoding → ℕ → ℤ → List ℤ
  | .remap => Ozaki.ADP.remap
  | .floorU8 => floorDigits
  | .naiveS8 => naiveDigits

/-- Whether `s` slices hold every integer in `[−2^W, 2^W)` (the Z3 model's `capacity_ok`). -/
def SliceEncoding.fits : SliceEncoding → ℕ → ℕ → Bool
  | .remap => remapFits
  | .floorU8 => fun W s => decide (W + 1 ≤ 8 * s)
  | .naiveS8 => naiveFits

theorem floorDigits_length : ∀ (s : ℕ) (N : ℤ), (floorDigits s N).length = s
  | 0, _ => rfl
  | 1, _ => rfl
  | s + 2, N => by simp [floorDigits, floorDigits_length (s + 1) (N / 256)]

theorem SliceEncoding.digits_length (enc : SliceEncoding) (s : ℕ) (N : ℤ) :
    (enc.digits s N).length = s := by
  cases enc
  · exact remapFrom_length 0 s N
  · exact floorDigits_length s N
  · exact naiveDigits_length s N

/-- Floor digits are at most `255` in magnitude on the prototype's range. -/
theorem floorDigits_natAbs_le : ∀ (s : ℕ) (N : ℤ), 0 < s →
    -128 * 256 ^ (s - 1) ≤ N → N < 128 * 256 ^ (s - 1) → ∀ d ∈ floorDigits s N, d.natAbs ≤ 255
  | 0, _, h, _, _ => absurd h (by decide)
  | 1, N, _, h1, h2 => by simp [floorDigits] at h1 h2 ⊢; omega
  | s + 2, N, _, h1, h2 => by
    have hP : (256 : ℤ) ^ (s + 1) = 256 * 256 ^ s := by rw [Int.pow_succ]; omega
    simp only [show s + 2 - 1 = s + 1 by omega, hP] at h1 h2
    intro d hd
    simp only [floorDigits, List.mem_cons] at hd
    rcases hd with rfl | hd
    · omega
    · exact floorDigits_natAbs_le (s + 1) (N / 256) (by omega)
        (by simp only [show s + 1 - 1 = s by omega]; omega)
        (by simp only [show s + 1 - 1 = s by omega]; omega) d hd

/-- `2^W ≤ 128 · 256^(s−1)` when `W + 1 ≤ 8s`. -/
theorem two_pow_le_floor_range {W s : ℕ} (h : W + 1 ≤ 8 * s) :
    (2 : ℤ) ^ W ≤ 128 * 256 ^ (s - 1) := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have h1 : 2 ^ W ≤ 2 ^ (8 * t + 7) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 2 ^ (8 * t + 7) = 128 * 256 ^ t := by
    rw [Nat.pow_add, Nat.pow_mul, Nat.mul_comm]
  have h3 : (2 ^ W : ℕ) ≤ 128 * 256 ^ t := h2 ▸ h1
  rw [show t + 1 - 1 = t by omega]
  have h4 := Int.ofNat_le.mpr h3
  have e1 : ((2 ^ W : ℕ) : ℤ) = (2 : ℤ) ^ W := by simp
  have e2 : ((128 * 256 ^ t : ℕ) : ℤ) = 128 * (256 : ℤ) ^ t := by simp
  omega

/-- `|N| < 128^s` when `N ∈ [−2^W, 2^W)` and naive slices hold `W` bits. -/
theorem natAbs_lt_of_naiveFits {W s : ℕ} (h : naiveFits W s = true) {N : ℤ}
    (h1 : -(2 ^ W : ℤ) ≤ N) (h2 : N < 2 ^ W) : N.natAbs < 128 ^ s := by
  unfold naiveFits at h
  have h' : 2 ^ W ≤ 128 ^ s - 1 := of_decide_eq_true h
  have hp : ((2 ^ W : ℕ) : ℤ) = (2 : ℤ) ^ W := by simp
  have : N.natAbs ≤ 2 ^ W := by omega
  have := Nat.one_le_two_pow (n := W)
  omega

/-- **Each encoding reconstructs the fixed-point integers it is sized for.** -/
theorem SliceEncoding.digits_value (enc : SliceEncoding) {W s : ℕ} (hs : 0 < s)
    (hfit : enc.fits W s = true) {N : ℤ} (h1 : -(2 ^ W : ℤ) ≤ N) (h2 : N < 2 ^ W) :
    baseValue enc.base (enc.digits s N) = N := by
  cases enc
  · show baseValue 256 (Ozaki.ADP.remap s N) = N
    rw [baseValue_256]; exact remap_value hs N
  · show baseValue 256 (floorDigits s N) = N
    rw [baseValue_256]; exact floorDigits_value s N hs
  · exact (naiveDigits_s8 hs (natAbs_lt_of_naiveFits hfit h1 h2)).2

/-- **Each encoding's slices are bytes**: magnitude at most `255` (signed or unsigned). -/
theorem SliceEncoding.digits_natAbs_le (enc : SliceEncoding) {W s : ℕ} (hs : 0 < s)
    (hfit : enc.fits W s = true) {N : ℤ} (h1 : -(2 ^ W : ℤ) ≤ N) (h2 : N < 2 ^ W) :
    ∀ d ∈ enc.digits s N, d.natAbs ≤ 255 := by
  cases enc
  · have ⟨hlo, hhi⟩ := of_decide_eq_true hfit
    have := (remap_s8 hs N).mpr ⟨by omega, by omega⟩
    intro d hd; have := this d hd; omega
  · have h := two_pow_le_floor_range (of_decide_eq_true hfit)
    exact floorDigits_natAbs_le s N hs (by omega) (by omega)
  · intro d hd
    have := (naiveDigits_s8 hs (natAbs_lt_of_naiveFits hfit h1 h2)).1 d hd
    omega

/-! ## Recombination for any encoding -/

/-- The `t`-th slice of a vector in an encoding. -/
def sliceVecWith (enc : SliceEncoding) (s t : ℕ) (N : List ℤ) : List ℤ :=
  N.map fun z => (enc.digits s z).getD t 0

theorem sliceVecWith_length (enc : SliceEncoding) (s t : ℕ) (N : List ℤ) :
    (sliceVecWith enc s t N).length = N.length := by simp [sliceVecWith]

/-- One entry: the weighted slice products of two digit lists of length `s` add up to the product
of their values. -/
theorem entry_recombination_base (B : ℤ) {s : ℕ} {da db : List ℤ} (ha : da.length = s)
    (hb : db.length = s) :
    ((List.range s).map fun t => ((List.range s).map fun u =>
      B ^ (t + u) * (da.getD t 0 * db.getD u 0)).sum).sum = baseValue B da * baseValue B db := by
  rw [baseValue_eq_sum, baseValue_eq_sum, ha, hb]
  rw [← sumZ_map_mul_right]
  congr 1; apply List.map_congr_left; intro t _
  rw [← sumZ_map_mul_left]
  congr 1; apply List.map_congr_left; intro u _
  rw [Int.pow_add]; grind

/-- **Recombination for any encoding** (`[R.1]`): when every integer's digits reconstruct it, the
`s²` slice products, weighted by `base^(t+u)`, add up to the product of the integers. -/
theorem slice_recombination_with (enc : SliceEncoding) (s : ℕ) :
    ∀ (Na Nb : List ℤ), (∀ z ∈ Na, baseValue enc.base (enc.digits s z) = z) →
      (∀ z ∈ Nb, baseValue enc.base (enc.digits s z) = z) →
      ((List.range s).map fun t => ((List.range s).map fun u =>
        enc.base ^ (t + u) * dotZ (sliceVecWith enc s t Na) (sliceVecWith enc s u Nb)).sum).sum =
        dotZ Na Nb
  | [], Nb, _, _ => by simp [sliceVecWith, sumZ_map_zero]
  | _ :: _, [], _, _ => by simp [sliceVecWith, sumZ_map_zero]
  | a :: Na, b :: Nb, ha, hb => by
    have ih := slice_recombination_with enc s Na Nb (fun z hz => ha z (List.mem_cons_of_mem _ hz))
      (fun z hz => hb z (List.mem_cons_of_mem _ hz))
    simp only [sliceVecWith, List.map_cons, dotZ_cons] at ih ⊢
    simp only [Int.mul_add]
    have he := entry_recombination_base enc.base (enc.digits_length s a) (enc.digits_length s b)
    rw [ha a List.mem_cons_self, hb b List.mem_cons_self] at he
    rw [← he, ← ih]
    rw [← sumZ_map_add]; congr 1; apply List.map_congr_left; intro t _
    rw [← sumZ_map_add]

/-! ## Slice counts (`[T.3]`) -/

/-- **Remapped slices never need more than naive ones** (`[T.3]`): wherever `s` naive slices hold
`W` bits, so do `s` remapped slices. -/
theorem naiveFits_remapFits {W s : ℕ} (hs : 0 < s) (h : naiveFits W s = true) :
    remapFits W s = true := by
  unfold naiveFits at h
  have hW : 2 ^ W ≤ 128 ^ s - 1 := of_decide_eq_true h
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  -- `D = (256^s − 1) / 255 ≥ 256^t`, and `256^t = 2^t · 128^t`
  have hD : 256 ^ t ≤ (256 ^ (t + 1) - 1) / 255 := by
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    have := Nat.one_le_pow t 256 (by decide)
    rw [Nat.pow_succ]; omega
  have h256 : 256 ^ t = 2 ^ t * 128 ^ t := by
    rw [show (256 : ℕ) = 2 * 128 from rfl, Nat.mul_pow]
  have h128 : 128 ^ (t + 1) = 128 * 128 ^ t := by rw [Nat.pow_succ, Nat.mul_comm]
  have hM := Nat.one_le_pow t 128 (by decide)
  have hP := Nat.one_le_two_pow (n := t)
  -- `128 D ≥ 128^s ≥ 2^W` and `127 D ≥ 128^s − 2 ≥ 2^W − 1`
  have hlo : 2 ^ W ≤ 128 * ((256 ^ (t + 1) - 1) / 255) := by
    have : 128 ^ t ≤ 256 ^ t := by rw [h256]; exact Nat.le_mul_of_pos_left _ hP
    omega
  have hhi : 2 ^ W ≤ 127 * ((256 ^ (t + 1) - 1) / 255) + 1 := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp at hW ⊢; omega
    · have hP2 : 2 ≤ 2 ^ t := by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) ht; simpa using this
      have : 2 * 128 ^ t ≤ 256 ^ t := by rw [h256]; exact Nat.mul_le_mul_right _ hP2
      omega
  unfold remapFits remapLo remapHi
  apply decide_eq_true
  generalize (256 ^ (t + 1) - 1) / 255 = D at hlo hhi
  have : ((2 ^ W : ℕ) : ℤ) = (2 : ℤ) ^ W := by simp
  constructor <;> omega

/-! ## The paper's remap example (`[T.2]`) -/

/-- **The paper's example** (`[T.2]`, §3): `123 · 256 + 200` is `[200, 123]` in floor digits and
`[−56, 124]` remapped, and `−56` has the bit pattern of `200`. -/
theorem paper_remap_example :
    floorDigits 2 (123 * 256 + 200) = [200, 123] ∧ remap 2 (123 * 256 + 200) = [-56, 124] ∧
      (-56 : ℤ) % 256 = 200 := by decide

/-! ## Block size one (`[T.5]`) -/

theorem blocksOf_one : ∀ (l : List Exp), blocksOf 1 l.length l = l.map fun e => [e]
  | [] => rfl
  | e :: l => by
    simp only [List.length_cons, blocksOf, reduceCtorEq, if_false, List.take, List.drop,
      List.map_cons]
    rw [blocksOf_one l]

theorem maxE_singleton (e : Exp) : maxE [e] = e := by cases e <;> rfl

theorem eMax_self (e : Exp) : eMax e e = e := by
  cases e with
  | none => rfl
  | some a => simp [eMax]

theorem zipWith_blocks_one : ∀ (ex ey : List Exp), ex.length = ey.length →
    List.zipWith (fun bx by_ => eMax (eAdd (blockRep bx).1 (blockRep by_).2)
      (eAdd (blockRep bx).2 (blockRep by_).1)) (ex.map fun e => [e]) (ey.map fun e => [e]) =
      List.zipWith eAdd ex ey
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | a :: ex, b :: ey, h => by
    rw [List.map_cons, List.map_cons, List.zipWith_cons_cons, List.zipWith_cons_cons,
      zipWith_blocks_one ex ey (by simpa using h)]
    congr 1
    simp only [blockRep, maxE_singleton, minE]
    exact eMax_self _

/-- **Blocks of one entry give the exact estimate.** -/
theorem coarseEst_one {ex ey : List Exp} (hlen : ex.length = ey.length) :
    coarseEst 1 ex ey = fExact ex ey := by
  unfold coarseEst coarseEstWith fExact
  rw [blocksOf_one, blocksOf_one, zipWith_blocks_one ex ey hlen]

/-- **Block size `1` coarsening is the exact ESC** (`[T.5]`), for every dot product with a nonzero
product. -/
theorem escCoarse_one {x y : List ℚ} (hlen : x.length = y.length) {F : ℤ}
    (hF : fExact (expsOf x) (expsOf y) = some F) : escCoarse 1 x y = some (escExact x y) := by
  have hl : (expsOf x).length = (expsOf y).length := by simp [expsOf, hlen]
  obtain ⟨a, b, hab, ha, hb, _⟩ := fExact_attained hF
  have hax : expOf a ∈ expsOf x := List.mem_map_of_mem (List.of_mem_zip hab).1
  have hby : expOf b ∈ expsOf y := List.mem_map_of_mem (List.of_mem_zip hab).2
  have hpx := le_maxE hax
  have hpy := le_maxE hby
  rw [expOf_ne ha] at hpx; rw [expOf_ne hb] at hpy
  unfold escCoarse escExact
  cases hp : maxE (expsOf x) with
  | none => simp [hp, eLe] at hpx
  | some xp =>
    cases hq : maxE (expsOf y) with
    | none => simp [hq, eLe] at hpy
    | some yq => simp only [coarseEst_one hl, hF, Option.map_some]

/-! ## Zero policies (`[T.12]`) -/

/-- The Z3 model's `zeros_case`: row `[1.5 · 2^10, 1.25, 0, 0]`, column `[0, 1.75, 0, 0]`. -/
def zerosX : List ℚ := [3 / 2 * 2 ^ (10 : ℤ), 5 / 4, 0, 0]
def zerosY : List ℚ := [0, 7 / 4, 0, 0]

/-- The Z3 model's `field0_case`: row `[1.5 · 2^1000, 1.25 · 2^-1000, 0, 0]`, column
`[0, 1.75 · 2^-20, 0, 0]`. -/
def field0X : List ℚ := [3 / 2 * 2 ^ (1000 : ℤ), 5 / 4 * 2 ^ (-1000 : ℤ), 0, 0]
def field0Y : List ℚ := [0, 7 / 4 * 2 ^ (-20 : ℤ), 0, 0]

/-- **Skipping zeros is caught by `[X.4]`** (`[T.12]`): on the Z3 model's `zeros_case` the estimate
with zeros skipped exceeds the exact largest product exponent, while zeros as `−∞` do not. -/
theorem zeros_case_caught :
    ¬ eLe (coarseEstSkip 2 (expsOf zerosX) (expsOf zerosY)) (fExact (expsOf zerosX) (expsOf zerosY)) ∧
      eLe (coarseEst 2 (expsOf zerosX) (expsOf zerosY)) (fExact (expsOf zerosX) (expsOf zerosY)) := by
  decide +kernel

/-- **Zeros at exponent `−1022` are caught by `[X.4]`** (`[T.12]`), on the Z3 model's
`field0_case`. -/
theorem field0_case_caught :
    ¬ eLe (coarseEstField0 2 (expsOf field0X) (expsOf field0Y))
        (fExact (expsOf field0X) (expsOf field0Y)) ∧
      eLe (coarseEst 2 (expsOf field0X) (expsOf field0Y)) (fExact (expsOf field0X) (expsOf field0Y)) := by
  decide +kernel

end Ozaki.ADP
