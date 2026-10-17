import OzakiTC.ADPFix
import Ozaki.ADPEncodings

/-! # The Z3 ADP model's test-level checks

The Z3 model of ADP (`ozaki-NVIDIA/tests.py`) runs fourteen test-level checks `[T.1]`–`[T.14]`.
Those that are statements about all inputs are theorems here; the others are kernel-checked on the
model's own inputs in `tests/OzakiTCTests/ADPLabels.lean`.

* **`[T.1]` decoding.** Every decoded binary64 value is `m · 2^(exp(v) − 52)` with `|m| < 2^53`
  (`value64_onGrid`, `value64_bound`), and both zeros decode to `0` with exponent `−∞`
  (`decode_zeros`).
* **`[T.4]` the three encodings agree.** `adpWith cfg enc` is `adp` with the slice encoding `enc`
  (the Z3 model's `Config(encoding=…)`); with `enc = remap` it is `adp` (`adpWith_remap`). With any
  encoding, each slice is a byte and every slice product is exact in the INT32 register when
  `k · 2^16 < 2^31` (the Z3 model's static bound `[E.4]`), so an emulated entry is the binary64
  rounding of the same fixed-point product (`emulEntryWith_eq`), and two encodings that both emulate
  return the same values (`encodings_agree`, `adpWith_encodings_agree`), each with its own slice
  count (`slicesNeededWith_spec`).
* **`[T.3]` slice counts.** Remapped slices never need more than naive ones
  (`slicesNeeded_le_naive`); `53` bits need `8` naive and `7` remapped slices (`ADP.slices_53`).
* **`[T.7]` valid path.** Finite inputs take the emulated or the native-slow path
  (`adp_finite_path`).
* **`[T.10]` emergent overflow.** An emulated entry fails exactly when the rounded fixed-point product
  exceeds the largest finite binary64 value (`emulEntry_none_iff`); where the Z3 model returns
  `±Inf`, `adp` returns no values.
* **`[T.11]` subnormal inputs.** `adp` takes the emulated or native-slow path; `adpSafe` takes the
  native path (`adpSafe_subnormal`).

`[T.2]`, `[T.5]` and `[T.12]`'s zero policies are in `Ozaki.ADPEncodings`. `[T.6]`, `[T.8]` and
`[T.9]` are recorded cases. `[T.13]` (each injected fault trips its own label) and `[T.14]` (every
label is exercised) check the Z3 model's test harness, not ADP; their counterpart here is that each
label has a theorem or a kernel-checked test (`THEOREMS.md`). -/

open TensorCore

namespace Ozaki.TC

/-! ## Decoding (`[T.1]`) -/

/-- **Both zeros decode to `0`, with exponent `−∞`** (`[T.1]`). -/
theorem decode_zeros :
    value64 (0x8000000000000000 : BitVec 64) = some 0 ∧ value64 (0 : BitVec 64) = some 0 ∧
      ADP.expOf 0 = none := by
  refine ⟨by decide +kernel, by decide +kernel, by simp [ADP.expOf]⟩

/-! ## Slices of any encoding on the INT8 matrix multiplier (`[T.4]`) -/

/-- The weighted slice products of an encoding on the INT8 matrix multiplier. -/
def int8RecombineWith (enc : ADP.SliceEncoding) (s : ℕ) (Na Nb : List ℤ) : ℤ :=
  ((List.range s).map fun t => ((List.range s).map fun u =>
    enc.base ^ (t + u) *
      int8Dot 32 (ADP.sliceVecWith enc s t Na) (ADP.sliceVecWith enc s u Nb)).sum).sum

theorem int8RecombineWith_remap (s : ℕ) (Na Nb : List ℤ) :
    int8RecombineWith .remap s Na Nb = int8Recombine s Na Nb := rfl

theorem getD_natAbs_le {l : List ℤ} {B : ℕ} (h : ∀ d ∈ l, d.natAbs ≤ B) (t : ℕ) :
    (l.getD t 0).natAbs ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  cases hl : l[t]? with
  | none => simp
  | some d =>
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hl
    simpa using h _ (List.getElem_mem hi)

/-- **Any encoding's slice products recombine to the fixed-point product** on the INT8 matrix
multiplier, for integers in `[−2^W, 2^W)`, a slice count that holds `W` bits, and `k · 2^16 < 2^31`.
-/
theorem int8RecombineWith_eq {enc : ADP.SliceEncoding} {W s : ℕ} (hs : 0 < s)
    (hfit : enc.fits W s = true) {Na Nb : List ℤ}
    (ha : ∀ z ∈ Na, -(2 ^ W : ℤ) ≤ z ∧ z < 2 ^ W) (hb : ∀ z ∈ Nb, -(2 ^ W : ℤ) ≤ z ∧ z < 2 ^ W)
    (hk : Na.length * 2 ^ 16 < 2 ^ 31) : int8RecombineWith enc s Na Nb = dotZ Na Nb := by
  unfold int8RecombineWith
  rw [← ADP.slice_recombination_with enc s Na Nb
    (fun z hz => enc.digits_value hs hfit (ha z hz).1 (ha z hz).2)
    (fun z hz => enc.digits_value hs hfit (hb z hz).1 (hb z hz).2)]
  have bound : ∀ (N : List ℤ), (∀ z ∈ N, -(2 ^ W : ℤ) ≤ z ∧ z < 2 ^ W) → ∀ t,
      ∀ d ∈ ADP.sliceVecWith enc s t N, d.natAbs ≤ 255 := by
    intro N hN t d hd
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hd
    exact getD_natAbs_le (enc.digits_natAbs_le hs hfit (hN z hz).1 (hN z hz).2) t
  congr 1; apply List.map_congr_left; intro t _
  congr 1; apply List.map_congr_left; intro u _
  congr 1
  apply int8Dot_exact (by decide)
  refine Nat.lt_of_le_of_lt (dotAbs_le _ _ 255 255 (bound Na ha t) (bound Nb hb u)) ?_
  rw [ADP.sliceVecWith_length]
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (by decide)) hk

/-- One emulated entry with the slice encoding `enc`. -/
def emulEntryWith (enc : ADP.SliceEncoding) (W s : ℕ) (x y : List ℚ) : Option ℚ :=
  fp64Round ((int8RecombineWith enc s (toFixed (ADP.shiftOf W x) x) (toFixed (ADP.shiftOf W y) y) :
    ℚ) * pow2 (-(ADP.shiftOf W x + ADP.shiftOf W y)))

theorem emulEntryWith_remap (W s : ℕ) (x y : List ℚ) :
    emulEntryWith .remap W s x y = emulEntry W s x y := rfl

/-- Fixed point with ADP's shift lies in `[−2^W, 2^W)` (`[F.1]`). -/
theorem toFixed_shiftOf_range (W : ℕ) (x : List ℚ) :
    ∀ z ∈ toFixed (ADP.shiftOf W x) x, -(2 ^ W : ℤ) ≤ z ∧ z < 2 ^ W := by
  have hp : (0 : ℤ) < 2 ^ W := Int.pow_pos (by decide)
  intro z hz
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
  unfold ADP.shiftOf
  cases hm : ADP.maxE (ADP.expsOf x) with
  | none =>
    rw [ADP.eq_zero_of_maxE_none hm a ha]
    simp only [Rat.zero_mul, ADP.floor_zero]
    omega
  | some e =>
    simp only
    exact ADP.fixed_range (e := e) (ADP.exp64_le_maxE hm a ha) W

/-- **An emulated entry is the same rounding for every encoding** whose slice count holds `W`
bits. -/
theorem emulEntryWith_eq {enc : ADP.SliceEncoding} {W s : ℕ} (hs : 0 < s)
    (hfit : enc.fits W s = true) {x y : List ℚ} (hk : x.length * 2 ^ 16 < 2 ^ 31) :
    emulEntryWith enc W s x y = fp64Round (ADP.fixedProduct W x y) := by
  unfold emulEntryWith
  rw [int8RecombineWith_eq hs hfit (toFixed_shiftOf_range W x) (toFixed_shiftOf_range W y)
    (by simpa [toFixed] using hk)]
  rfl

/-- **The encodings agree** (`[T.4]`), entry by entry. -/
theorem encodings_agree (enc enc' : ADP.SliceEncoding) {W s s' : ℕ} (hs : 0 < s) (hs' : 0 < s')
    (hfit : enc.fits W s = true) (hfit' : enc'.fits W s' = true) {x y : List ℚ}
    (hk : x.length * 2 ^ 16 < 2 ^ 31) :
    emulEntryWith enc W s x y = emulEntryWith enc' W s' x y := by
  rw [emulEntryWith_eq hs hfit hk, emulEntryWith_eq hs' hfit' hk]

/-! ## Slice counts per encoding (`[B.2]`, `[T.3]`) -/

/-- The first `s` from `start` (within `fuel` tries) whose slices hold `W` bits. -/
def slicesFromWith (enc : ADP.SliceEncoding) (W : ℕ) : ℕ → ℕ → ℕ
  | s, 0 => s
  | s, fuel + 1 => if enc.fits W s then s else slicesFromWith enc W (s + 1) fuel

/-- The fewest slices of an encoding that hold `W` bits. -/
def slicesNeededWith (enc : ADP.SliceEncoding) (W : ℕ) : ℕ := slicesFromWith enc W 1 (W + 1)

theorem slicesFromWith_remap (W : ℕ) :
    ∀ fuel s, slicesFromWith .remap W s fuel = slicesFrom W s fuel
  | 0, _ => rfl
  | fuel + 1, s => by
    simp only [slicesFromWith, slicesFrom, ADP.SliceEncoding.fits, slicesFromWith_remap W fuel]

theorem slicesNeededWith_remap (W : ℕ) : slicesNeededWith .remap W = slicesNeeded W :=
  slicesFromWith_remap W _ _

/-- `W + 1` slices of every encoding hold `W` bits. -/
theorem fits_succ (enc : ADP.SliceEncoding) (W : ℕ) : enc.fits W (W + 1) = true := by
  cases enc
  · exact remapFits_succ W
  · simp only [ADP.SliceEncoding.fits]; apply decide_eq_true; omega
  · simp only [ADP.SliceEncoding.fits, ADP.naiveFits]
    apply decide_eq_true
    have h1 : 2 ^ W < 2 ^ (7 * (W + 1)) := Nat.pow_lt_pow_right (by decide) (by omega)
    have h2 : 2 ^ (7 * (W + 1)) = 128 ^ (W + 1) := by rw [Nat.pow_mul]
    omega

theorem slicesFromWith_spec (enc : ADP.SliceEncoding) (W : ℕ) : ∀ fuel s,
    s ≤ slicesFromWith enc W s fuel ∧
    (∀ t, s ≤ t → t < slicesFromWith enc W s fuel → enc.fits W t = false) ∧
    (enc.fits W (slicesFromWith enc W s fuel) = true ∨ slicesFromWith enc W s fuel = s + fuel)
  | 0, s => ⟨Nat.le_refl _, fun t h1 h2 => by simp [slicesFromWith] at h2; omega,
      Or.inr (by simp [slicesFromWith])⟩
  | fuel + 1, s => by
    unfold slicesFromWith
    split
    · rename_i h; exact ⟨Nat.le_refl _, fun t h1 h2 => by omega, Or.inl h⟩
    · rename_i h
      obtain ⟨a, b, c⟩ := slicesFromWith_spec enc W fuel (s + 1)
      refine ⟨by omega, fun t h1 h2 => ?_, by rcases c with c | c; exact Or.inl c; right; omega⟩
      by_cases ht : t = s
      · subst ht; simpa using h
      · exact b t (by omega) h2

/-- **Each encoding's slice count is the minimum that holds `W` bits** (`[B.2]`). -/
theorem slicesNeededWith_spec (enc : ADP.SliceEncoding) (W : ℕ) :
    1 ≤ slicesNeededWith enc W ∧ enc.fits W (slicesNeededWith enc W) = true ∧
      ∀ t, 1 ≤ t → t < slicesNeededWith enc W → enc.fits W t = false := by
  obtain ⟨a, b, c⟩ := slicesFromWith_spec enc W (W + 1) 1
  unfold slicesNeededWith
  refine ⟨a, ?_, b⟩
  rcases c with c | c
  · exact c
  · have := b (W + 1) (by omega) (by omega)
    rw [fits_succ] at this; exact absurd this (by decide)

/-- **Remapped slices never need more than naive ones** (`[T.3]`): the remap count is at most every
naive count that holds `W` bits, in particular the fewest. -/
theorem slicesNeeded_le_naive {W s : ℕ} (hs : 1 ≤ s) (h : ADP.naiveFits W s = true) :
    slicesNeeded W ≤ s := by
  obtain ⟨_, _, hmin⟩ := slicesNeeded_spec W
  apply Classical.byContradiction; intro hlt
  have := hmin s hs (by omega)
  rw [ADP.naiveFits_remapFits (by omega) h] at this
  exact absurd this (by decide)

theorem slicesNeeded_le_naiveNeeded (W : ℕ) : slicesNeeded W ≤ slicesNeededWith .naiveS8 W :=
  slicesNeeded_le_naive (slicesNeededWith_spec .naiveS8 W).1 (slicesNeededWith_spec .naiveS8 W).2.1

/-! ## The routine with any encoding (`[T.4]`) -/

/-- **ADP with the slice encoding `enc`** (the Z3 model's `Config(encoding=enc)`): the same scan,
ESC, width and heuristic, with `enc`'s slice count and slices. -/
def adpWith (cfg : ADPConfig) (enc : ADP.SliceEncoding) (A B : List (List (BitVec 64))) :
    ADPPath × Option (List (List ℚ)) :=
  match decodeMatrix64 A, decodeMatrix64 B with
  | some Aq, some Bq =>
    match matrixEsc cfg.block Aq (transpose Bq) with
    | none => (.nativeSlow, nativeGemm64 Aq (transpose Bq))
    | some esc =>
      if slicesNeededWith enc (adpWidth esc) * slicesNeededWith enc (adpWidth esc) ≤
          cfg.speedRatio then
        (.emulated, Aq.mapM fun x => (transpose Bq).mapM fun y =>
          emulEntryWith enc (adpWidth esc) (slicesNeededWith enc (adpWidth esc)) x y)
      else (.nativeSlow, nativeGemm64 Aq (transpose Bq))
  | _, _ => (.nativeNonfinite, none)

/-- With remapped slices, `adpWith` is `adp`. -/
theorem adpWith_remap (cfg : ADPConfig) (A B : List (List (BitVec 64))) :
    adpWith cfg .remap A B = adp cfg A B := by
  unfold adpWith adp
  cases decodeMatrix64 A <;> cases decodeMatrix64 B <;> try rfl
  rename_i Aq Bq
  cases he : matrixEsc cfg.block Aq (transpose Bq) <;>
    simp only [he, slicesNeededWith_remap, emulEntryWith_remap]

theorem mapM_congr_mem {f g : α → Option β} : ∀ {l : List α}, (∀ a ∈ l, f a = g a) →
    l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h a List.mem_cons_self,
      mapM_congr_mem (l := l) fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- **On the emulated path, every encoding returns the binary64 roundings of the fixed-point
products**, when the rows of `A` have `k · 2^16 < 2^31`. -/
theorem adpWith_emulated_values {cfg : ADPConfig} {enc : ADP.SliceEncoding}
    {A B : List (List (BitVec 64))} (h : (adpWith cfg enc A B).1 = .emulated)
    (hk : ∀ r ∈ A, r.length * 2 ^ 16 < 2 ^ 31) :
    ∃ Aq Bq esc, decodeMatrix64 A = some Aq ∧ decodeMatrix64 B = some Bq ∧
      matrixEsc cfg.block Aq (transpose Bq) = some esc ∧
      (adpWith cfg enc A B).2 = Aq.mapM fun x => (transpose Bq).mapM fun y =>
        fp64Round (ADP.fixedProduct (adpWidth esc) x y) := by
  unfold adpWith at h ⊢
  cases hA : decodeMatrix64 A <;> cases hB : decodeMatrix64 B <;> simp only [hA, hB,
    reduceCtorEq] at h
  rename_i Aq Bq
  cases he : matrixEsc cfg.block Aq (transpose Bq) with
  | none => simp [he] at h
  | some esc =>
    simp only [he] at h ⊢
    split at h
    · refine ⟨Aq, Bq, esc, rfl, rfl, he, ?_⟩
      rw [if_pos (by assumption)]
      simp only
      apply mapM_congr_mem; intro x hx
      apply mapM_congr_mem; intro y _
      obtain ⟨r, hr, hrx⟩ := mapM_some_mem hA x hx
      have hlen := (mapM_some_index r x hrx).1
      obtain ⟨hs1, hfit, _⟩ := slicesNeededWith_spec enc (adpWidth esc)
      exact emulEntryWith_eq (by omega) hfit (by rw [hlen]; exact hk r hr)
    · simp at h

/-- **The three encodings agree on the whole routine** (`[T.4]`): any two encodings that both
take the emulated path return the same values. -/
theorem adpWith_encodings_agree {cfg : ADPConfig} {enc enc' : ADP.SliceEncoding}
    {A B : List (List (BitVec 64))} (h : (adpWith cfg enc A B).1 = .emulated)
    (h' : (adpWith cfg enc' A B).1 = .emulated) (hk : ∀ r ∈ A, r.length * 2 ^ 16 < 2 ^ 31) :
    (adpWith cfg enc A B).2 = (adpWith cfg enc' A B).2 := by
  obtain ⟨Aq, Bq, esc, hA, hB, he, hv⟩ := adpWith_emulated_values h hk
  obtain ⟨Aq', Bq', esc', hA', hB', he', hv'⟩ := adpWith_emulated_values h' hk
  rw [hA] at hA'; rw [hB] at hB'
  cases hA'; cases hB'
  rw [he] at he'; cases he'
  rw [hv, hv']

/-! ## Paths (`[T.7]`, `[T.10]`, `[T.11]`) -/

/-- **Finite inputs take a valid path** (`[T.7]`): emulated or native-slow. -/
theorem adp_finite_path (cfg : ADPConfig) {A B : List (List (BitVec 64))} {Aq Bq : List (List ℚ)}
    (hA : decodeMatrix64 A = some Aq) (hB : decodeMatrix64 B = some Bq) :
    (adp cfg A B).1 = .emulated ∨ (adp cfg A B).1 = .nativeSlow := by
  unfold adp
  rw [hA, hB]
  simp only
  split
  · exact Or.inr rfl
  · split
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- **Emergent overflow** (`[T.10]`): an emulated entry fails exactly when the rounded fixed-point
product exceeds the largest finite binary64 value. The Z3 model returns `±Inf` there; `adp`
returns no values. -/
theorem emulEntry_none_iff {W s : ℕ} (hs : 0 < s) (hfit : ADP.remapFits W s = true)
    {x y : List ℚ} (hk : x.length * (128 * 128) < 2 ^ 31) :
    emulEntry W s x y = none ↔
      fp64.maxFinite < Rat.abs (rneU 53 (-1022) (ADP.fixedProduct W x y)) := by
  rw [emulEntry_eq hs hfit hk]; exact fp64Round_none_iff _

/-- **Subnormal inputs** (`[T.11]`): with a subnormal entry, `adpSafe` takes the native path. -/
theorem adpSafe_subnormal (cfg : ADPConfig) {A B : List (List (BitVec 64))}
    {Aq Bq : List (List ℚ)} (hA : decodeMatrix64 A = some Aq) (hB : decodeMatrix64 B = some Bq)
    (hsub : (subnormalFree Aq && subnormalFree Bq) = false) :
    adpSafe cfg A B = (.nativeSlow, nativeGemm64 Aq (transpose Bq)) := by
  unfold adpSafe
  rw [hA, hB]
  simp only [hsub, Bool.false_eq_true, if_false]

end Ozaki.TC
