import OzakiTC.ADP
import OzakiTC.Correct
import OzakiTC.LongDot
import Ozaki.SplitK
import Ozaki.Exact64

/-! # ADP's loose ends: subnormal inputs, success, and an exact fallback on the INT8 matrix multiplier

Three gaps of `OzakiTC/ADP.lean` and `OzakiTC/Correct.lean`:

* **Subnormal inputs.** `adp` can break Grade A on subnormal inputs, even returning the wrong sign:
  on `x = [2^-1074, 2^-1023 × 7]`, `y = [1, −2^-60 × 7]` it emulates and returns `−2^-1074` for a
  positive exact product, because the exponent clamp at `−1022` lets `2^F` exceed the largest
  product. `adpSafe` adds one guardrail, sending inputs with a nonzero entry below `2^-1022` to the
  native path, and `adpSafe_accuracy` is `adp_accuracy` with no normality hypothesis: every entry
  meets Grade A on the emulated path and the `γₖ` bound on the native path. On the five cases
  recorded from the Z3 model `adpSafe` returns what `adp` returns.
* **Success.** `adp` and `adpSafe` return values for finite inputs whose products are within range
  (`adp_isSome`, `adpSafe_isSome`; `adp` needs normal inputs, `adpSafe` does not).
* **The exact fallback on the INT8 matrix multiplier.** `adpCR` falls back to the exact rational
  product. `adpCRE` takes its exact fallback on the INT8 matrix multiplier instead: Ozaki-I with all
  `s²` slice products of `6`-bit slices (signed bytes), split into chunks so that INT32 never wraps,
  at the smallest slice count that leaves nothing over. Its fixed-point enclosures run on the INT8
  matrix multiplier with split-K too, so it is correctly rounded for binary64 inputs of any length
  (`adpCRE_eq`): the IEEE round to nearest even of `x · y`, the rounding of the other any-length
  variants on both vendors. -/

open TensorCore

namespace Ozaki.TC

/-! ## A guardrail for subnormal inputs -/

/-- Normal or zero, as a test. -/
def isNormal64 (a : ℚ) : Bool := a == 0 || decide ((2 : ℚ) ^ (-1022 : ℤ) ≤ Rat.abs a)

/-- Every entry of a decoded matrix is normal or zero. -/
def subnormalFree (A : List (List ℚ)) : Bool := A.all fun x => x.all isNormal64

theorem subnormalFree_normal {A : List (List ℚ)} (h : subnormalFree A = true) :
    ∀ x ∈ A, ∀ a ∈ x, ADP.Normal64 a := by
  intro x hx a ha
  unfold subnormalFree at h
  have := List.all_eq_true.mp (List.all_eq_true.mp h x hx) a ha
  unfold isNormal64 at this
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  exact this

/-- **ADP with a subnormal guardrail**: inputs with a subnormal entry take the native path
(reported as `nativeSlow`); otherwise `adp`. -/
def adpSafe (cfg : ADPConfig) (A B : List (List (BitVec 64))) :
    ADPPath × Option (List (List ℚ)) :=
  match decodeMatrix64 A, decodeMatrix64 B with
  | some Aq, some Bq =>
    if subnormalFree Aq && subnormalFree Bq then adp cfg A B
    else (.nativeSlow, nativeGemm64 Aq (transpose Bq))
  | _, _ => (.nativeNonfinite, none)

/-- **The guardrail.** `adpSafe` emulates only normal or zero inputs. -/
theorem adpSafe_emulated_normal {cfg : ADPConfig} {A B : List (List (BitVec 64))}
    (h : (adpSafe cfg A B).1 = .emulated) :
    ∃ Aq Bq, decodeMatrix64 A = some Aq ∧ decodeMatrix64 B = some Bq ∧
      (∀ x ∈ Aq, ∀ a ∈ x, ADP.Normal64 a) ∧ (∀ r ∈ Bq, ∀ b ∈ r, ADP.Normal64 b) := by
  unfold adpSafe at h
  cases hA : decodeMatrix64 A <;> cases hB : decodeMatrix64 B <;> simp only [hA, hB,
    reduceCtorEq] at h
  rename_i Aq Bq
  split at h
  · rename_i hn
    simp only [Bool.and_eq_true] at hn
    exact ⟨Aq, Bq, rfl, rfl, subnormalFree_normal hn.1, subnormalFree_normal hn.2⟩
  · simp at h

/-- Native FP64 GEMM meets the `γₖ` bound entry by entry. -/
theorem nativeGemm64_accuracy {Aq cols C : List (List ℚ)} (hC : nativeGemm64 Aq cols = some C)
    (hshape : ∀ x ∈ Aq, ∀ y ∈ cols, x.length = y.length)
    (hk : ∀ x ∈ Aq, x.length * (128 * 128) < 2 ^ 31) :
    C.length = Aq.length ∧ ∀ i (hi : i < Aq.length) (hiC : i < C.length),
      C[i].length = cols.length ∧ ∀ j (hj : j < cols.length) (hjC : j < C[i].length),
        Rat.abs (C[i][j] - dot Aq[i] cols[j]) ≤
          Aq[i].length * 2 ^ (-53 : ℤ) / (1 - Aq[i].length * 2 ^ (-53 : ℤ)) *
            ((List.zipWith (· * ·) Aq[i] cols[j]).map Rat.abs).sum +
          2 * Aq[i].length * (1 + 2 ^ (-53 : ℤ)) ^ Aq[i].length * 2 ^ (-1075 : ℤ) := by
  obtain ⟨hl, hrows⟩ := mapM_some_index Aq C hC
  refine ⟨hl, fun i hi hiC => ?_⟩
  obtain ⟨hl2, hents⟩ := mapM_some_index cols C[i] (hrows i hi hiC)
  refine ⟨hl2, fun j hj hjC => ?_⟩
  exact nativeEntry_error (hshape _ (List.getElem_mem _) _ (List.getElem_mem _))
    (hk _ (List.getElem_mem _)) (hents j hj hjC)

/-- **ADP with the guardrail meets Grade A for every finite input.** As `adp_accuracy`, without
any normality hypothesis: whenever `adpSafe` returns values for finite inputs of matching shapes
with `k · 2^14 < 2^31`, every entry meets Grade A on the emulated path and the `γₖ` bound on the
native path. -/
theorem adpSafe_accuracy {cfg : ADPConfig} {A B : List (List (BitVec 64))} {path : ADPPath}
    {C : List (List ℚ)} (h : adpSafe cfg A B = (path, some C)) {Aq Bq : List (List ℚ)}
    (hA : decodeMatrix64 A = some Aq) (hB : decodeMatrix64 B = some Bq)
    (hshape : ∀ x ∈ Aq, ∀ y ∈ transpose Bq, x.length = y.length)
    (hk : ∀ x ∈ Aq, x.length * (128 * 128) < 2 ^ 31) :
    C.length = Aq.length ∧ ∀ i (hi : i < Aq.length) (hiC : i < C.length),
      C[i].length = (transpose Bq).length ∧
      ∀ j (hj : j < (transpose Bq).length) (hjC : j < C[i].length),
        (path = .emulated → Rat.abs (C[i][j] - dot Aq[i] (transpose Bq)[j]) ≤
          (4 * Aq[i].length + 1) * 2 ^ (-53 : ℤ) *
            ((List.zipWith (· * ·) Aq[i] (transpose Bq)[j]).map Rat.abs).sum + 2 ^ (-1075 : ℤ)) ∧
        (path = .nativeSlow → Rat.abs (C[i][j] - dot Aq[i] (transpose Bq)[j]) ≤
          Aq[i].length * 2 ^ (-53 : ℤ) / (1 - Aq[i].length * 2 ^ (-53 : ℤ)) *
            ((List.zipWith (· * ·) Aq[i] (transpose Bq)[j]).map Rat.abs).sum +
          2 * Aq[i].length * (1 + 2 ^ (-53 : ℤ)) ^ Aq[i].length * 2 ^ (-1075 : ℤ)) := by
  unfold adpSafe at h
  rw [hA, hB] at h
  simp only at h
  split at h
  · rename_i hn
    simp only [Bool.and_eq_true] at hn
    exact adp_accuracy h hA hB hshape (subnormalFree_normal hn.1) (subnormalFree_normal hn.2) hk
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, hC⟩ := h
    obtain ⟨hl, hrest⟩ := nativeGemm64_accuracy hC hshape hk
    refine ⟨hl, fun i hi hiC => ?_⟩
    obtain ⟨hl2, hents⟩ := hrest i hi hiC
    exact ⟨hl2, fun j hj hjC => ⟨fun h => absurd h (by decide), fun _ => hents j hj hjC⟩⟩

/-! ## The exact fallback on the INT8 matrix multiplier -/

/-- The INT8 matrix multiplier as a `MatrixMultiplier`: products accumulated in `TensorCore`'s 32-bit
register. -/
def int8Multiplier : MatrixMultiplier := fun x y => some ((int8Dot 32 x y : ℤ) : ℚ)

/-- Exact on `6`-bit slices (signed bytes) while the products total less than `2^31`. -/
theorem int8Multiplier_exactOn : int8Multiplier.ExactOn 6 (2 ^ 31 - 1) := by
  intro x y _ _ _ hb
  unfold int8Multiplier
  rw [int8Dot_exact (by decide) (Nat.lt_of_le_of_lt hb (by decide))]
  rfl

/-- Split-K on the INT8 matrix multiplier: chunks of `2^18` products of `6`-bit slices
(`2^18 · 2^12 = 2^30 < 2^31`), the chunk results added exactly. -/
def int8SplitK : MatrixMultiplier := chunked (2 ^ 18) int8Multiplier

theorem int8SplitK_exactOn (B : ℕ) : int8SplitK.ExactOn 6 B :=
  chunked_exactOn int8Multiplier_exactOn (by decide) (by decide) B

/-- The INT8 dot product of signed bytes with split-K: chunks of `2^16` products, each in the
32-bit register, the chunk results added exactly. -/
def int8DotK (x y : List ℤ) : ℤ :=
  (((chunksOf (2 ^ 16) x).zip (chunksOf (2 ^ 16) y)).map fun p => int8Dot 32 p.1 p.2).sum

/-- With split-K the INT8 dot product of bytes is exact for every length. -/
theorem int8DotK_exact {x y : List ℤ} (hlen : x.length = y.length)
    (hx : ∀ a ∈ x, a.natAbs ≤ 128) (hy : ∀ b ∈ y, b.natAbs ≤ 128) : int8DotK x y = dotZ x y := by
  unfold int8DotK chunksOf
  rw [hlen]
  obtain ⟨hpairs, hsum⟩ := chunksAux_pairs (m := 2 ^ 16) (by decide) y.length x y hlen (by omega)
  rw [← hsum]
  congr 1
  apply List.map_congr_left
  intro p hp
  obtain ⟨_, h2, h3, h4⟩ := hpairs p hp
  apply int8Dot_exact (by decide)
  refine Nat.lt_of_le_of_lt (dotAbs_le _ _ 128 128 (fun a ha => hx a (h3 a ha))
    (fun b hb => hy b (h4 b hb))) ?_
  calc p.1.length * (128 * 128) ≤ 2 ^ 16 * (128 * 128) := Nat.mul_le_mul_right _ h2
    _ < 2 ^ (32 - 1) := by decide

/-- ADP's recombination with split-K INT8 slice products. -/
def int8RecombineK (s : ℕ) (Na Nb : List ℤ) : ℤ :=
  ((List.range s).map fun t => ((List.range s).map fun u =>
    256 ^ (t + u) * int8DotK (ADP.sliceVec s t Na) (ADP.sliceVec s u Nb)).sum).sum

theorem int8RecombineK_eq {s : ℕ} (hs : 0 < s) {Na Nb : List ℤ} (hlen : Na.length = Nb.length)
    (hx : ∀ z ∈ Na, ADP.remapLo s ≤ z ∧ z ≤ ADP.remapHi s)
    (hy : ∀ z ∈ Nb, ADP.remapLo s ≤ z ∧ z ≤ ADP.remapHi s) : int8RecombineK s Na Nb = dotZ Na Nb := by
  unfold int8RecombineK
  rw [← ADP.slice_recombination hs]
  congr 1; apply List.map_congr_left; intro t _
  congr 1; apply List.map_congr_left; intro u _
  congr 1
  exact int8DotK_exact (by simp [ADP.sliceVec, hlen]) (sliceVec_s8 hs hx t) (sliceVec_s8 hs hy u)

/-- The enclosure from `s` slices of width `W`, with split-K INT8 slice products. -/
def adpEnclosureK (s W : ℕ) (x y : List ℚ) : ℚ × ℚ :=
  ((int8RecombineK s (toFixed (fixedShift W x) x) (toFixed (fixedShift W y) y) : ℚ) *
      2 ^ (-(fixedShift W x + fixedShift W y)), adpBound W x y)

theorem adpEnclosureK_sound {s W : ℕ} (hs : 0 < s) (hfit : ADP.remapFits W s = true)
    {x y : List ℚ} (hlen : x.length = y.length) :
    Rat.abs (dot x y - (adpEnclosureK s W x y).1) ≤ (adpEnclosureK s W x y).2 := by
  unfold adpEnclosureK
  dsimp only
  rw [int8RecombineK_eq hs (by simp [toFixed, hlen]) (toFixed_remap hfit x) (toFixed_remap hfit y)]
  rw [← dot_scaledInts]
  exact dot_approx_error x (fixedVals W x) y (fixedVals W y) (fixedVals_length W x).symm
    (fixedVals_length W y).symm

/-- **ADP's slicing, correctly rounded, with every product on the INT8 matrix multiplier.** The
configurations `(s, W)` in turn, each an enclosure of split-K INT8 slice products, then the exact
fallback: Ozaki-I with all slice products of `6`-bit slices on the split-K INT8 matrix multiplier.
-/
def adpCREWith (rnd : ℚ → Option ℚ) (cfgs : List (ℕ × ℕ)) (smax : ℕ) (x y : List ℚ) :
    Option ℚ :=
  roundingTest rnd (cfgs.map fun c => some (adpEnclosureK c.1 c.2 x y))
    (ozaki1ExactFallback int8SplitK 6 smax x y)

theorem adpCREWith_eq {R : ℚ → Prop} {rnd : ℚ → Option ℚ} (h : RoundsToNearest R rnd)
    (hI : RoundsOnIntervals rnd) {cfgs : List (ℕ × ℕ)}
    (hcfg : ∀ c ∈ cfgs, 0 < c.1 ∧ ADP.remapFits c.2 c.1 = true) {smax : ℕ}
    (hsmax : 2098 < smax * 7) {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    adpCREWith rnd cfgs smax x y = rnd (dot x y) := by
  apply roundingTest_eq h hI _ _ _
    (ozaki1ExactFallback_eq (int8SplitK_exactOn _) hlen (Nat.le_refl _)
      (vanish64 (by decide) (by simpa using hsmax) hx hy))
  intro c hc H B hcB
  obtain ⟨cfg, hmem, rfl⟩ := List.mem_map.mp hc
  obtain ⟨hs, hfit⟩ := hcfg cfg hmem
  cases hcB
  exact adpEnclosureK_sound hs hfit hlen

/-- Correctly rounded ADP-style slicing, rounded to binary64 (IEEE's round to nearest even). -/
def adpCRE (cfgs : List (ℕ × ℕ)) (smax : ℕ) (x y : List ℚ) : Option ℚ :=
  adpCREWith fp64Round cfgs smax x y

/-- **ADP's slicing, correctly rounded, for binary64 inputs of any length**, every product on the
INT8 matrix multiplier. -/
theorem adpCRE_eq {cfgs : List (ℕ × ℕ)} (hcfg : ∀ c ∈ cfgs, 0 < c.1 ∧ ADP.remapFits c.2 c.1 = true)
    {smax : ℕ} (hsmax : 2098 < smax * 7) {x y : List ℚ} (hx : ∀ a ∈ x, Binary64Value a)
    (hy : ∀ a ∈ y, Binary64Value a) (hlen : x.length = y.length) :
    adpCRE cfgs smax x y = fp64Round (dot x y) :=
  adpCREWith_eq fp64Round_nearest fp64Round_intervals hcfg hsmax hx hy hlen

/-! ## Success -/

theorem mapM_isSome {f : α → Option β} : ∀ {l : List α}, (∀ a ∈ l, ∃ b, f a = some b) →
    ∃ r, l.mapM f = some r
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨r, hr⟩ := mapM_isSome (l := l) fun c hc => h c (List.mem_cons_of_mem _ hc)
    exact ⟨b :: r, by simp [List.mapM_cons, hb, hr]⟩

/-- Binary64 rounding succeeds up to the largest finite value. -/
theorem fp64Round_succeeds : RoundSucceeds fp64Round fp64.maxFinite := by
  intro q hq
  exact Option.isSome_iff_exists.mp (fp64Round_isSome hq)

theorem maxFinite64_ge : (2 : ℚ) ^ (1023 : ℤ) ≤ fp64.maxFinite := by decide +kernel

theorem pow_one_add_le_two {n : ℕ} (hn : n * (128 * 128) < 2 ^ 31) :
    (1 + (2 : ℚ) ^ (-53 : ℤ)) ^ n ≤ 2 := by
  have hu := two_pow_pos (-53 : ℤ)
  have h1 := pow_mul_one_sub_le (Rat.le_of_lt hu) n
  have hnu : (n : ℚ) * 2 ^ (-53 : ℤ) ≤ 1 / 2 := by
    have := two_k_u_le hn; grind
  have hP : 0 ≤ (1 + (2 : ℚ) ^ (-53 : ℤ)) ^ n := Rat.le_trans (by decide) (one_le_pow_one_add (Rat.le_of_lt hu) n)
  have : (1 + (2 : ℚ) ^ (-53 : ℤ)) ^ n * (1 / 2) ≤ (1 + (2 : ℚ) ^ (-53 : ℤ)) ^ n * (1 - n * 2 ^ (-53 : ℤ)) :=
    Rat.mul_le_mul_of_nonneg_left (by grind) hP
  grind

/-- **Native FP64 returns a value** when `Σ|xᵢyᵢ| ≤ 2^1000` and `k · 2^14 < 2^31`. -/
theorem nativeDot_isSome {x y : List ℚ} (hk : x.length * (128 * 128) < 2 ^ 31)
    (hS : ((List.zipWith (· * ·) x y).map Rat.abs).sum ≤ 2 ^ (1000 : ℤ)) :
    ∃ v, nativeDot fp64Round x y = some v := by
  have hzl : (List.zipWith (· * ·) x y).length ≤ x.length := by simp; omega
  unfold nativeDot
  generalize List.zipWith (· * ·) x y = zl at hS hzl
  cases zl with
  | nil => exact ⟨0, rfl⟩
  | cons z zs =>
    simp only [List.map_cons, List.sum_cons, List.length_cons] at hS hzl
    have hL := maxFinite64_ge
    have hA : (2 : ℚ) ^ (1000 : ℤ) ≤ 2 ^ (1023 : ℤ) := two_pow_le (by decide)
    have hzs0 : 0 ≤ (zs.map Rat.abs).sum := sum_nonneg fun a _ => abs_nonneg a
    have hz : Rat.abs z ≤ fp64.maxFinite := by have := abs_nonneg z; grind
    obtain ⟨p, hp⟩ := fp64Round_succeeds z hz
    obtain ⟨ps, hps⟩ := mapM_isSome (f := fp64Round) (l := zs) fun w hw => by
      have := le_sum_of_mem (l := zs) (f := Rat.abs) (fun c _ => abs_nonneg c) hw
      exact fp64Round_succeeds w (by have := abs_nonneg z; grind)
    dsimp only
    rw [hp, Option.bind_some, hps, Option.bind_some]
    obtain ⟨hlen, _, hsum⟩ := mapM_round_bounds fp64Round_within zs ps hps
    have hu := two_pow_pos (-53 : ℤ)
    have hη := two_pow_pos (-1075 : ℤ)
    have hpz := fp64Round_within z p hp
    have hn : ps.length * (128 * 128) < 2 ^ 31 := by
      rw [hlen]; exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) hk
    have hP := pow_one_add_le_two hn
    have hP1 := one_le_pow_one_add (Rat.le_of_lt hu) ps.length
    have hnq : (ps.length : ℚ) ≤ 2 ^ (17 : ℤ) := by
      have : ps.length ≤ 2 ^ 17 := by omega
      have e : (2 : ℚ) ^ (17 : ℤ) = ((2 ^ 17 : ℕ) : ℚ) := two_pow_natCast 17
      rw [e]; exact Rat.natCast_le_natCast.mpr this
    rw [← hlen] at hsum
    have hQ0 : 0 ≤ (ps.map Rat.abs).sum := sum_nonneg fun a _ => abs_nonneg a
    have hu1 : (2 : ℚ) ^ (-53 : ℤ) ≤ 1 := by decide +kernel
    have hηn : (4 * (2 : ℚ) ^ (17 : ℤ) + 2) * 2 ^ (-1075 : ℤ) ≤ 1 := by decide +kernel
    have hfin : 4 * (2 : ℚ) ^ (1000 : ℤ) + 1 ≤ 2 ^ (1023 : ℤ) := by decide +kernel
    refine sumWith_isSome_from (u := 2 ^ (-53 : ℤ)) (η := 2 ^ (-1075 : ℤ)) (L := fp64.maxFinite)
      (Rat.le_of_lt hu) (Rat.le_of_lt hη) (addOfRound_within fp64Round_within)
      (addOfRound_succeeds fp64Round_succeeds) ps p z (2 ^ (-53 : ℤ) * Rat.abs z + 2 ^ (-1075 : ℤ))
      (Rat.abs z + (ps.map Rat.abs).sum) hpz (Rat.le_refl) ?_
    have ha0 := abs_nonneg z
    have hnq00 : (0 : ℚ) ≤ (ps.length : ℚ) := Rat.natCast_nonneg
    generalize (2 : ℚ) ^ (-53 : ℤ) = u at *
    generalize (2 : ℚ) ^ (-1075 : ℤ) = η at *
    generalize (1 + u) ^ ps.length = P at *
    generalize ((ps.length : ℕ) : ℚ) = nq at *
    generalize (ps.map Rat.abs).sum = Q at *
    generalize (zs.map Rat.abs).sum = Z at *
    generalize Rat.abs z = a at *
    have ha : 0 ≤ a := ha0
    -- e + T ≤ 2 (a + Z) + (nq + 1) η
    have hET : u * a + η + (a + Q) ≤ 2 * 2 ^ (1000 : ℤ) + (nq + 1) * η := by
      have h1 : u * a ≤ a := by have := Rat.mul_le_mul_of_nonneg_right hu1 ha; grind
      have h2 : u * Z ≤ Z := by have := Rat.mul_le_mul_of_nonneg_right hu1 hzs0; grind
      grind
    have hET0 : 0 ≤ u * a + η + (a + Q) := by
      have := Rat.mul_nonneg (Rat.le_of_lt hu) ha
      grind
    have e1 : P * (u * a + η + (a + Q)) ≤ 2 * (u * a + η + (a + Q)) :=
      Rat.mul_le_mul_of_nonneg_right hP hET0
    have hnq0 : 0 ≤ nq := hnq00
    have e2 : nq * P * η ≤ nq * 2 * η := by
      have := Rat.mul_le_mul_of_nonneg_left hP hnq0
      exact Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt hη)
    have e3 : (4 * nq + 2) * η ≤ (4 * 2 ^ (17 : ℤ) + 2) * η :=
      Rat.mul_le_mul_of_nonneg_right (by grind) (Rat.le_of_lt hη)
    grind

/-- **An emulated entry returns a value** for normal or zero entries with `Σ|xᵢyᵢ| ≤ 2^1000`: the
fixed-point product is within `k 2^(F−52) ≤ Σ|xᵢyᵢ|` of `x · y`, so it is at most `2^1001`. -/
theorem emulEntry_isSome {W s : ℕ} (hs : 0 < s) (hfit : ADP.remapFits W s = true) {n : ℕ}
    {x y : List ℚ} (hlen : x.length = y.length) (hx : ∀ a ∈ x, ADP.OnGrid64 a)
    (hy : ∀ b ∈ y, ADP.OnGrid64 b) (hnx : ∀ a ∈ x, ADP.Normal64 a) (hny : ∀ b ∈ y, ADP.Normal64 b)
    {c : ℤ} (hc : ADP.escCoarse n x y = some c) (hW : 54 + c ≤ (W : ℤ))
    (hk : x.length * (128 * 128) < 2 ^ 31)
    (hS : ((List.zipWith (· * ·) x y).map Rat.abs).sum ≤ 2 ^ (1000 : ℤ)) :
    ∃ v, emulEntry W s x y = some v := by
  rw [emulEntry_eq hs hfit hk]
  apply fp64Round_succeeds
  obtain ⟨hsome, hnone⟩ := ADP.fixedProduct_error hlen hx hy hc hW
  have hdot := ADP.abs_dot_le_sum x y
  have hL := maxFinite64_ge
  have h1001 : 2 * (2 : ℚ) ^ (1000 : ℤ) ≤ 2 ^ (1023 : ℤ) := by decide +kernel
  generalize hSdef : ((List.zipWith (· * ·) x y).map Rat.abs).sum = S at *
  cases hF : ADP.fExact (ADP.expsOf x) (ADP.expsOf y) with
  | none =>
    rw [hnone hF]
    have := two_pow_pos (1000 : ℤ)
    grind
  | some F =>
    have hH := hsome F hF
    have hSF := ADP.two_pow_F_le hnx hny hF
    rw [hSdef] at hSF
    have hk52 : (x.length : ℚ) * 2 ^ (-52 : ℤ) ≤ 1 := by
      have := two_k_u_le hk
      have e : (2 : ℚ) ^ (-52 : ℤ) = 2 * 2 ^ (-53 : ℤ) := by
        rw [show (-52 : ℤ) = 1 + -53 by omega, two_pow_add, two_pow_one]
      rw [e]; grind
    have hterm : (x.length : ℚ) * 2 ^ (F - 52) ≤ S := by
      have e : (x.length : ℚ) * 2 ^ (F - 52) = ((x.length : ℚ) * 2 ^ (-52 : ℤ)) * 2 ^ F := by
        rw [show F - 52 = -52 + F by omega, two_pow_add]; grind
      rw [e]
      have hS0 : 0 ≤ (2 : ℚ) ^ F := Rat.le_of_lt (two_pow_pos F)
      have := Rat.mul_le_mul_of_nonneg_right hk52 hS0
      grind
    have t := abs_add_le (dot x y) (ADP.fixedProduct W x y - dot x y)
    rw [show dot x y + (ADP.fixedProduct W x y - dot x y) = ADP.fixedProduct W x y by grind,
      abs_sub_comm] at t
    grind

/-- **`adp` returns values** for finite inputs of matching shapes with `k · 2^14 < 2^31`, normal or
zero entries, and every `Σ|xᵢyᵢ| ≤ 2^1000`. -/
theorem adp_isSome {cfg : ADPConfig} {A B : List (List (BitVec 64))} {Aq Bq : List (List ℚ)}
    (hA : decodeMatrix64 A = some Aq) (hB : decodeMatrix64 B = some Bq)
    (hshape : ∀ x ∈ Aq, ∀ y ∈ transpose Bq, x.length = y.length)
    (hk : ∀ x ∈ Aq, x.length * (128 * 128) < 2 ^ 31)
    (hnA : ∀ x ∈ Aq, ∀ a ∈ x, ADP.Normal64 a) (hnB : ∀ r ∈ Bq, ∀ b ∈ r, ADP.Normal64 b)
    (hS : ∀ x ∈ Aq, ∀ y ∈ transpose Bq,
      ((List.zipWith (· * ·) x y).map Rat.abs).sum ≤ 2 ^ (1000 : ℤ)) :
    ∃ C, (adp cfg A B).2 = some C := by
  have gA := decode_onGrid hA
  have gB := decode_onGrid hB
  have gcol : ∀ y ∈ transpose Bq, ∀ b ∈ y, ADP.OnGrid64 b := fun y hy b hb => by
    obtain ⟨r, hr, hbr⟩ := mem_transpose Bq y hy b hb; exact gB r hr b hbr
  have ncol : ∀ y ∈ transpose Bq, ∀ b ∈ y, ADP.Normal64 b := fun y hy b hb => by
    obtain ⟨r, hr, hbr⟩ := mem_transpose Bq y hy b hb; exact hnB r hr b hbr
  have hnat : ∃ C, nativeGemm64 Aq (transpose Bq) = some C :=
    mapM_isSome fun x hx => mapM_isSome fun y hy => nativeDot_isSome (hk x hx) (hS x hx y hy)
  unfold adp
  rw [hA, hB]
  simp only
  cases he : matrixEsc cfg.block Aq (transpose Bq) with
  | none => exact hnat
  | some esc =>
    simp only
    split
    · obtain ⟨hs1, hfit, _⟩ := slicesNeeded_spec (adpWidth esc)
      exact mapM_isSome fun x hx => mapM_isSome fun y hy => by
        obtain ⟨c0, hc0, hle⟩ := matrixEsc_ge he x hx y hy
        have hW : 54 + c0 ≤ ((adpWidth esc : ℕ) : ℤ) := by unfold adpWidth; omega
        exact emulEntry_isSome hs1 hfit (hshape x hx y hy) (gA x hx) (gcol y hy) (hnA x hx)
          (ncol y hy) hc0 hW (hk x hx) (hS x hx y hy)
    · exact hnat

/-- **`adpSafe` returns values** for finite inputs of matching shapes with `k · 2^14 < 2^31` and
every `Σ|xᵢyᵢ| ≤ 2^1000`, subnormal entries included. -/
theorem adpSafe_isSome {cfg : ADPConfig} {A B : List (List (BitVec 64))} {Aq Bq : List (List ℚ)}
    (hA : decodeMatrix64 A = some Aq) (hB : decodeMatrix64 B = some Bq)
    (hshape : ∀ x ∈ Aq, ∀ y ∈ transpose Bq, x.length = y.length)
    (hk : ∀ x ∈ Aq, x.length * (128 * 128) < 2 ^ 31)
    (hS : ∀ x ∈ Aq, ∀ y ∈ transpose Bq,
      ((List.zipWith (· * ·) x y).map Rat.abs).sum ≤ 2 ^ (1000 : ℤ)) :
    ∃ C, (adpSafe cfg A B).2 = some C := by
  unfold adpSafe
  rw [hA, hB]
  simp only
  split
  · rename_i hn
    simp only [Bool.and_eq_true] at hn
    exact adp_isSome hA hB hshape hk (subnormalFree_normal hn.1) (subnormalFree_normal hn.2) hS
  · exact mapM_isSome fun x hx => mapM_isSome fun y hy => nativeDot_isSome (hk x hx) (hS x hx y hy)

/-! ### The subnormal counterexample -/

/-- `x = [2^-1074, 2^-1023 × 7]`, one row. -/
def subA : List (List (BitVec 64)) :=
  [[0x0000000000000001, 0x0008000000000000, 0x0008000000000000, 0x0008000000000000,
    0x0008000000000000, 0x0008000000000000, 0x0008000000000000, 0x0008000000000000]]

/-- `y = [1, −2^-60 × 7]`, one column. -/
def subB : List (List (BitVec 64)) :=
  [[0x3FF0000000000000], [0xBC30000000000000], [0xBC30000000000000], [0xBC30000000000000],
    [0xBC30000000000000], [0xBC30000000000000], [0xBC30000000000000], [0xBC30000000000000]]

/-- `adp` emulates and returns `−2^-1074`; the exact product `2^-1074 − 7 · 2^-1083 = 505 · 2^-1083`
is positive. -/
example : adp {} subA subB = (.emulated, some [[-(2 : ℚ) ^ (-1074 : ℤ)]]) := by decide +kernel

example : (do
    let Aq ← decodeMatrix64 subA; let Bq ← decodeMatrix64 subB
    pure (dot Aq[0]! (transpose Bq)[0]!)) = some (505 * (2 : ℚ) ^ (-1083 : ℤ)) := by decide +kernel

/-- `adpSafe` takes the native path and returns `2^-1074`, the correctly rounded product here. -/
example : adpSafe {} subA subB = (.nativeSlow, some [[(2 : ℚ) ^ (-1074 : ℤ)]]) := by decide +kernel

/-- Within the native `γₖ` bound (`k = 8`). -/
example : Rat.abs ((2 : ℚ) ^ (-1074 : ℤ) - 505 * 2 ^ (-1083 : ℤ)) ≤
    8 * 2 ^ (-53 : ℤ) / (1 - 8 * 2 ^ (-53 : ℤ)) * (2 ^ (-1074 : ℤ) + 7 * 2 ^ (-1083 : ℤ)) +
      2 * 8 * (1 + 2 ^ (-53 : ℤ)) ^ 8 * 2 ^ (-1075 : ℤ) := by decide +kernel

/-- The counterexample's inputs as values. -/
def subX : List ℚ := (2 : ℚ) ^ (-1074 : ℤ) :: List.replicate 7 ((2 : ℚ) ^ (-1023 : ℤ))
def subY : List ℚ := 1 :: List.replicate 7 (-(2 : ℚ) ^ (-60 : ℤ))

/-- The correctly rounded variant on the counterexample: the enclosure of `8` slices of width `56`
does not decide it, the exact fallback on the INT8 matrix multiplier does (at `2` slices of `6`
bits), and the result is the correctly rounded `2^-1074`. -/
example : roundEnclosure fp64Round (adpEnclosureK 8 56 subX subY).1 (adpEnclosureK 8 56 subX subY).2 =
    none := by decide +kernel
example : adpCRE [(8, 56)] 300 subX subY = some ((2 : ℚ) ^ (-1074 : ℤ)) := by decide +kernel

/-! ### The recorded Z3 cases: the guardrail changes nothing -/

/-- `A` of the recorded Z3 case `uniform`. -/
def z3A_uniform : List (List (BitVec 64)) :=
  [[0x3FEB0580F98A7DBE, 0x3FE84129978F9C1A, 0x3FDAEAA51052E978, 0x3FD092178FB945A6],
    [0x3FE05C5CCDF19707, 0x3FD9EA70DF588B3C, 0x3FE914E0C751C4F5, 0x3FD36979C7BE0DEC],
    [0x3FDE809082DD48FC, 0x3FE2AB10CF910F7D, 0x3FED0F42C0DFAF73, 0x3FE026650C8E9DC4],
    [0x3FD209A1991E3308, 0x3FE82F8C4C611B50, 0x3FE3C9ADC7329696, 0x3FD0084BBFE5E826]]

/-- `B` of the recorded Z3 case `uniform`. -/
def z3B_uniform : List (List (BitVec 64)) :=
  [[0x3FDFD7A39ED876D2, 0x3FD108FD82E9ABFE, 0x3FE465AC17903163, 0x3FCF09939B14A818],
    [0x3FDE4864DE229DC8, 0x3FEF0CFE6551F84D, 0x3FB5CEE2913B5428, 0x3FD44FEFA9CB8E80],
    [0x3FE5A56DCA3A0E8D, 0x3FB5D25FFDC4E570, 0x3FC39FE8A58E0AFC, 0x3FEA68A4B464DFE6],
    [0x3FEF59E3BD63DBC0, 0x3FD4700B59C77160, 0x3FC83022C1198DA4, 0x3FEF1DB2B375014F]]

/-- `A` of the recorded Z3 case `signed`. -/
def z3A_signed : List (List (BitVec 64)) :=
  [[0xBFB861B50897ADB0, 0x3FBE9A7C76D6D7E0, 0x3FEB2644263FEF40, 0xBFB1965063152DF0],
    [0x3F900F15DAE44540, 0x3FC65EDA2613AD68, 0xBFE42E8661919CB8, 0x3F98638E79CB9E80],
    [0x3FD09FFF39D2C67C, 0x3FE2C022117D48A0, 0xBFE9F9E19C6D6092, 0xBFD92A25BDBB3508],
    [0xBFEA327433B0C176, 0x3FE3D1374F1F7FCE, 0x3FD8C2979A26B7F4, 0xBFED51D5233C8BCA]]

/-- `B` of the recorded Z3 case `signed`. -/
def z3B_signed : List (List (BitVec 64)) :=
  [[0xBFAA0A24DD9192E0, 0x3FD4280F187751D4, 0x3FD54CF03598B88C, 0xBFE6DFA2C4F26632],
    [0xBFEF4E100006EAEE, 0xBFD0080B78478564, 0xBFDCEBFD95B49908, 0x3FE3DCBE13AE86EA],
    [0x3FD865570DD45AF0, 0x3FC9F916A748DCD0, 0x3FBDCB16001B4B30, 0x3FD4A62B59FCDB9C],
    [0xBFE6B35BE82CF922, 0xBFBEB123687855B0, 0xBFE59D69854855C4, 0x3FE9FB7619AE986A]]

/-- `A` of the recorded Z3 case `test2_b2`. -/
def z3A_test2_b2 : List (List (BitVec 64)) :=
  [[0x3FD52E6B43E54E9C, 0x3FE269E0D2CA264E, 0x400A6A3A4418B900, 0x401128B2F3A47E10],
    [0x401128B2F3A47E10, 0x3FD52E6B43E54E9C, 0x3FE269E0D2CA264E, 0x400A6A3A4418B900],
    [0x400A6A3A4418B900, 0x401128B2F3A47E10, 0x3FD52E6B43E54E9C, 0x3FE269E0D2CA264E],
    [0x3FE269E0D2CA264E, 0x400A6A3A4418B900, 0x401128B2F3A47E10, 0x3FD52E6B43E54E9C]]

/-- `B` of the recorded Z3 case `test2_b2`. -/
def z3B_test2_b2 : List (List (BitVec 64)) :=
  [[0x40152E6B43E54E9C, 0x3FD128B2F3A47E10, 0x3FEA6A3A4418B900, 0x400269E0D2CA264E],
    [0x400269E0D2CA264E, 0x40152E6B43E54E9C, 0x3FD128B2F3A47E10, 0x3FEA6A3A4418B900],
    [0x3FEA6A3A4418B900, 0x400269E0D2CA264E, 0x40152E6B43E54E9C, 0x3FD128B2F3A47E10],
    [0x3FD128B2F3A47E10, 0x3FEA6A3A4418B900, 0x400269E0D2CA264E, 0x40152E6B43E54E9C]]

/-- `A` of the recorded Z3 case `test2_b64`. -/
def z3A_test2_b64 : List (List (BitVec 64)) :=
  [[0x3BF52E6B43E54E9C, 0x3D1269E0D2CA264E, 0x3E4A6A3A4418B900, 0x3F6128B2F3A47E10, 0x408892F9023031D0, 0x41A5D9DC9F2A6330, 0x42D0ED9047D1C4BB, 0x43F81E74EE6DECEC],
    [0x43F81E74EE6DECEC, 0x3BF52E6B43E54E9C, 0x3D1269E0D2CA264E, 0x3E4A6A3A4418B900, 0x3F6128B2F3A47E10, 0x408892F9023031D0, 0x41A5D9DC9F2A6330, 0x42D0ED9047D1C4BB],
    [0x42D0ED9047D1C4BB, 0x43F81E74EE6DECEC, 0x3BF52E6B43E54E9C, 0x3D1269E0D2CA264E, 0x3E4A6A3A4418B900, 0x3F6128B2F3A47E10, 0x408892F9023031D0, 0x41A5D9DC9F2A6330],
    [0x41A5D9DC9F2A6330, 0x42D0ED9047D1C4BB, 0x43F81E74EE6DECEC, 0x3BF52E6B43E54E9C, 0x3D1269E0D2CA264E, 0x3E4A6A3A4418B900, 0x3F6128B2F3A47E10, 0x408892F9023031D0],
    [0x408892F9023031D0, 0x41A5D9DC9F2A6330, 0x42D0ED9047D1C4BB, 0x43F81E74EE6DECEC, 0x3BF52E6B43E54E9C, 0x3D1269E0D2CA264E, 0x3E4A6A3A4418B900, 0x3F6128B2F3A47E10],
    [0x3F6128B2F3A47E10, 0x408892F9023031D0, 0x41A5D9DC9F2A6330, 0x42D0ED9047D1C4BB, 0x43F81E74EE6DECEC, 0x3BF52E6B43E54E9C, 0x3D1269E0D2CA264E, 0x3E4A6A3A4418B900],
    [0x3E4A6A3A4418B900, 0x3F6128B2F3A47E10, 0x408892F9023031D0, 0x41A5D9DC9F2A6330, 0x42D0ED9047D1C4BB, 0x43F81E74EE6DECEC, 0x3BF52E6B43E54E9C, 0x3D1269E0D2CA264E],
    [0x3D1269E0D2CA264E, 0x3E4A6A3A4418B900, 0x3F6128B2F3A47E10, 0x408892F9023031D0, 0x41A5D9DC9F2A6330, 0x42D0ED9047D1C4BB, 0x43F81E74EE6DECEC, 0x3BF52E6B43E54E9C]]

/-- `B` of the recorded Z3 case `test2_b64`. -/
def z3B_test2_b64 : List (List (BitVec 64)) :=
  [[0x43F52E6B43E54E9C, 0x3BF81E74EE6DECEC, 0x3D10ED9047D1C4BB, 0x3E45D9DC9F2A6330, 0x3F6892F9023031D0, 0x408128B2F3A47E10, 0x41AA6A3A4418B900, 0x42D269E0D2CA264E],
    [0x42D269E0D2CA264E, 0x43F52E6B43E54E9C, 0x3BF81E74EE6DECEC, 0x3D10ED9047D1C4BB, 0x3E45D9DC9F2A6330, 0x3F6892F9023031D0, 0x408128B2F3A47E10, 0x41AA6A3A4418B900],
    [0x41AA6A3A4418B900, 0x42D269E0D2CA264E, 0x43F52E6B43E54E9C, 0x3BF81E74EE6DECEC, 0x3D10ED9047D1C4BB, 0x3E45D9DC9F2A6330, 0x3F6892F9023031D0, 0x408128B2F3A47E10],
    [0x408128B2F3A47E10, 0x41AA6A3A4418B900, 0x42D269E0D2CA264E, 0x43F52E6B43E54E9C, 0x3BF81E74EE6DECEC, 0x3D10ED9047D1C4BB, 0x3E45D9DC9F2A6330, 0x3F6892F9023031D0],
    [0x3F6892F9023031D0, 0x408128B2F3A47E10, 0x41AA6A3A4418B900, 0x42D269E0D2CA264E, 0x43F52E6B43E54E9C, 0x3BF81E74EE6DECEC, 0x3D10ED9047D1C4BB, 0x3E45D9DC9F2A6330],
    [0x3E45D9DC9F2A6330, 0x3F6892F9023031D0, 0x408128B2F3A47E10, 0x41AA6A3A4418B900, 0x42D269E0D2CA264E, 0x43F52E6B43E54E9C, 0x3BF81E74EE6DECEC, 0x3D10ED9047D1C4BB],
    [0x3D10ED9047D1C4BB, 0x3E45D9DC9F2A6330, 0x3F6892F9023031D0, 0x408128B2F3A47E10, 0x41AA6A3A4418B900, 0x42D269E0D2CA264E, 0x43F52E6B43E54E9C, 0x3BF81E74EE6DECEC],
    [0x3BF81E74EE6DECEC, 0x3D10ED9047D1C4BB, 0x3E45D9DC9F2A6330, 0x3F6892F9023031D0, 0x408128B2F3A47E10, 0x41AA6A3A4418B900, 0x42D269E0D2CA264E, 0x43F52E6B43E54E9C]]

/-- `A` of the recorded Z3 case `nonfinite`. -/
def z3A_nonfinite : List (List (BitVec 64)) :=
  [[0xBFEF36D54C3E4DCC, 0xBFE8CE7501E36018, 0xBFCB6F02BB7E1D30, 0x3FD788DD50B13A00],
    [0xBFE71FB01065DA2A, 0xBFE8CDB983B7E2B2, 0x7FF0000000000000, 0x3FE07C65311DE238],
    [0xBFE690FA782572D8, 0x3FDECDCA2087A440, 0x3FD4C1E080F849D8, 0xBFE7424C262690C2],
    [0x3FB24241AEDF3640, 0xBFBAC063DE54E110, 0xBFC661CE997138C8, 0x3FEFC41854BEA17E]]

/-- `B` of the recorded Z3 case `nonfinite`. -/
def z3B_nonfinite : List (List (BitVec 64)) :=
  [[0xBFEB0B8580968872, 0xBFE2541A3ED7C454, 0xBFD9331734D38ACC, 0x3FE99D19D9E7010A],
    [0xBF7EB317E7183E00, 0x3FDC30D7D09DE6E4, 0xBFE995BE6566F902, 0x3F92485954913BC0],
    [0x3FE5F4E82874DD2A, 0x3FA758B3D8648240, 0x3FEC75FA27F0F80A, 0x3FE86F69D3C00AFC],
    [0xBFD0845C56616F40, 0xBFEFF3C6A3A9252C, 0x3FE0564C2E409558, 0xBFE7E8E95BCD7ED0]]

example : adpSafe {} z3A_uniform z3B_uniform = adp {} z3A_uniform z3B_uniform := by decide +kernel
example : adpSafe {} z3A_signed z3B_signed = adp {} z3A_signed z3B_signed := by decide +kernel
example : adpSafe {} z3A_test2_b2 z3B_test2_b2 = adp {} z3A_test2_b2 z3B_test2_b2 := by
  decide +kernel
example : adpSafe {} z3A_test2_b64 z3B_test2_b64 = adp {} z3A_test2_b64 z3B_test2_b64 := by
  decide +kernel
example : adpSafe {} z3A_nonfinite z3B_nonfinite = adp {} z3A_nonfinite z3B_nonfinite := by
  decide +kernel

end Ozaki.TC
