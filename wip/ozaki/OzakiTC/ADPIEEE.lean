import OzakiTC.IEEESchemes

/-! # ADP with IEEE special values

`adp` returns no values on its non-finite path, and none either where an emulated or native result
overflows; the Z3 model of ADP returns native FP64 results there, `±Inf` and NaN included, and
`±Inf` for an emulated result that overflows. `adpIEEE` is the routine on IEEE data:

* the words are decoded to IEEE data (`decodeF64`: `±0` keep their sign, `±Inf`, NaN, exactly as
  IEEE classifies the word, `decodeF64_inf_iff`, `decodeF64_nan_iff`);
* the non-finite and native paths run native FP64 with IEEE operations (`nativeGemmIEEE`: each
  product rounded and added left to right from `+0`, as `acc = acc + A[i][t] * B[t][j]`);
* the emulated path rounds the recombined fixed-point product once, to `±Inf` on overflow and to
  `+0` for a zero product, as converting the exact sum to a double does.

It takes the same path as `adp` and, wherever `adp` returns values, the same values
(`adpIEEE_agrees`); `adpSafeIEEE` is the same for the routine with the subnormal guardrail
(`adpSafeIEEE_agrees`). On the Z3 model's cases with an infinity, a NaN and an emulated overflow it
returns the Z3 model's words, class for class (`tests/OzakiTCTests/Specials.lean`). -/

open TensorCore

namespace Ozaki.TC

/-! ## Decoding -/

/-- The sign bit of a binary64 word. -/
def signBit64 (w : BitVec 64) : Bool := decide (w.toNat / 2 ^ 63 = 1)

/-- **A binary64 word as an IEEE datum**: its value when finite, signed by the value's sign or, for
a zero, by the sign bit; `±Inf` and NaN for the words TensorCore does not decode (exponent field all
ones), told apart by the significand field. -/
def decodeF64 (w : BitVec 64) : FVal :=
  match value64 w with
  | some v => .fin ⟨v, if v = 0 then signBit64 w else decide (v < 0)⟩
  | none => if w.toNat % 2 ^ 52 = 0 then .inf (signBit64 w) else .nan

/-- Decoded words are binary64 data. -/
theorem decodeF64_inFormat (w : BitVec 64) : (decodeF64 w).InFormat 53 (-1022) 1023 := by
  unfold decodeF64
  cases hv : value64 w with
  | none => simp only; split <;> trivial
  | some v =>
    refine ⟨fp64_binary64 (binaryValue_finiteValue fp64_wellFormed hv), fun h0 => ?_⟩
    show (if v = 0 then signBit64 w else decide (v < 0)) = decide (v < 0)
    rw [if_neg h0]

theorem classify64_infinity {n : ℕ} {neg : Bool} (hn : n < 2 ^ 64)
    (h : classifyNat fp64 n = .infinity neg) : n % 2 ^ 52 = 0 ∧ neg = decide (n / 2 ^ 63 = 1) := by
  unfold classifyNat at h
  dsimp only [fp64] at h
  split at h
  · split at h
    · cases h
      refine ⟨by assumption, ?_⟩
      have : n / 2 ^ 63 < 2 := by omega
      by_cases h1 : n / 2 ^ 63 = 1 <;> simp_all <;> omega
    · cases h
  · split at h
    · split at h <;> cases h
    · cases h

theorem classify64_nan {n : ℕ} (h : classifyNat fp64 n = .nan) :
    n % 2 ^ 52 ≠ 0 ∧ n / 2 ^ 52 % 2 ^ 11 = 2 ^ 11 - 1 := by
  unfold classifyNat at h
  dsimp only [fp64] at h
  split at h
  · split at h
    · cases h
    · exact ⟨by assumption, by assumption⟩
  · split at h
    · split at h <;> cases h
    · cases h

/-- **Decoding is IEEE's for NaN**: a word decodes to NaN exactly when its exponent field is all ones
and its significand field is nonzero. -/
theorem decodeF64_nan_iff (w : BitVec 64) : decodeF64 w = .nan ↔ classify fp64 w = .nan := by
  unfold decodeF64 value64 binaryValue classify
  cases hc : classifyNat fp64 w.toNat with
  | zero _ => simp [Classification.finite]
  | subnormal _ => simp [Classification.finite]
  | normal _ => simp [Classification.finite]
  | infinity m =>
    obtain ⟨h0, _⟩ := classify64_infinity w.isLt hc
    simp [Classification.finite, h0]
  | nan =>
    obtain ⟨h0, _⟩ := classify64_nan hc
    simp [Classification.finite, h0]

/-- **Decoding is IEEE's for infinities**: a word decodes to `±Inf` exactly when it is an infinity of
that sign. -/
theorem decodeF64_inf_iff (w : BitVec 64) (n : Bool) :
    decodeF64 w = .inf n ↔ classify fp64 w = .infinity n := by
  unfold decodeF64 value64 binaryValue classify
  cases hc : classifyNat fp64 w.toNat with
  | zero _ => simp [Classification.finite]
  | subnormal _ => simp [Classification.finite]
  | normal _ => simp [Classification.finite]
  | infinity m =>
    obtain ⟨h0, hs⟩ := classify64_infinity w.isLt hc
    simp [Classification.finite, h0, signBit64, hs]
  | nan =>
    obtain ⟨h0, _⟩ := classify64_nan hc
    simp [Classification.finite, h0]

/-- The value of a finite datum. -/
def finVal (v : FVal) : Option ℚ := (finPart v).map Signed.val

/-- The values of a matrix of data, `none` if an entry is infinite or NaN. -/
def readValues (C : List (List FVal)) : Option (List (List ℚ)) := C.mapM (·.mapM finVal)

/-- A decoded row of finite words is a row of finite data with the decoded values. -/
theorem decodeRow : ∀ (ws : List (BitVec 64)) {r : List ℚ}, ws.mapM value64 = some r →
    ∃ sx : List Signed, ws.map decodeF64 = sx.map .fin ∧ sx.map Signed.val = r
  | [], r, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨[], rfl, rfl⟩
  | w :: ws, r, h => by
    rw [List.mapM_cons] at h
    cases hw : value64 w with
    | none => simp [hw] at h
    | some v =>
      cases hws : ws.mapM value64 with
      | none => simp [hw, hws] at h
      | some rs =>
        simp only [hw, hws, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        obtain ⟨sx, h1, h2⟩ := decodeRow ws hws
        refine ⟨⟨v, if v = 0 then signBit64 w else decide (v < 0)⟩ :: sx, ?_, ?_⟩
        · simp only [List.map_cons, h1]
          unfold decodeF64; rw [hw]
        · simp only [List.map_cons, h2]

theorem decodeMatrix64_fin : ∀ (A : List (List (BitVec 64))) {Aq : List (List ℚ)},
    decodeMatrix64 A = some Aq →
    ∃ As : List (List Signed), A.map (·.map decodeF64) = As.map (·.map .fin) ∧
      As.map (·.map Signed.val) = Aq
  | [], Aq, h => by
    simp only [decodeMatrix64, List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact ⟨[], rfl, rfl⟩
  | ws :: A, Aq, h => by
    unfold decodeMatrix64 at h
    rw [List.mapM_cons] at h
    cases hw : ws.mapM value64 with
    | none => simp [hw] at h
    | some r =>
      cases hA : A.mapM (·.mapM value64) with
      | none => simp [hw, hA] at h
      | some rs =>
        simp only [hw, hA, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        obtain ⟨sx, h1, h2⟩ := decodeRow ws hw
        obtain ⟨As, h3, h4⟩ := decodeMatrix64_fin A hA
        exact ⟨sx :: As, by simp only [List.map_cons, h1, h3], by simp only [List.map_cons, h2, h4]⟩

/-! ## Transposition and mapping -/

/-- `transpose` for any entry type. -/
def transposeG {α : Type} : List (List α) → List (List α)
  | [] => []
  | [r] => r.map fun a => [a]
  | r :: rs => List.zipWith List.cons r (transposeG rs)

theorem transpose_eq_transposeG : ∀ B : List (List ℚ), transpose B = transposeG B
  | [] => rfl
  | [_] => rfl
  | r :: r' :: rs => by
    have ih := transpose_eq_transposeG (r' :: rs)
    simp only [transpose, transposeG] at ih ⊢
    rw [ih]

theorem zipWith_cons_map {α β : Type} (f : α → β) :
    ∀ (r : List α) (rs : List (List α)),
      List.zipWith List.cons (r.map f) (rs.map (·.map f)) =
        (List.zipWith List.cons r rs).map (·.map f)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: r, b :: rs => by
    simp only [List.map_cons, List.zipWith_cons_cons]
    rw [zipWith_cons_map f r rs]

theorem transposeG_map {α β : Type} (f : α → β) :
    ∀ B : List (List α), transposeG (B.map (·.map f)) = (transposeG B).map (·.map f)
  | [] => rfl
  | [r] => by simp [transposeG, List.map_map]
  | r :: r' :: rs => by
    have ih := transposeG_map f (r' :: rs)
    simp only [List.map_cons, transposeG] at ih ⊢
    rw [ih, zipWith_cons_map]

/-- `mapM` through a map: if `f a = some c` forces `r (g a) = some c`, then reading the mapped list
with `r` gives what `mapM f` gives. -/
theorem mapM_map_of {α β γ : Type} {f : α → Option β} {g : α → γ} {r : γ → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, ∀ c, f a = some c → r (g a) = some c) →
    ∀ {cs : List β}, l.mapM f = some cs → (l.map g).mapM r = some cs
  | [], _, cs, h => h
  | a :: l, hfg, cs, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some c =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some cs' =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        rw [List.map_cons, List.mapM_cons, hfg a List.mem_cons_self c ha,
          mapM_map_of (fun a' ha' => hfg a' (List.mem_cons_of_mem _ ha')) hl]
        rfl

/-! ## Native FP64 and the emulated entry with special values -/

/-- **Native FP64 GEMM with IEEE operations**, `A` by rows and `B` by columns. -/
def nativeGemmIEEE (A cols : List (List FVal)) : List (List FVal) :=
  A.map fun x => cols.map fun y => nativeDotIEEE 53 (-1022) 1023 x y

/-- The value the emulated path rounds: the recombined fixed-point product, rescaled. -/
def emulValue (W s : ℕ) (x y : List ℚ) : ℚ :=
  (int8Recombine s (toFixed (ADP.shiftOf W x) x) (toFixed (ADP.shiftOf W y) y) : ℚ) *
    pow2 (-(ADP.shiftOf W x + ADP.shiftOf W y))

theorem emulEntry_eq_value (W s : ℕ) (x y : List ℚ) :
    emulEntry W s x y = rne64 (emulValue W s x y) := rfl

/-- **One emulated entry with special values**: the fixed-point product rounded once, `±Inf` on
overflow, `+0` for a zero product. -/
def emulEntryF (W s : ℕ) (x y : List ℚ) : FVal :=
  roundF 53 (-1022) 1023 (emulValue W s x y) false

theorem finVal_emulEntryF {W s : ℕ} {x y : List ℚ} {c : ℚ} (h : emulEntry W s x y = some c) :
    finVal (emulEntryF W s x y) = some c := by
  unfold emulEntryF
  rw [emulEntry_eq_value] at h
  rw [roundF_of_some h]; rfl

/-- On finite inputs native FP64 with IEEE operations returns native FP64's values. -/
theorem nativeGemmIEEE_agrees {A B : List (List (BitVec 64))} {Aq Bq : List (List ℚ)}
    (hA : decodeMatrix64 A = some Aq) (hB : decodeMatrix64 B = some Bq) {C : List (List ℚ)}
    (h : nativeGemm64 Aq (transpose Bq) = some C) :
    readValues (nativeGemmIEEE (A.map (·.map decodeF64))
      (transposeG (B.map (·.map decodeF64)))) = some C := by
  obtain ⟨As, hAf, rfl⟩ := decodeMatrix64_fin A hA
  obtain ⟨Bs, hBf, rfl⟩ := decodeMatrix64_fin B hB
  rw [hAf, hBf, transposeG_map]
  rw [transpose_eq_transposeG, transposeG_map] at h
  unfold nativeGemm64 at h
  unfold nativeGemmIEEE readValues
  rw [List.mapM_map] at h
  rw [List.map_map]
  refine mapM_map_of (fun sx _ cs hcs => ?_) h
  simp only [Function.comp_apply] at hcs ⊢
  rw [List.mapM_map] at hcs
  rw [List.map_map]
  refine mapM_map_of (fun sy _ c hc => ?_) hcs
  simp only [Function.comp_apply] at hc ⊢
  obtain ⟨n, hn⟩ := nativeDotIEEE_fin (p := 53) (emin := -1022) (emax := 1023) (by decide)
    (by decide) hc
  rw [hn]; rfl

/-! ## The routine -/

/-- **ADP with IEEE special values**: `adp`'s paths, with native FP64 on IEEE data on the native
and non-finite paths and the emulated entries rounded with overflow to `±Inf`. -/
def adpIEEE (cfg : ADPConfig) (A B : List (List (BitVec 64))) : ADPPath × List (List FVal) :=
  match decodeMatrix64 A, decodeMatrix64 B with
  | some Aq, some Bq =>
    match matrixEsc cfg.block Aq (transpose Bq) with
    | none => (.nativeSlow, nativeGemmIEEE (A.map (·.map decodeF64))
        (transposeG (B.map (·.map decodeF64))))
    | some esc =>
      if slicesNeeded (adpWidth esc) * slicesNeeded (adpWidth esc) ≤ cfg.speedRatio then
        (.emulated, Aq.map fun x => (transpose Bq).map fun y =>
          emulEntryF (adpWidth esc) (slicesNeeded (adpWidth esc)) x y)
      else (.nativeSlow, nativeGemmIEEE (A.map (·.map decodeF64))
        (transposeG (B.map (·.map decodeF64))))
  | _, _ => (.nativeNonfinite, nativeGemmIEEE (A.map (·.map decodeF64))
      (transposeG (B.map (·.map decodeF64))))

/-- **The non-finite path is native FP64 with IEEE operations**: when the routine takes it (some word
is an infinity or a NaN), every entry is the IEEE dot product of the decoded row and column, each
product rounded and added left to right. -/
theorem adpIEEE_nonfinite {cfg : ADPConfig} {A B : List (List (BitVec 64))}
    (h : (adpIEEE cfg A B).1 = .nativeNonfinite) :
    (adpIEEE cfg A B).2 = nativeGemmIEEE (A.map (·.map decodeF64))
      (transposeG (B.map (·.map decodeF64))) := by
  unfold adpIEEE at h ⊢
  cases hA : decodeMatrix64 A <;> cases hB : decodeMatrix64 B <;> simp only [hA, hB] at h ⊢
  rename_i Aq Bq
  cases he : matrixEsc cfg.block Aq (transpose Bq) with
  | none => simp only [he] at h; cases h
  | some esc =>
    simp only [he] at h
    split at h <;> cases h

/-- **`adpIEEE` is `adp` with special values**: the same path, and wherever `adp` returns values,
the same values. -/
theorem adpIEEE_agrees (cfg : ADPConfig) (A B : List (List (BitVec 64))) :
    (adpIEEE cfg A B).1 = (adp cfg A B).1 ∧
      ∀ C, (adp cfg A B).2 = some C → readValues (adpIEEE cfg A B).2 = some C := by
  unfold adpIEEE adp
  cases hA : decodeMatrix64 A with
  | none => exact ⟨rfl, fun C h => by simp at h⟩
  | some Aq =>
    cases hB : decodeMatrix64 B with
    | none => exact ⟨rfl, fun C h => by simp at h⟩
    | some Bq =>
      simp only
      cases matrixEsc cfg.block Aq (transpose Bq) with
      | none => exact ⟨rfl, fun C h => nativeGemmIEEE_agrees hA hB h⟩
      | some esc =>
        simp only
        split
        · refine ⟨rfl, fun C h => ?_⟩
          unfold readValues
          refine mapM_map_of (fun x _ cs hcs => ?_) h
          exact mapM_map_of (fun y _ c hc => finVal_emulEntryF hc) hcs
        · exact ⟨rfl, fun C h => nativeGemmIEEE_agrees hA hB h⟩

/-- ADP with the subnormal guardrail and IEEE special values. -/
def adpSafeIEEE (cfg : ADPConfig) (A B : List (List (BitVec 64))) : ADPPath × List (List FVal) :=
  match decodeMatrix64 A, decodeMatrix64 B with
  | some Aq, some Bq =>
    if subnormalFree Aq && subnormalFree Bq then adpIEEE cfg A B
    else (.nativeSlow, nativeGemmIEEE (A.map (·.map decodeF64))
      (transposeG (B.map (·.map decodeF64))))
  | _, _ => (.nativeNonfinite, nativeGemmIEEE (A.map (·.map decodeF64))
      (transposeG (B.map (·.map decodeF64))))

theorem adpSafeIEEE_agrees (cfg : ADPConfig) (A B : List (List (BitVec 64))) :
    (adpSafeIEEE cfg A B).1 = (adpSafe cfg A B).1 ∧
      ∀ C, (adpSafe cfg A B).2 = some C → readValues (adpSafeIEEE cfg A B).2 = some C := by
  unfold adpSafeIEEE adpSafe
  cases hA : decodeMatrix64 A with
  | none => exact ⟨rfl, fun C h => by simp at h⟩
  | some Aq =>
    cases hB : decodeMatrix64 B with
    | none => exact ⟨rfl, fun C h => by simp at h⟩
    | some Bq =>
      simp only
      split
      · exact adpIEEE_agrees cfg A B
      · exact ⟨rfl, fun C h => nativeGemmIEEE_agrees hA hB h⟩

/-- On finite inputs the IEEE routine's emulated results are finite or `±Inf`, never NaN. -/
theorem emulEntryF_ne_nan (W s : ℕ) (x y : List ℚ) : emulEntryF W s x y ≠ .nan :=
  roundF_ne_nan _ _

end Ozaki.TC
