import MatrixCore.MC.Contract

/-! # Inner products of the input vectors

The blocks of an inner product cover the input vectors: their exact products add up to
`Σ_ℓ a_ℓ b_ℓ` over the whole vectors, the zero padding contributing nothing
(`runBlocks_products`). The loss accounting and the error bounds of an inner product are
therefore statements about the exact inner product `exactDot P a b c = c + Σ_ℓ a_ℓ b_ℓ`. -/

namespace MatrixCore

/-- The value of an operand word; `0` for an infinity or NaN. -/
def InputFormat.wordValue (i : InputFormat) (w : i.Word) : ℚ :=
  ((i.read w).toFinite.map Unpacked.value).getD 0

/-- The exact `Σ_ℓ a_ℓ b_ℓ` of two operand vectors. -/
def exactProducts (P : Model) (a : List P.a.Word) (b : List P.b.Word) : ℚ :=
  sumQ (List.zipWith (fun x y => P.a.wordValue x * P.b.wordValue y) a b)

/-- The exact inner product `c + Σ_ℓ a_ℓ b_ℓ` of Eq. (1). -/
def exactDot (P : Model) (a : List P.a.Word) (b : List P.b.Word) (c : F32) : ℚ :=
  wordValue c + exactProducts P a b

/-! ## One block -/

theorem decodeNat_zero {f : Format} {u : Unpacked} (h : f.decodeNat 0 = .finite u) : u.m = 0 := by
  unfold Format.decodeNat at h
  dsimp only at h
  simp only [Nat.zero_mod, Nat.zero_div] at h
  unfold Format.unpackFields at h
  split at h
  · split at h
    · split at h <;> simp at h
    · simp at h; rw [← h]
  · split at h
    · simp at h
    · simp at h; rw [← h]

/-- A zero word is worth zero (or does not decode to a finite value). -/
theorem InputFormat.wordValue_zero (i : InputFormat) : i.wordValue 0 = 0 := by
  unfold InputFormat.wordValue
  cases i with
  | packed f =>
    change ((f.decodeNat 0).toFinite.map Unpacked.value).getD 0 = 0
    cases hd : f.decodeNat 0 with
    | finite u =>
      simp only [Datum.toFinite, Option.map_some, Option.getD_some]
      exact (Unpacked.value_eq_zero_iff u).mpr (decodeNat_zero hd)
    | infinity s => rfl
    | nan => rfl
  | xf32 => decide +kernel

theorem mapM_products {P : Model} : ∀ (xa : List P.a.Word) (xb : List P.b.Word)
    (A B : List Unpacked), xa.mapM (fun w => (P.a.read w).toFinite) = some A →
    xb.mapM (fun w => (P.b.read w).toFinite) = some B →
    sumQ (List.zipWith (fun u v => u.value * v.value) A B) = exactProducts P xa xb
  | [], xb, A, B, ha, _ => by
    simp at ha; subst ha; simp [exactProducts, sumQ]
  | _ :: _, [], A, B, _, hb => by
    simp at hb; subst hb; cases A <;> simp [exactProducts, sumQ]
  | x :: xs, y :: ys, A, B, ha, hb => by
    simp only [List.mapM_cons] at ha hb
    cases hx : (P.a.read x).toFinite with
    | none => rw [hx] at ha; simp at ha
    | some u =>
      cases hxs : xs.mapM (fun w => (P.a.read w).toFinite) with
      | none => rw [hx, hxs] at ha; simp at ha
      | some us =>
        cases hy : (P.b.read y).toFinite with
        | none => rw [hy] at hb; simp at hb
        | some v =>
          cases hys : ys.mapM (fun w => (P.b.read w).toFinite) with
          | none => rw [hy, hys] at hb; simp at hb
          | some vs =>
            rw [hx, hxs] at ha; rw [hy, hys] at hb
            simp at ha hb; subst ha; subst hb
            have ih := mapM_products xs ys us vs hxs hys
            unfold exactProducts at ih ⊢
            simp only [List.zipWith_cons_cons, sumQ, ih, InputFormat.wordValue, hx, hy,
              Option.map_some, Option.getD_some]

/-- The exact products of an accepted block are `Σ a_ℓ b_ℓ` of its operand words. -/
theorem evalBlock_products {P : Model} {xa : List P.a.Word} {xb : List P.b.Word} {c : F32}
    {t : BlockTrace P} (h : evalBlock (P := P) ⟨xa, xb, c⟩ = .ok t) :
    t.prepared.products = exactProducts P xa xb := by
  have hp := (evalBlock_ok h).2.2.1
  unfold prepare at hp
  cases hA : xa.mapM fun w => (P.a.read w).toFinite <;> rw [hA] at hp <;> simp at hp
  cases hB : xb.mapM fun w => (P.b.read w).toFinite <;> rw [hB] at hp <;> simp at hp
  cases hC : (fp32.decode c).toFinite <;> rw [hC] at hp <;> simp at hp
  rename_i A B _
  rw [← hp]
  unfold Prepared.products Prepared.p
  rw [← mapM_products xa xb A B hA hB]
  congr 1
  clear hA hB hp
  induction A generalizing B with
  | nil => rfl
  | cons u us ih =>
    cases B with
    | nil => rfl
    | cons v vs => simp only [List.zipWith_cons_cons, List.map_cons, Unpacked.value_mul, ih]

/-! ## The blocks of an inner product -/

theorem runBlocks_products_blocks {P : Model} {c : F32}
    {bs : List (List P.a.Word × List P.b.Word)} {ts : List (BlockTrace P)}
    (h : runBlocks P c bs = .ok ts) :
    sumQ (ts.map fun t => t.prepared.products) =
      sumQ (bs.map fun ab => exactProducts P ab.1 ab.2) := by
  induction bs generalizing c ts with
  | nil => simp [runBlocks] at h; subst h; rfl
  | cons ab rest ih =>
    obtain ⟨t, ts', he, hr, rfl⟩ := runBlocks_cons h
    simp only [List.map_cons, sumQ, evalBlock_products he, ih hr]

theorem sum_chunks (f : α → β → ℚ) (n : ℕ) (hn : 0 < n) : ∀ (k : ℕ) (xs : List α) (ys : List β),
    xs.length = ys.length → xs.length ≤ k →
    sumQ ((List.zip (chunks n k xs) (chunks n k ys)).map fun p => sumQ (List.zipWith f p.1 p.2)) =
      sumQ (List.zipWith f xs ys)
  | 0, xs, ys, hl, hk => by
    have : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    have : ys = [] := List.eq_nil_of_length_eq_zero (by simp at hl; omega)
    subst this
    rfl
  | k + 1, [], ys, hl, _ => by
    have : ys = [] := List.eq_nil_of_length_eq_zero (by simp at hl; omega)
    subst this; rfl
  | k + 1, x :: xs, [], hl, _ => by simp at hl
  | k + 1, x :: xs, y :: ys, hl, hk => by
    simp only [chunks, List.zip_cons_cons, List.map_cons, sumQ]
    have hl' : (x :: xs).length = (y :: ys).length := hl
    rw [sum_chunks f n hn k _ _ (by simp [hl']) (by simp at hk ⊢; omega)]
    conv => rhs; rw [← List.take_append_drop n (x :: xs), ← List.take_append_drop n (y :: ys)]
    rw [List.zipWith_append (by simp [hl']), sumQ_append]

theorem padToBlocks_length (n : ℕ) (xs : List (BitVec w)) :
    (padToBlocks n xs).length = xs.length + (n - xs.length % n) % n := by
  simp [padToBlocks]

/-- The blocks' exact products add up to `Σ_ℓ a_ℓ b_ℓ` of the whole vectors. -/
theorem blocks_products (P : Model) (hn : 0 < P.nfma) {a : List P.a.Word} {b : List P.b.Word}
    (hlen : a.length = b.length) :
    sumQ ((blocks P a b).map fun ab => exactProducts P ab.1 ab.2) = exactProducts P a b := by
  unfold blocks
  dsimp only
  have hpl : (padToBlocks P.nfma a).length = (padToBlocks P.nfma b).length := by
    rw [padToBlocks_length, padToBlocks_length, hlen]
  rw [← hpl]
  have := sum_chunks (fun x y => P.a.wordValue x * P.b.wordValue y) P.nfma hn
    (padToBlocks P.nfma a).length (padToBlocks P.nfma a) (padToBlocks P.nfma b) hpl (Nat.le_refl _)
  unfold exactProducts
  rw [this]
  unfold padToBlocks
  rw [List.zipWith_append hlen, sumQ_append, hlen, List.zipWith_replicate,
    InputFormat.wordValue_zero, InputFormat.wordValue_zero]
  have hz : ∀ m : ℕ, sumQ (List.replicate m ((0 : ℚ) * 0)) = 0 := by
    intro m; induction m with
    | zero => rfl
    | succ m ih => simp only [List.replicate_succ, sumQ, ih]; decide +kernel
  rw [hz]; grind

/-- **Exact inner product.** The blocks of an accepted inner product have exact products
`Σ_ℓ a_ℓ b_ℓ` over the whole vectors. -/
theorem runBlocks_products (P : Model) (hn : 0 < P.nfma) {a : List P.a.Word}
    {b : List P.b.Word} {c : F32} {ts : List (BlockTrace P)} (hlen : a.length = b.length)
    (h : runBlocks P c (blocks P a b) = .ok ts) :
    sumQ (ts.map fun t => t.prepared.products) = exactProducts P a b := by
  rw [runBlocks_products_blocks h, blocks_products P hn hlen]

/-- The exact inner product equals the output plus the blocks' residuals. -/
theorem dotBits_exact_ledger (P : Model) (hn : 0 < P.nfma) {a : List P.a.Word}
    {b : List P.b.Word} {c d : F32} (hlen : a.length = b.length) (h : dotBits P a b c = .ok d) :
    ∃ ts, runBlocks P c (blocks P a b) = .ok ts ∧ lastOutput c ts = d ∧
      exactDot P a b c = wordValue d + sumQ (ts.map BlockTrace.residual) := by
  obtain ⟨ts, hr, hd, _, _, hl⟩ := dotBits_residual_ledger P hlen h
  refine ⟨ts, hr, hd, ?_⟩
  unfold exactDot
  rw [← runBlocks_products P hn hlen hr, hl]

/-- **Error of an inner product.** If every accepted block's residual is bounded by `B`, the
output is within the sum of the blocks' bounds of the exact `c + Σ_ℓ a_ℓ b_ℓ`. -/
theorem dotBits_exact_error (P : Model) (hn : 0 < P.nfma) {B : BlockTrace P → ℚ}
    (hB : ∀ x t, evalBlock x = .ok t → absQ t.residual ≤ B t)
    {a : List P.a.Word} {b : List P.b.Word} {c d : F32}
    (hlen : a.length = b.length) (h : dotBits P a b c = .ok d) :
    ∃ ts, runBlocks P c (blocks P a b) = .ok ts ∧ lastOutput c ts = d ∧
      absQ (exactDot P a b c - wordValue d) ≤ sumQ (ts.map B) := by
  obtain ⟨ts, hr, hd, he⟩ := dotBits_error_bound P hB hlen h
  refine ⟨ts, hr, hd, ?_⟩
  unfold exactDot
  rw [← runBlocks_products P hn hlen hr]
  exact he

end MatrixCore
