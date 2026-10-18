import MatrixCore.MC.Monotonicity
import MatrixCore.MC.InnerProduct

/-! # Monotonicity in the products

SFMA and CDNA 1 are monotone in the products; CDNA 2 and CDNA 3 are not, on every input format
of the paper. -/

namespace MatrixCore

/-- The exact products `a_ℓ b_ℓ` of a block's operand words. -/
def productValues (P : Model) (a : List P.a.Word) (b : List P.b.Word) : List ℚ :=
  List.zipWith (fun x y => P.a.wordValue x * P.b.wordValue y) a b

/-- `x'` has the same number of products as `x`, and each is at least as large. -/
def productsLE {P : Model} (x x' : BlockInput P) : Bool :=
  (productValues P x.a x.b).length == (productValues P x'.a x'.b).length &&
    ((productValues P x.a x.b).zip (productValues P x'.a x'.b)).all fun q => decide (q.1 ≤ q.2)

theorem sumQ_le_of_all : ∀ (l l' : List ℚ), l.length = l'.length →
    (l.zip l').all (fun q => decide (q.1 ≤ q.2)) = true → sumQ l ≤ sumQ l'
  | [], [], _, _ => Rat.le_refl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | x :: xs, y :: ys, hl, h => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have := sumQ_le_of_all xs ys (by simpa using hl) h.2
    simp only [sumQ]; grind

theorem productsLE_exactProducts {P : Model} {x x' : BlockInput P} (h : productsLE x x' = true) :
    exactProducts P x.a x.b ≤ exactProducts P x'.a x'.b := by
  unfold productsLE at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact sumQ_le_of_all _ _ h.1 h.2

/-! ## SFMA and CDNA 1 -/

/-- SFMA and CDNA 1: the output depends only on the exact `Σ a_ℓ b_ℓ + c`, monotonically. -/
theorem correctRounding_exact_monotone {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true)
    {x x' : BlockInput P} {t t' : BlockTrace P} (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t')
    (he : exactDot P x.a x.b x.c ≤ exactDot P x'.a x'.b x'.c) : wordValue t.d ≤ wordValue t'.d := by
  have e1 := (correctRounding_nearestEven hacc hov hs h).1
  have e2 := (correctRounding_nearestEven hacc hov hs h').1
  have hx : t.prepared.exact = exactDot P x.a x.b x.c := by
    have hp := (evalBlock_ok h).2.2.1
    have := evalBlock_products (xa := x.a) (xb := x.b) (c := x.c) h
    unfold exactDot Prepared.exact
    rw [wordValue_of_decode (prepare_c hp), ← this, Prepared.products]; grind
  have hx' : t'.prepared.exact = exactDot P x'.a x'.b x'.c := by
    have hp := (evalBlock_ok h').2.2.1
    have := evalBlock_products (xa := x'.a) (xb := x'.b) (c := x'.c) h'
    unfold exactDot Prepared.exact
    rw [wordValue_of_decode (prepare_c hp), ← this, Prepared.products]; grind
  exact fl32_mono (evalBlock_ok h).2.2.2.2 (evalBlock_ok h').2.2.2.2 (by rw [e1, e2, hx, hx']; exact he)

/-- SFMA and CDNA 1 are monotone in the products and in `c`. -/
theorem correctRounding_product_monotone {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true)
    {x x' : BlockInput P} {t t' : BlockTrace P} (h : evalBlock x = .ok t) (h' : evalBlock x' = .ok t')
    (hp : productsLE x x' = true) (hc : wordValue x.c ≤ wordValue x'.c) :
    wordValue t.d ≤ wordValue t'.d := by
  apply correctRounding_exact_monotone hacc hov hs h h'
  unfold exactDot
  have := productsLE_exactProducts hp
  grind

/-- Blocks pairwise at least as large in their exact products. -/
def BlocksLE (P : Model) :
    List (List P.a.Word × List P.b.Word) → List (List P.a.Word × List P.b.Word) → Prop
  | [], [] => True
  | ab :: r, ab' :: r' => exactProducts P ab.1 ab.2 ≤ exactProducts P ab'.1 ab'.2 ∧ BlocksLE P r r'
  | _, _ => False

/-- SFMA and CDNA 1 inner products are monotone in the blockwise exact products and in `c`. -/
theorem runBlocks_correctRounding_monotone {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true) :
    ∀ (bs bs' : List (List P.a.Word × List P.b.Word)) (c c' : F32) (ts ts' : List (BlockTrace P)),
      BlocksLE P bs bs' → runBlocks P c bs = .ok ts → runBlocks P c' bs' = .ok ts' →
      wordValue c ≤ wordValue c' → wordValue (lastOutput c ts) ≤ wordValue (lastOutput c' ts')
  | [], [], c, c', ts, ts', _, h, h', hc => by
    simp [runBlocks] at h h'; subst h; subst h'; exact hc
  | ab :: r, ab' :: r', c, c', ts, ts', hle, h, h', hc => by
    obtain ⟨t, us, he, hr, rfl⟩ := runBlocks_cons h
    obtain ⟨t', us', he', hr', rfl⟩ := runBlocks_cons h'
    have hd := correctRounding_exact_monotone hacc hov hs he he' (by
      unfold exactDot; have := hle.1; simp only; grind)
    exact runBlocks_correctRounding_monotone hacc hov hs r r' t.d t'.d us us' hle.2 hr hr' hd
  | [], _ :: _, _, _, _, _, hle, _, _, _ => absurd hle id
  | _ :: _, [], _, _, _, _, hle, _, _, _ => absurd hle id

/-! ## CDNA 2 and CDNA 3: non-monotonicity -/

/-- Every product of `x'` is at least that of `x`, `c` is the same, and the output is smaller. -/
def ProductNonmonotone {P : Model} (x x' : BlockInput P) : Prop :=
  productsLE x x' = true ∧ x.c = x'.c ∧
    ∃ d d', blockBits x = .ok d ∧ blockBits x' = .ok d' ∧ wordValue d' < wordValue d

/-- SFMA and CDNA 1 have no non-monotone pair. -/
theorem correctRounding_not_nonmonotone {P : Model} (hacc : P.accumulation = .correctRounding)
    (hov : P.productOverflow = false) (hs : P.subnormals = true) (x x' : BlockInput P) :
    ¬ ProductNonmonotone x x' := by
  rintro ⟨hp, hc, d, d', hd, hd', hlt⟩
  unfold blockBits at hd hd'
  cases h : evalBlock x with
  | error e => rw [h] at hd; simp [Except.map] at hd
  | ok t =>
    cases h' : evalBlock x' with
    | error e => rw [h'] at hd'; simp [Except.map] at hd'
    | ok t' =>
      rw [h] at hd; rw [h'] at hd'
      simp only [Except.map, Except.ok.injEq] at hd hd'
      have := correctRounding_product_monotone hacc hov hs h h' hp (by rw [hc]; exact Rat.le_refl)
      rw [hd, hd'] at this
      exact Rat.not_le.mpr hlt this

theorem sfmaF32_not_nonmonotone (x x' : BlockInput sfmaF32) :
    ¬ ProductNonmonotone x x' := correctRounding_not_nonmonotone rfl rfl rfl x x'
theorem cdna1F16_not_nonmonotone (x x' : BlockInput cdna1F16) : ¬ ProductNonmonotone x x' :=
  correctRounding_not_nonmonotone rfl rfl rfl x x'
theorem cdna1BF16_not_nonmonotone (x x' : BlockInput cdna1BF16) : ¬ ProductNonmonotone x x' :=
  correctRounding_not_nonmonotone rfl rfl rfl x x'

/-- CDNA 2 FP16: `p₁` rises from a product with a flushed subnormal operand to `−2^-11`. -/
theorem cdna2F16_nonmonotonic :
    ProductNonmonotone (P := cdna2F16) ⟨[0x0200, 0, 0, 0], [0xD200, 0, 0, 0], 0⟩
      ⟨[0x0400, 0, 0, 0], [0xC800, 0, 0, 0], 0⟩ :=
  ⟨by decide +kernel, rfl, 0x00000000, 0xBA000000, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- CDNA 2 BF16: `p₁` rises from `−2^-27` (subnormal operand, flushed) to `−2^-28`. -/
theorem cdna2BF16_nonmonotonic :
    ProductNonmonotone (P := cdna2BF16) ⟨[0x0040, 0], [0xF180, 0], 0⟩ ⟨[0x0080, 0], [0xF080, 0], 0⟩ :=
  ⟨by decide +kernel, rfl, 0x00000000, 0xB1800000, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem cdna2BF16_1k_nonmonotonic :
    ProductNonmonotone (P := cdna2BF16_1k) ⟨[0x0040, 0, 0, 0], [0xF180, 0, 0, 0], 0⟩
      ⟨[0x0080, 0, 0, 0], [0xF080, 0, 0, 0], 0⟩ :=
  ⟨by decide +kernel, rfl, 0x00000000, 0xB1800000, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- CDNA 3 FP16: `p₁` rises from `2^-9 − 2^-29` to `2^-9`, and `e_max` from `−10` to `1`. -/
theorem cdna3F16_nonmonotonic :
    ProductNonmonotone (P := cdna3F16)
      ⟨0x3C01 :: List.replicate 7 0x0C00, 0x17FE :: List.replicate 7 0x0C00, 0⟩
      ⟨0x0001 :: List.replicate 7 0x0C00, 0x7800 :: List.replicate 7 0x0C00, 0⟩ :=
  ⟨by decide +kernel, rfl, 0x3B0006F8, 0x3B000000, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- CDNA 3 BF16: `p₁` rises from `2^-6 − 2^-21` to `2^-6` with `e_p = 1`. -/
theorem cdna3BF16_nonmonotonic :
    ProductNonmonotone (P := cdna3BF16)
      ⟨0x3FD9 :: List.replicate 7 0x3980, 0x3C17 :: List.replicate 7 0x39FE, 0⟩
      ⟨0x0001 :: List.replicate 7 0x3980, 0x7F00 :: List.replicate 7 0x39FE, 0⟩ :=
  ⟨by decide +kernel, rfl, 0x3C8000BC, 0x3C800000, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- CDNA 3 XF32: the FP16 construction in `tf19`. -/
theorem cdna3XF32_nonmonotonic :
    ProductNonmonotone (P := cdna3XF32)
      ⟨0x3F802000 :: List.replicate 3 0x39800000, 0x3AFFC000 :: List.replicate 3 0x39800000, 0⟩
      ⟨0x00002000 :: List.replicate 3 0x39800000, 0x7F000000 :: List.replicate 3 0x39800000, 0⟩ :=
  ⟨by decide +kernel, rfl, 0x3B0002F8, 0x3B000000, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- CDNA 3 FP8 E4M3: equal products `1.875·2^-3 · 1` and `2^-10 · 240`; `c = 2^-25` is lost. -/
theorem cdna3E4M3_nonmonotonic :
    ProductNonmonotone (P := cdna3FP8 e4m3fnuz e4m3fnuz)
      ⟨0x2F :: List.replicate 15 0, 0x40 :: List.replicate 15 0, 0x33000000⟩
      ⟨0x01 :: List.replicate 15 0, 0x7F :: List.replicate 15 0, 0x33000000⟩ :=
  ⟨by decide +kernel, rfl, 0x3E700002, 0x3E700000, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- CDNA 3 FP8 E5M2: equal products `1.75·2^-2 · 1` and `2^-17 · 57344`; `c = 2^-25` is lost. -/
theorem cdna3E5M2_nonmonotonic :
    ProductNonmonotone (P := cdna3FP8 e5m2fnuz e5m2fnuz)
      ⟨0x3B :: List.replicate 15 0, 0x40 :: List.replicate 15 0, 0x33000000⟩
      ⟨0x01 :: List.replicate 15 0, 0x7F :: List.replicate 15 0, 0x33000000⟩ :=
  ⟨by decide +kernel, rfl, 0x3EE00001, 0x3EE00000, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- CDNA 3 FP16, normal operands: equal products `1.5 · 1.5` and `2.25 · 1` give different outputs. -/
theorem cdna3F16_products_not_determined :
    productValues cdna3F16 (0x3E00 :: List.replicate 7 0x0C00) (0x3E00 :: List.replicate 7 0x0C00) =
      productValues cdna3F16 (0x4080 :: List.replicate 7 0x0C00) (0x3C00 :: List.replicate 7 0x0C00) ∧
    blockBits (P := cdna3F16) ⟨0x3E00 :: List.replicate 7 0x0C00, 0x3E00 :: List.replicate 7 0x0C00, 0⟩ =
      .ok 0x40100002 ∧
    blockBits (P := cdna3F16) ⟨0x4080 :: List.replicate 7 0x0C00, 0x3C00 :: List.replicate 7 0x0C00, 0⟩ =
      .ok 0x40100000 := by
  decide +kernel

end MatrixCore
