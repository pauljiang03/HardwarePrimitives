import OzakiTC.LongDot

/-! # Two passes through `c`: full Tensor Core block FMAs of integer products, exactly

A Tensor Core block FMA of `b`-bit integer products is added exactly when `2b ≤ F`, and only the
final truncation to binary32 can lose bits, when the sum `S` exceeds `2^24`. TC-EFT's analysis of
how `c` takes part in alignment gives a way to recover those bits on the Tensor Core itself:

* pass 1 runs the block FMA from `c = +0` and returns `D1`, the binary32 truncation of `S`;
* pass 2 runs the same block FMA from `c = −D1`. While `|D1| < 2^(F+1)`, `c`'s exponent is at most
  `F`, so alignment is still exact and the accumulator holds `S − D1`, which is below `4` in
  magnitude and therefore returned exactly.

So `D1 + D2 = S` (`twoPass_exact`). The `F` of each variant grows with its FMA size, so a full block
FMA of `11`-bit products fits: `4 · 2^22 = 2^24` on V100 (`F = 23`), `8 · 2^22 = 2^25` on A100
(`F = 24`), `16 · 2^22 = 2^26` on H100 (`F = 25`). When the sum reaches `2^(F+1)` exactly, every
product is `±2^(2b)` and pass 2 aligns on the grid `2`, still exactly.

`tcMultiplier2` runs every block FMA of a dot product twice and adds the results exactly; it is
exact on `b`-bit vectors of every length whenever `K · 2^(2b) ≤ 2^(F+1)` (`tcMultiplier2_exactOn`),
so A100 and H100 can use their full block FMAs with `11`-bit slices (`a100F16_exactOn2`,
`h100F16_exactOn2`). -/

open TensorCore

namespace Ozaki.TC

/-! ## One block on a grid -/

/-- **A block of integer products and an integer `c`, on a grid `2^g`.** If every product and `c`
are multiples of `2^g`, `|c| < 2^(g+F+1)`, and the result is in range, the accumulator is exact and
the output is the binary32 truncation of `c + Σ aᵢbᵢ`. -/
theorem evalBlock_int_grid {p : Model} {b : ℕ} (hp : IntExact p b) {x : BlockInput p}
    (hlen : x.products.length = p.nfma)
    (hops : ∀ q ∈ x.products, IntWord p b q.1 ∧ IntWord p b q.2) (g : ℕ)
    (hpg : ∀ q ∈ x.products, ∃ k : ℤ, wordValue p q.1 * wordValue p q.2 = k * pow2 g)
    {zc : ℤ} (hc : value32 x.c = some (zc : ℚ)) (hcg : ∃ k : ℤ, (zc : ℚ) = k * pow2 g)
    (hcF : Rat.abs (zc : ℚ) < 2 ^ ((g : ℤ) + p.alignFracBits + 1))
    (hfin : absQ ((zc : ℚ) + wordProducts p x.products) ≤ maxFinite32) :
    ∃ t, evalBlock x = .ok t ∧
      t.output.value = signedRounded .truncate ((zc : ℚ) + wordProducts p x.products) := by
  obtain ⟨dc, hdc, hdcv⟩ := decode32_isSome_of_value32 hc
  have hpp := prepareProducts_eq p x.products (fun q hq => ⟨(hops q hq).1.1, (hops q hq).2.1⟩)
  have hprep : prepare x = some ⟨p, x.products.map fun q => (decodeD p q.1, decodeD p q.2), dc⟩ := by
    unfold prepare; rw [hdc, hpp]
  generalize hblk : (⟨p, x.products.map fun q => (decodeD p q.1, decodeD p q.2), dc⟩ :
    PreparedBlock) = blk at hprep
  have hev : evalBlock x = evalPrepared blk := by
    unfold evalBlock; rw [if_neg (by simp [hlen]), hprep]
  have hprods : blk.exactProducts = wordProducts p x.products := by
    rw [← hblk]; unfold PreparedBlock.exactProducts wordProducts wordValue
    rw [sumQ_eq, List.map_map]; rfl
  have hexact : blk.exactDot = zc + wordProducts p x.products := by
    unfold PreparedBlock.exactDot; rw [hprods, ← hblk]; simp only; rw [hdcv]
  -- every product term: exponent at most `F`, value a multiple of `2^g`
  have hprod : ∀ q ∈ x.products, (denormalizedMul (decodeD p q.1) (decodeD p q.2)).significand ≠ 0 →
      (denormalizedMul (decodeD p q.1) (decodeD p q.2)).exponent ≤ p.alignFracBits ∧
      ∃ k : ℤ, (denormalizedMul (decodeD p q.1) (decodeD p q.2)).value = k * pow2 g := by
    intro q hq hnz
    obtain ⟨⟨h1, za, hza, hza'⟩, ⟨h2, zb, hzb, hzb'⟩⟩ := hops q hq
    simp only [denormalizedMul] at hnz ⊢
    have hn1 : (decodeD p q.1).significand ≠ 0 := fun h => hnz (by rw [h, Int.zero_mul])
    have hn2 : (decodeD p q.2).significand ≠ 0 := fun h => hnz (by rw [h, Int.mul_zero])
    obtain ⟨d1, hd1⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨d2, hd2⟩ := Option.isSome_iff_exists.mp h2
    have hD1 : decodeD p q.1 = d1 := by simp [decodeD, hd1]
    have hD2 : decodeD p q.2 = d2 := by simp [decodeD, hd2]
    have hbnd : ∀ z : ℤ, z.natAbs ≤ 2 ^ b → Rat.abs (z : ℚ) < 2 ^ ((b : ℤ) + 1) := by
      intro z hz
      have := abs_intCast_le hz
      rw [← two_pow_natCast] at this
      have := two_pow_lt (show (b : ℤ) < b + 1 by omega)
      grind
    have e1 := decode_exp_le (f := p.input) (w := q.1) (d := d1) hd1 hp.emin
      (by rw [← hD1]; unfold wordValue at hza; rw [hza]; exact hbnd za hza') (by rw [← hD1]; exact hn1)
    have e2 := decode_exp_le (f := p.input) (w := q.2) (d := d2) hd2 hp.emin
      (by rw [← hD2]; unfold wordValue at hzb; rw [hzb]; exact hbnd zb hzb') (by rw [← hD2]; exact hn2)
    refine ⟨by rw [hD1, hD2]; have := hp.align; omega, ?_⟩
    obtain ⟨k, hk⟩ := hpg q hq
    refine ⟨k, ?_⟩
    have hv := denormalizedProduct_value (decodeD p q.1) (decodeD p q.2)
    simp only [denormalizedMul] at hv
    rw [hv]
    exact hk
  have hterms : blk.terms = ⟨dc.significand, dc.exponent, dc.mantissaBits⟩ ::
      x.products.map fun q => denormalizedMul (decodeD p q.1) (decodeD p q.2) := by
    rw [← hblk]; simp [PreparedBlock.terms, List.map_map, Function.comp_def]
  have hprof : blk.model = p := by rw [← hblk]
  have hacc : blk.accumulator = blk.exactDot := by
    apply accumulator_eq_exactDot_of_grid blk g
    · intro f hf; rw [hprof] at hf ⊢; have := hp.eAlignMin f hf; omega
    · intro t ht hnz
      rw [hterms] at ht
      rcases List.mem_cons.mp ht with rfl | ht
      · refine ⟨?_, ?_⟩
        · have := decode_exp_le (f := fp32) (w := x.c) (d := dc) hdc
            (E := (g : ℤ) + p.alignFracBits)
            (by have := hp.wide; show (1 : ℤ) - 127 ≤ _; omega)
            (by rw [hdcv]; exact hcF) hnz
          show dc.exponent ≤ (g : ℤ) + blk.model.alignFracBits
          rw [hprof]; exact this
        · obtain ⟨k, hk⟩ := hcg
          exact ⟨k, by change dc.value = _; rw [hdcv, hk]⟩
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
        rw [hprof]
        obtain ⟨h1, h2⟩ := hprod q hq hnz
        exact ⟨by omega, h2⟩
  have hr : absQ blk.accumulator ≤ maxFinite32 := by rw [hacc, hexact]; exact hfin
  obtain ⟨t, ht⟩ := evalPrepared_total blk hr
  refine ⟨t, by rw [hev]; exact ht, ?_⟩
  rw [evalPrepared_output_value ht, hacc, hexact]

/-! ## Truncation of an integer -/

/-- Truncation never increases the magnitude. -/
theorem abs_signedRounded_trunc_le (x : ℚ) : absQ (signedRounded .truncate x) ≤ absQ x := by
  have key : ∀ m : ℚ, 0 ≤ m →
      0 ≤ magnitudeRounded .truncate m ∧ magnitudeRounded .truncate m ≤ m := by
    intro m hm
    unfold magnitudeRounded roundedSignificand roundSignificand
    have hq := pow2_pos (normExp m - 23)
    generalize pow2 (normExp m - 23) = q at hq ⊢
    have h1 := Rat.floor_le (m / q)
    have hdiv : 0 ≤ m / q := div_nonneg_of_pos _ _ hm hq
    have h0 : (0 : ℤ) ≤ (m / q).floor := Rat.le_floor_iff.mpr (by simpa using hdiv)
    have h0' : (0 : ℚ) ≤ ((m / q).floor : ℚ) := by exact_mod_cast h0
    constructor
    · exact Rat.mul_nonneg h0' (Rat.le_of_lt hq)
    · have := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hq)
      rwa [Rat.div_mul_cancel (Rat.ne_of_gt hq)] at this
  obtain ⟨h0, hle⟩ := key (absQ x) (absQ_nonneg x)
  unfold signedRounded
  split
  · rw [absQ_neg, absQ_of_nonneg h0]; exact hle
  · rw [absQ_of_nonneg h0]; exact hle

/-- A binary32 value of magnitude at least `2^23` is an integer. -/
theorem finiteValue32_int {v : ℚ} (h : FiniteValue32 v) (hv : (2 : ℚ) ^ (23 : ℤ) ≤ Rat.abs v) :
    ∃ z : ℤ, v = z := by
  obtain ⟨k, e, _, _, hk, rfl⟩ := h
  by_cases he : 23 ≤ e
  · refine ⟨k * ((2 ^ (e - 23).toNat : ℕ) : ℤ), ?_⟩
    rw [pow2_eq, Rat.intCast_mul, Rat.intCast_natCast, ← two_pow_natCast]
    congr 2; omega
  · exfalso
    rw [pow2_eq, abs_mul_two_pow, abs_intCast] at hv
    have hk' : ((k.natAbs : ℕ) : ℚ) < 2 ^ (24 : ℤ) := by
      have e : (2 : ℚ) ^ (24 : ℤ) = ((2 ^ 24 : ℕ) : ℚ) := by rw [← two_pow_natCast]; rfl
      rw [e]; exact_mod_cast hk
    have hle : (2 : ℚ) ^ (e - 23) ≤ 2 ^ (-1 : ℤ) := two_pow_le (by omega)
    have hpos := two_pow_pos (e - 23)
    have h1 : ((k.natAbs : ℕ) : ℚ) * 2 ^ (e - 23) ≤ ((k.natAbs : ℕ) : ℚ) * 2 ^ (-1 : ℤ) :=
      Rat.mul_le_mul_of_nonneg_left hle Rat.natCast_nonneg
    have h2 : ((k.natAbs : ℕ) : ℚ) * 2 ^ (-1 : ℤ) < 2 ^ (24 : ℤ) * 2 ^ (-1 : ℤ) :=
      Rat.mul_lt_mul_of_pos_right hk' (two_pow_pos _)
    have h3 : (2 : ℚ) ^ (24 : ℤ) * 2 ^ (-1 : ℤ) = 2 ^ (23 : ℤ) := by
      rw [← two_pow_add]; rfl
    grind

/-- **Truncating an integer below `2^26`.** The binary32 truncation `D` of an integer `S` with
`|S| ≤ 2^26` is an integer with `|D| ≤ |S|` and `|S − D| < 4`. -/
theorem trunc_int {S : ℤ} (hS : S.natAbs ≤ 2 ^ 26)
    (hfin : FiniteValue32 (signedRounded .truncate (S : ℚ))) :
    ∃ D : ℤ, signedRounded .truncate (S : ℚ) = D ∧ D.natAbs ≤ S.natAbs ∧ (S - D).natAbs < 4 := by
  by_cases hsmall : S.natAbs ≤ 2 ^ 24
  · exact ⟨S, signedRounded_trunc_of_finite _ (int_finiteValue32 S hsmall), Nat.le_refl _, by simp⟩
  by_cases hmax : S.natAbs = 2 ^ 26
  · have h8 : S = (S / 8) * 8 := by omega
    have hf : FiniteValue32 (S : ℚ) := by
      have := grid_finiteValue32 (S / 8) 3 (by omega) (by omega) (by omega)
      have e8 : pow2 3 = ((8 : ℤ) : ℚ) := by rw [pow2_eq]; rfl
      rw [e8, ← Rat.intCast_mul, ← h8] at this
      exact this
    exact ⟨S, signedRounded_trunc_of_finite _ hf, Nat.le_refl _, by simp⟩
  -- `2^24 < |S| < 2^26`
  have hres := trunc_signed_residual (S : ℚ)
  have hpos : 0 < absQ (S : ℚ) := by
    rw [absQ_eq, abs_intCast]; exact_mod_cast (show 0 < S.natAbs by omega)
  have hlt : absQ (S : ℚ) < pow2 (25 + 1) := by
    rw [absQ_eq, abs_intCast, pow2_eq, show (25 : ℤ) + 1 = ((26 : ℕ) : ℤ) by rfl, two_pow_natCast]
    exact_mod_cast (show S.natAbs < 2 ^ 26 by omega)
  have hne := normExp_le_of_lt (absQ (S : ℚ)) hpos 25 hlt
  have hq : pow2 (normExp (absQ (S : ℚ)) - 23) ≤ pow2 2 := pow2_le_of_le (by omega)
  have h4 : pow2 2 = (4 : ℚ) := rfl
  have hdiff : absQ ((S : ℚ) - signedRounded .truncate (S : ℚ)) < 4 := by
    rw [← h4]; grind
  have habs := abs_signedRounded_trunc_le (S : ℚ)
  generalize hDdef : signedRounded .truncate (S : ℚ) = Dq at hfin hdiff habs
  rw [absQ_eq] at hdiff habs
  rw [absQ_eq, abs_intCast] at habs
  have hSbig : (16777216 : ℚ) < ((S.natAbs : ℕ) : ℚ) := by
    exact_mod_cast (show 16777216 < S.natAbs by omega)
  have hDbig : (2 : ℚ) ^ (23 : ℤ) ≤ Rat.abs Dq := by
    have h1 := abs_add_le ((S : ℚ) - Dq) Dq
    rw [show (S : ℚ) - Dq + Dq = (S : ℚ) by grind, abs_intCast] at h1
    have e23 : (2 : ℚ) ^ (23 : ℤ) = 8388608 := by decide +kernel
    grind
  obtain ⟨D, rfl⟩ := finiteValue32_int hfin hDbig
  refine ⟨D, rfl, ?_, ?_⟩
  · rw [abs_intCast] at habs; exact_mod_cast habs
  · rw [← Rat.intCast_sub, abs_intCast] at hdiff
    have : ((S - D).natAbs : ℚ) < ((4 : ℕ) : ℚ) := by simpa using hdiff
    exact_mod_cast this

/-! ## Two passes of one block FMA -/

/-- The binary32 word of a binary32 value (round to nearest returns it unchanged). -/
def word32 (v : ℚ) : F32 := (round32 .nearestEven v).getD 0

theorem value32_word32 {v : ℚ} (h : FiniteValue32 v) : value32 (word32 v) = some v := by
  obtain ⟨w, hw, hv⟩ := round32_exact_of_finite h
  simp [word32, hw, hv]

/-- **Two passes of one block FMA**: from `c = +0`, giving `D1`, then from `c = −D1`, giving `D2`;
the result is `D1 + D2`. -/
def twoPass (p : Model) (ps : List (p.Word × p.Word)) : Option ℚ :=
  match evalBlock (p := p) ⟨ps, 0⟩ with
  | .ok t1 =>
    match evalBlock (p := p) ⟨ps, word32 (-t1.output.value)⟩ with
    | .ok t2 => some (t1.output.value + t2.output.value)
    | .error _ => none
  | .error _ => none

/-- A product of two `b`-bit integer words has magnitude at most `2^b · 2^b`. -/
theorem abs_word_product_le {p : Model} {b : ℕ} {q : p.Word × p.Word}
    (h : IntWord p b q.1 ∧ IntWord p b q.2) :
    Rat.abs (wordValue p q.1 * wordValue p q.2) ≤ 2 ^ (b : ℤ) * 2 ^ (b : ℤ) := by
  obtain ⟨⟨_, za, hza, hza'⟩, ⟨_, zb, hzb, hzb'⟩⟩ := h
  rw [hza, hzb, two_pow_natCast]
  exact mul_le_mul_abs (abs_intCast_le hza') (abs_intCast_le hzb')

theorem wordDotAbs_le_length {p : Model} {b : ℕ} {ps : List (p.Word × p.Word)}
    (hops : ∀ q ∈ ps, IntWord p b q.1 ∧ IntWord p b q.2) :
    wordDotAbs p ps ≤ ps.length * (2 ^ (b : ℤ) * 2 ^ (b : ℤ)) :=
  sum_le_length_mul fun q hq => abs_word_product_le (hops q hq)

/-- If no term exceeds `M` and the terms total at least `n · M`, every term is `M`. -/
theorem eq_of_sum_ge {l : List α} {f : α → ℚ} {M : ℚ} (hle : ∀ a ∈ l, f a ≤ M)
    (hsum : (l.length : ℚ) * M ≤ (l.map f).sum) : ∀ a ∈ l, f a = M := by
  induction l with
  | nil => intro a ha; cases ha
  | cons a l ih =>
    have hrest := sum_le_length_mul (l := l) (f := f) (B := M) fun c hc => hle c (List.mem_cons_of_mem _ hc)
    have ha := hle a List.mem_cons_self
    simp only [List.length_cons, List.map_cons, List.sum_cons, natCast_succ] at hsum
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · grind
    · exact ih (fun d hd => hle d (List.mem_cons_of_mem _ hd)) (by grind) c hc

theorem maxFinite32_ge : (2 : ℚ) ^ (27 : ℤ) ≤ maxFinite32 := by decide +kernel

/-- **Two passes recover a full block FMA exactly.** For `b`-bit integer operands (`1 ≤ b`), on a
variant with `2b ≤ F ≤ 25` and `K · 2^(2b) ≤ 2^(F+1)`, the two passes succeed and
`D1 + D2 = Σ aᵢbᵢ`. -/
theorem twoPass_exact {p : Model} {b : ℕ} (hp : IntExact p b) (hb1 : 1 ≤ b)
    (hF : p.alignFracBits ≤ 25)
    (hK : (p.nfma : ℚ) * (2 ^ (b : ℤ) * 2 ^ (b : ℤ)) ≤ 2 ^ (p.alignFracBits + 1))
    {ps : List (p.Word × p.Word)} (hlen : ps.length = p.nfma)
    (hops : ∀ q ∈ ps, IntWord p b q.1 ∧ IntWord p b q.2) :
    twoPass p ps = some (wordProducts p ps) := by
  obtain ⟨S, hS, hSb⟩ := wordProducts_int ps hops
  have hbud := wordDotAbs_le_length hops
  rw [hlen] at hbud
  have hSF : Rat.abs (S : ℚ) ≤ 2 ^ (p.alignFracBits + 1) :=
    Rat.le_trans hSb (Rat.le_trans hbud hK)
  have hF26 : (2 : ℚ) ^ (p.alignFracBits + 1) ≤ 2 ^ (26 : ℤ) := two_pow_le (by omega)
  have hS26 : S.natAbs ≤ 2 ^ 26 := by
    have h1 : ((S.natAbs : ℕ) : ℚ) ≤ ((2 ^ 26 : ℕ) : ℚ) := by
      rw [← abs_intCast, ← two_pow_natCast]; exact Rat.le_trans hSF hF26
    exact_mod_cast h1
  have h27 := maxFinite32_ge
  have h2627 : (2 : ℚ) ^ (26 : ℤ) ≤ 2 ^ (27 : ℤ) := two_pow_le (by omega)
  have hpg0 : ∀ q ∈ ps, ∃ k : ℤ, wordValue p q.1 * wordValue p q.2 = k * pow2 0 := by
    intro q hq
    obtain ⟨⟨_, za, hza, _⟩, ⟨_, zb, hzb, _⟩⟩ := hops q hq
    exact ⟨za * zb, by rw [hza, hzb, pow2_zero, Rat.mul_one, Rat.intCast_mul]⟩
  have hFw := hp.wide
  -- pass 1, from `c = +0`
  obtain ⟨t1, ht1, hv1⟩ := evalBlock_int_grid hp (x := ⟨ps, 0⟩) hlen hops 0 hpg0 (zc := 0)
    (by show value32 (0 : F32) = some ((0 : ℤ) : ℚ); decide +kernel) ⟨0, by simp⟩
    (by rw [Rat.intCast_zero, abs_zero]; exact two_pow_pos _)
    (by
      show absQ (((0 : ℤ) : ℚ) + wordProducts p ps) ≤ maxFinite32
      rw [Rat.intCast_zero, Rat.zero_add, hS, absQ_eq]
      exact Rat.le_trans hSF (Rat.le_trans hF26 (Rat.le_trans h2627 h27)))
  change t1.output.value = signedRounded .truncate (((0 : ℤ) : ℚ) + wordProducts p ps) at hv1
  rw [Rat.intCast_zero, Rat.zero_add, hS] at hv1
  have hfin1 : FiniteValue32 t1.output.value := value32_finite _ _ (value32_output t1)
  obtain ⟨D, hD, hDS, hdiff⟩ := trunc_int hS26 (by rw [← hv1]; exact hfin1)
  rw [hD] at hv1
  have hc2 : value32 (word32 (-t1.output.value)) = some ((-D : ℤ) : ℚ) := by
    rw [hv1, Rat.intCast_neg]
    exact value32_word32 (finiteValue32_neg (by rw [← hv1]; exact hfin1))
  have hDabs : Rat.abs (D : ℚ) ≤ Rat.abs (S : ℚ) := by
    rw [abs_intCast, abs_intCast]; exact_mod_cast hDS
  have hSDsmall : (S - D).natAbs ≤ 2 ^ 24 := by omega
  -- pass 2, from `c = −D1`
  have hpass2 : ∃ t2, evalBlock (p := p) ⟨ps, word32 (-t1.output.value)⟩ = .ok t2 ∧
      t2.output.value = ((S - D : ℤ) : ℚ) := by
    have hfin2 : absQ (((-D : ℤ) : ℚ) + wordProducts p ps) ≤ maxFinite32 := by
      rw [hS, ← Rat.intCast_add, absQ_eq, abs_intCast]
      have : ((-D + S).natAbs : ℚ) ≤ ((2 ^ 24 : ℕ) : ℚ) := by
        exact_mod_cast (show (-D + S).natAbs ≤ 2 ^ 24 by omega)
      rw [← two_pow_natCast] at this
      have h2427 : (2 : ℚ) ^ ((24 : ℕ) : ℤ) ≤ 2 ^ (27 : ℤ) := two_pow_le (by omega)
      exact Rat.le_trans this (Rat.le_trans h2427 h27)
    have hout : ∀ t2 : BlockTrace,
        t2.output.value = signedRounded .truncate (((-D : ℤ) : ℚ) + wordProducts p ps) →
        t2.output.value = ((S - D : ℤ) : ℚ) := by
      intro t2 h
      rw [h, hS, ← Rat.intCast_add, show -D + S = S - D by omega]
      exact signedRounded_trunc_of_finite _ (int_finiteValue32 _ hSDsmall)
    by_cases hlt : Rat.abs (D : ℚ) < 2 ^ (p.alignFracBits + 1)
    · obtain ⟨t2, ht2, hv2⟩ := evalBlock_int_grid hp (x := ⟨ps, word32 (-t1.output.value)⟩) hlen
        hops 0 hpg0 hc2 ⟨-D, by simp [pow2_zero]⟩
        (by rw [Rat.intCast_neg, abs_neg]; simpa using hlt) hfin2
      exact ⟨t2, ht2, hout t2 hv2⟩
    · -- `|D1| = 2^(F+1)`: then `S = D1` and every product is `±2^(2b)`
      have heq : Rat.abs (D : ℚ) = 2 ^ (p.alignFracBits + 1) := by
        have := Rat.le_trans hDabs hSF; grind
      have hFnat : p.alignFracBits + 1 = (((p.alignFracBits + 1).toNat : ℕ) : ℤ) := by omega
      have hDnat : D.natAbs = 2 ^ (p.alignFracBits + 1).toNat := by
        have h1 : ((D.natAbs : ℕ) : ℚ) = ((2 ^ (p.alignFracBits + 1).toNat : ℕ) : ℚ) := by
          rw [← abs_intCast, heq, ← two_pow_natCast, ← hFnat]
        exact_mod_cast h1
      have hSnat : S.natAbs = D.natAbs := by
        have h1 : Rat.abs (S : ℚ) = 2 ^ (p.alignFracBits + 1) := by grind
        have h2 : ((S.natAbs : ℕ) : ℚ) = ((D.natAbs : ℕ) : ℚ) := by
          rw [← abs_intCast, ← abs_intCast, h1, heq]
        exact_mod_cast h2
      have hbig : 2 ^ 24 ≤ D.natAbs := by
        rw [hDnat]; exact Nat.pow_le_pow_right (by decide) (by omega)
      have hSD : S = D := by omega
      have hall : ∀ q ∈ ps, Rat.abs (wordValue p q.1 * wordValue p q.2) =
          2 ^ (b : ℤ) * 2 ^ (b : ℤ) := by
        apply eq_of_sum_ge (fun q hq => abs_word_product_le (hops q hq))
        rw [hlen]
        have : Rat.abs (S : ℚ) ≤ wordDotAbs p ps := hSb
        have h1 : Rat.abs (S : ℚ) = 2 ^ (p.alignFracBits + 1) := by grind
        unfold wordDotAbs at this
        grind
      have hpg1 : ∀ q ∈ ps, ∃ k : ℤ, wordValue p q.1 * wordValue p q.2 = k * pow2 1 := by
        intro q hq
        obtain ⟨⟨_, za, hza, _⟩, ⟨_, zb, hzb, _⟩⟩ := hops q hq
        have h1 := hall q hq
        rw [hza, hzb, ← Rat.intCast_mul, abs_intCast, two_pow_natCast, ← Rat.natCast_mul] at h1
        have h2 : (za * zb).natAbs = 2 ^ b * 2 ^ b := by exact_mod_cast h1
        have h3 : (za * zb).natAbs % 2 = 0 := by
          rw [h2]
          obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
          simp [Nat.pow_succ, Nat.mul_mod]
        refine ⟨za * zb / 2, ?_⟩
        rw [hza, hzb, pow2_one, ← Rat.intCast_mul]
        have h4 : za * zb = za * zb / 2 * 2 := by omega
        conv => lhs; rw [h4]
        rw [Rat.intCast_mul, Rat.intCast_ofNat]
      have hcg1 : ∃ k : ℤ, (((-D : ℤ)) : ℚ) = k * pow2 1 := by
        have h3 : D.natAbs % 2 = 0 := by
          rw [hDnat]
          obtain ⟨c, hc⟩ : ∃ c, (p.alignFracBits + 1).toNat = c + 1 :=
            ⟨_, (Nat.succ_pred_eq_of_pos (by omega)).symm⟩
          rw [hc]; simp [Nat.pow_succ]
        refine ⟨-D / 2, ?_⟩
        rw [pow2_one, ← Rat.intCast_ofNat, ← Rat.intCast_mul]
        congr 1; omega
      obtain ⟨t2, ht2, hv2⟩ := evalBlock_int_grid hp (x := ⟨ps, word32 (-t1.output.value)⟩) hlen
        hops 1 hpg1 hc2 hcg1
        (by
          rw [Rat.intCast_neg, abs_neg, heq]
          exact two_pow_lt (by omega)) hfin2
      exact ⟨t2, ht2, hout t2 hv2⟩
  obtain ⟨t2, ht2, hv2⟩ := hpass2
  unfold twoPass
  rw [ht1]
  simp only
  rw [ht2]
  simp only [Option.some.injEq]
  rw [hv1, hv2, hS, Rat.intCast_sub]
  grind

/-! ## The two-pass matrix multiplier -/

/-- **The two-pass Tensor Core matrix multiplier.** Encode the integers exactly, pad with zero words
to whole block FMAs of `K` products, run every block FMA twice (`twoPass`), and add their results
exactly. -/
def tcMultiplier2 (p : Model) : MatrixMultiplier := fun x y => do
  let ax ← x.mapM (encodeInt p.input)
  let ay ← y.mapM (encodeInt p.input)
  let vs ← (groupsOf p.nfma (0, 0) (List.zip ax ay)).mapM (twoPass p)
  pure vs.sum

theorem wordProducts_flatten (p : Model) :
    ∀ gs : List (List (p.Word × p.Word)),
      (gs.map (wordProducts p)).sum = wordProducts p gs.flatten
  | [] => by simp [wordProducts]
  | g :: gs => by
    rw [List.map_cons, List.sum_cons, List.flatten_cons, wordProducts_append,
      wordProducts_flatten p gs]

/-- **The two-pass matrix multiplier is exact on vectors of every length.** On a variant with
`2b ≤ F ≤ 25` and `K · 2^(2b) ≤ 2^(F+1)`, whose input format holds `b`-bit integers (`1 ≤ b`), it
returns `Σ xᵢyᵢ` exactly for `b`-bit vectors of any length, whatever their total. -/
theorem tcMultiplier2_exactOn {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (hb1 : 1 ≤ b) (hF : p.alignFracBits ≤ 25) (hK0 : 0 < p.nfma)
    (hK : (p.nfma : ℚ) * (2 ^ (b : ℤ) * 2 ^ (b : ℤ)) ≤ 2 ^ (p.alignFracBits + 1))
    (B : ℕ) : (tcMultiplier2 p).ExactOn b B := by
  intro x y hlen hx hy _
  have henc : ∀ z : ℤ, z.natAbs ≤ 2 ^ b → ∃ w, encodeInt p.input z = some w ∧
      (p.decode w).isSome ∧ wordValue p w = z := by
    intro z hz
    obtain ⟨w, hw, d, hd, hv⟩ := encodeInt_spec hh.wellFormed hh.emin hh.emax
      (Nat.le_trans hz (Nat.pow_le_pow_right (by decide) hh.bits))
    refine ⟨w, hw, by simp [Model.decode, hd], ?_⟩
    unfold wordValue decodeD Model.decode; rw [hd]; exact hv
  let E : ℤ → p.Word := fun z => (encodeInt p.input z).getD 0
  have hE : ∀ z : ℤ, z.natAbs ≤ 2 ^ b → encodeInt p.input z = some (E z) ∧
      IntWord p b (E z) ∧ wordValue p (E z) = z := by
    intro z hz
    obtain ⟨w, hw, hs, hv⟩ := henc z hz
    have : E z = w := by simp [E, hw]
    rw [this]; exact ⟨hw, ⟨hs, z, hv, hz⟩, hv⟩
  have hmx : x.mapM (encodeInt p.input) = some (x.map E) :=
    mapM_eq_some_map fun z hz => (hE z (hx z hz)).1
  have hmy : y.mapM (encodeInt p.input) = some (y.map E) :=
    mapM_eq_some_map fun z hz => (hE z (hy z hz)).1
  have hzip : List.zip (x.map E) (y.map E) = (List.zip x y).map (Prod.map E E) := List.zip_map
  have hz0 : IntWord p b (0 : p.Word) := by
    refine ⟨by rw [Model.decode, decode_zero_word p.input hh.wellFormed]; rfl, 0, ?_, by simp⟩
    unfold wordValue decodeD Model.decode; rw [decode_zero_word p.input hh.wellFormed]
    simp [Decoded.value]
  obtain ⟨hglen, hflat⟩ := groupsOf_spec hK0 ((0 : p.Word), (0 : p.Word))
    ((List.zip x y).map (Prod.map E E))
  generalize hpad : groupCount p.nfma ((List.zip x y).map (Prod.map E E)).length * p.nfma -
    ((List.zip x y).map (Prod.map E E)).length = n at hflat
  have hzw := wordDotAbs_replicate_zero p hh.wellFormed n
  have hvals : ∀ q ∈ List.zip x y, wordValue p (E q.1) * wordValue p (E q.2) = (q.1 : ℚ) * q.2 := by
    intro q hq
    have := List.of_mem_zip hq
    rw [(hE q.1 (hx _ this.1)).2.2, (hE q.2 (hy _ this.2)).2.2]
  have hprod : wordProducts p ((List.zip x y).map (Prod.map E E)) = (dotZ x y : ℚ) := by
    unfold wordProducts; rw [List.map_map, dotZ_eq_zip_sum]
    exact congrArg List.sum (List.map_congr_left hvals)
  have hblocks : ∀ g ∈ groupsOf p.nfma (0, 0) ((List.zip x y).map (Prod.map E E)),
      twoPass p g = some (wordProducts p g) := by
    intro g hg
    refine twoPass_exact hp hb1 hF hK (hglen g hg) fun q hq => ?_
    have hq' : q ∈ (groupsOf p.nfma (0, 0) ((List.zip x y).map (Prod.map E E))).flatten :=
      List.mem_flatten.mpr ⟨g, hg, hq⟩
    rw [hflat] at hq'
    rcases List.mem_append.mp hq' with hq' | hq'
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq'
      have := List.of_mem_zip hr
      exact ⟨(hE r.1 (hx _ this.1)).2.1, (hE r.2 (hy _ this.2)).2.1⟩
    · rw [(List.mem_replicate.mp hq').2]; exact ⟨hz0, hz0⟩
  unfold tcMultiplier2
  simp only [hmx, hmy, Option.bind_eq_bind, Option.bind_some, hzip]
  rw [mapM_eq_some_map hblocks]
  simp only [Option.bind_some, Option.pure_def]
  rw [wordProducts_flatten, hflat, wordProducts_append, hzw.2, hprod]
  congr 1; grind

/-! ## Full A100 and H100 block FMAs of `11`-bit slices -/

/-- **A100 fp16 with full block FMAs**: eight products of `11`-bit slices
(`8 · 2^22 = 2^25 = 2^(F+1)`), two passes each, exact for every length. -/
theorem a100F16_exactOn2 (B : ℕ) : (tcMultiplier2 ampereF16F32).ExactOn 11 B :=
  tcMultiplier2_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by decide +kernel) B

/-- **H100 fp16 with full block FMAs**: sixteen products of `11`-bit slices
(`16 · 2^22 = 2^26 = 2^(F+1)`), two passes each, exact for every length. -/
theorem h100F16_exactOn2 (B : ℕ) : (tcMultiplier2 hopperF16F32).ExactOn 11 B :=
  tcMultiplier2_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by decide +kernel) B

/-- **V100 fp16**: four products of `11`-bit slices (`4 · 2^22 = 2^24 = 2^(F+1)`). -/
theorem v100F16_exactOn2 (B : ℕ) : (tcMultiplier2 v100F16F32).ExactOn 11 B :=
  tcMultiplier2_exactOn ⟨by decide, by decide, (fun _ hf => by cases hf), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by decide +kernel) B

/-- **A100 bf16**: eight products of `8`-bit slices. -/
theorem a100BF16_exactOn2 (B : ℕ) : (tcMultiplier2 a100BF16F32).ExactOn 8 B :=
  tcMultiplier2_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by decide +kernel) B

/-- **H100 bf16**: sixteen products of `8`-bit slices. -/
theorem h100BF16_exactOn2 (B : ℕ) : (tcMultiplier2 hopperBF16F32).ExactOn 8 B :=
  tcMultiplier2_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by decide +kernel) B

/-- **A100 tf32**: four products of `11`-bit slices. -/
theorem a100TF32_exactOn2 (B : ℕ) : (tcMultiplier2 a100TF32F32).ExactOn 11 B :=
  tcMultiplier2_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by decide +kernel) B

/-- **H100 tf32 (wmma)**: four products of `11`-bit slices. -/
theorem h100TF32Wmma_exactOn2 (B : ℕ) : (tcMultiplier2 hopperTF32WmmaF32).ExactOn 11 B :=
  tcMultiplier2_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by decide +kernel) B

/-- **H100 tf32 (mma)**: eight products of `11`-bit slices (`8 · 2^22 = 2^25 ≤ 2^26`). -/
theorem h100TF32Mma_exactOn2 (B : ℕ) : (tcMultiplier2 hopperTF32MmaF32).ExactOn 11 B :=
  tcMultiplier2_exactOn ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide) (by decide) (by decide)
    (by decide +kernel) B

/-- Ozaki-I on the two-pass matrix multiplier, binary32 recombination. -/
def tcOzaki1TP (p : Model) (b s : ℕ) (x y : List ℚ) : Option ℚ :=
  ozaki1 (tcMultiplier2 p) add32 b s x y

/-- **Ozaki-I on full A100 or H100 block FMAs, for every inner dimension**: the bound of
`tcOzaki1_error` with no condition on `k`, on any variant where the two-pass matrix multiplier is
exact. -/
theorem tcOzaki1TP_error {p : Model} {b : ℕ} (hmult : ∀ B, (tcMultiplier2 p).ExactOn b B) (s : ℕ)
    {x y : List ℚ} (hlen : x.length = y.length) {v : ℚ} (hv : tcOzaki1TP p b s x y = some v) :
    Rat.abs (v - dot x y) ≤
      ((1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length - 1) *
          ((trianglePairs s).length * (x.length * 2 ^ (splitExp b x + splitExp b y))) +
        (trianglePairs s).length * (1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length *
          2 ^ (-150 : ℤ) +
        ((s + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp b x + splitExp b y - s * (b + 1)) :=
  ozaki1_error (hmult _) (Rat.le_of_lt (two_pow_pos _)) (Rat.le_of_lt (two_pow_pos _))
    add32_within hlen (Nat.le_refl _) hv

theorem a100_ozaki1TP_error (s : ℕ) {x y : List ℚ} (hlen : x.length = y.length) {v : ℚ}
    (hv : tcOzaki1TP ampereF16F32 11 s x y = some v) :
    Rat.abs (v - dot x y) ≤
      ((1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length - 1) *
          ((trianglePairs s).length * (x.length * 2 ^ (splitExp 11 x + splitExp 11 y))) +
        (trianglePairs s).length * (1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length *
          2 ^ (-150 : ℤ) +
        ((s + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp 11 x + splitExp 11 y - s * (11 + 1)) :=
  tcOzaki1TP_error a100F16_exactOn2 s hlen hv

theorem h100_ozaki1TP_error (s : ℕ) {x y : List ℚ} (hlen : x.length = y.length) {v : ℚ}
    (hv : tcOzaki1TP hopperF16F32 11 s x y = some v) :
    Rat.abs (v - dot x y) ≤
      ((1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length - 1) *
          ((trianglePairs s).length * (x.length * 2 ^ (splitExp 11 x + splitExp 11 y))) +
        (trianglePairs s).length * (1 + 2 ^ (-24 : ℤ)) ^ (trianglePairs s).length *
          2 ^ (-150 : ℤ) +
        ((s + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp 11 x + splitExp 11 y - s * (11 + 1)) :=
  tcOzaki1TP_error h100F16_exactOn2 s hlen hv

/-! ## Examples -/

/-- A100: seven products `2047²` (sum `29331463`, above `2^24`). One pass from `c = +0` truncates
to `29331462`; two passes recover the sum. -/
example : (evalBlock (p := ampereF16F32) ⟨List.replicate 7 (0x67FF, 0x67FF) ++ [(0, 0)], 0⟩).map
    (fun t => t.output.value) = .ok 29331462 := by decide +kernel

example : twoPass ampereF16F32 (List.replicate 7 (0x67FF, 0x67FF) ++ [(0, 0)]) = some 29331463 := by
  decide +kernel

/-- H100: fifteen products `2047²` and one `2047 · 2046` (sum `67041297`). One pass truncates to
`67041296`; two passes recover the sum. -/
example : (evalBlock (p := hopperF16F32)
    ⟨List.replicate 15 (0x67FF, 0x67FF) ++ [(0x67FF, 0x67FE)], 0⟩).map
    (fun t => t.output.value) = .ok 67041296 := by decide +kernel

example : twoPass hopperF16F32 (List.replicate 15 (0x67FF, 0x67FF) ++ [(0x67FF, 0x67FE)]) =
    some 67041297 := by decide +kernel

/-- The two-pass matrix multiplier on a dot product of twenty `2047²` terms on H100: two block FMAs
of sixteen (the second padded), each run twice. -/
example : tcMultiplier2 hopperF16F32 (List.replicate 20 2047) (List.replicate 20 2047) =
    some (20 * 2047 * 2047) := by decide +kernel

end Ozaki.TC
