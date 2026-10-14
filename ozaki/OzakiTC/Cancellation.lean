import OzakiTC.Models
import OzakiTC.Limits

/-! # Exact blocks with cancellation

`evalBlock_int` asks the magnitudes to total at most `2^24`: `|c| + Σ|aᵢbᵢ| ≤ 2^24`. That is a
sufficient condition, chosen so that it can be checked before the block runs. The Tensor Core model
needs less. A block aligns every term to the largest exponent and keeps `F` bits below it, adds the
aligned terms exactly, and truncates the sum once to binary32. For integer operands:

* alignment keeps every integer bit when every term has exponent at most `F`: every product of
  `b`-bit integers does (`2b ≤ F`), and `c` does when `|c| < 2^(F+1)`;
* the final truncation returns the exact sum when that sum is a binary32 value, for instance an
  integer of magnitude at most `2^24`.

So a block is exact whenever `|c| < 2^(F+1)` and the exact sum `c + Σ aᵢbᵢ` is a binary32 value,
whatever the magnitudes of the products (`evalBlock_cancel`); cancellation inside a block is free.
The condition on the sum is also necessary: a block's output is a binary32 value
(`evalBlock_exact_needs_binary32`). A chain of blocks is exact when every running value it passes
on stays below `2^24` (`runBlocks_cancel`), and so is the matrix multiplier when the dot products of
the prefixes at its block boundaries do (`tcMultiplier_cancel`).

Witnesses where the old condition fails and the new one holds: on A100, four products `2^22` and four
`−2^22` (total magnitude `2^25`) return `0`, and four products `2047²` and three `−2047²` return
`2047²` (`a100_cancel_zero`, `a100_cancel_2047`); on H100, eight `2^22` and eight `−2^22` return `0`
(`h100_cancel_zero`).

This is the exact condition, not a scheduling rule: the running values are known only after the
products are computed, so a scheme that must know in advance that a call is exact still uses the
exactness bound on `Σ|aᵢbᵢ|`. -/

open TensorCore

namespace Ozaki.TC

/-- The products of two `b`-bit integer words are integer terms of exponent at most `F`. -/
theorem int_product_term {p : Model} {b : ℕ} (hp : IntExact p b) {q : p.Word × p.Word}
    (hq : IntWord p b q.1 ∧ IntWord p b q.2)
    (hnz : (denormalizedMul (decodeD p q.1) (decodeD p q.2)).significand ≠ 0) :
    (denormalizedMul (decodeD p q.1) (decodeD p q.2)).exponent ≤ p.alignFracBits ∧
      ∃ k : ℤ, (denormalizedMul (decodeD p q.1) (decodeD p q.2)).value = k * pow2 0 := by
  obtain ⟨⟨h1, za, hza, hza'⟩, ⟨h2, zb, hzb, hzb'⟩⟩ := hq
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
  refine ⟨by rw [hD1, hD2]; have := hp.align; omega, za * zb, ?_⟩
  have hv := denormalizedProduct_value (decodeD p q.1) (decodeD p q.2)
  simp only [denormalizedMul] at hv
  rw [hv, pow2_zero, Rat.mul_one, Rat.intCast_mul]
  unfold wordValue at hza hzb
  rw [hza, hzb]

/-- **Exact block with cancellation.** Operands that are integers of magnitude at most `2^b`
(`2b ≤ F`), an integer `c` with `|c| < 2^(F+1)`, and an exact sum `c + Σ aᵢbᵢ` that is a binary32
value: the block returns that sum, however large `Σ|aᵢbᵢ|` is. -/
theorem evalBlock_cancel {p : Model} {b : ℕ} (hp : IntExact p b) {x : BlockInput p}
    (hlen : x.products.length = p.nfma)
    (hops : ∀ q ∈ x.products, IntWord p b q.1 ∧ IntWord p b q.2)
    {zc : ℤ} (hc : value32 x.c = some (zc : ℚ))
    (hcF : Rat.abs (zc : ℚ) < 2 ^ (p.alignFracBits + 1))
    (hfin : FiniteValue32 ((zc : ℚ) + wordProducts p x.products)) :
    ∃ t, evalBlock x = .ok t ∧ t.output.value = zc + wordProducts p x.products := by
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
  have hterms : blk.terms = ⟨dc.significand, dc.exponent, dc.mantissaBits⟩ ::
      x.products.map fun q => denormalizedMul (decodeD p q.1) (decodeD p q.2) := by
    rw [← hblk]; simp [PreparedBlock.terms, List.map_map, Function.comp_def]
  have hprof : blk.model = p := by rw [← hblk]
  have hbias : (1 : ℤ) - fp32.bias ≤ p.alignFracBits := by
    have : fp32.bias = 127 := rfl
    have := hp.wide; omega
  have hacc : blk.accumulator = blk.exactDot := by
    apply accumulator_eq_exactDot_of_grid blk 0
    · intro f hf; rw [hprof] at hf ⊢; have := hp.eAlignMin f hf; omega
    · intro t ht hnz
      rw [hterms] at ht
      rcases List.mem_cons.mp ht with rfl | ht
      · refine ⟨?_, zc, ?_⟩
        · have := decode_exp_le (f := fp32) (w := x.c) (d := dc) hdc (E := p.alignFracBits)
            hbias (by rw [hdcv]; exact hcF) hnz
          show dc.exponent ≤ 0 + blk.model.alignFracBits
          rw [hprof]; omega
        · change dc.value = _; rw [hdcv, pow2_zero, Rat.mul_one]
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
        rw [hprof]
        obtain ⟨h1, h2⟩ := int_product_term hp (hops q hq) hnz
        exact ⟨by omega, h2⟩
  obtain ⟨t, ht, hv⟩ := evalPrepared_exact blk hacc (by rw [hexact]; exact hfin)
    (by rw [hprof]; exact hp.output)
  exact ⟨t, by rw [hev]; exact ht, by rw [hv, hexact]⟩

/-- **The condition on the sum is necessary.** A block that returns its exact sum returns a
binary32 value. -/
theorem evalBlock_exact_needs_binary32 {p : Model} {x : BlockInput p} {t : BlockTrace}
    (_ht : evalBlock x = .ok t) {v : ℚ} (hv : t.output.value = v) : FiniteValue32 v := by
  rw [← hv]; exact value32_finite _ _ (value32_output t)

/-- `2^24 ≤ 2^(F+1)` on every variant (`F ≥ 23`). -/
theorem two_pow_24_le {p : Model} {b : ℕ} (hp : IntExact p b) :
    (2 : ℚ) ^ (24 : ℤ) ≤ 2 ^ (p.alignFracBits + 1) :=
  two_pow_le (by have := hp.wide; omega)

/-- **Exact integer block with cancellation**: `|c| < 2^24` and `|c + Σ aᵢbᵢ| ≤ 2^24` suffice. -/
theorem evalBlock_cancel_int {p : Model} {b : ℕ} (hp : IntExact p b) {x : BlockInput p}
    (hlen : x.products.length = p.nfma)
    (hops : ∀ q ∈ x.products, IntWord p b q.1 ∧ IntWord p b q.2)
    {zc : ℤ} (hc : value32 x.c = some (zc : ℚ)) (hc24 : Rat.abs (zc : ℚ) < 2 ^ (24 : ℤ))
    (hsum : Rat.abs ((zc : ℚ) + wordProducts p x.products) ≤ 2 ^ (24 : ℤ)) :
    ∃ t, evalBlock x = .ok t ∧ t.output.value = zc + wordProducts p x.products := by
  obtain ⟨Z, hZ, _⟩ := wordProducts_int x.products hops
  refine evalBlock_cancel hp hlen hops hc (by have := two_pow_24_le hp; grind) ?_
  rw [hZ, ← Rat.intCast_add]
  apply int_finiteValue32
  rw [hZ, ← Rat.intCast_add, abs_intCast] at hsum
  have h2 : ((zc + Z).natAbs : ℚ) ≤ ((2 ^ 24 : ℕ) : ℚ) := by rw [← two_pow_natCast]; exact hsum
  exact Rat.natCast_le_natCast.mp h2

/-! ## Chains -/

/-- Every running value a chain passes on is below `2^24`, and the last one at most `2^24`:
starting from `v`, each block FMA's result `v + Σ_group` is at most `2^24` in magnitude, and is
below `2^24` if another block FMA follows. -/
def ChainOK (p : Model) : ℚ → List (List (p.Word × p.Word)) → Prop
  | _, [] => True
  | v, g :: rest => Rat.abs v < 2 ^ (24 : ℤ) ∧ Rat.abs (v + wordProducts p g) ≤ 2 ^ (24 : ℤ) ∧
      ChainOK p (v + wordProducts p g) rest

/-- **Exact chain with cancellation.** Blocks of `b`-bit integer operands chained from an integer
`c` return `c + Σ aᵢbᵢ` exactly when every running value stays within `2^24`, however large the
products' magnitudes. -/
theorem runBlocks_cancel {p : Model} {b : ℕ} (hp : IntExact p b) :
    ∀ (blocks : List (List (p.Word × p.Word))) (c : F32) (zc : ℤ), value32 c = some (zc : ℚ) →
      (∀ g ∈ blocks, g.length = p.nfma ∧ ∀ q ∈ g, IntWord p b q.1 ∧ IntWord p b q.2) →
      ChainOK p (zc : ℚ) blocks →
      ∃ ts, runBlocks p c blocks = .ok ts ∧
        runValue c ts = zc + wordProducts p blocks.flatten
  | [], c, zc, hc, _, _ => ⟨[], rfl, by simp [runValue, value32D, hc, wordProducts]; grind⟩
  | g :: rest, c, zc, hc, hg, ⟨hv, hsum, hrest⟩ => by
    obtain ⟨hlen, hops⟩ := hg g (by simp)
    obtain ⟨t, ht, htv⟩ := evalBlock_cancel_int (x := ⟨g, c⟩) hp hlen hops hc hv hsum
    obtain ⟨Z, hZ, _⟩ := wordProducts_int g hops
    have hc' : value32 t.output.bits = some ((zc + Z : ℤ) : ℚ) := by
      rw [value32_output, htv, hZ, Rat.intCast_add]
    have hrest' : ChainOK p ((zc + Z : ℤ) : ℚ) rest := by
      rw [Rat.intCast_add, ← hZ]; exact hrest
    obtain ⟨ts, hts, hval⟩ := runBlocks_cancel hp rest t.output.bits (zc + Z) hc'
      (fun g' hg' => hg g' (by simp [hg'])) hrest'
    refine ⟨t :: ts, ?_, ?_⟩
    · simp only [runBlocks]; rw [ht]; simp only; rw [hts]
    · rw [runValue_cons, hval, List.flatten_cons, wordProducts_append, hZ, Rat.intCast_add]
      grind

/-- A chain whose running values at every block boundary, and its total, stay within `2^24`. -/
theorem chainOK_of_prefixes (p : Model) :
    ∀ (blocks : List (List (p.Word × p.Word))) (v : ℚ),
      (∀ j < blocks.length, Rat.abs (v + wordProducts p (blocks.take j).flatten) < 2 ^ (24 : ℤ)) →
      Rat.abs (v + wordProducts p blocks.flatten) ≤ 2 ^ (24 : ℤ) → ChainOK p v blocks
  | [], _, _, _ => trivial
  | g :: rest, v, hpre, htot => by
    have h0 := hpre 0 (by simp)
    simp only [List.take_zero, List.flatten_nil] at h0
    rw [show wordProducts p [] = 0 from rfl, Rat.add_zero] at h0
    refine ⟨h0, ?_, ?_⟩
    · cases rest with
      | nil => simpa [wordProducts_append, show wordProducts p [] = 0 from rfl] using htot
      | cons g' rest' =>
        have h1 := hpre 1 (by simp)
        simp only [List.take_succ_cons, List.take_zero, List.flatten_cons, List.flatten_nil,
          List.append_nil] at h1
        exact Rat.le_of_lt h1
    · apply chainOK_of_prefixes p rest
      · intro j hj
        have := hpre (j + 1) (by simp; omega)
        simp only [List.take_succ_cons, List.flatten_cons, wordProducts_append] at this
        rw [Rat.add_assoc]; exact this
      · simp only [List.flatten_cons, wordProducts_append] at htot
        rw [Rat.add_assoc]; exact htot

/-- `chunks n m xs` has `m` groups. -/
theorem chunks_count (n : ℕ) : ∀ (m : ℕ) (xs : List α), (chunks n m xs).length = m
  | 0, _ => rfl
  | m + 1, xs => by simp [chunks, chunks_count n m]

theorem groupsOf_count (K : ℕ) (pad : α) (ps : List α) :
    (groupsOf K pad ps).length = groupCount K ps.length := by
  unfold groupsOf; exact chunks_count _ _ _

/-- The first `j` blocks of length `K` are the first `j K` elements. -/
theorem take_flatten_groups {K : ℕ} :
    ∀ (gs : List (List α)) (j : ℕ), (∀ g ∈ gs, g.length = K) →
      (gs.take j).flatten = gs.flatten.take (j * K)
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | g :: gs, j + 1, h => by
    have hg := h g (by simp)
    simp only [List.take_succ_cons, List.flatten_cons]
    rw [take_flatten_groups gs j (fun g' hg' => h g' (by simp [hg'])), Nat.succ_mul,
      Nat.add_comm (j * K) K, List.take_append, List.take_of_length_le (l := g) (by omega), hg,
      Nat.add_sub_cancel_left]

theorem groupCount_lt {K L j : ℕ} (hK : 0 < K) (hj : j < groupCount K L) : j * K < L := by
  unfold groupCount at hj
  have := (Nat.le_div_iff_mul_le hK).mp (show j + 1 ≤ (L + K - 1) / K by omega)
  rw [Nat.succ_mul] at this
  omega

theorem take_zip' (x : List α) (y : List β) (m : ℕ) :
    (List.zip x y).take m = List.zip (x.take m) (y.take m) := by
  rw [List.zip_eq_zipWith, List.take_zipWith, ← List.zip_eq_zipWith]

/-- The dot products of the prefixes at every block boundary before the last stay below `2^24`,
and the whole dot product within `2^24`. -/
def PrefixesOK (K : ℕ) (x y : List ℤ) : Prop :=
  (∀ j, j * K < x.length → (dotZ (x.take (j * K)) (y.take (j * K))).natAbs < 2 ^ 24) ∧
    (dotZ x y).natAbs ≤ 2 ^ 24

theorem intCast_abs_lt {z : ℤ} {n : ℕ} (h : z.natAbs < 2 ^ n) : Rat.abs (z : ℚ) < 2 ^ (n : ℤ) := by
  rw [abs_intCast, two_pow_natCast]; exact Rat.natCast_lt_natCast.mpr h

theorem intCast_abs_le {z : ℤ} {n : ℕ} (h : z.natAbs ≤ 2 ^ n) : Rat.abs (z : ℚ) ≤ 2 ^ (n : ℤ) := by
  rw [abs_intCast, two_pow_natCast]; exact Rat.natCast_le_natCast.mpr h

/-- **The matrix multiplier with cancellation.** On `b`-bit integer vectors whose dot products of
the prefixes at the block boundaries stay below `2^24`, and whose dot product is within `2^24`, the
Tensor Core matrix multiplier is exact, however large `Σ|xᵢyᵢ|` is. -/
theorem tcMultiplier_cancel {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (hK : 0 < p.nfma) {x y : List ℤ} (hlen : x.length = y.length)
    (hx : ∀ a ∈ x, a.natAbs ≤ 2 ^ b) (hy : ∀ a ∈ y, a.natAbs ≤ 2 ^ b)
    (hok : PrefixesOK p.nfma x y) : tcMultiplier p x y = some (dotZ x y) := by
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
  generalize hps : (List.zip x y).map (Prod.map E E) = ps
  obtain ⟨hglen, hflat⟩ := groupsOf_spec hK ((0 : p.Word), (0 : p.Word)) ps
  generalize hpad : groupCount p.nfma ps.length * p.nfma - ps.length = n at hflat
  -- the products of every prefix of the encoded pairs
  have hpre_val : ∀ m, wordProducts p (ps.take m) = (dotZ (x.take m) (y.take m) : ℚ) := by
    intro m
    rw [← hps, ← List.map_take, take_zip']
    unfold wordProducts; rw [List.map_map, dotZ_eq_zip_sum]
    refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
    have hq' := List.of_mem_zip hq
    have h1 := List.mem_of_mem_take hq'.1
    have h2 := List.mem_of_mem_take hq'.2
    simp only [Function.comp_def, Prod.map]
    rw [(hE q.1 (hx _ h1)).2.2, (hE q.2 (hy _ h2)).2.2]
  have hpadded : ∀ m, wordProducts p ((ps ++ List.replicate n ((0 : p.Word), (0 : p.Word))).take m) =
      wordProducts p (ps.take m) := by
    intro m
    rw [List.take_append, wordProducts_append, List.take_replicate,
      (wordDotAbs_replicate_zero p hh.wellFormed _).2, Rat.add_zero]
  have hpslen : ps.length = x.length := by rw [← hps]; simp [hlen]
  have hchain : ChainOK p 0 (groupsOf p.nfma (0, 0) ps) := by
    apply chainOK_of_prefixes
    · intro j hj
      rw [groupsOf_count] at hj
      rw [take_flatten_groups _ j hglen, hflat, hpadded, hpre_val, Rat.zero_add]
      exact intCast_abs_lt (hok.1 j (by rw [← hpslen]; exact groupCount_lt hK hj))
    · rw [hflat, wordProducts_append, (wordDotAbs_replicate_zero p hh.wellFormed n).2, Rat.add_zero,
        ← List.take_length (l := ps), hpre_val, hpslen, List.take_length,
        show y.take x.length = y by rw [hlen]; exact List.take_length, Rat.zero_add]
      exact intCast_abs_le hok.2
  obtain ⟨ts, hts, hval⟩ := runBlocks_cancel hp (groupsOf p.nfma (0, 0) ps) 0 0
    (by decide +kernel)
    (fun g hg => ⟨hglen g hg, fun q hq => by
      have hq' : q ∈ (groupsOf p.nfma (0, 0) ps).flatten := List.mem_flatten.mpr ⟨g, hg, hq⟩
      rw [hflat] at hq'
      rcases List.mem_append.mp hq' with hq' | hq'
      · rw [← hps] at hq'
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq'
        have := List.of_mem_zip hr
        exact ⟨(hE r.1 (hx _ this.1)).2.1, (hE r.2 (hy _ this.2)).2.1⟩
      · rw [(List.mem_replicate.mp hq').2]; exact ⟨hz0, hz0⟩⟩)
    (by rw [Rat.intCast_zero]; exact hchain)
  unfold tcMultiplier
  simp only [hmx, hmy, Option.bind_eq_bind, Option.bind_some, hzip, hps, hts]
  rw [hval, hflat, wordProducts_append, (wordDotAbs_replicate_zero p hh.wellFormed n).2,
    ← List.take_length (l := ps), hpre_val, hpslen, List.take_length,
    show y.take x.length = y by rw [hlen]; exact List.take_length, Rat.intCast_zero]
  congr 1; grind

/-- A matrix multiplier exact on every pair of vectors that satisfies `P`. -/
def ExactWhen (mult : MatrixMultiplier) (P : List ℤ → List ℤ → Prop) : Prop :=
  ∀ x y, P x y → mult x y = some (dotZ x y)

/-- `b`-bit vectors of equal length whose prefix dot products at the block boundaries of `K` stay
within `2^24`. -/
def CancelOK (b K : ℕ) (x y : List ℤ) : Prop :=
  x.length = y.length ∧ (∀ a ∈ x, a.natAbs ≤ 2 ^ b) ∧ (∀ a ∈ y, a.natAbs ≤ 2 ^ b) ∧
    PrefixesOK K x y

theorem tcMultiplier_exactWhen {p : Model} {b : ℕ} (hp : IntExact p b) (hh : HoldsInts p b)
    (hK : 0 < p.nfma) : ExactWhen (tcMultiplier p) (CancelOK b p.nfma) :=
  fun _ _ ⟨hlen, hx, hy, hok⟩ => tcMultiplier_cancel hp hh hK hlen hx hy hok

/-! ## Witnesses -/

/-- fp16 `−2048` (`0xE800`) times `2048`. -/
def negPair : F16 × F16 := (0xE800, 0x6800)
/-- fp16 `2048 · 2048 = 2^22`. -/
def posPair : F16 × F16 := (0x6800, 0x6800)

/-- **A100, cancellation to zero.** Four products `2^22` and four `−2^22` total `2^25` in magnitude,
twice the exactness bound, and the block returns the exact `0`. -/
theorem a100_cancel_zero :
    (evalBlock (p := ampereF16F32) ⟨List.replicate 4 posPair ++ List.replicate 4 negPair, 0⟩).map
      (fun t => t.output.value) = .ok 0 ∧
    wordDotAbs ampereF16F32 (List.replicate 4 posPair ++ List.replicate 4 negPair) =
      2 ^ (25 : ℤ) := by
  decide +kernel

/-- **A100, cancellation to `2047²`.** Four products `2047²` and three `−2047²` total
`7 · 2047² > 2^24` in magnitude; the block returns the exact `2047² = 4190209`. Without the three
negative products, seven `2047²` lose a bit (`a100_full_blockFMA`). -/
theorem a100_cancel_2047 :
    (evalBlock (p := ampereF16F32)
      ⟨List.replicate 4 (0x67FF, 0x67FF) ++ List.replicate 3 (0xE7FF, 0x67FF) ++ [(0, 0)], 0⟩).map
      (fun t => t.output.value) = .ok 4190209 ∧
    (7 * 2047 * 2047 : ℤ) > 2 ^ 24 := by
  decide +kernel

/-- **H100, cancellation to zero.** Eight products `2^22` and eight `−2^22`, a full block FMA of
sixteen with total magnitude `2^26`, return the exact `0`. -/
theorem h100_cancel_zero :
    (evalBlock (p := hopperF16F32) ⟨List.replicate 8 posPair ++ List.replicate 8 negPair, 0⟩).map
      (fun t => t.output.value) = .ok 0 := by
  decide +kernel

/-- The witness at the level of the matrix multiplier: `x = [2048 ×4, −2048 ×4]`, `y = [2048 ×8]` on
A100. `Σ|xᵢyᵢ| = 2^25` exceeds the exactness bound of `tcMultiplier_exactOn`, but every prefix stays
within `2^24`, so the matrix multiplier is exact by `tcMultiplier_cancel`. -/
def cancelX : List ℤ := List.replicate 4 2048 ++ List.replicate 4 (-2048)
def cancelY : List ℤ := List.replicate 8 2048

theorem a100_multiplier_cancel :
    tcMultiplier ampereF16F32 cancelX cancelY = some 0 ∧ dotAbs cancelX cancelY = 2 ^ 25 := by
  refine ⟨?_, by decide⟩
  have := tcMultiplier_cancel (p := ampereF16F32) (b := 11)
    ⟨by decide, by decide, eAlignMin_ok _ _ (by decide), by decide, by decide⟩
    ⟨by decide, by decide, by decide, by decide⟩ (by decide) (x := cancelX) (y := cancelY)
    (by decide) (by decide) (by decide) ⟨fun j hj => by
      have h8 : ampereF16F32.nfma = 8 := rfl
      have hl : cancelX.length = 8 := rfl
      rw [h8, hl] at hj
      have : j = 0 := by omega
      subst this; decide, by decide⟩
  rw [this]; decide

end Ozaki.TC
