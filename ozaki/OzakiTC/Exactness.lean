import TensorCore
import Ozaki

/-! # Exact integer blocks on the Tensor Core model

The Ozaki schemes need the Tensor Core to multiply small integers exactly. On the model of
`TensorCore`, a block aligns every term to the largest exponent and truncates it to `F` bits below
it, accumulates exactly, and truncates the sum to binary32. This file gives conditions under which
nothing is lost:

* `accumulator_eq_exactDot_of_grid`: alignment is exact when every nonzero term lies on a grid
  `2^g` and has exponent at most `g + F`;
* `evalBlock_int`: a block whose operands are integers of magnitude at most `2^b`, with `2b ≤ F`,
  and whose `c` is an integer, returns `c + Σ aᵢbᵢ` exactly when `|c| + Σ|aᵢbᵢ| ≤ 2^24`;
* `runBlocks_int`: the same for a chain of blocks, each passing its output word as the next `c`.

The conditions are those of the Z3 models' `2b + log₂ k ≤ 24`, made precise for this hardware:
alignment needs `2b ≤ F` (`F = 23` on V100, `24` on A100, `25` on H100) and the final binary32
truncation needs the sum within `2^24`. Unlike the Z3 models' engine, the model accumulates with
`F + 3` or more bits, so only the final sum, not every partial sum, must fit binary32. -/

open TensorCore

namespace Ozaki.TC

/-! ## Bridges to the scheme library's arithmetic -/

theorem absQ_eq (x : ℚ) : absQ x = Rat.abs x := by
  unfold absQ; rw [abs_def]; split <;> split <;> grind

theorem pow2_eq (e : ℤ) : pow2 e = (2 : ℚ) ^ e := rfl

theorem sumQ_eq (xs : List ℚ) : sumQ xs = xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumQ, ih]

/-! ## Alignment on a grid -/

/-- If every nonzero term is a multiple of `2^g` with exponent at most `g + F`, and the floor is at
most `g + F`, alignment loses nothing. -/
theorem accumulator_eq_exactDot_of_grid (b : PreparedBlock) (g : ℤ)
    (hfloor : ∀ f ∈ b.model.eAlignMin, f ≤ g + b.model.alignFracBits)
    (hterm : ∀ t ∈ b.terms, t.significand ≠ 0 →
      t.unnormalizedExp ≤ g + b.model.alignFracBits ∧ ∃ k : ℤ, t.value = k * pow2 g) :
    b.accumulator = b.exactDot := by
  rw [accumulator_value, ← terms_value]
  congr 1
  apply List.map_congr_left
  intro t ht
  by_cases hz : t.significand = 0
  · have hv : t.value = 0 := by simp [UnnormalizedProduct.value, hz]
    rw [hv]; exact truncGrid_zero _
  · obtain ⟨_, k, hk⟩ := hterm t ht hz
    obtain ⟨e, he, _⟩ := alignExp_term b t ht hz
    have hup := alignExp_upper b _ hfloor (fun t' ht' hz' => (hterm t' ht' hz').1) e (by simp [he])
    have hgrid : b.alignGridExponent ≤ g := by
      unfold PreparedBlock.alignGridExponent; rw [he]; simp only [Option.getD_some]; omega
    rw [hk]; exact truncGrid_exact_of_grid k g _ hgrid

/-- An exact accumulator whose value is a binary32 number is returned unchanged. -/
theorem evalPrepared_exact (b : PreparedBlock) (hacc : b.accumulator = b.exactDot)
    (hfin : FiniteValue32 b.exactDot) :
    ∃ t, evalPrepared b = .ok t ∧ t.output.value = b.exactDot := by
  have hr : absQ b.accumulator ≤ maxFinite32 := by rw [hacc]; exact finiteValue32_abs_le hfin
  obtain ⟨t, ht⟩ := evalPrepared_total b hr
  refine ⟨t, ht, ?_⟩
  rw [evalPrepared_output_value ht, hacc, signedRounded_trunc_of_finite _ hfin]

/-! ## Integers -/

/-- Every integer of magnitude at most `2^24` is a binary32 number. -/
theorem int_finiteValue32 (z : ℤ) (h : z.natAbs ≤ 2 ^ 24) : FiniteValue32 (z : ℚ) := by
  by_cases hz : z.natAbs < 2 ^ 24
  · have := grid_finiteValue32 z 0 (by omega) (by omega) hz
    rwa [pow2_zero, Rat.mul_one] at this
  · have hz' : z = 2 * (z / 2) := by omega
    have := grid_finiteValue32 (z / 2) 1 (by omega) (by omega) (by omega)
    rw [pow2_one] at this
    rw [hz', Rat.intCast_mul]
    have h2 : ((2 : ℤ) : ℚ) = 2 := rfl
    rw [h2, Rat.mul_comm]
    exact this

/-- A finite word of a format whose value has magnitude below `2^(E+1)` has exponent at most `E`. -/
theorem decode_exp_le {f : Format} {w : BitVec f.width} {d : Decoded}
    (hd : (classify f w).finite = some d) {E : ℤ} (hE : 1 - f.bias ≤ E)
    (hm : Rat.abs d.value < 2 ^ (E + 1)) (hn : d.significand ≠ 0) : d.unnormalizedExp ≤ E :=
  classifyNat_scale_le_of_magnitude f w.toNat d hd E hE (by rw [absQ_eq]; exact hm) hn

theorem intCast_eq_zero {z : ℤ} (h : (z : ℚ) = 0) : z = 0 :=
  Rat.intCast_inj.mp (by rw [h, Rat.intCast_zero])

theorem decoded_value_eq_zero {d : Decoded} : d.value = 0 ↔ d.significand = 0 := by
  unfold Decoded.value
  constructor
  · intro h
    rcases Rat.mul_eq_zero.mp h with h | h
    · exact intCast_eq_zero h
    · exact absurd h (Rat.ne_of_gt (pow2_pos _))
  · intro h; simp [h]

/-- The decoded operand of a word, `0` if it is not finite. -/
def decodeD (p : Model) (w : p.Word) : Decoded := (p.decode w).getD ⟨0, 0, 0⟩

/-- The value of an operand word, `0` if it is not finite. -/
def wordValue (p : Model) (w : p.Word) : ℚ := (decodeD p w).value

/-- The value of a binary32 word, `0` if it is not finite. -/
def value32D (c : F32) : ℚ := (value32 c).getD 0

/-- A finite word whose value is an integer of magnitude at most `2^b`. -/
def IntWord (p : Model) (b : ℕ) (w : p.Word) : Prop :=
  (p.decode w).isSome ∧ ∃ z : ℤ, wordValue p w = z ∧ z.natAbs ≤ 2 ^ b

/-- `Σ aᵢbᵢ` of encoded operand pairs. -/
def wordProducts (p : Model) (ps : List (p.Word × p.Word)) : ℚ :=
  (ps.map fun q => wordValue p q.1 * wordValue p q.2).sum

/-- `Σ |aᵢbᵢ|` of encoded operand pairs. -/
def wordDotAbs (p : Model) (ps : List (p.Word × p.Word)) : ℚ :=
  (ps.map fun q => Rat.abs (wordValue p q.1 * wordValue p q.2)).sum

theorem wordDotAbs_nonneg (p : Model) (ps : List (p.Word × p.Word)) : 0 ≤ wordDotAbs p ps :=
  sum_nonneg fun _ _ => abs_nonneg _

theorem wordDotAbs_append (p : Model) (xs ys : List (p.Word × p.Word)) :
    wordDotAbs p (xs ++ ys) = wordDotAbs p xs + wordDotAbs p ys := by
  unfold wordDotAbs; rw [sum_map_append]

theorem wordProducts_append (p : Model) (xs ys : List (p.Word × p.Word)) :
    wordProducts p (xs ++ ys) = wordProducts p xs + wordProducts p ys := by
  unfold wordProducts; rw [sum_map_append]

/-- Products of integer words add up to an integer within their budget. -/
theorem wordProducts_int {p : Model} {b : ℕ} :
    ∀ ps : List (p.Word × p.Word), (∀ q ∈ ps, IntWord p b q.1 ∧ IntWord p b q.2) →
      ∃ z : ℤ, wordProducts p ps = z ∧ Rat.abs (z : ℚ) ≤ wordDotAbs p ps
  | [], _ => ⟨0, by simp [wordProducts], by simp [wordDotAbs]⟩
  | q :: ps, h => by
    obtain ⟨⟨_, za, hza, _⟩, ⟨_, zb, hzb, _⟩⟩ := h q (by simp)
    obtain ⟨z, hz, hb⟩ := wordProducts_int ps (fun q' hq => h q' (by simp [hq]))
    refine ⟨za * zb + z, ?_, ?_⟩
    · simp only [wordProducts, List.map_cons, List.sum_cons] at hz ⊢
      rw [hz, hza, hzb, Rat.intCast_add, Rat.intCast_mul]
    · simp only [wordDotAbs, List.map_cons, List.sum_cons] at hb ⊢
      rw [hza, hzb, Rat.intCast_add, Rat.intCast_mul]
      have := abs_add_le ((za : ℚ) * zb) (z : ℚ)
      grind

/-- Preparation of finite operand pairs. -/
theorem prepareProducts_eq (p : Model) :
    ∀ ps : List (p.Word × p.Word), (∀ q ∈ ps, (p.decode q.1).isSome ∧ (p.decode q.2).isSome) →
      prepareProducts p ps = some (ps.map fun q => (decodeD p q.1, decodeD p q.2))
  | [], _ => rfl
  | q :: ps, h => by
    obtain ⟨h1, h2⟩ := h q (by simp)
    have ih := prepareProducts_eq p ps (fun q' hq => h q' (by simp [hq]))
    obtain ⟨d1, hd1⟩ := Option.isSome_iff_exists.mp h1
    obtain ⟨d2, hd2⟩ := Option.isSome_iff_exists.mp h2
    simp only [prepareProducts] at ih ⊢
    simp only [List.mapM_cons, hd1, hd2, ih, decodeD, List.map_cons]
    rfl

theorem decode32_isSome_of_value32 {c : F32} {v : ℚ} (h : value32 c = some v) :
    ∃ d, decode32 c = some d ∧ d.value = v := by
  unfold value32 at h
  cases hd : decode32 c with
  | none => simp [hd] at h
  | some d => simp only [hd, Option.map_some, Option.some.injEq] at h; exact ⟨d, rfl, h⟩

/-! ## One block -/

/-- Profile conditions for exact `b`-bit integer blocks: `2b ≤ F`, `F ≥ 23`, a floor at most `F`,
and a minimum normal exponent at most `b` (every format in use). -/
structure IntExact (p : Model) (b : ℕ) : Prop where
  align : 2 * (b : ℤ) ≤ p.alignFracBits
  wide : 23 ≤ p.alignFracBits
  eAlignMin : ∀ f ∈ p.eAlignMin, f ≤ p.alignFracBits
  emin : 1 - p.input.bias ≤ b

/-- **Exact integer block.** Operands that are integers of magnitude at most `2^b` and an integer
`c` with `|c| + Σ|aᵢbᵢ| ≤ 2^24` give `c + Σ aᵢbᵢ` exactly. -/
theorem evalBlock_int {p : Model} {b : ℕ} (hp : IntExact p b) {x : BlockInput p}
    (hlen : x.products.length = p.nfma)
    (hops : ∀ q ∈ x.products, IntWord p b q.1 ∧ IntWord p b q.2)
    {zc : ℤ} (hc : value32 x.c = some (zc : ℚ))
    (hbound : Rat.abs (zc : ℚ) + wordDotAbs p x.products ≤ 2 ^ (24 : ℤ)) :
    ∃ t, evalBlock x = .ok t ∧ t.output.value = zc + wordProducts p x.products := by
  obtain ⟨dc, hdc, hdcv⟩ := decode32_isSome_of_value32 hc
  have hpp := prepareProducts_eq p x.products (fun q hq => ⟨(hops q hq).1.1, (hops q hq).2.1⟩)
  have hprep : prepare x = some ⟨p, x.products.map fun q => (decodeD p q.1, decodeD p q.2), dc⟩ := by
    unfold prepare; rw [hdc, hpp]
  generalize hblk : (⟨p, x.products.map fun q => (decodeD p q.1, decodeD p q.2), dc⟩ :
    PreparedBlock) = blk at hprep
  have hev : evalBlock x = evalPrepared blk := by
    unfold evalBlock; rw [if_neg (by simp [hlen]), hprep]
  obtain ⟨Z, hZ, hZb⟩ := wordProducts_int x.products hops
  have hprods : blk.exactProducts = wordProducts p x.products := by
    rw [← hblk]; unfold PreparedBlock.exactProducts wordProducts wordValue
    rw [sumQ_eq, List.map_map]; rfl
  have hexact : blk.exactDot = zc + wordProducts p x.products := by
    unfold PreparedBlock.exactDot; rw [hprods, ← hblk]; simp only; rw [hdcv]
  have hbound0 := wordDotAbs_nonneg p x.products
  have hzc : (zc.natAbs : ℚ) ≤ 2 ^ (24 : ℤ) := by rw [← abs_intCast]; grind
  -- every product term
  have hprod : ∀ q ∈ x.products, (unnormalizedMul (decodeD p q.1) (decodeD p q.2)).significand ≠ 0 →
      (unnormalizedMul (decodeD p q.1) (decodeD p q.2)).unnormalizedExp ≤ p.alignFracBits ∧
      ∃ k : ℤ, (unnormalizedMul (decodeD p q.1) (decodeD p q.2)).value = k * pow2 0 := by
    intro q hq hnz
    obtain ⟨⟨h1, za, hza, hza'⟩, ⟨h2, zb, hzb, hzb'⟩⟩ := hops q hq
    simp only [unnormalizedMul] at hnz ⊢
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
    have hv := unnormalizedProduct_value (decodeD p q.1) (decodeD p q.2)
    simp only [unnormalizedMul] at hv
    rw [hv, pow2_zero, Rat.mul_one, Rat.intCast_mul]
    unfold wordValue at hza hzb
    rw [hza, hzb]
  have hterms : blk.terms = ⟨dc.significand, dc.unnormalizedExp, dc.mantissaBits⟩ ::
      x.products.map fun q => unnormalizedMul (decodeD p q.1) (decodeD p q.2) := by
    rw [← hblk]; simp [PreparedBlock.terms, List.map_map, Function.comp_def]
  have hprof : blk.model = p := by rw [← hblk]
  -- two cases: `|c| < 2^24` (every term on the grid `2^0`), or `|c| = 2^24` and every product
  -- is zero (`c` alone, on the grid `2^1`)
  have hacc : blk.accumulator = blk.exactDot := by
    by_cases hsmall : zc.natAbs < 2 ^ 24
    · apply accumulator_eq_exactDot_of_grid blk 0
      · intro f hf; rw [hprof] at hf ⊢; have := hp.eAlignMin f hf; omega
      · intro t ht hnz
        rw [hterms] at ht
        rcases List.mem_cons.mp ht with rfl | ht
        · refine ⟨?_, zc, ?_⟩
          · have := decode_exp_le (f := fp32) (w := x.c) (d := dc) hdc (E := 23) (by decide)
              (by rw [hdcv, abs_intCast]
                  have : ((zc.natAbs : ℕ) : ℚ) < ((2 ^ 24 : ℕ) : ℚ) := Rat.natCast_lt_natCast.mpr hsmall
                  rw [← two_pow_natCast] at this; exact this) hnz
            show dc.unnormalizedExp ≤ 0 + blk.model.alignFracBits
            rw [hprof]; have := hp.wide; omega
          · change dc.value = _; rw [hdcv, pow2_zero, Rat.mul_one]
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
          rw [hprof]
          obtain ⟨h1, h2⟩ := hprod q hq hnz
          exact ⟨by omega, h2⟩
    · -- `|c| = 2^24`: the budget leaves every product zero
      have hceq : zc.natAbs = 2 ^ 24 := by
        have : ((zc.natAbs : ℕ) : ℚ) ≤ ((2 ^ 24 : ℕ) : ℚ) := by rw [← two_pow_natCast]; exact hzc
        have := Rat.natCast_le_natCast.mp this; omega
      have hzero : ∀ q ∈ x.products, wordValue p q.1 * wordValue p q.2 = 0 := by
        have hb0 : wordDotAbs p x.products ≤ 0 := by
          have h24 : Rat.abs (zc : ℚ) = 2 ^ (24 : ℤ) := by
            rw [abs_intCast, hceq]; exact (two_pow_natCast 24).symm
          rw [h24] at hbound
          grind
        intro q hq
        have hle : Rat.abs (wordValue p q.1 * wordValue p q.2) ≤ wordDotAbs p x.products := by
          unfold wordDotAbs
          exact le_sum_of_mem (l := x.products) (f := fun q => Rat.abs (wordValue p q.1 * wordValue p q.2))
            (fun _ _ => abs_nonneg _) hq
        have := abs_nonneg (wordValue p q.1 * wordValue p q.2)
        exact abs_eq_zero.mp (by grind)
      apply accumulator_eq_exactDot_of_grid blk 1
      · intro f hf; rw [hprof] at hf ⊢; have := hp.eAlignMin f hf; omega
      · intro t ht hnz
        rw [hterms] at ht
        rcases List.mem_cons.mp ht with rfl | ht
        · refine ⟨?_, zc / 2, ?_⟩
          · have := decode_exp_le (f := fp32) (w := x.c) (d := dc) hdc (E := 24) (by decide)
              (by rw [hdcv, abs_intCast, hceq, ← two_pow_natCast]; exact two_pow_lt (by omega)) hnz
            show dc.unnormalizedExp ≤ 1 + blk.model.alignFracBits
            rw [hprof]; have := hp.wide; omega
          · change dc.value = _
            rw [hdcv, pow2_one]
            have : zc = (zc / 2) * 2 := by omega
            conv => lhs; rw [this]
            rw [Rat.intCast_mul, Rat.intCast_ofNat]
        · exfalso
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ht
          apply hnz
          have hv := unnormalizedProduct_value (decodeD p q.1) (decodeD p q.2)
          have : (unnormalizedMul (decodeD p q.1) (decodeD p q.2)).value = 0 := by
            rw [hv]; exact hzero q hq
          unfold UnnormalizedProduct.value at this
          rcases Rat.mul_eq_zero.mp this with h | h
          · exact intCast_eq_zero h
          · exact absurd h (Rat.ne_of_gt (pow2_pos _))
  have hfin : FiniteValue32 blk.exactDot := by
    rw [hexact, hZ, ← Rat.intCast_add]
    apply int_finiteValue32
    have h1 := abs_add_le (zc : ℚ) (Z : ℚ)
    rw [← Rat.intCast_add, abs_intCast] at h1
    have h2 : ((zc + Z).natAbs : ℚ) ≤ ((2 ^ 24 : ℕ) : ℚ) := by
      rw [← two_pow_natCast]; grind
    exact Rat.natCast_le_natCast.mp h2
  obtain ⟨t, ht, hv⟩ := evalPrepared_exact blk hacc hfin
  exact ⟨t, by rw [hev]; exact ht, by rw [hv, hexact]⟩

/-! ## Chained blocks -/

/-- The value a run of blocks ends with: the last output, or `c` when there is no block. -/
def runValue (c : F32) (ts : List BlockTrace) : ℚ :=
  (ts.getLast?.map fun t => t.output.value).getD (value32D c)

theorem value32_output (t : BlockTrace) : value32 t.output.bits = some t.output.value := by
  unfold value32; rw [t.output.valid]; rfl

theorem runValue_cons (c : F32) (t : BlockTrace) (ts : List BlockTrace) :
    runValue c (t :: ts) = runValue t.output.bits ts := by
  unfold runValue
  cases ts with
  | nil => simp [value32D, value32_output]
  | cons u us =>
    rw [List.getLast?_cons_cons]
    cases h : (u :: us).getLast? with
    | none => simp at h
    | some v => rfl

/-- **Exact chain.** Blocks of `b`-bit integer operands, chained through their binary32 outputs
from an integer `c`, return `c + Σ aᵢbᵢ` exactly when `|c| + Σ|aᵢbᵢ| ≤ 2^24`. -/
theorem runBlocks_int {p : Model} {b : ℕ} (hp : IntExact p b) :
    ∀ (groups : List (List (p.Word × p.Word))) (c : F32) (zc : ℤ), value32 c = some (zc : ℚ) →
      (∀ g ∈ groups, g.length = p.nfma ∧ ∀ q ∈ g, IntWord p b q.1 ∧ IntWord p b q.2) →
      Rat.abs (zc : ℚ) + wordDotAbs p groups.flatten ≤ 2 ^ (24 : ℤ) →
      ∃ ts, runBlocks p c groups = .ok ts ∧
        runValue c ts = zc + wordProducts p groups.flatten
  | [], c, zc, hc, _, _ => ⟨[], rfl, by simp [runValue, value32D, hc, wordProducts]; grind⟩
  | g :: rest, c, zc, hc, hg, hbound => by
    obtain ⟨hlen, hops⟩ := hg g (by simp)
    rw [List.flatten_cons, wordDotAbs_append] at hbound
    have hrest0 := wordDotAbs_nonneg p rest.flatten
    obtain ⟨t, ht, hv⟩ := evalBlock_int (x := ⟨g, c⟩) hp hlen hops hc (by grind)
    obtain ⟨Z, hZ, hZb⟩ := wordProducts_int g hops
    have hc' : value32 t.output.bits = some ((zc + Z : ℤ) : ℚ) := by
      rw [value32_output, hv, hZ, Rat.intCast_add]
    have hbound' : Rat.abs ((zc + Z : ℤ) : ℚ) + wordDotAbs p rest.flatten ≤ 2 ^ (24 : ℤ) := by
      have := abs_add_le (zc : ℚ) (Z : ℚ)
      rw [← Rat.intCast_add] at this
      grind
    obtain ⟨ts, hts, hval⟩ := runBlocks_int hp rest t.output.bits (zc + Z) hc'
      (fun g' hg' => hg g' (by simp [hg'])) hbound'
    refine ⟨t :: ts, ?_, ?_⟩
    · simp only [runBlocks]; rw [ht]; simp only; rw [hts]
    · rw [runValue_cons, hval, List.flatten_cons, wordProducts_append, hZ, Rat.intCast_add]
      grind

end Ozaki.TC
