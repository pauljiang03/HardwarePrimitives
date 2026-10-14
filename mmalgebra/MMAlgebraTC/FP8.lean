import MMAlgebraTC.ChainVariants

/-! # The FP8 Tensor Cores in the reduction algebra

The FP8 block FMAs of Ada (`adaE4M3F32`, `adaE5M2F32`: `N_FMA = 16`) and Hopper (`hopperE4M3F32`,
`hopperE5M2F32`: `N_FMA = 32`) keep a 13-bit mantissa after alignment, ten bits fewer than FP32,
and truncate the block output to a 13-bit mantissa; those of Blackwell (`blackwellE4M3F32`,
`blackwellE5M2F32`) keep the 23-bit mantissa plus 2 padding bits and return binary32.

On the other Tensor Core models an empty block FMA passes a finite accumulator other than `−0`
through (`tc_pass_any`, `fp8_blackwell_pass`). On Ada and Hopper FP8 it does not: `c` is aligned
together with the products and keeps only a 13-bit mantissa, so an empty block truncates `c` to a
13-bit mantissa (`tc_empty_block_trunc13`, `fp8_empty_block_trunc13`).
Block outputs already have a 13-bit mantissa, so the truncation shows only on the initial `C` or
after a binary32 addition (split-K, a stream-K fix-up). The pass law fails, and the schedule
algebra of Ada and Hopper FP8 is the rigid algebra with *truncation nodes*: an empty block over an
addition, absorbed by a following nonempty block. Blackwell FP8 is rigid.

Kernel-checked witnesses on the E4M3 models (`fp8_empty_block`, `fp8_trunc_after_add`,
`fp8_c_in_accumulator`, `fp8_absorb_instance`), and the NVIDIA side of a cross-vendor input with
four different results (`xvendor_nvidia`; the CDNA 3 side is `MMAlgebra.MC.xvendor_cdna3`). E4M3
words are given in their 8-bit encoding and passed to the models through `widenE4M3Pairs`. -/

open TensorCore Ozaki Ozaki.TC

namespace MMAlgebra.TC

/-! ## An empty block truncates `c`

With a 13-bit mantissa after alignment, the only nonzero term of an empty block, `c`, sets the
alignment exponent and is truncated toward zero to a 13-bit mantissa. The result is the value of
`c` with the ten low bits of its mantissa cleared, a binary32 value that the truncation to binary32
and the 13-bit block output keep. -/

/-- Truncating `K · 2^g` toward zero to the grid `2^(g+10)` clears the ten low bits of `K`. -/
theorem truncGrid_nat_ten (K : ℕ) (g : ℤ) :
    truncGrid ((K : ℚ) * pow2 g) (g + 10) = ((K / 1024 * 1024 : ℕ) : ℚ) * pow2 g := by
  have hp := pow2_pos g
  have h10 : pow2 (g + 10) = pow2 g * 1024 := by
    rw [pow2_add, show (10 : ℤ) = ((10 : ℕ) : ℤ) from rfl, pow2_natCast]; rfl
  have hk := Nat.div_add_mod K 1024
  have hr := Nat.mod_lt K (show 1024 > 0 by decide)
  generalize K / 1024 = q at hk ⊢
  generalize K % 1024 = r at hk hr
  subst hk
  have hrq : (r : ℚ) < 1024 := by
    have := Rat.natCast_lt_natCast.mpr hr
    simpa using this
  have hr0 : (0 : ℚ) ≤ r := Rat.natCast_nonneg
  have hq0 : (0 : ℚ) ≤ q := Rat.natCast_nonneg
  have hX : (((1024 * q + r : ℕ)) : ℚ) * pow2 g = (q : ℚ) * (pow2 g * 1024) + (r : ℚ) * pow2 g := by
    rw [Rat.natCast_add, Rat.natCast_mul]
    have : ((1024 : ℕ) : ℚ) = 1024 := rfl
    rw [this]; grind
  have hrp : 0 ≤ (r : ℚ) * pow2 g := Rat.mul_nonneg hr0 (Rat.le_of_lt hp)
  have hrp2 : (r : ℚ) * pow2 g < 1024 * pow2 g := Rat.mul_lt_mul_of_pos_right hrq hp
  have hqp : 0 ≤ (q : ℚ) * (pow2 g * 1024) :=
    Rat.mul_nonneg hq0 (Rat.mul_nonneg (Rat.le_of_lt hp) (by decide))
  have hP : (0 : ℚ) < pow2 g * 1024 := Rat.mul_pos hp (by decide)
  have hx : 0 ≤ (((1024 * q + r : ℕ)) : ℚ) * pow2 g := by rw [hX]; grind
  unfold truncGrid
  rw [truncBits_nonneg_eq _ _ hx, h10, hX]
  have hfl : (((q : ℚ) * (pow2 g * 1024) + (r : ℚ) * pow2 g) / (pow2 g * 1024)).floor = (q : ℤ) := by
    apply floor_eq_of_bounds
    · rw [Rat.intCast_natCast]
      apply Rat.not_lt.mp
      rw [Rat.div_lt_iff hP]
      grind
    · rw [Rat.intCast_natCast, Rat.div_lt_iff hP]
      grind
  rw [hfl, Rat.intCast_natCast, Rat.natCast_mul]
  have : ((1024 : ℕ) : ℚ) = 1024 := rfl
  rw [this]; grind
/-- The same for a signed significand. -/
theorem truncGrid_signed_ten (s : Bool) (K : ℕ) (g : ℤ) :
    truncGrid ((((if s then -(K : ℤ) else (K : ℤ)) : ℤ) : ℚ) * pow2 g) (g + 10) =
      (((if s then -((K / 1024 * 1024 : ℕ) : ℤ) else ((K / 1024 * 1024 : ℕ) : ℤ)) : ℤ) : ℚ) *
        pow2 g := by
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, Rat.intCast_natCast]
    exact truncGrid_nat_ten K g
  · simp only [↓reduceIte, Rat.intCast_neg, Rat.intCast_natCast, Rat.neg_mul]
    rw [truncGrid_neg, truncGrid_nat_ten]

/-- Clearing the ten low mantissa bits of a finite binary32 word truncates its value toward zero
to a 13-bit mantissa. -/
theorem value32_truncateMantissa32_13 {d : F32} {dc : Decoded} (h : decode32 d = some dc) :
    value32 (truncateMantissa32 13 d) = some (truncGrid dc.value (dc.exponent - 13)) := by
  have hlt := d.isLt
  have hn : (truncateMantissa32 13 d).toNat = d.toNat / 1024 * 1024 := by
    rw [truncateMantissa32_toNat]
  have hs : d.toNat / 1024 * 1024 / 2147483648 = d.toNat / 2147483648 := by omega
  unfold value32
  rw [decode32_eq, hn, classifyNat_fp32, hs]
  rcases decode32_fields d dc h with ⟨hE, hM, rfl⟩ | ⟨hE, hM, rfl⟩ | ⟨hE1, hE2, rfl⟩
  · have h1 : d.toNat / 1024 * 1024 / 8388608 % 256 = 0 := by omega
    have h3 : d.toNat / 1024 * 1024 % 8388608 = 0 := by omega
    simp [h1, h3, Classification.finite, Decoded.value, truncGrid_zero]
  · have h1 : d.toNat / 1024 * 1024 / 8388608 % 256 = 0 := by omega
    have hm : d.toNat / 1024 * 1024 % 8388608 = d.toNat % 8388608 / 1024 * 1024 := by omega
    have ht := truncGrid_signed_ten (d.toNat / 2147483648 != 0) (d.toNat % 8388608) (-126 - 23)
    rw [show (-126 - 23 : ℤ) + 10 = -126 - 13 by omega] at ht
    simp only [Decoded.value]
    rw [show ((23 : ℤ)) = 23 from rfl, ht, h1, hm]
    by_cases h0 : d.toNat % 8388608 / 1024 * 1024 = 0
    · simp only [show (0 : ℕ) ≠ 255 by decide, if_false, if_true, h0, Classification.finite]
      cases d.toNat / 2147483648 != 0 <;> simp [Decoded.value]
    · simp only [show (0 : ℕ) ≠ 255 by decide, if_false, if_true, h0, Classification.finite,
        Option.map_some, Decoded.value]
  · have h1 : d.toNat / 1024 * 1024 / 8388608 % 256 = d.toNat / 8388608 % 256 := by omega
    have hm : (8388608 + d.toNat / 1024 * 1024 % 8388608) =
        (8388608 + d.toNat % 8388608) / 1024 * 1024 := by omega
    have ht := truncGrid_signed_ten (d.toNat / 2147483648 != 0) (8388608 + d.toNat % 8388608)
      (((d.toNat / 8388608 % 256 : ℕ) : ℤ) - 127 - 23)
    rw [show (((d.toNat / 8388608 % 256 : ℕ) : ℤ) - 127 - 23) + 10 =
      ((d.toNat / 8388608 % 256 : ℕ) : ℤ) - 127 - 13 by omega] at ht
    simp only [Decoded.value]
    rw [ht, h1, hm, if_neg (by omega), if_neg (by omega)]
    simp [Classification.finite, Decoded.value]

/-- `c` truncated toward zero to a 13-bit mantissa (the ten low bits of its mantissa cleared), with
a zero result `+0`. -/
def trunc13 (c : F32) : F32 :=
  if truncateMantissa32 13 c = 0x80000000 then 0 else truncateMantissa32 13 c

/-- A word of value zero is `+0` or `−0`. -/
theorem value32_eq_zero {w : F32} (h : value32 w = some 0) : w = 0 ∨ w = 0x80000000 := by
  unfold value32 at h
  cases hd : decode32 w with
  | none => simp [hd] at h
  | some dc =>
    rw [hd] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hlt := w.isLt
    rcases decode32_fields w dc hd with ⟨hE, hM, rfl⟩ | ⟨hE, hM, rfl⟩ | ⟨hE1, hE2, rfl⟩
    · have : w.toNat = 0 ∨ w.toNat = 2147483648 := by omega
      rcases this with h0 | h0
      · left; exact BitVec.eq_of_toNat_eq (by simp [h0])
      · right; exact BitVec.eq_of_toNat_eq (by simp [h0])
    · exfalso
      refine Decoded.value_ne_zero _ ?_ h
      show (if (w.toNat / 2147483648 != 0) then -((w.toNat % 8388608 : ℕ) : ℤ)
        else ((w.toNat % 8388608 : ℕ) : ℤ)) ≠ 0
      split <;> omega
    · exfalso
      refine Decoded.value_ne_zero _ ?_ h
      show (if (w.toNat / 2147483648 != 0) then -((8388608 + w.toNat % 8388608 : ℕ) : ℤ)
        else ((8388608 + w.toNat % 8388608 : ℕ) : ℤ)) ≠ 0
      split <;> omega

theorem truncateMantissa32_13_idem (w : F32) :
    truncateMantissa32 13 (truncateMantissa32 13 w) = truncateMantissa32 13 w := by
  apply BitVec.eq_of_toNat_eq
  rw [truncateMantissa32_toNat, truncateMantissa32_toNat]
  omega

/-- **An empty block FMA truncates `c` to a 13-bit mantissa**, on any Tensor Core model that keeps a
13-bit mantissa after alignment and truncates the block output to a 13-bit mantissa (the FP8 models
of Ada and Hopper), with a minimum alignment exponent at most `−126` and a zero word that decodes
to zero: for every finite accumulator input, the output is `c` with the ten low bits of its
mantissa cleared, or `+0` when that is zero. -/
theorem tc_empty_block_trunc13 (p : Model) (hF : p.alignMantissaBits = 13)
    (hout : p.outputMantissaBits = 13) (hmin : ∀ f ∈ p.eAlignMin, f ≤ -126)
    (hz : p.decode 0 = some ⟨0, 0, 0⟩) (d : F32) (hd : (finite32 d).isSome) :
    (tcMachine p).block d (List.replicate p.nfma none) = some (trunc13 d) := by
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp hd
  have hc : decode32 d = some f.decoded := by rw [← finite32_bits hf]; exact f.valid
  have hslot : slotPairs p (List.replicate p.nfma none) = List.replicate p.nfma (0, 0) := by
    simp [slotPairs]
  have hps := prepareProducts_replicate p 0 0 ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ p.nfma hz hz
  have hterms : (PreparedBlock.mk p (List.replicate p.nfma (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) f.decoded).terms =
      ⟨f.decoded.significand, f.decoded.exponent, f.decoded.mantissaBits⟩ ::
        List.replicate p.nfma ⟨0, 0, 0⟩ := by
    simp [PreparedBlock.terms, List.map_replicate, denormalizedMul]
  have hacc : (PreparedBlock.mk p (List.replicate p.nfma (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) f.decoded).accumulator =
      truncGrid f.decoded.value (f.decoded.exponent - 13) := by
    rw [accumulator_value, hterms, sumQ_eq]
    simp only [List.map_cons, List.map_replicate, List.sum_cons]
    have h0 : ∀ g : ℤ, truncGrid (DenormalizedProduct.value ⟨0, 0, 0⟩) g = 0 := by
      intro g
      have : DenormalizedProduct.value ⟨0, 0, 0⟩ = 0 := by simp [DenormalizedProduct.value]
      rw [this, truncGrid_zero]
    have hr : ∀ n : ℕ, (List.replicate n (0 : ℚ)).sum = 0 := by
      intro n; induction n with
      | zero => rfl
      | succ n ih => rw [List.replicate_succ, List.sum_cons, ih, Rat.add_zero]
    rw [h0, hr, Rat.add_zero]
    show truncGrid f.decoded.value _ = _
    by_cases hsig : f.decoded.significand = 0
    · have hv : f.decoded.value = 0 := by simp [Decoded.value, hsig]
      rw [hv, truncGrid_zero, truncGrid_zero]
    · have hlow : -126 ≤ f.decoded.exponent := by
        rcases decode32_fields d f.decoded hc with ⟨_, _, h0⟩ | ⟨_, _, h0⟩ | ⟨hE1, _, h0⟩
        · rw [h0] at hsig; exact absurd rfl hsig
        · rw [h0]; exact Int.le_refl _
        · rw [h0]; simp; omega
      have hexp : (PreparedBlock.mk p (List.replicate p.nfma (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) f.decoded).alignExp =
          some f.decoded.exponent := by
        apply alignExp_eq _ _ (fun g hg => by have := hmin g hg; omega)
        · intro u hu hnz
          rw [hterms] at hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact Int.le_refl _
          · rw [List.mem_replicate] at hu; rw [hu.2] at hnz; exact absurd rfl hnz
        · exact ⟨_, by rw [hterms]; exact List.mem_cons_self, hsig, rfl⟩
      unfold PreparedBlock.alignGridExponent
      rw [hexp]
      simp only [Option.getD_some]
      rw [hF]
  have hval := value32_truncateMantissa32_13 hc
  show (blockOut (p := p) ⟨slotPairs p (List.replicate p.nfma none), d⟩).toOption = some (trunc13 d)
  rw [hslot]
  unfold blockOut evalBlock
  rw [if_neg (by simp)]
  simp only [prepare, hc, hps]
  unfold evalPrepared
  rw [hacc, show (PreparedBlock.mk p (List.replicate p.nfma (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) f.decoded).model = p
    from rfl, hout]
  by_cases h0 : truncGrid f.decoded.value (f.decoded.exponent - 13) = 0
  · rw [h0] at hval ⊢
    have hr : round32 .truncate 0 = some (0 : F32) := by decide +kernel
    have hz13 : truncateMantissa32 13 (0 : F32) = 0 := by decide
    obtain ⟨g, hg, hgb, _⟩ := finite32_of_value32 (0 : F32) 0 (by decide +kernel)
    rw [hr]
    simp only [hz13, hg]
    show some g.bits = some (trunc13 d)
    rw [hgb]
    unfold trunc13
    rcases value32_eq_zero hval with h1 | h1 <;> rw [h1] <;> decide
  · rw [value32_round32 .truncate _ _ hval h0]
    obtain ⟨g, hg, hgb, _⟩ := finite32_of_value32 _ _ hval
    simp only [truncateMantissa32_13_idem, hg]
    show some g.bits = some (trunc13 d)
    rw [hgb]
    unfold trunc13
    rw [if_neg]
    intro h1
    rw [h1] at hval
    exact h0 (Option.some.inj ((by decide +kernel : value32 0x80000000 = some 0).symm.trans hval)).symm

/-- **Ada and Hopper FP8, E4M3 and E5M2: an empty block truncates `c`** to a 13-bit mantissa, for
every finite accumulator input. -/
theorem fp8_empty_block_trunc13 :
    (∀ d : F32, (finite32 d).isSome →
      (tcMachine adaE4M3F32).block d (List.replicate 16 none) = some (trunc13 d)) ∧
    (∀ d : F32, (finite32 d).isSome →
      (tcMachine adaE5M2F32).block d (List.replicate 16 none) = some (trunc13 d)) ∧
    (∀ d : F32, (finite32 d).isSome →
      (tcMachine hopperE4M3F32).block d (List.replicate 32 none) = some (trunc13 d)) ∧
    (∀ d : F32, (finite32 d).isSome →
      (tcMachine hopperE5M2F32).block d (List.replicate 32 none) = some (trunc13 d)) :=
  ⟨tc_empty_block_trunc13 adaE4M3F32 rfl rfl (by simp [adaE4M3F32]) (by decide),
    tc_empty_block_trunc13 adaE5M2F32 rfl rfl (by simp [adaE5M2F32]) (by decide),
    tc_empty_block_trunc13 hopperE4M3F32 rfl rfl (by simp [hopperE4M3F32]) (by decide),
    tc_empty_block_trunc13 hopperE5M2F32 rfl rfl (by simp [hopperE5M2F32]) (by decide)⟩

/-- **Blackwell FP8: an empty block passes `c` through**, for every finite accumulator input other
than `−0` (`tc_pass_any`). -/
theorem fp8_blackwell_pass :
    (∀ d : F32, Good d →
      (tcMachine blackwellE4M3F32).block d (List.replicate 32 none) = some d) ∧
    (∀ d : F32, Good d →
      (tcMachine blackwellE5M2F32).block d (List.replicate 32 none) = some d) :=
  ⟨tc_pass_any blackwellE4M3F32 (by decide) (by decide) (by simp [blackwellE4M3F32]) (by decide),
    tc_pass_any blackwellE5M2F32 (by decide) (by decide) (by simp [blackwellE5M2F32]) (by decide)⟩

/-- One block FMA on the given products, its other slots zero pairs: the output word, or `none`
on an error. -/
def padBlock (p : Model) (c : F32) (ps : List (p.Word × p.Word)) : Option F32 :=
  (blockOut (p := p) ⟨ps ++ List.replicate (p.nfma - ps.length) (0, 0), c⟩).toOption

/-! ## Witnesses

E4M3 words: `0x38 = 1`, `0x30 = 2^-1`, `0x01 = 2^-9`. Binary32 words: `0x3F800000 = 1`,
`0x3F800008 = 1 + 2^-20`, `0x3F800020 = 1 + 2^-18`. -/

/-- **An empty block truncates `c`** to a 13-bit mantissa on Ada and Hopper FP8
(`1 + 2^-20 ↦ 1`), and passes it through on Blackwell FP8. -/
theorem fp8_empty_block :
    padBlock hopperE4M3F32 0x3F800008 [] = some 0x3F800000 ∧
    padBlock adaE4M3F32 0x3F800008 [] = some 0x3F800000 ∧
    padBlock blackwellE4M3F32 0x3F800008 [] = some 0x3F800008 := by
  decide +kernel

/-- **The truncation node is observable after an addition.** Products `x = 1·1` and
`y = 2^-9·2^-9`: the split-K sum `[x] ⊕ [y]` is `1 + 2^-18` on every FP8 model, and an empty
block FMA after it returns `1` on Hopper and Ada and `1 + 2^-18` on Blackwell. -/
theorem fp8_trunc_after_add :
    ((padBlock hopperE4M3F32 0 (widenE4M3Pairs [(0x38, 0x38)])).bind fun a =>
      (padBlock hopperE4M3F32 0 (widenE4M3Pairs [(0x01, 0x01)])).bind fun b =>
        addBinary32 a b) = some 0x3F800020 ∧
    ((padBlock hopperE4M3F32 0 (widenE4M3Pairs [(0x38, 0x38)])).bind fun a =>
      (padBlock hopperE4M3F32 0 (widenE4M3Pairs [(0x01, 0x01)])).bind fun b =>
        (addBinary32 a b).bind fun s => padBlock hopperE4M3F32 s []) = some 0x3F800000 ∧
    ((padBlock adaE4M3F32 0 (widenE4M3Pairs [(0x38, 0x38)])).bind fun a =>
      (padBlock adaE4M3F32 0 (widenE4M3Pairs [(0x01, 0x01)])).bind fun b =>
        (addBinary32 a b).bind fun s => padBlock adaE4M3F32 s []) = some 0x3F800000 ∧
    ((padBlock blackwellE4M3F32 0 (widenE4M3Pairs [(0x38, 0x38)])).bind fun a =>
      (padBlock blackwellE4M3F32 0 (widenE4M3Pairs [(0x01, 0x01)])).bind fun b =>
        (addBinary32 a b).bind fun s => padBlock blackwellE4M3F32 s []) = some 0x3F800020 := by
  decide +kernel

/-- **`C` in the accumulator or in the epilogue.** With `A·B = 0` (`k = 32` zero products) and
`C = 1 + 2^-20`, Hopper FP8 returns `1` when `C` is the block FMA's accumulator input
(`Model.dot`) and `1 + 2^-20` when `C` is added after it (`Model.dotThenAdd`). -/
theorem fp8_c_in_accumulator :
    hopperE4M3F32.dot 0x3F800008 (List.replicate 32 (0, 0)) = some 0x3F800000 ∧
    hopperE4M3F32.dotThenAdd 0x3F800008 (List.replicate 32 (0, 0)) = some 0x3F800008 := by
  decide +kernel

/-- **Absorption, on an instance.** An empty block before a nonempty block changes nothing, and
neither does an empty block after a block: from `c = 1 + 2^-20` with the product `2^-1·1`, both
orders return the block's own output. -/
theorem fp8_absorb_instance :
    ((padBlock hopperE4M3F32 0x3F800008 []).bind fun d =>
        padBlock hopperE4M3F32 d (widenE4M3Pairs [(0x30, 0x38)])) =
      padBlock hopperE4M3F32 0x3F800008 (widenE4M3Pairs [(0x30, 0x38)]) ∧
    ((padBlock hopperE4M3F32 0x3F800008 (widenE4M3Pairs [(0x30, 0x38)])).bind fun d =>
        padBlock hopperE4M3F32 d []) =
      padBlock hopperE4M3F32 0x3F800008 (widenE4M3Pairs [(0x30, 0x38)]) := by
  decide +kernel

/-! ## One input, four results

`k = 32`, `c = 0`, nonzero products in slots 11, 13 and 21 (counting from 0):
`(−7/16)·(13/256)`, `(−9/4)·(−36)` and `(−96)·128`, values common to E4M3 and E4M3 FNUZ, with exact
sum `−12207.0222…`. Ada sums two block FMAs of 16 (the third product is in the second), Hopper and
Blackwell one of 32. E4M3 words: `0xae = −7/16`, `0x15 = 13/256`, `0xc1 = −9/4`, `0xe1 = −36`,
`0xec = −96`, `0x70 = 128`. -/

/-- The operand pairs of a `k`-long inner product with the given pairs in the given slots and
zero pairs elsewhere. -/
def placePairs (k : ℕ) (xs : List (ℕ × (BitVec 8 × BitVec 8))) : List (BitVec 8 × BitVec 8) :=
  (List.range k).map fun i => (xs.lookup i).getD (0, 0)

/-- **The NVIDIA side of the cross-vendor witness.** Ada returns `−12208`, Hopper `−12207` and
Blackwell `−12207.021484375`; CDNA 3 returns `−12207.0224609375`
(`MMAlgebra.MC.xvendor_cdna3`), the binary32 value nearest the exact sum. -/
theorem xvendor_nvidia :
    adaE4M3F32.dot 0 (widenE4M3Pairs
        (placePairs 32 [(11, (0xae, 0x15)), (13, (0xc1, 0xe1)), (21, (0xec, 0x70))])) =
      some 0xC63EC000 ∧
    hopperE4M3F32.dot 0 (widenE4M3Pairs
        (placePairs 32 [(11, (0xae, 0x15)), (13, (0xc1, 0xe1)), (21, (0xec, 0x70))])) =
      some 0xC63EBC00 ∧
    blackwellE4M3F32.dot 0 (widenE4M3Pairs
        (placePairs 32 [(11, (0xae, 0x15)), (13, (0xc1, 0xe1)), (21, (0xec, 0x70))])) =
      some 0xC63EBC16 := by
  decide +kernel

end MMAlgebra.TC
