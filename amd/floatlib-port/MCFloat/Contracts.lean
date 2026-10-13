import MCFloat.Equivalence

/-! # Contracts of the FloatLib implementation

Matrix-Core's per-model contracts and chaining theorems, stated for the FloatLib
implementation: whenever a FloatLib block or inner product returns a finite word,

* the same input is an accepted Matrix-Core block (or run of blocks) with the same word;
* the word is FloatLib's own `fl{S_acc}` (`MCFloat.fl`), and on SFMA and CDNA 1 FloatLib's own
  round-to-nearest-even of the exact `Σ a_ℓ b_ℓ + c` (`MCFloat.round32`);
* the block satisfies its model's contract (`CorrectRoundingContract`, `PairwiseContract`,
  `AlignedContract`), including the output error bound and the bound from the inputs alone, and
  every block of an inner product does, with the loss accounting and the error bound of the whole
  inner product against the exact `c + Σ_ℓ a_ℓ b_ℓ`;
* the output is monotone in `c`, for blocks and inner products.

Everything is transported through `block_agree` and `dot_agree`. -/

namespace MCFloat.Equivalence

/-- A finite FloatLib binary32 word. -/
def Finite (w : MCFloat.F32) : Prop := ∃ v, MCFloat.classifyModel w = .finite v

theorem observe_finite {w : MCFloat.F32} (hf : Finite w) :
    observe w = .finite (BitVec.ofNat 32 (MCFloat.bits w)) := by
  obtain ⟨v, hv⟩ := hf
  unfold observe
  rw [hv]

theorem toNat_ofNat_bits (w : MCFloat.F32) : (BitVec.ofNat 32 (MCFloat.bits w)).toNat = MCFloat.bits w := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bits_lt w)]

/-- A finite FloatLib block output is an accepted Matrix-Core block with the same word. -/
theorem block_finite {P : MCFloat.MCModel} {Q : MatrixCore.Model} (h : Corresponds P Q)
    {x : MatrixCore.BlockInput Q} {w : MCFloat.F32}
    (hw : MCFloat.block P (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat = some w)
    (hf : Finite w) : ∃ t, MatrixCore.evalBlock x = .ok t ∧ MCFloat.bits w = t.d.toNat := by
  have hb := block_agree h x
  rw [hw, Option.map_some, observe_finite hf] at hb
  have hbits := (MatrixCore.blockOutcome_finite_iff x _).mp hb.symm
  unfold MatrixCore.blockBits at hbits
  cases he : MatrixCore.evalBlock x with
  | error e => rw [he] at hbits; simp [Except.map] at hbits
  | ok t =>
    rw [he] at hbits
    simp only [Except.map, Except.ok.injEq] at hbits
    exact ⟨t, rfl, by rw [hbits, toNat_ofNat_bits]⟩

/-- The FloatLib word is FloatLib's `fl{S_acc}` of the corresponding Matrix-Core block. -/
theorem bits_fl {Q : MatrixCore.Model} {x : MatrixCore.BlockInput Q} {t : MatrixCore.BlockTrace Q}
    (ht : MatrixCore.evalBlock x = .ok t) :
    MCFloat.bits (MCFloat.fl (!Q.subnormals) t.sAcc) = t.d.toNat := by
  rw [fl_bits]
  unfold refWord
  rw [(MatrixCore.evalBlock_contract ht).output]

/-- **Transport.** A finite FloatLib block output satisfies every property `C` of accepted
Matrix-Core blocks, and is FloatLib's `fl{S_acc}`. -/
theorem floatlib_block {P : MCFloat.MCModel} {Q : MatrixCore.Model} (h : Corresponds P Q)
    {C : MatrixCore.BlockInput Q → MatrixCore.BlockTrace Q → Prop} {x : MatrixCore.BlockInput Q}
    (hC : ∀ t, MatrixCore.evalBlock x = .ok t → C x t) {w : MCFloat.F32}
    (hw : MCFloat.block P (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat = some w)
    (hf : Finite w) :
    ∃ t, MatrixCore.evalBlock x = .ok t ∧ MCFloat.bits w = t.d.toNat ∧
      MCFloat.bits w = MCFloat.bits (MCFloat.fl (!Q.subnormals) t.sAcc) ∧ C x t := by
  obtain ⟨t, ht, hb⟩ := block_finite h hw hf
  exact ⟨t, ht, hb, by rw [bits_fl ht, hb], hC t ht⟩

/-- Every model: the block contract. -/
theorem floatlib_contract {P : MCFloat.MCModel} {Q : MatrixCore.Model} (h : Corresponds P Q)
    {x : MatrixCore.BlockInput Q} {w : MCFloat.F32}
    (hw : MCFloat.block P (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat = some w)
    (hf : Finite w) :
    ∃ t, MatrixCore.evalBlock x = .ok t ∧ MCFloat.bits w = t.d.toNat ∧
      MCFloat.bits w = MCFloat.bits (MCFloat.fl (!Q.subnormals) t.sAcc) ∧
      MatrixCore.BlockContract x t :=
  floatlib_block h (fun _ ht => MatrixCore.evalBlock_contract ht) hw hf

/-! ## SFMA and CDNA 1: FloatLib's nearest-even rounding of the exact sum -/

theorem floatlib_correctRounding {P : MCFloat.MCModel} {Q : MatrixCore.Model}
    (h : Corresponds P Q) (hacc : Q.accumulation = .correctRounding)
    (hov : Q.productOverflow = false) (hs : Q.subnormals = true)
    {x : MatrixCore.BlockInput Q} {w : MCFloat.F32}
    (hw : MCFloat.block P (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat = some w)
    (hf : Finite w) :
    ∃ t, MatrixCore.evalBlock x = .ok t ∧ MCFloat.bits w = t.d.toNat ∧
      MCFloat.bits w = MCFloat.bits (MCFloat.round32 t.prepared.exact) ∧
      MatrixCore.CorrectRoundingContract x t := by
  obtain ⟨t, ht, hb, hfl, hc⟩ :=
    floatlib_block h (fun _ ht => MatrixCore.correctRounding_contract hacc hov hs ht) hw hf
  refine ⟨t, ht, hb, ?_, hc⟩
  rw [hfl, hs, ← hc.exact]
  rfl

theorem floatlib_sfma {x : MatrixCore.BlockInput MatrixCore.sfmaF32} {w : MCFloat.F32}
    (hw : MCFloat.block MCFloat.sfma (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat = some w)
    (hf : Finite w) :
    ∃ t, MatrixCore.evalBlock x = .ok t ∧ MCFloat.bits w = t.d.toNat ∧
      MCFloat.bits w = MCFloat.bits (MCFloat.round32 t.prepared.exact) ∧
      MatrixCore.CorrectRoundingContract x t :=
  floatlib_correctRounding sfma rfl rfl rfl hw hf

theorem floatlib_cdna1F16 {x : MatrixCore.BlockInput MatrixCore.cdna1F16} {w : MCFloat.F32}
    (hw : MCFloat.block MCFloat.cdna1F16 (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat =
      some w) (hf : Finite w) :
    ∃ t, MatrixCore.evalBlock x = .ok t ∧ MCFloat.bits w = t.d.toNat ∧
      MCFloat.bits w = MCFloat.bits (MCFloat.round32 t.prepared.exact) ∧
      MatrixCore.CorrectRoundingContract x t :=
  floatlib_correctRounding cdna1F16 rfl rfl rfl hw hf

theorem floatlib_cdna1BF16 {x : MatrixCore.BlockInput MatrixCore.cdna1BF16} {w : MCFloat.F32}
    (hw : MCFloat.block MCFloat.cdna1BF16 (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat =
      some w) (hf : Finite w) :
    ∃ t, MatrixCore.evalBlock x = .ok t ∧ MCFloat.bits w = t.d.toNat ∧
      MCFloat.bits w = MCFloat.bits (MCFloat.round32 t.prepared.exact) ∧
      MatrixCore.CorrectRoundingContract x t :=
  floatlib_correctRounding cdna1BF16 rfl rfl rfl hw hf

/-! ## CDNA 2 -/

theorem floatlib_cdna2F16 {x : MatrixCore.BlockInput MatrixCore.cdna2F16} {w : MCFloat.F32}
    (hw : MCFloat.block MCFloat.cdna2F16 (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat =
      some w) (hf : Finite w) :
    ∃ t, MatrixCore.evalBlock x = .ok t ∧ MCFloat.bits w = t.d.toNat ∧
      MCFloat.bits w = MCFloat.bits (MCFloat.fl true t.sAcc) ∧ MatrixCore.PairwiseContract x t :=
  floatlib_block cdna2F16 (fun _ ht => MatrixCore.cdna2F16_contract ht) hw hf

theorem floatlib_cdna2BF16 {x : MatrixCore.BlockInput MatrixCore.cdna2BF16} {w : MCFloat.F32}
    (hw : MCFloat.block MCFloat.cdna2BF16 (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat =
      some w) (hf : Finite w) :
    ∃ t, MatrixCore.evalBlock x = .ok t ∧ MCFloat.bits w = t.d.toNat ∧
      MCFloat.bits w = MCFloat.bits (MCFloat.fl true t.sAcc) ∧ MatrixCore.PairwiseContract x t :=
  floatlib_block cdna2BF16 (fun _ ht => MatrixCore.cdna2BF16_contract ht) hw hf

theorem floatlib_cdna2BF16_1k {x : MatrixCore.BlockInput MatrixCore.cdna2BF16_1k} {w : MCFloat.F32}
    (hw : MCFloat.block MCFloat.cdna2BF16_1k (x.a.map BitVec.toNat) (x.b.map BitVec.toNat)
      x.c.toNat = some w) (hf : Finite w) :
    ∃ t, MatrixCore.evalBlock x = .ok t ∧ MCFloat.bits w = t.d.toNat ∧
      MCFloat.bits w = MCFloat.bits (MCFloat.fl true t.sAcc) ∧ MatrixCore.PairwiseContract x t :=
  floatlib_block cdna2BF16_1k (fun _ ht => MatrixCore.cdna2BF16_1k_contract ht) hw hf

/-! ## CDNA 3 -/

theorem floatlib_cdna3F16 {x : MatrixCore.BlockInput MatrixCore.cdna3F16} {w : MCFloat.F32}
    (hw : MCFloat.block MCFloat.cdna3F16 (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat =
      some w) (hf : Finite w) :
    ∃ t, MatrixCore.evalBlock x = .ok t ∧ MCFloat.bits w = t.d.toNat ∧
      MCFloat.bits w = MCFloat.bits (MCFloat.fl false t.sAcc) ∧ MatrixCore.AlignedContract x t 30 :=
  floatlib_block (C := fun x t => MatrixCore.AlignedContract x t 30) cdna3F16
    (fun _ ht => MatrixCore.cdna3F16_contract ht) hw hf

theorem floatlib_cdna3BF16 {x : MatrixCore.BlockInput MatrixCore.cdna3BF16} {w : MCFloat.F32}
    (hw : MCFloat.block MCFloat.cdna3BF16 (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat =
      some w) (hf : Finite w) :
    ∃ t, MatrixCore.evalBlock x = .ok t ∧ MCFloat.bits w = t.d.toNat ∧
      MCFloat.bits w = MCFloat.bits (MCFloat.fl false t.sAcc) ∧ MatrixCore.AlignedContract x t 30 :=
  floatlib_block (C := fun x t => MatrixCore.AlignedContract x t 30) cdna3BF16
    (fun _ ht => MatrixCore.cdna3BF16_contract ht) hw hf

theorem floatlib_cdna3XF32 {x : MatrixCore.BlockInput MatrixCore.cdna3XF32} {w : MCFloat.F32}
    (hw : MCFloat.block MCFloat.cdna3XF32 (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat =
      some w) (hf : Finite w) :
    ∃ t, MatrixCore.evalBlock x = .ok t ∧ MCFloat.bits w = t.d.toNat ∧
      MCFloat.bits w = MCFloat.bits (MCFloat.fl false t.sAcc) ∧ MatrixCore.AlignedContract x t 29 :=
  floatlib_block (C := fun x t => MatrixCore.AlignedContract x t 29) cdna3XF32
    (fun _ ht => MatrixCore.cdna3XF32_contract ht) hw hf

/-- CDNA 3 binary8, for any corresponding fp8 operand formats. -/
theorem floatlib_cdna3FP8 {a b : FloatLib.Floats.Formats.BinaryInterchange.FloatFormat}
    {fa fb : MatrixCore.Format} (ha : OperandAgree (.fmt a) (.packed fa))
    (hb : OperandAgree (.fmt b) (.packed fb)) {x : MatrixCore.BlockInput (MatrixCore.cdna3FP8 fa fb)}
    {w : MCFloat.F32}
    (hw : MCFloat.block (MCFloat.cdna3FP8 a b) (x.a.map BitVec.toNat) (x.b.map BitVec.toNat)
      x.c.toNat = some w) (hf : Finite w) :
    ∃ t, MatrixCore.evalBlock x = .ok t ∧ MCFloat.bits w = t.d.toNat ∧
      MCFloat.bits w = MCFloat.bits (MCFloat.fl false t.sAcc) ∧ MatrixCore.AlignedContract x t 31 :=
  floatlib_block (C := fun x t => MatrixCore.AlignedContract x t 31) (cdna3FP8 ha hb)
    (fun _ ht => MatrixCore.cdna3FP8_contract fa fb ht) hw hf

/-! ## Inner products -/

/-- **Chaining.** A finite FloatLib inner product is a run of linked, accepted Matrix-Core blocks
ending in the same word; every block satisfies any property `C` of accepted blocks (such as the
model's contract), and the initial `c` plus every block's products equal the output plus every
block's residual. -/
theorem floatlib_dot_blocks {P : MCFloat.MCModel} {Q : MatrixCore.Model} (h : Corresponds P Q)
    {C : MatrixCore.BlockInput Q → MatrixCore.BlockTrace Q → Prop}
    (hC : ∀ x t, MatrixCore.evalBlock x = .ok t → C x t)
    {a : List Q.a.Word} {b : List Q.b.Word} {c : MatrixCore.F32} {w : MCFloat.F32}
    (hw : MCFloat.dot P (a.map BitVec.toNat) (b.map BitVec.toNat) c.toNat = some w)
    (hf : Finite w) :
    ∃ ts, MatrixCore.runBlocks Q c (MatrixCore.blocks Q a b) = .ok ts ∧
      MCFloat.bits w = (MatrixCore.lastOutput c ts).toNat ∧ MatrixCore.Chain c ts ∧
      (∀ t ∈ ts, ∃ x, C x t) ∧
      MatrixCore.wordValue c + MatrixCore.sumQ (ts.map fun t => t.prepared.products) =
        MatrixCore.wordValue (MatrixCore.lastOutput c ts) +
          MatrixCore.sumQ (ts.map MatrixCore.BlockTrace.residual) := by
  have hd := dot_agree h a b c
  rw [hw, Option.map_some, observe_finite hf] at hd
  obtain ⟨hlen, hbits⟩ := MatrixCore.dotOutcome_finite Q hd.symm
  obtain ⟨ts, hr, hl, hc, hall, hledger⟩ := MatrixCore.dotBits_blocks Q hC hlen hbits
  refine ⟨ts, hr, by rw [hl, toNat_ofNat_bits], hc, hall, by rw [hl]; exact hledger⟩

/-- Every block of a finite FloatLib inner product satisfies the block contract. -/
theorem floatlib_dot_contract {P : MCFloat.MCModel} {Q : MatrixCore.Model} (h : Corresponds P Q)
    {a : List Q.a.Word} {b : List Q.b.Word} {c : MatrixCore.F32} {w : MCFloat.F32}
    (hw : MCFloat.dot P (a.map BitVec.toNat) (b.map BitVec.toNat) c.toNat = some w)
    (hf : Finite w) :
    ∃ ts, MatrixCore.runBlocks Q c (MatrixCore.blocks Q a b) = .ok ts ∧
      MCFloat.bits w = (MatrixCore.lastOutput c ts).toNat ∧ MatrixCore.Chain c ts ∧
      ∀ t ∈ ts, ∃ x, MatrixCore.BlockContract x t := by
  obtain ⟨ts, hr, hl, hc, hall, _⟩ :=
    floatlib_dot_blocks h (fun _ _ ht => MatrixCore.evalBlock_contract ht) hw hf
  exact ⟨ts, hr, hl, hc, hall⟩

/-- **Error of a FloatLib inner product.** If every accepted block's residual `exact − d` is
bounded by `B` (for example by the `error` field of the model's contract), a finite FloatLib inner
product is within the sum of the blocks' bounds of the initial `c` plus all products. -/
theorem floatlib_dot_error {P : MCFloat.MCModel} {Q : MatrixCore.Model} (h : Corresponds P Q)
    {B : MatrixCore.BlockTrace Q → ℚ}
    (hB : ∀ x t, MatrixCore.evalBlock x = .ok t → MatrixCore.absQ t.residual ≤ B t)
    {a : List Q.a.Word} {b : List Q.b.Word} {c : MatrixCore.F32} {w : MCFloat.F32}
    (hw : MCFloat.dot P (a.map BitVec.toNat) (b.map BitVec.toNat) c.toNat = some w)
    (hf : Finite w) :
    ∃ ts, MatrixCore.runBlocks Q c (MatrixCore.blocks Q a b) = .ok ts ∧
      MCFloat.bits w = (MatrixCore.lastOutput c ts).toNat ∧
      MatrixCore.absQ (MatrixCore.wordValue c + MatrixCore.sumQ (ts.map fun t => t.prepared.products) -
        MatrixCore.wordValue (MatrixCore.lastOutput c ts)) ≤ MatrixCore.sumQ (ts.map B) := by
  have hd := dot_agree h a b c
  rw [hw, Option.map_some, observe_finite hf] at hd
  obtain ⟨hlen, hbits⟩ := MatrixCore.dotOutcome_finite Q hd.symm
  obtain ⟨ts, hr, hl, he⟩ := MatrixCore.dotBits_error_bound Q hB hlen hbits
  exact ⟨ts, hr, by rw [hl, toNat_ofNat_bits], by rw [hl]; exact he⟩

theorem ofNat_bits_eq {w : MCFloat.F32} {d : MatrixCore.F32} (h : MCFloat.bits w = d.toNat) :
    BitVec.ofNat 32 (MCFloat.bits w) = d := by
  apply BitVec.eq_of_toNat_eq; rw [toNat_ofNat_bits, h]

/-! ## Monotonicity in `c` -/

/-- **Monotonicity.** For the same `a` and `b`, a FloatLib block never returns a smaller finite
value for a larger `c`, on every configuration of the paper. -/
theorem floatlib_c_monotone {P : MCFloat.MCModel} {Q : MatrixCore.Model} (h : Corresponds P Q)
    (hQ : MatrixCore.MonotoneModel Q) {a : List Q.a.Word} {b : List Q.b.Word} {c c' : MatrixCore.F32}
    {w w' : MCFloat.F32}
    (hw : MCFloat.block P (a.map BitVec.toNat) (b.map BitVec.toNat) c.toNat = some w)
    (hw' : MCFloat.block P (a.map BitVec.toNat) (b.map BitVec.toNat) c'.toNat = some w')
    (hf : Finite w) (hf' : Finite w') (hc : MatrixCore.wordValue c ≤ MatrixCore.wordValue c') :
    MatrixCore.wordValue (BitVec.ofNat 32 (MCFloat.bits w)) ≤
      MatrixCore.wordValue (BitVec.ofNat 32 (MCFloat.bits w')) := by
  obtain ⟨t, ht, hb⟩ := block_finite (x := ⟨a, b, c⟩) h hw hf
  obtain ⟨t', ht', hb'⟩ := block_finite (x := ⟨a, b, c'⟩) h hw' hf'
  rw [ofNat_bits_eq hb, ofNat_bits_eq hb']
  exact MatrixCore.evalBlock_c_monotone hQ ht ht' hc

/-- The same for inner products of any length. -/
theorem floatlib_dot_c_monotone {P : MCFloat.MCModel} {Q : MatrixCore.Model} (h : Corresponds P Q)
    (hQ : MatrixCore.MonotoneModel Q) {a : List Q.a.Word} {b : List Q.b.Word}
    {c c' : MatrixCore.F32} {w w' : MCFloat.F32}
    (hw : MCFloat.dot P (a.map BitVec.toNat) (b.map BitVec.toNat) c.toNat = some w)
    (hw' : MCFloat.dot P (a.map BitVec.toNat) (b.map BitVec.toNat) c'.toNat = some w')
    (hf : Finite w) (hf' : Finite w') (hc : MatrixCore.wordValue c ≤ MatrixCore.wordValue c') :
    MatrixCore.wordValue (BitVec.ofNat 32 (MCFloat.bits w)) ≤
      MatrixCore.wordValue (BitVec.ofNat 32 (MCFloat.bits w')) := by
  have hd := dot_agree h a b c
  rw [hw, Option.map_some, observe_finite hf] at hd
  have hd' := dot_agree h a b c'
  rw [hw', Option.map_some, observe_finite hf'] at hd'
  obtain ⟨hlen, hb⟩ := MatrixCore.dotOutcome_finite Q hd.symm
  obtain ⟨_, hb'⟩ := MatrixCore.dotOutcome_finite Q hd'.symm
  exact MatrixCore.dotBits_c_monotone hQ hlen hb hb' hc

/-- SFMA and CDNA 1: the FloatLib output is monotone in the exact `Σ a_ℓ b_ℓ + c`. -/
theorem floatlib_correctRounding_monotone {P : MCFloat.MCModel} {Q : MatrixCore.Model}
    (h : Corresponds P Q) (hacc : Q.accumulation = .correctRounding)
    (hov : Q.productOverflow = false) (hs : Q.subnormals = true)
    {x x' : MatrixCore.BlockInput Q} {w w' : MCFloat.F32}
    (hw : MCFloat.block P (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat = some w)
    (hw' : MCFloat.block P (x'.a.map BitVec.toNat) (x'.b.map BitVec.toNat) x'.c.toNat = some w')
    (hf : Finite w) (hf' : Finite w')
    (he : MatrixCore.exactDot Q x.a x.b x.c ≤ MatrixCore.exactDot Q x'.a x'.b x'.c) :
    MatrixCore.wordValue (BitVec.ofNat 32 (MCFloat.bits w)) ≤
      MatrixCore.wordValue (BitVec.ofNat 32 (MCFloat.bits w')) := by
  obtain ⟨t, ht, hb⟩ := block_finite h hw hf
  obtain ⟨t', ht', hb'⟩ := block_finite h hw' hf'
  rw [ofNat_bits_eq hb, ofNat_bits_eq hb']
  exact MatrixCore.correctRounding_exact_monotone hacc hov hs ht ht' he

/-- A Matrix-Core non-monotone pair is one for the FloatLib implementation: the FloatLib blocks
return the same words, the larger products giving the smaller output. -/
theorem floatlib_nonmonotone {P : MCFloat.MCModel} {Q : MatrixCore.Model} (h : Corresponds P Q)
    {x x' : MatrixCore.BlockInput Q} (hn : MatrixCore.ProductNonmonotone x x') :
    ∃ w w', MCFloat.block P (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat = some w ∧
      MCFloat.block P (x'.a.map BitVec.toNat) (x'.b.map BitVec.toNat) x'.c.toNat = some w' ∧
      MatrixCore.wordValue (BitVec.ofNat 32 (MCFloat.bits w')) <
        MatrixCore.wordValue (BitVec.ofNat 32 (MCFloat.bits w)) := by
  obtain ⟨_, _, d, d', hd, hd', hlt⟩ := hn
  obtain ⟨w, hw, hb⟩ := blockBits_agree h x d hd
  obtain ⟨w', hw', hb'⟩ := blockBits_agree h x' d' hd'
  exact ⟨w, w', hw, hw', by rw [ofNat_bits_eq hb, ofNat_bits_eq hb']; exact hlt⟩

/-! ## The exact inner product -/

/-- **Error of a FloatLib inner product against the exact `c + Σ_ℓ a_ℓ b_ℓ`.** -/
theorem floatlib_dot_exact_error {P : MCFloat.MCModel} {Q : MatrixCore.Model} (h : Corresponds P Q)
    (hn : 0 < Q.nfma) {B : MatrixCore.BlockTrace Q → ℚ}
    (hB : ∀ x t, MatrixCore.evalBlock x = .ok t → MatrixCore.absQ t.residual ≤ B t)
    {a : List Q.a.Word} {b : List Q.b.Word} {c : MatrixCore.F32} {w : MCFloat.F32}
    (hw : MCFloat.dot P (a.map BitVec.toNat) (b.map BitVec.toNat) c.toNat = some w)
    (hf : Finite w) :
    ∃ ts, MatrixCore.runBlocks Q c (MatrixCore.blocks Q a b) = .ok ts ∧
      MatrixCore.absQ (MatrixCore.exactDot Q a b c -
        MatrixCore.wordValue (BitVec.ofNat 32 (MCFloat.bits w))) ≤ MatrixCore.sumQ (ts.map B) := by
  have hd := dot_agree h a b c
  rw [hw, Option.map_some, observe_finite hf] at hd
  obtain ⟨hlen, hbits⟩ := MatrixCore.dotOutcome_finite Q hd.symm
  obtain ⟨ts, hr, _, he⟩ := MatrixCore.dotBits_exact_error Q hn hB hlen hbits
  exact ⟨ts, hr, he⟩

end MCFloat.Equivalence
