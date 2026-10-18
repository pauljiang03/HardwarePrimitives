import MCFloat.Equivalence.Dot

/-! # FloatLib implementation ≡ Matrix-Core

Every MCFloat model corresponds to the Matrix-Core model of the same name, so for every
architecture and input format of the paper:

* `block_agree`: one block observes as `blockOutcome` for any input words;
* `dot_agree`: an inner product of any length observes as `dotOutcome`;
* `blockBits_agree`: where Matrix-Core's finite-domain `blockBits` returns a word, the FloatLib
  block returns the same word.

The proofs use only Lean's standard axioms (`tests/Audit.lean`). -/

namespace MCFloat.Equivalence

theorem rules_of {P : MCFloat.MCModel} {Q : MatrixCore.Model}
    (hl : P.productLimit = Q.productOverflow)
    (hp : P.kind = .pairwise ↔ Q.accumulation = .pairWiseSum)
    (hs : Q.accumulation = .pairWiseSum → Q.subnormals = false) : ProductRules P Q :=
  ⟨hl, hp, hs⟩

theorem sfma : Corresponds MCFloat.sfma MatrixCore.sfmaF32 :=
  ⟨operand_fp32, operand_fp32, rfl,
    rules_of rfl (by simp [MCFloat.sfma, MatrixCore.sfmaF32]) (by simp [MatrixCore.sfmaF32]),
    rfl, rfl, ⟨rfl, rfl⟩⟩

theorem cdna1F16 : Corresponds MCFloat.cdna1F16 MatrixCore.cdna1F16 :=
  ⟨operand_fp16, operand_fp16, rfl,
    rules_of rfl (by simp [MCFloat.cdna1F16, MatrixCore.cdna1F16]) (by simp [MatrixCore.cdna1F16]),
    rfl, rfl, ⟨rfl, rfl⟩⟩

theorem cdna1BF16 : Corresponds MCFloat.cdna1BF16 MatrixCore.cdna1BF16 :=
  ⟨operand_bf16, operand_bf16, rfl,
    rules_of rfl (by simp [MCFloat.cdna1BF16, MatrixCore.cdna1BF16]) (by simp [MatrixCore.cdna1BF16]),
    rfl, rfl, ⟨rfl, rfl⟩⟩

theorem cdna2F16 : Corresponds MCFloat.cdna2F16 MatrixCore.cdna2F16 :=
  ⟨operand_fp16, operand_fp16, rfl,
    rules_of rfl (by simp [MCFloat.cdna2F16, MatrixCore.cdna2F16]) (fun _ => rfl),
    rfl, rfl, ⟨rfl, rfl⟩⟩

theorem cdna2BF16 : Corresponds MCFloat.cdna2BF16 MatrixCore.cdna2BF16 :=
  ⟨operand_bf16, operand_bf16, rfl,
    rules_of rfl (by simp [MCFloat.cdna2BF16, MatrixCore.cdna2BF16]) (fun _ => rfl),
    rfl, rfl, ⟨rfl, rfl⟩⟩

theorem cdna2BF16_1k : Corresponds MCFloat.cdna2BF16_1k MatrixCore.cdna2BF16_1k :=
  ⟨operand_bf16, operand_bf16, rfl,
    rules_of rfl (by simp [MCFloat.cdna2BF16_1k, MatrixCore.cdna2BF16_1k]) (fun _ => rfl),
    rfl, rfl, ⟨rfl, rfl⟩⟩

theorem cdna3F16 : Corresponds MCFloat.cdna3F16 MatrixCore.cdna3F16 :=
  ⟨operand_fp16, operand_fp16, rfl,
    rules_of rfl (by simp [MCFloat.cdna3F16, MatrixCore.cdna3F16]) (by simp [MatrixCore.cdna3F16]),
    rfl, rfl, ⟨rfl, rfl, rfl⟩⟩

theorem cdna3BF16 : Corresponds MCFloat.cdna3BF16 MatrixCore.cdna3BF16 :=
  ⟨operand_bf16, operand_bf16, rfl,
    rules_of rfl (by simp [MCFloat.cdna3BF16, MatrixCore.cdna3BF16]) (by simp [MatrixCore.cdna3BF16]),
    rfl, rfl, ⟨rfl, rfl, rfl⟩⟩

theorem cdna3XF32 : Corresponds MCFloat.cdna3XF32 MatrixCore.cdna3XF32 :=
  ⟨operand_xf32, operand_xf32, rfl,
    rules_of rfl (by simp [MCFloat.cdna3XF32, MatrixCore.cdna3XF32]) (by simp [MatrixCore.cdna3XF32]),
    rfl, rfl, ⟨rfl, rfl, rfl⟩⟩

/-- CDNA 3 binary8 for any combination of corresponding fp8 operand formats. -/
theorem cdna3FP8 {a b : FloatLib.Floats.Formats.BinaryInterchange.FloatFormat}
    {fa fb : MatrixCore.Format} (ha : OperandAgree (.fmt a) (.packed fa))
    (hb : OperandAgree (.fmt b) (.packed fb)) :
    Corresponds (MCFloat.cdna3FP8 a b) (MatrixCore.cdna3FP8 fa fb) :=
  ⟨ha, hb, rfl,
    rules_of rfl (by simp [MCFloat.cdna3FP8, MatrixCore.cdna3FP8]) (by simp [MatrixCore.cdna3FP8]),
    rfl, rfl, ⟨rfl, rfl, rfl⟩⟩

theorem cdna3E4M3 : Corresponds (MCFloat.cdna3FP8 .e4m3fnuz .e4m3fnuz)
    (MatrixCore.cdna3FP8 MatrixCore.e4m3fnuz MatrixCore.e4m3fnuz) :=
  cdna3FP8 operand_e4m3fnuz operand_e4m3fnuz
theorem cdna3E5M2 : Corresponds (MCFloat.cdna3FP8 .e5m2fnuz .e5m2fnuz)
    (MatrixCore.cdna3FP8 MatrixCore.e5m2fnuz MatrixCore.e5m2fnuz) :=
  cdna3FP8 operand_e5m2fnuz operand_e5m2fnuz
theorem cdna3E4M3E5M2 : Corresponds (MCFloat.cdna3FP8 .e4m3fnuz .e5m2fnuz)
    (MatrixCore.cdna3FP8 MatrixCore.e4m3fnuz MatrixCore.e5m2fnuz) :=
  cdna3FP8 operand_e4m3fnuz operand_e5m2fnuz
theorem cdna3E5M2E4M3 : Corresponds (MCFloat.cdna3FP8 .e5m2fnuz .e4m3fnuz)
    (MatrixCore.cdna3FP8 MatrixCore.e5m2fnuz MatrixCore.e4m3fnuz) :=
  cdna3FP8 operand_e5m2fnuz operand_e4m3fnuz

/-- On Matrix-Core's finite domain the FloatLib block returns the same binary32 word. -/
theorem blockBits_agree {P : MCFloat.MCModel} {Q : MatrixCore.Model} (h : Corresponds P Q)
    (x : MatrixCore.BlockInput Q) (d : MatrixCore.F32) (hd : MatrixCore.blockBits x = .ok d) :
    ∃ w, MCFloat.block P (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat = some w ∧
      MCFloat.bits w = d.toNat := by
  have hb := block_agree h x
  rw [(MatrixCore.blockOutcome_finite_iff x d).mpr hd] at hb
  cases hk : MCFloat.block P (x.a.map BitVec.toNat) (x.b.map BitVec.toNat) x.c.toNat with
  | none => rw [hk] at hb; simp at hb
  | some w =>
    rw [hk] at hb
    simp only [Option.map_some, Option.some.injEq, observe] at hb
    refine ⟨w, rfl, ?_⟩
    split at hb <;> simp at hb
    rw [← hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (bits_lt w)]

end MCFloat.Equivalence
