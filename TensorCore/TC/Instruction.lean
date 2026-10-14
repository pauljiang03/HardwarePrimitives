import TensorCore.Numerics.RoundTrip
import TensorCore.TC.CanonicalEAlignMin
import TensorCore.TC.Monotonicity
import TensorCore.TC.Composition

/-! Instruction variants. -/

namespace TensorCore

/-- `m` consecutive groups of `n` elements. -/
def chunks (n : ℕ) : ℕ → List α → List (List α)
  | 0, _ => []
  | m + 1, xs => xs.take n :: chunks n m (xs.drop n)

theorem chunks_flatten (n m : ℕ) (xs : List α) (h : xs.length = m * n) :
    (chunks n m xs).flatten = xs := by
  induction m generalizing xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by simpa using h)
    subst hx
    rfl
  | succ m ih =>
    simp only [chunks, List.flatten_cons]
    rw [Nat.succ_mul] at h
    rw [ih (xs.drop n) (by simp only [List.length_drop]; omega)]
    exact List.take_append_drop n xs

theorem chunks_first_group (n m : ℕ) (g rest : List α) (hg : g.length = n) :
    chunks n (m + 1) (g ++ rest) = g :: chunks n m rest := by
  simp only [chunks]
  rw [← hg, List.take_left, List.drop_left]

theorem chunks_replicate (n m : ℕ) (a : α) :
    chunks n m (List.replicate (m * n) a) = List.replicate m (List.replicate n a) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [chunks, List.take_replicate, List.drop_replicate, List.replicate_succ]
    rw [Nat.succ_mul]
    have h1 : min n (m * n + n) = n := by omega
    have h2 : m * n + n - n = m * n := by omega
    rw [h1, h2, ih]

theorem lastOutput_bits (initial : Finite32) (ts : List BlockTrace) :
    ((ts.getLast?.map fun t => t.output.bits).getD initial.bits) =
      (lastOutput initial ts).bits := by
  induction ts generalizing initial with
  | nil => rfl
  | cons t ts ih =>
    cases ts with
    | nil => rfl
    | cons u us => exact ih t.output

theorem getD_of_cons (f : α → β) (u : α) (us : List α) (d₁ d₂ : β) :
    (((u :: us).getLast?).map f).getD d₁ = (((u :: us).getLast?).map f).getD d₂ := by
  induction us generalizing u with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.getLast?_cons_cons]
    exact ih v

theorem finite32_self (f : Finite32) : finite32 f.bits = some f := by
  unfold finite32
  split
  · rename_i h; rw [f.valid] at h; contradiction
  · rename_i d h; rw [f.valid] at h; cases Option.some.inj h; rfl

theorem finite32_bits {c : F32} {initial : Finite32} (h : finite32 c = some initial) :
    initial.bits = c := by
  unfold finite32 at h
  split at h
  · contradiction
  · cases Option.some.inj h; rfl

/-- The bits of a finite encoding of value zero, other than `−0`, are `0`. -/
theorem zero_value_bits (c : F32) (d : Decoded) (hd : decode32 c = some d)
    (hz : d.significand = 0) (hneg : c ≠ 0x80000000) : c = 0 := by
  have hlt := c.isLt
  rcases decode32_fields c d hd with ⟨hE, hm, rfl⟩ | ⟨_, hm, rfl⟩ | ⟨_, _, rfl⟩
  · apply BitVec.eq_of_toNat_eq
    have hq : c.toNat / 2147483648 = 0 ∨ c.toNat / 2147483648 = 1 := by omega
    rcases hq with hq | hq
    · show c.toNat = 0
      omega
    · exfalso
      apply hneg
      apply BitVec.eq_of_toNat_eq
      show c.toNat = 2147483648
      omega
  · exfalso
    try dsimp only at hz
    split at hz <;> omega
  · exfalso
    try dsimp only at hz
    split at hz <;> omega

theorem Decoded.value_ne_zero (d : Decoded) (h : d.significand ≠ 0) : d.value ≠ 0 := by
  intro h0
  unfold Decoded.value at h0
  have hq := pow2_pos (d.exponent - d.mantissaBits)
  have hne := Rat.ne_of_gt hq
  have h1 : (d.significand : ℚ) = ((0 : ℤ) : ℚ) := by
    rw [Rat.intCast_zero]
    calc (d.significand : ℚ) = (d.significand : ℚ) * pow2 (d.exponent - d.mantissaBits) /
          pow2 (d.exponent - d.mantissaBits) := (Rat.mul_div_cancel hne).symm
      _ = 0 / pow2 (d.exponent - d.mantissaBits) := by rw [h0]
      _ = 0 := by rw [Rat.div_def, Rat.zero_mul]
  exact h (Rat.intCast_inj.mp h1)

/-- With only zero products, the alignment exponent is the accumulator input's exponent, whenever the minimum alignment exponent is at most `−126`. -/
theorem zero_products_alignExp (K padding : ℕ) (eAlignMin : Option ℤ) (hfl : ∀ f ∈ eAlignMin, f ≤ -126)
    (c : Decoded) (hc : c.significand ≠ 0) (hlow : -126 ≤ c.exponent) :
    (PreparedBlock.mk (fp16Fp32Model K padding eAlignMin)
      (List.replicate K (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) c).alignExp = some c.exponent := by
  have hterms : (PreparedBlock.mk (fp16Fp32Model K padding eAlignMin)
      (List.replicate K (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) c).terms =
      ⟨c.significand, c.exponent, c.mantissaBits⟩ :: List.replicate K ⟨0, 0, 0⟩ := by
    simp [PreparedBlock.terms, List.map_replicate, denormalizedMul]
  have hmem : (⟨c.significand, c.exponent, c.mantissaBits⟩ : DenormalizedProduct) ∈
      (PreparedBlock.mk (fp16Fp32Model K padding eAlignMin)
        (List.replicate K (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) c).terms := by
    rw [hterms]; simp
  obtain ⟨e, he, hle⟩ := maxTermExp_term _ _ hmem hc
  have hle' : c.exponent ≤ e := hle
  have hup := maxTermExp_upper (PreparedBlock.mk (fp16Fp32Model K padding eAlignMin)
      (List.replicate K (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) c).terms c.exponent (by
        intro t ht hnz
        rw [hterms] at ht
        simp only [List.mem_cons, List.mem_replicate] at ht
        rcases ht with rfl | ⟨_, rfl⟩
        · exact Int.le_refl _
        · exact absurd rfl hnz) e (by rw [he]; simp)
  have heq : e = c.exponent := by omega
  subst heq
  unfold PreparedBlock.alignExp
  rw [he]
  unfold Model.applyEAlignMin
  have heAlignMin : (fp16Fp32Model K padding eAlignMin).eAlignMin = eAlignMin := rfl
  simp only [heAlignMin]
  cases hf : eAlignMin with
  | none => rfl
  | some f =>
    have := hfl f (by rw [hf]; simp)
    simp [Int.max_eq_left (by omega : f ≤ c.exponent)]

/-- A block FMA whose products are all zero pairs returns its accumulator input unchanged, for every finite input other than `−0`. -/
theorem zero_products_passthrough (K padding : ℕ) (eAlignMin : Option ℤ)
    (hfl : ∀ f ∈ eAlignMin, f ≤ -126) (c : F32) (f : Finite32) (hf : finite32 c = some f)
    (hneg : c ≠ 0x80000000) :
    ∃ t : BlockTrace,
      evalBlock (⟨List.replicate K (0, 0), c⟩ : BlockInput (fp16Fp32Model K padding eAlignMin)) =
        .ok t ∧ t.output.bits = c := by
  have hbits := finite32_bits hf
  have hc : decode32 c = some f.decoded := by rw [← hbits]; exact f.valid
  have hz : (fp16Fp32Model K padding eAlignMin).decode 0 = some ⟨0, 0, 0⟩ := by
    show (classify fp16 0).finite = some _
    decide +kernel
  have hps := prepareProducts_replicate (fp16Fp32Model K padding eAlignMin) 0 0 ⟨0, 0, 0⟩ ⟨0, 0, 0⟩
    K hz hz
  have hlen : ¬ ((List.replicate K ((0 : F16), (0 : F16))).length !=
      (fp16Fp32Model K padding eAlignMin).nfma) = true := by simp [fp16Fp32Model]
  have hcoef := construction_alignedBits (fp16Fp32Model K padding eAlignMin) K ⟨0, 0, 0⟩ ⟨0, 0, 0⟩
    f.decoded
  have hprod : ∀ q : ℤ, truncBits (denormalizedMul ⟨0, 0, 0⟩ ⟨0, 0, 0⟩).value q = 0 := by
    intro q
    simp [denormalizedMul, DenormalizedProduct.value, truncBits, Rat.div_def]
    all_goals decide +kernel
  have hacc : (PreparedBlock.mk (fp16Fp32Model K padding eAlignMin)
      (List.replicate K (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) f.decoded).accumulator = f.value := by
    by_cases hsig : f.decoded.significand = 0
    · have hv : f.decoded.value = 0 := by simp [Decoded.value, hsig]
      have hcz : ∀ q : ℤ, truncBits f.decoded.value q = 0 := by
        intro q; rw [hv]; simp [truncBits, Rat.div_def]
        all_goals decide +kernel
      unfold PreparedBlock.accumulator
      rw [hcoef]
      simp only [sumZ, hcz, hprod, sumZ_replicate, Int.mul_zero, Int.add_zero]
      unfold Finite32.value
      rw [hv]
      simp
    · obtain ⟨hmant, hlow⟩ : f.decoded.mantissaBits = 23 ∧ -126 ≤ f.decoded.exponent := by
        rcases decode32_fields c f.decoded hc with ⟨_, _, h0⟩ | ⟨_, _, h0⟩ | ⟨hE1, _, h0⟩
        · rw [h0] at hsig; exact absurd rfl hsig
        · rw [h0]; exact ⟨rfl, Int.le_refl _⟩
        · rw [h0]; exact ⟨rfl, by simp; omega⟩
      have heta := zero_products_alignExp K padding eAlignMin hfl f.decoded hsig hlow
      have hq : (PreparedBlock.mk (fp16Fp32Model K padding eAlignMin)
          (List.replicate K (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) f.decoded).alignGridExponent =
          f.decoded.exponent - ((23 + padding : ℕ) : ℤ) := by
        unfold PreparedBlock.alignGridExponent
        rw [heta]
        rfl
      rw [hq] at hcoef
      have hcval : f.decoded.value =
          ((f.decoded.significand * ((2 ^ padding : ℕ) : ℤ) : ℤ) : ℚ) *
            pow2 (f.decoded.exponent - ((23 + padding : ℕ) : ℤ)) := by
        unfold Decoded.value
        rw [hmant, Rat.intCast_mul, Rat.intCast_natCast, ← pow2_natCast, Rat.mul_assoc, ← pow2_add]
        congr 2
        omega
      have hcc : truncBits f.decoded.value (f.decoded.exponent - ((23 + padding : ℕ) : ℤ)) =
          f.decoded.significand * ((2 ^ padding : ℕ) : ℤ) := by
        rw [hcval, truncBits_of_grid]
      unfold PreparedBlock.accumulator
      rw [hcoef, hq]
      simp only [sumZ, hcc, hprod, sumZ_replicate, Int.mul_zero, Int.add_zero]
      rw [← hcval]
      rfl
  have hrun : evalPrepared (PreparedBlock.mk (fp16Fp32Model K padding eAlignMin)
      (List.replicate K (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) f.decoded) =
      .ok ⟨PreparedBlock.mk (fp16Fp32Model K padding eAlignMin)
        (List.replicate K (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) f.decoded, f⟩ := by
    by_cases hsig : f.decoded.significand = 0
    · have hc0 : c = 0 := zero_value_bits c f.decoded hc hsig hneg
      have hv : f.value = 0 := by simp [Finite32.value, Decoded.value, hsig]
      have hr : round32 .truncate 0 = some (0 : F32) := by decide +kernel
      have hf0 : finite32 (0 : F32) = some f := by rw [← hc0]; exact hf
      simp only [evalPrepared, hacc, hv, hr, fp16Fp32Model_outputMantissaBits, truncateMantissa32_23, hf0]
    · have hv : f.value ≠ 0 := Decoded.value_ne_zero f.decoded hsig
      have hval32 : value32 c = some f.value := by
        unfold value32; rw [hc]; rfl
      have hr := value32_round32 .truncate c f.value hval32 hv
      simp only [evalPrepared, hacc, hr, fp16Fp32Model_outputMantissaBits, truncateMantissa32_23, hf]
  refine ⟨⟨PreparedBlock.mk (fp16Fp32Model K padding eAlignMin)
    (List.replicate K (⟨0, 0, 0⟩, ⟨0, 0, 0⟩)) f.decoded, f⟩, ?_, hbits⟩
  unfold evalBlock
  rw [if_neg hlen]
  simp only [prepare, hc, hps]
  exact hrun

/-- Block FMAs with zero products pass a finite accumulator, other than `−0`, through unchanged. -/
theorem runBlocks_zero_blocks (K padding : ℕ) (eAlignMin : Option ℤ)
    (hfl : ∀ f ∈ eAlignMin, f ≤ -126) (m : ℕ) (c : F32) (f : Finite32) (hf : finite32 c = some f)
    (hneg : c ≠ 0x80000000) :
    ∃ ts : List BlockTrace,
      runBlocks (fp16Fp32Model K padding eAlignMin) c
        (List.replicate m (List.replicate K (0, 0))) = .ok ts ∧
      ((ts.getLast?.map fun t => t.output.bits).getD c) = c := by
  induction m generalizing c f with
  | zero => exact ⟨[], rfl, rfl⟩
  | succ m ih =>
    obtain ⟨t, ht, hbits⟩ := zero_products_passthrough K padding eAlignMin hfl c f hf hneg
    have hf' : finite32 t.output.bits = some t.output := finite32_self t.output
    obtain ⟨ts, hts, hlast⟩ := ih t.output.bits t.output hf' (by rw [hbits]; exact hneg)
    refine ⟨t :: ts, ?_, ?_⟩
    · simp only [List.replicate_succ, runBlocks, ht, hts]
    · cases ts with
      | nil => simpa using hbits
      | cons u us =>
        simp only [List.getLast?_cons_cons] at hlast ⊢
        rw [hbits] at hlast
        exact hlast

/-- A pinned instruction variant: the inner dimension `k`, the FMA size N_FMA, the padding bits, the minimum alignment exponent, and the source of these numerical features. -/
structure InstructionVariant where
  name : String
  k : ℕ
  nfma : ℕ
  padding : ℕ
  eAlignMin : Option ℤ
  evidence : String
  nfmaPos : 0 < nfma
  kDiv : nfma ∣ k

abbrev InstructionVariant.model (p : InstructionVariant) : Model :=
  fp16Fp32Model p.nfma p.padding p.eAlignMin

def InstructionVariant.blocks (p : InstructionVariant) : ℕ := p.k / p.nfma

/-- The schedule of one instruction: `k / N_FMA` block FMAs of contiguous products, in increasing k. -/
def InstructionVariant.schedule (p : InstructionVariant) (pairs : List (F16 × F16)) :
    List (List (p.model.Word × p.model.Word)) :=
  chunks p.nfma p.blocks pairs

/-- Execute the instruction. -/
def InstructionVariant.run (p : InstructionVariant) (c : F32) (pairs : List (F16 × F16)) :
    Except ModelError (List BlockTrace) :=
  if pairs.length != p.k then .error .wrongProductCount
  else runBlocks p.model c (p.schedule pairs)

/-- The instruction's FP32 result: the output of the last block FMA, or the accumulator input when there are none. -/
def InstructionVariant.output (p : InstructionVariant) (c : F32) (pairs : List (F16 × F16)) :
    Option F32 :=
  match p.run c pairs with
  | .ok ts => some ((ts.getLast?.map fun t => t.output.bits).getD c)
  | .error _ => none

def InstructionVariant.describe (p : InstructionVariant) : String :=
  s!"{p.name}: k = {p.k}, N_FMA = {p.nfma}, padding bits = {p.padding}, " ++
  s!"minimum alignment exponent = {repr p.eAlignMin}, block FMAs per instruction = {p.blocks}; evidence: {p.evidence}"

theorem InstructionVariant.schedule_flatten (p : InstructionVariant) (pairs : List (F16 × F16))
    (h : pairs.length = p.k) : (p.schedule pairs).flatten = pairs := by
  apply chunks_flatten
  rw [h]
  exact (Nat.div_mul_cancel p.kDiv).symm

/-- A device conforms if it returns the model's bits wherever the model returns a result. -/
def Conforms (p : InstructionVariant) (device : F32 → List (F16 × F16) → Option F32) : Prop :=
  ∀ c pairs out, p.output c pairs = some out → device c pairs = some out

theorem InstructionVariant.run_length (p : InstructionVariant) (c : F32) (pairs : List (F16 × F16))
    (ts : List BlockTrace) (h : p.run c pairs = .ok ts) : pairs.length = p.k := by
  unfold InstructionVariant.run at h
  split at h
  · contradiction
  · rename_i hne
    simpa using hne

theorem InstructionVariant.run_blocks (p : InstructionVariant) (c : F32) (pairs : List (F16 × F16))
    (ts : List BlockTrace) (h : p.run c pairs = .ok ts) :
    runBlocks p.model c (p.schedule pairs) = .ok ts := by
  unfold InstructionVariant.run at h
  split at h
  · contradiction
  · exact h

/-- If only the first block FMA has nonzero products, the instruction returns that block FMA's output. -/
theorem single_block_output (p : InstructionVariant) (hfl : ∀ f ∈ p.eAlignMin, f ≤ -126)
    (hk : p.nfma ≤ p.k) (c : F32) (g : List (F16 × F16)) (hg : g.length = p.nfma)
    (t : BlockTrace) (h1 : evalBlock (⟨g, c⟩ : BlockInput p.model) = .ok t)
    (hneg : t.output.bits ≠ 0x80000000) :
    p.output c (g ++ List.replicate (p.k - p.nfma) (0, 0)) = some t.output.bits := by
  have hblocks : p.blocks = (p.blocks - 1) + 1 := by
    have : 1 ≤ p.blocks := by
      unfold InstructionVariant.blocks
      exact (Nat.le_div_iff_mul_le p.nfmaPos).mpr (by omega)
    omega
  have hrest : p.k - p.nfma = (p.blocks - 1) * p.nfma := by
    have hkm := Nat.div_mul_cancel p.kDiv
    unfold InstructionVariant.blocks at hblocks ⊢
    have : p.k = (p.k / p.nfma - 1 + 1) * p.nfma := by rw [← hblocks]; exact hkm.symm
    rw [Nat.succ_mul] at this
    omega
  have hsched : p.schedule (g ++ List.replicate (p.k - p.nfma) (0, 0)) =
      g :: List.replicate (p.blocks - 1) (List.replicate p.nfma (0, 0)) := by
    unfold InstructionVariant.schedule
    rw [hblocks, chunks_first_group _ _ _ _ hg, hrest, chunks_replicate]
    simp only [Nat.add_sub_cancel]
  obtain ⟨ts, hts, hlast⟩ := runBlocks_zero_blocks p.nfma p.padding p.eAlignMin hfl
    (p.blocks - 1) t.output.bits t.output (finite32_self t.output) hneg
  have hlenpad : (g ++ List.replicate (p.k - p.nfma) (0, 0)).length = p.k := by
    simp only [List.length_append, List.length_replicate, hg]
    omega
  unfold InstructionVariant.output InstructionVariant.run
  rw [if_neg (by rw [hlenpad]; simp), hsched]
  simp only [runBlocks, h1, hts]
  cases ts with
  | nil => rfl
  | cons u us =>
    simp only [List.getLast?_cons_cons]
    rw [getD_of_cons _ u us c t.output.bits, hlast]

/-- V100: WMMA m16n16k16 FP16 → FP32 lowers to HMMA.844; four block FMAs of four products. -/
def v100Wmma16 : InstructionVariant :=
  ⟨"V100 WMMA m16n16k16 FP16->FP32 (HMMA.844)", 16, 4, 0, none,
    "Accurate Models v4 §4.1.1 and Tables 3-4; MATLAB v0.5 GEMM.m increasing-k rule; " ++
    "Jia et al. arXiv:1804.06826 (four sets of four HMMA.884 steps)", by decide, by decide⟩

/-- A100/A2/A30/L40S/Ada: WMMA m16n16k16 FP16 → FP32 lowers to HMMA.1688; two block FMAs of eight products, validated by Accurate Models on k = 16 inputs. -/
def ampereWmma16 : InstructionVariant :=
  ⟨"Ampere/Ada WMMA m16n16k16 FP16->FP32 (HMMA.1688)", 16, 8, 1, some (-132),
    "Accurate Models v4 §4.1.2, §4.2 (k = 16 with N_FMA = 8, 10^7-vector validation), Tables 3-4",
    by decide, by decide⟩

/-- H100/H200/B200: WMMA m16n16k16 FP16 → FP32 lowers to HMMA.16816; one block FMA of sixteen products. -/
def hopperWmma16 : InstructionVariant :=
  ⟨"Hopper/Blackwell WMMA m16n16k16 FP16->FP32 (HMMA.16816)", 16, 16, 2, some (-133),
    "Accurate Models v4 §4.1.6 and Tables 3-4", by decide, by decide⟩

end TensorCore
