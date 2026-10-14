import TensorCore.TC.OutputWidth
import TensorCore.TC.Specification.Equivalence
import TensorCore.TC.Specification.Schedule
import TensorCore.TC.Composition
import TensorCore.TC.MachineRefinement
import TensorCore.TC.GPUs

/-! # The independent specification with an `m`-bit block output

`Rounds` selects the output word by ordering all finite binary32 values: the one of largest
magnitude between zero and the accumulated value, with the accumulated value's sign. With a block
output of `m < 23` mantissa bits (Ada and Hopper FP8, `m = 13`), the same ordering runs over the
words whose low `23 − m` mantissa bits are zero (`RoundsM`). `evalBlock_eq_specM` proves that the
model's output word, and every rejection, agree with this specification on every encoded input of
every model, with no hypothesis on the output width; `machine_eq_specM` and `runBlocks_eq_specM`
extend it to modular accumulator widths and to every finite schedule of blocks. `bitsM_eq_bits`
shows that the specification is the one of `Rounds` when `23 ≤ m`, so `evalBlock_eq_spec` is the
case of a binary32 block output. -/

namespace TensorCore.IndependentSpec

set_option maxRecDepth 4096

set_option maxRecDepth 4096

/-- Truncation to an `m`-bit mantissa within binary32's exponent range, specified by ordering the
finite binary32 words whose low `23 − m` mantissa bits are zero. -/
def RoundsM (m : ℕ) (x : ℚ) (bits : BitVec 32) : Prop :=
  (bits.toNat / 2147483648 != 0) = decide (x < 0) ∧ bits.toNat % 2 ^ (23 - m) = 0 ∧
  ∃ d, IndependentSpec.value32 bits = some d ∧ Between x d ∧
    ∀ other y, IndependentSpec.value32 other = some y → other.toNat % 2 ^ (23 - m) = 0 →
      Between x y → magnitude y ≤ magnitude d

def ResultM (p : Parameters) (m : ℕ) (x : Input p) (bits : BitVec 32) : Prop :=
  x.products.length = p.nfma ∧ ∃ ts,
    terms p x = some ts ∧ magnitude (accumulated p ts) ≤ maxFinite ∧
      RoundsM m (accumulated p ts) bits

/-- Mathematical output selector with an `m`-bit block output. -/
noncomputable def bitsM (p : Parameters) (m : ℕ) (x : Input p) : Option (BitVec 32) := by
  classical
  exact if h : ∃ b, ResultM p m x b then some (Classical.choose h) else none

theorem between_of_truncated {x d d' : ℚ} (h : Between x d)
    (h' : (0 ≤ d → 0 ≤ d' ∧ d' ≤ d) ∧ (d ≤ 0 → d ≤ d' ∧ d' ≤ 0)) : Between x d' := by
  unfold Between at *
  rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have := h'.1 h2; left; exact ⟨h1, this.1, by grind⟩
  · have := h'.2 h3; right; exact ⟨h1, by grind, this.2⟩

/-- The model's final stage satisfies `RoundsM`: binary32 truncation, then the low `23 − m`
mantissa bits cleared. -/
theorem roundsM_of_round32 (m : ℕ) (x : ℚ) (b : F32) (h : round32 .truncate x = some b) :
    RoundsM m x (truncateMantissa32 m b) := by
  obtain ⟨hs, d, hd, hbet, hmax⟩ := round32_rounds x b h
  rw [value32_eq] at hd
  obtain ⟨d', hd', -, -⟩ := truncateMantissa32_values (m := m) hd
  refine ⟨?_, ?_, d', by rw [value32_eq]; exact hd', ?_, ?_⟩
  · have := (truncateMantissa32_parts m b).1
    simp only [Nat.reducePow] at this
    rw [this]; exact hs
  · rw [truncateMantissa32_toNat]; exact Nat.mul_mod_left _ _
  · exact between_of_truncated hbet (truncateMantissa32_between hd hd')
  · intro other y hy hlow hxy
    rw [value32_eq] at hy
    have hle := hmax other y (by rw [value32_eq]; exact hy) hxy
    rw [magnitude_eq] at hle ⊢
    exact truncateMantissa32_max hd hd' hy hlow hle

theorem roundsM_unique (m : ℕ) (x : ℚ) (a b : F32) (ha : RoundsM m x a) (hb : RoundsM m x b) :
    a = b := by
  obtain ⟨hsa, hla, va, hva, hba, hma⟩ := ha
  obtain ⟨hsb, hlb, vb, hvb, hbb, hmb⟩ := hb
  have hle := hma b vb hvb hlb hbb
  have hge := hmb a va hva hla hba
  have hv : va = vb := by
    unfold Between magnitude at *
    grind
  subst vb
  rw [value32_eq] at hva hvb
  by_cases hz : va = 0
  · subst va
    have za := zeroBits_of_value a hva
    have zb := zeroBits_of_value b hvb
    have hsign := hsa.trans hsb.symm
    apply BitVec.eq_of_toNat_eq
    rcases za with za | za <;> rcases zb with zb | zb <;> simp_all
  · exact value32_injective a b va hva hvb hz

theorem result_of_evalM {p : Model} {x : BlockInput p} {t : BlockTrace}
    (h : evalBlock x = .ok t) :
    ResultM (parametersOf p) p.outputMantissaBits (inputOf x) t.output.bits := by
  have hp := evalBlock_prepared h
  have hv := (evalBlock_success_iff p x).mp ⟨t, h⟩
  obtain ⟨bits, hr, ht⟩ := evalPrepared_output_mantissa (evalBlock_evalPrepared h)
  have ha := accumulated_eq t.block
  rw [prepare_model hp] at ha
  rw [evalBlock_model h] at ht
  refine ⟨hv.1, t.block.terms.map denormalizedTermOf, ?_, ?_, ?_⟩
  · rw [terms_eq, hp]; rfl
  · rw [ha]; exact round32_range hr
  · rw [ha, ht]; exact roundsM_of_round32 _ _ _ hr

theorem resultM_unique {p : Parameters} {m : ℕ} {x : Input p} {a b : F32}
    (ha : ResultM p m x a) (hb : ResultM p m x b) : a = b := by
  obtain ⟨_, ta, hta, _, hra⟩ := ha
  obtain ⟨_, tb, htb, _, hrb⟩ := hb
  rw [hta] at htb
  cases Option.some.inj htb
  exact roundsM_unique _ _ _ _ hra hrb

theorem resultM_iff_eval {p : Model} (x : BlockInput p) (b : F32) :
    ResultM (parametersOf p) p.outputMantissaBits (inputOf x) b ↔
      ∃ t, evalBlock x = .ok t ∧ t.output.bits = b := by
  constructor
  · intro h
    have hv : Valid (parametersOf p) (inputOf x) := by
      obtain ⟨hs, ts, ht, hr, _⟩ := h
      exact ⟨hs, ts, ht, hr⟩
    obtain ⟨t, ht⟩ := (valid_iff x).mp hv
    exact ⟨t, ht, resultM_unique (result_of_evalM ht) h⟩
  · rintro ⟨t, ht, rfl⟩
    exact result_of_evalM ht

theorem bitsM_eq_of_result {p : Parameters} {m : ℕ} {x : Input p} {b : F32}
    (h : ResultM p m x b) : bitsM p m x = some b := by
  classical
  unfold bitsM
  rw [dif_pos ⟨b, h⟩]
  exact congrArg some (resultM_unique (Classical.choose_spec (show ∃ b, ResultM p m x b from ⟨b, h⟩)) h)

/-- Every encoded input of every model, whatever its block-output width: successful output bits
and all rejection cases agree with the independent specification. -/
theorem evalBlock_eq_specM {p : Model} (x : BlockInput p) :
    (evalBlock x).toOption.map (fun t => t.output.bits) =
      bitsM (parametersOf p) p.outputMantissaBits (inputOf x) := by
  classical
  cases he : evalBlock x with
  | ok t => exact (bitsM_eq_of_result (result_of_evalM he)).symm
  | error e =>
    have hn : ¬ ∃ b, ResultM (parametersOf p) p.outputMantissaBits (inputOf x) b := by
      rintro ⟨b, hb⟩
      obtain ⟨t, ht, _⟩ := (resultM_iff_eval x b).mp hb
      rw [he] at ht
      contradiction
    simp [bitsM, hn, Except.toOption]

/-- With at least 23 output mantissa bits the specification is `Rounds`, the binary32 one. -/
theorem roundsM_iff_rounds {m : ℕ} (hm : 23 ≤ m) (x : ℚ) (b : F32) : RoundsM m x b ↔ Rounds x b := by
  have h1 : 23 - m = 0 := by omega
  unfold RoundsM Rounds
  rw [h1]
  simp only [Nat.pow_zero, Nat.mod_one, true_and, forall_const]

theorem bitsM_eq_bits {p : Parameters} {m : ℕ} (hm : 23 ≤ m) (x : Input p) :
    bitsM p m x = bits p x := by
  classical
  have h : ∀ b, ResultM p m x b ↔ Result p x b := by
    intro b
    unfold ResultM Result
    simp only [roundsM_iff_rounds hm]
  by_cases he : ∃ b, Result p x b
  · obtain ⟨b, hb⟩ := he
    rw [bitsM_eq_of_result ((h b).mpr hb), bits_eq_of_result hb]
  · have hn : ¬ ∃ b, ResultM p m x b := fun ⟨b, hb⟩ => he ⟨b, (h b).mp hb⟩
    unfold bitsM bits
    rw [dif_neg hn, dif_neg he]

/-- Adequate modular accumulator widths inherit the specification equality, for every output
width. -/
theorem machine_eq_specM {p : Model} (x : BlockInput p) (w F carryBits : ℕ)
    (hF : p.alignMantissaBits = F) (hc : p.nfma + 1 ≤ 2 ^ carryBits) (hw : F + 3 + carryBits ≤ w) :
    (evalBlockMachine w x).toOption.map (fun t => t.output.bits) =
      bitsM (parametersOf p) p.outputMantissaBits (inputOf x) := by
  rw [evalBlockMachine_eq x w F carryBits hF hc (by omega)]
  exact evalBlock_eq_specM x

/-- Ordered composition of specified block FMAs with an `m`-bit block output. -/
noncomputable def runChainM (p : Parameters) (m : ℕ) : BitVec 32 →
    List (List (BitVec p.input.width × BitVec p.input.width)) → Option (List (BitVec 32))
  | _, [] => some []
  | c, block :: rest => do
    let d ← bitsM p m ⟨block, c⟩
    let tail ← runChainM p m d rest
    return d :: tail

/-- All intermediate outputs of every finite schedule, and failures, agree with the specification,
for every block-output width. -/
theorem runBlocks_eq_specM (p : Model) (c : F32) (blocks : List (List (p.Word × p.Word))) :
    (runBlocks p c blocks).toOption.map (fun ts => ts.map fun t => t.output.bits) =
      runChainM (parametersOf p) p.outputMantissaBits c blocks := by
  induction blocks generalizing c with
  | nil => rfl
  | cons block rest ih =>
    have hb := evalBlock_eq_specM (⟨block, c⟩ : BlockInput p)
    change (evalBlock (⟨block, c⟩ : BlockInput p)).toOption.map (fun t => t.output.bits) =
      bitsM (parametersOf p) p.outputMantissaBits ⟨block, c⟩ at hb
    simp only [runChainM, ← hb]
    cases he : evalBlock (⟨block, c⟩ : BlockInput p) with
    | error e => simp [runBlocks, he, Except.toOption]
    | ok t =>
      have hr := ih t.output.bits
      cases ht : runBlocks p t.output.bits rest with
      | error e => simp [runBlocks, he, ht, Except.toOption] at hr ⊢; rw [← hr]; rfl
      | ok ts => simp [runBlocks, he, ht, Except.toOption] at hr ⊢; rw [← hr]; rfl

/-- The Ada and Hopper FP8 instances. -/
theorem fp8_eq_spec :
    (∀ x : BlockInput adaE4M3F32, (evalBlock x).toOption.map (·.output.bits) =
      bitsM (parametersOf adaE4M3F32) 13 (inputOf x)) ∧
    (∀ x : BlockInput adaE5M2F32, (evalBlock x).toOption.map (·.output.bits) =
      bitsM (parametersOf adaE5M2F32) 13 (inputOf x)) ∧
    (∀ x : BlockInput hopperE4M3F32, (evalBlock x).toOption.map (·.output.bits) =
      bitsM (parametersOf hopperE4M3F32) 13 (inputOf x)) ∧
    (∀ x : BlockInput hopperE5M2F32, (evalBlock x).toOption.map (·.output.bits) =
      bitsM (parametersOf hopperE5M2F32) 13 (inputOf x)) :=
  ⟨evalBlock_eq_specM, evalBlock_eq_specM, evalBlock_eq_specM, evalBlock_eq_specM⟩

end TensorCore.IndependentSpec
