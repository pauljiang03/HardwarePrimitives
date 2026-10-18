import TCFloat.Equivalence.Representations

/-! # The FP8 block FMAs of Ada, Hopper and B200

The port reads E4M3 words with FloatLib's OCP E4M3 format `e4m3fn`; the parent reads them in the
9-bit layout `e4m3x`. Both decode every word to the same value, so the two implementations agree
on every FP8 input. -/

set_option backward.isDefEq.respectTransparency false
namespace TCFloat.Equivalence
open FloatLib.Floats.Formats.BinaryInterchange

/-- The same block FMA, with E4M3 words in the `e4m3x` layout. -/
def widened (p : TCModel) : TCModel := { p with format := e4m3x }

def widenPairs (ps : List (Nat × Nat)) : List (Nat × Nat) :=
  ps.map fun (a, b) => (widenE4M3 a, widenE4M3 b)

theorem term_fields_injective :
    Function.Injective (fun t : Term => (t.dyadic, t.exponent, t.mantissaBits)) := by
  intro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

set_option maxRecDepth 100000 in
/-- FloatLib's OCP E4M3 format decodes every word as `e4m3x` decodes the widened word. -/
theorem e4m3fn_decode_widen (n : Nat) : decode .e4m3fn n = decode e4m3x (widenE4M3 n) := by
  have h : ∀ n, n < 256 →
      (decode .e4m3fn n).map (fun t => (t.dyadic, t.exponent, t.mantissaBits)) =
        (decode e4m3x (widenE4M3 n)).map (fun t => (t.dyadic, t.exponent, t.mantissaBits)) := by
    decide +kernel
  by_cases hn : n < 256
  · exact Option.map_injective term_fields_injective (h n hn)
  · rw [decode_none_of_ge .e4m3fn (show 2^FloatFormat.e4m3fn.bitWidth ≤ n by
        change 2^8 ≤ n; omega),
      decode_none_of_ge e4m3x (show 2^e4m3x.bitWidth ≤ widenE4M3 n by
        change 2^9 ≤ widenE4M3 n; unfold widenE4M3; split <;> omega)]

theorem mapM_widen (p : TCModel) (hp : p.format = .e4m3fn) (ps : List (Nat × Nat)) :
    ps.mapM (fun (a, b) => do return (← decode p.format a, ← decode p.format b)) =
      (widenPairs ps).mapM
        (fun (a, b) => do return (← decode (widened p).format a, ← decode (widened p).format b)) := by
  rw [widenPairs, List.mapM_map]
  congr 1
  funext ab
  simp [widened, hp, e4m3fn_decode_widen]

theorem prepare_widen (p : TCModel) (hp : p.format = .e4m3fn) (ps : List (Nat × Nat)) (c : Nat) :
    prepare (widened p) (widenPairs ps) c =
      (prepare p ps c).map fun b => ⟨widened p, b.c, b.products⟩ := by
  have hm := mapM_widen p hp ps
  have hl : (widenPairs ps).length = ps.length := by simp [widenPairs]
  unfold prepare
  rw [hl, ← hm, show (widened p).nfma = p.nfma from rfl]
  by_cases h : (ps.length != p.nfma) = true
  · simp only [h, ite_true, Option.map_none]
  · simp only [h, Bool.false_eq_true, ite_false]
    cases decode .binary32 c <;> simp [Option.map_bind]

theorem prepare_model {p : TCModel} {ps : List (Nat × Nat)} {c : Nat} {b : Block}
    (h : prepare p ps c = some b) : b.model = p := by
  unfold prepare at h
  split at h
  · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, _, _, rfl⟩ := h
    rfl

theorem tc_widen (p : TCModel) (hp : p.format = .e4m3fn) (ps : List (Nat × Nat)) (c : Nat) :
    Interface.tc p ps c = Interface.tc (widened p) (widenPairs ps) c := by
  unfold Interface.tc
  rw [prepare_widen p hp]
  cases h : prepare p ps c with
  | none => rfl
  | some b =>
    have hb := prepare_model h
    obtain ⟨m, c', qs⟩ := b
    cases hb
    rfl

/-- The EFT reads the model only through the alignment grid. -/
theorem encodedAlgorithm_model (m m' : TCModel) (c : Term) (ps : List (Term × Term)) (d : Nat) (v : ℚ)
    (h : Block.q ⟨m, c, ps⟩ = Block.q ⟨m', c, ps⟩) :
    Trace.encodedAlgorithm ⟨⟨m, c, ps⟩, d, v⟩ = Trace.encodedAlgorithm ⟨⟨m', c, ps⟩, d, v⟩ := by
  simp only [Trace.encodedAlgorithm, Trace.algorithm, Trace.scalar, Trace.scalarPredicate,
    Trace.scalarUnchecked, Trace.exactConsolidation, Trace.lowCoefficients, Trace.supportExponent,
    Trace.lowParts, Trace.extractionExponent, Trace.overlap, Trace.retained, Trace.coarse,
    Block.terms, h]

theorem eft_widen (p : TCModel) (hp : p.format = .e4m3fn) (ps : List (Nat × Nat)) (c d : Nat) :
    Interface.eft p ps c d = Interface.eft (widened p) (widenPairs ps) c d := by
  unfold Interface.eft
  rw [prepare_widen p hp]
  cases h : prepare p ps c with
  | none => rfl
  | some b =>
    have hb := prepare_model h
    obtain ⟨m, c', qs⟩ := b
    cases hb
    simp only [Option.map_some, Option.bind_some, trace]
    split
    · rfl
    · cases value32 d with
      | none => rfl
      | some v =>
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some]
        rw [encodedAlgorithm_model m (widened m) c' qs d v rfl]

/-- The port's FP8 models are the parent's `adaE4M3F32`, `adaE5M2F32`, `hopperE4M3F32`,
`hopperE5M2F32`, `blackwellE4M3F32` and `blackwellE5M2F32`. -/
theorem fp8_models :
    model (widened adaE4M3) = ⟨⟨3, 5, 7⟩, 16, 13, none, 13⟩ ∧
    model adaE5M2 = ⟨⟨2, 5, 15⟩, 16, 13, none, 13⟩ ∧
    model (widened hopperE4M3) = ⟨⟨3, 5, 7⟩, 32, 13, none, 13⟩ ∧
    model hopperE5M2 = ⟨⟨2, 5, 15⟩, 32, 13, none, 13⟩ ∧
    model (widened blackwellE4M3) = ⟨⟨3, 5, 7⟩, 32, 25, none, 23⟩ ∧
    model blackwellE5M2 = ⟨⟨2, 5, 15⟩, 32, 25, none, 23⟩ := by
  decide

/-- E5M2 block FMAs, for every output width: the same bits, branches and errors on every input. -/
theorem e5m2_equivalence (p : TCModel) (hp : p.format = .e5m2)
    (x : TensorCore.BlockInput (model p)) (D : TensorCore.F32) :
    Interface.tc p (inputPairs x) x.c.toNat =
        (TensorCore.evalBlock x).toOption.map (fun t => t.output.bits.toNat) ∧
    Interface.eft p (inputPairs x) x.c.toNat D.toNat =
        (TensorCore.tcEftEncoded x D).toOption.map encodedResult :=
  supportedFormat_equivalence p (Or.inr (Or.inr (Or.inr (Or.inl hp)))) x D

/-- The `e4m3x` word of an E4M3 word, as the parent's `widenE4M3` defines it. -/
def widenWord (w : BitVec 8) : BitVec 9 := BitVec.ofNat 9 (widenE4M3 w.toNat)

theorem widenWord_toNat (w : BitVec 8) : (widenWord w).toNat = widenE4M3 w.toNat := by
  unfold widenWord
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := w.isLt
  unfold widenE4M3; split <;> omega

/-- E4M3 block FMAs, for every output width: the port on 8-bit OCP E4M3 words and the parent on
their `e4m3x` words return the same bits, branches and errors. -/
theorem e4m3_equivalence (p : TCModel) (hp : p.format = .e4m3fn)
    (ps : List (BitVec 8 × BitVec 8)) (c D : TensorCore.F32) :
    Interface.tc p (ps.map fun (a, b) => (a.toNat, b.toNat)) c.toNat =
        (TensorCore.evalBlock (p := model (widened p))
          ⟨ps.map fun (a, b) => (widenWord a, widenWord b), c⟩).toOption.map
          (fun t => t.output.bits.toNat) ∧
    Interface.eft p (ps.map fun (a, b) => (a.toNat, b.toNat)) c.toNat D.toNat =
        (TensorCore.tcEftEncoded (p := model (widened p))
          ⟨ps.map fun (a, b) => (widenWord a, widenWord b), c⟩ D).toOption.map encodedResult := by
  have hx : widenPairs (ps.map fun (a, b) => (a.toNat, b.toNat)) =
      inputPairs (p := widened p) ⟨ps.map fun (a, b) => (widenWord a, widenWord b), c⟩ := by
    simp [widenPairs, inputPairs, widenWord_toNat]
  rw [tc_widen p hp, eft_widen p hp, hx]
  exact supportedFormat_equivalence (widened p) (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) _ D

end TCFloat.Equivalence
