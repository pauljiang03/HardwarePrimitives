import TensorCore.TC.Models
import TensorCore.TC.CanonicalDefs
import TensorCore.TC.CanonicalFormatDefs
import TensorCore.TC.GPUs
import TensorCore.TC.MmaSyncFP8
import Lean

open TensorCore Lean

private def qText (q : ℚ) : String := s!"{q.num}/{q.den}"

private def getFormat : String → Option TensorCore.Format
  | "fp16" => some fp16
  | "bf16" => some bf16
  | "tf19" => some tf19
  | "fp32" => some fp32
  | "fp64" => some fp64
  | "e5m2" => some e5m2
  | "e4m3x" => some e4m3x
  | _ => none

private def getModel : String → Option InvocationSpec
  | "v100" => some v100Invocation
  | "a100-f16" => some a100F16Invocation
  | "a100-bf16" => some a100BF16Invocation
  | "a100-tf32" => some a100TF32Invocation
  | "hopper-f16" => some hopperF16Invocation
  | "hopper-bf16" => some hopperBF16Invocation
  | "hopper-tf32-mma" => some hopperTF32MmaInvocation
  | "hopper-tf32-wmma" => some hopperTF32WmmaInvocation
  | "f64-rne" => some (fp64Fma .nearestEven)
  | "f64-rz" => some (fp64Fma .truncate)
  | "f64-rd" => some (fp64Fma .towardNegative)
  | "f64-ru" => some (fp64Fma .towardPositive)
  | "ada-e4m3" => some adaE4M3Invocation
  | "ada-e5m2" => some adaE5M2Invocation
  | "hopper-e4m3" => some hopperE4M3Invocation
  | "hopper-e5m2" => some hopperE5M2Invocation
  | "blackwell-e4m3" => some blackwellE4M3Invocation
  | "blackwell-e5m2" => some blackwellE5M2Invocation
  | "blackwell-e4m3-then-add" => some blackwellE4M3ThenAddInvocation
  | "blackwell-e5m2-then-add" => some blackwellE5M2ThenAddInvocation
  | _ => none

private def parsePairs (p : InvocationSpec) : List ℕ → Option (List (p.input.Word × p.input.Word))
  | [] => some []
  | a :: b :: rest => do
    if a ≥ 2 ^ p.input.width || b ≥ 2 ^ p.input.width then none
    else return (BitVec.ofNat _ a, BitVec.ofNat _ b) :: (← parsePairs p rest)
  | _ => none

private def eventJson (e : RoundingEvent) : Json := Json.mkObj [
  ("input", toJson (qText e.input)), ("bits", toJson e.output.bits.toNat),
  ("value", toJson (qText e.output.value)), ("loss", toJson (qText e.loss)),
  ("mantissaBits", toJson e.stage.format.mantissaBits), ("mode", toJson (reprStr e.stage.mode))]

private def invocationJson (p : InvocationSpec) (ns : List ℕ) : Option Json := do
  let c ← ns.getLast?
  if c ≥ 2 ^ p.cFormat.width then none else do
    let ps ← parsePairs p ns.dropLast
    let x : InvocationInput p := ⟨ps, BitVec.ofNat _ c⟩
    return match evalInvocation x with
    | .error e => Json.mkObj [("error", toJson (reprStr e))]
    | .ok t => Json.mkObj [
      ("bits", toJson t.output.bits.toNat), ("value", toJson (qText t.output.value)),
      ("ideal", toJson (qText t.prepared.exactDot)), ("residual", toJson (qText t.residual)),
      ("accumulated", toJson (qText t.accumulation.value)),
      ("alignmentLoss", toJson (qText t.accumulation.alignmentLoss)),
      ("localConversions", toJson (t.accumulation.roundings.map eventJson)),
      ("intermediate", toJson (t.intermediate.events.map eventJson))]

private def parseFp16Pairs : List ℕ → Option (List (F16 × F16))
  | [] => some []
  | a :: b :: rest => do
    if a ≥ 65536 || b ≥ 65536 then none
    else return (BitVec.ofNat 16 a, BitVec.ofNat 16 b) :: (← parseFp16Pairs rest)
  | _ => none

private def parseModelPairs (p : Model) : List ℕ → Option (List (p.Word × p.Word))
  | [] => some []
  | a :: b :: rest => do
    if a ≥ 2 ^ p.input.width || b ≥ 2 ^ p.input.width then none
    else return (BitVec.ofNat _ a, BitVec.ofNat _ b) :: (← parseModelPairs p rest)
  | _ => none

/-- Evaluate one block through a proven model rather than through a descriptor. -/
private def modelJson (p : Model) (ps : List (p.Word × p.Word)) (c : ℕ) : Json :=
  let x : BlockInput p := ⟨ps, BitVec.ofNat 32 c⟩
  match evalBlock x with
  | .error e => Json.mkObj [("error", toJson (reprStr e))]
  | .ok t => Json.mkObj [
    ("bits", toJson t.output.bits.toNat), ("value", toJson (qText t.output.value)),
    ("ideal", toJson (qText t.block.exactDot)), ("residual", toJson (qText t.residual)),
    ("accumulated", toJson (qText t.block.accumulator))]

private def bf16Json (K padding : ℕ) (eAlignMin : Option ℤ) (ns : List ℕ) : Option Json := do
  let c ← ns.getLast?
  if c ≥ 2 ^ 32 then none else do
    let ps ← parseModelPairs (bf16Fp32Model K padding eAlignMin) ns.dropLast
    return modelJson (bf16Fp32Model K padding eAlignMin) ps c

/-- TF32 register words: the thirteen low bits must be zero, then the value word is used. -/
private def tf32Json (K padding : ℕ) (eAlignMin : Option ℤ) (ns : List ℕ) : Option Json := do
  let c ← ns.getLast?
  if c ≥ 2 ^ 32 then none else do
    let words ← parseFp32Words ns.dropLast
    if words.any (fun w => !tf32Padded w) then
      return Json.mkObj [("error", toJson "invalidPadding")]
    else
      let ps := tf32UnpackPairs (pairUp words)
      return modelJson (tf19Fp32Model K padding eAlignMin) ps c
where
  parseFp32Words : List ℕ → Option (List tf32Register.Word)
    | [] => some []
    | w :: rest => do
      if w ≥ 2 ^ 32 then none else return (BitVec.ofNat _ w) :: (← parseFp32Words rest)
  pairUp : List tf32Register.Word → List (tf32Register.Word × tf32Register.Word)
    | a :: b :: rest => (a, b) :: pairUp rest
    | _ => []

/-- A named replay model with the conversion from input words to its operand words. -/
private structure ReplayModel where
  model : Model
  word : ℕ → Option model.Word

private def plainWord (p : Model) (n : ℕ) : Option p.Word :=
  if n < 2 ^ p.input.width then some (BitVec.ofNat _ n) else none

private def e4m3Word (n : ℕ) : Option (BitVec 9) :=
  if n < 256 then some (widenE4M3 (BitVec.ofNat 8 n)) else none

private def tf32Word (n : ℕ) : Option (BitVec 19) :=
  if n < 2 ^ 32 ∧ n % 2 ^ 13 = 0 then some (tf32Unpack (BitVec.ofNat 32 n)) else none

private def replayModel : String → Option ReplayModel
  | "ada-f16" => some ⟨adaF16F32, plainWord _⟩
  | "ada-bf16" => some ⟨adaBF16F32, plainWord _⟩
  | "ada-tf32" => some ⟨adaTF32F32, tf32Word⟩
  | "hopper-f16" => some ⟨hopperF16F32, plainWord _⟩
  | "hopper-bf16" => some ⟨hopperBF16F32, plainWord _⟩
  | "hopper-tf32-wmma" => some ⟨hopperTF32WmmaF32, tf32Word⟩
  | "blackwell-f16" => some ⟨blackwellF16F32, plainWord _⟩
  | "blackwell-bf16" => some ⟨blackwellBF16F32, plainWord _⟩
  | "blackwell-tf32-wmma" => some ⟨blackwellTF32WmmaF32, tf32Word⟩
  | "ada-e4m3" => some ⟨adaE4M3F32, e4m3Word⟩
  | "ada-e5m2" => some ⟨adaE5M2F32, plainWord _⟩
  | "hopper-e4m3" => some ⟨hopperE4M3F32, e4m3Word⟩
  | "hopper-e5m2" => some ⟨hopperE5M2F32, plainWord _⟩
  | "blackwell-e4m3" => some ⟨blackwellE4M3F32, e4m3Word⟩
  | "blackwell-e5m2" => some ⟨blackwellE5M2F32, plainWord _⟩
  -- Negative controls: Ada and Hopper FP8 with an FP32 block output.
  | "ada-e4m3-fp32-output" => some ⟨{adaE4M3F32 with outputMantissaBits := 23}, e4m3Word⟩
  | "ada-e5m2-fp32-output" => some ⟨{adaE5M2F32 with outputMantissaBits := 23}, plainWord _⟩
  | "hopper-e4m3-fp32-output" => some ⟨{hopperE4M3F32 with outputMantissaBits := 23}, e4m3Word⟩
  | "hopper-e5m2-fp32-output" => some ⟨{hopperE5M2F32 with outputMantissaBits := 23}, plainWord _⟩
  | _ => none

private def pairs {α : Type} : List α → Option (List (α × α))
  | [] => some []
  | a :: b :: rest => do return (a, b) :: (← pairs rest)
  | _ => none

private def bitsJson : Option ℕ → Json
  | some b => Json.mkObj [("bits", toJson b)]
  | none => Json.mkObj [("error", toJson "rejected")]

/-- The words of a replay row: operand pairs, then `c`. -/
private def replayDot (thenAdd : Bool) (name : String) (ns : List ℕ) : Option Json := do
  let r ← replayModel name
  let c ← ns.getLast?
  if c ≥ 2 ^ 32 then none else do
    let ps ← pairs (← ns.dropLast.mapM r.word)
    let out := if thenAdd then r.model.dotThenAdd (BitVec.ofNat 32 c) ps
      else r.model.dot (BitVec.ofNat 32 c) ps
    return bitsJson (out.map BitVec.toNat)

/-- Consecutive groups of `n` elements, the last padded. -/
private def groups {α : Type} (n : ℕ) (pad : α) (xs : List α) : List (List α) :=
  go xs.length xs
where
  go : ℕ → List α → List (List α)
  | 0, _ => []
  | _, [] => []
  | fuel + 1, xs =>
    let g := xs.take n
    (g ++ List.replicate (n - g.length) pad) :: go fuel (xs.drop n)

/-- Block FMAs chained in increasing `k`; each output word is the next accumulator input. -/
private def chainInvocation (p : InvocationSpec) (c : ℕ)
    (ps : List (p.input.Word × p.input.Word)) : Option ℕ :=
  (groups p.nfma (0, 0) ps).foldlM
    (fun c block => (invocationBits (p := p) ⟨block, BitVec.ofNat _ c⟩).map BitVec.toNat) c

private def replayChain (name : String) (ns : List ℕ) : Option Json := do
  let p ← getModel name
  let c ← ns.getLast?
  if c ≥ 2 ^ p.cFormat.width || p.nfma = 0 then none else do
    let ps ← parsePairs p ns.dropLast
    return bitsJson (chainInvocation p c ps)

/-- Input format and operand-word conversion for `model-dot` rows. -/
private def paramFormat : String → Option (TensorCore.Format × (ℕ → Option ℕ))
  | "fp16" => some (fp16, fun n => if n < 2 ^ 16 then some n else none)
  | "bf16" => some (bf16, fun n => if n < 2 ^ 16 then some n else none)
  | "tf32" => some (tf19, fun n => if n < 2 ^ 32 ∧ n % 2 ^ 13 = 0 then some (n / 2 ^ 13) else none)
  | "e5m2" => some (e5m2, fun n => if n < 256 then some n else none)
  | "e4m3" => some (e4m3x, fun n => if n < 256 then some (widenE4M3 (BitVec.ofNat 8 n)).toNat else none)
  | _ => none

/-- `Model.dot` from parameters: format, FMA size, mantissa bits after alignment, minimum
alignment exponent (or `none`), output mantissa bits, then `c` and the operand pairs. -/
private def paramDot (args : List String) : Option Json := do
  match args with
  | fmt :: k :: f :: e :: m :: c :: ws =>
    let (format, word) ← paramFormat fmt
    let K ← k.toNat?
    let F ← f.toInt?
    let eMin ← if e = "none" then some none else (e.toInt?).map some
    let mb ← m.toNat?
    let cw ← c.toNat?
    if cw ≥ 2 ^ 32 then none else do
      let p : Model := ⟨format, K, F, eMin, mb⟩
      let vs ← (← ws.mapM String.toNat?).mapM word
      let ps ← pairs (vs.map fun n => (BitVec.ofNat p.input.width n : p.Word))
      return bitsJson ((p.dot (BitVec.ofNat 32 cw) ps).map BitVec.toNat)
  | _ => none

/-- FP8 `mma.sync` of H100, H200 and B200: format, `k` (32 or 16), `c`, then 8-bit operand pairs. -/
private def mmaSyncDot (args : List String) : Option Json := do
  match args with
  | fmt :: k :: c :: ws =>
    let conv ← if fmt = "e4m3" then some e4m3ToF16 else if fmt = "e5m2" then some e5m2ToF16 else none
    let K ← k.toNat?
    let cw ← c.toNat?
    if cw ≥ 2 ^ 32 ∨ K = 0 then none else do
      let ns ← ws.mapM String.toNat?
      if ns.any (· ≥ 256) then none else do
        let ps ← pairs (ns.map fun n => BitVec.ofNat 8 n)
        return bitsJson ((mmaSyncFP8Dot conv K (BitVec.ofNat 32 cw) ps).map BitVec.toNat)
  | _ => none

private def command (args : List String) : Option Json := do
  match args with
  | ["round", fmt, n, d] =>
    let f ← getFormat fmt
    let num ← n.toInt?
    let den ← d.toNat?
    if den = 0 then none else
      let x : ℚ := num / (den : ℚ)
      return Json.mkObj (([("trunc", .truncate), ("rne", .nearestEven),
        ("rd", .towardNegative), ("ru", .towardPositive)] : List (String × BinaryRoundingMode)).map
        fun (name, mode) => (name, toJson ((roundBinary f mode x).map BitVec.toNat)))
  | ["decode", fmt, n] =>
    let bits ← n.toNat?
    let s ← if fmt = "tf32-register" then some tf32Register
      else if fmt = "e4m3" then some e4m3Encoding else (getFormat fmt).map packedIEEE
    if bits ≥ 2 ^ s.width then none else
      return Json.mkObj [("value", toJson ((s.decode (BitVec.ofNat _ bits)).map (qText ∘ Decoded.value)))]
  | "block" :: name :: words =>
    let p ← getModel name
    let ns ← words.mapM String.toNat?
    invocationJson p ns
  | "canonical" :: k :: padding :: eAlignMinText :: words =>
    let K ← k.toNat?
    let E ← padding.toNat?
    let eAlignMin ← if eAlignMinText = "none" then some none else eAlignMinText.toInt? |>.map some
    let ns ← words.mapM String.toNat?
    invocationJson (fp16Fp32Invocation K E eAlignMin) ns
  | "bf16" :: k :: padding :: eAlignMinText :: words =>
    let K ← k.toNat?
    let E ← padding.toNat?
    let eAlignMin ← if eAlignMinText = "none" then some none else eAlignMinText.toInt? |>.map some
    let ns ← words.mapM String.toNat?
    bf16Json K E eAlignMin ns
  | "tf32" :: k :: padding :: eAlignMinText :: words =>
    let K ← k.toNat?
    let E ← padding.toNat?
    let eAlignMin ← if eAlignMinText = "none" then some none else eAlignMinText.toInt? |>.map some
    let ns ← words.mapM String.toNat?
    if ns.dropLast.length % 2 != 0 then none else tf32Json K E eAlignMin ns
  | "dot" :: name :: words => do
    replayDot false name (← words.mapM String.toNat?)
  | "dot-then-add" :: name :: words => do
    replayDot true name (← words.mapM String.toNat?)
  | "chain" :: name :: words => do
    replayChain name (← words.mapM String.toNat?)
  | "model-dot" :: rest => paramDot rest
  | "mma-sync" :: rest => mmaSyncDot rest
  | _ => none

def main (args : List String) : IO Unit := do
  let lines ← match args with
    | ["--file", path] => pure ((← IO.FS.readFile path).splitOn "\n")
    | _ => pure [String.intercalate " " args]
  for line in lines do
    let words := (line.splitOn " ").filter (· != "")
    unless words.isEmpty do
      match command words with
      | none => throw (IO.userError s!"Invalid feature command: {line}")
      | some j => IO.println j.compress
