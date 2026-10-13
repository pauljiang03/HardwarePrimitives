import TensorCore.TC.Models
import TensorCore.TC.CanonicalDefs
import TensorCore.TC.CanonicalFormatDefs
import Lean

open TensorCore Lean

private def qText (q : ℚ) : String := s!"{q.num}/{q.den}"

private def getFormat : String → Option TensorCore.Format
  | "fp16" => some fp16
  | "bf16" => some bf16
  | "tf19" => some tf19
  | "fp32" => some fp32
  | "fp64" => some fp64
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
  | "f64-rne" => some (binary64Fma .nearestEven)
  | "f64-rz" => some (binary64Fma .truncate)
  | "f64-rd" => some (binary64Fma .towardNegative)
  | "f64-ru" => some (binary64Fma .towardPositive)
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

/-- Evaluate one block through a proved model rather than through a descriptor. -/
private def modelJson (p : Model) (ps : List (p.Word × p.Word)) (c : ℕ) : Json :=
  let x : BlockInput p := ⟨ps, BitVec.ofNat 32 c⟩
  match evalBlock x with
  | .error e => Json.mkObj [("error", toJson (reprStr e))]
  | .ok t => Json.mkObj [
    ("bits", toJson t.output.bits.toNat), ("value", toJson (qText t.output.value)),
    ("ideal", toJson (qText t.block.exactDot)), ("residual", toJson (qText t.residual)),
    ("accumulated", toJson (qText t.block.accumulator))]

private def bf16Json (K neab : ℕ) (eAlignMin : Option ℤ) (ns : List ℕ) : Option Json := do
  let c ← ns.getLast?
  if c ≥ 2 ^ 32 then none else do
    let ps ← parseModelPairs (bf16Fp32Model K neab eAlignMin) ns.dropLast
    return modelJson (bf16Fp32Model K neab eAlignMin) ps c

/-- TF32 register words: the thirteen low bits must be zero, then the value word is used. -/
private def tf32Json (K neab : ℕ) (eAlignMin : Option ℤ) (ns : List ℕ) : Option Json := do
  let c ← ns.getLast?
  if c ≥ 2 ^ 32 then none else do
    let words ← parseFp32Words ns.dropLast
    if words.any (fun w => !tf32Padded w) then
      return Json.mkObj [("error", toJson "invalidPadding")]
    else
      let ps := tf32UnpackPairs (pairUp words)
      return modelJson (tf19Fp32Model K neab eAlignMin) ps c
where
  parseFp32Words : List ℕ → Option (List tf32Register.Word)
    | [] => some []
    | w :: rest => do
      if w ≥ 2 ^ 32 then none else return (BitVec.ofNat _ w) :: (← parseFp32Words rest)
  pairUp : List tf32Register.Word → List (tf32Register.Word × tf32Register.Word)
    | a :: b :: rest => (a, b) :: pairUp rest
    | _ => []

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
    let s ← if fmt = "tf32-register" then some tf32Register else (getFormat fmt).map packedIEEE
    if bits ≥ 2 ^ s.width then none else
      return Json.mkObj [("value", toJson ((s.decode (BitVec.ofNat _ bits)).map (qText ∘ Decoded.value)))]
  | "block" :: name :: words =>
    let p ← getModel name
    let ns ← words.mapM String.toNat?
    invocationJson p ns
  | "canonical" :: k :: neab :: eAlignMinText :: words =>
    let K ← k.toNat?
    let E ← neab.toNat?
    let eAlignMin ← if eAlignMinText = "none" then some none else eAlignMinText.toInt? |>.map some
    let ns ← words.mapM String.toNat?
    invocationJson (fp16Fp32Invocation K E eAlignMin) ns
  | "bf16" :: k :: neab :: eAlignMinText :: words =>
    let K ← k.toNat?
    let E ← neab.toNat?
    let eAlignMin ← if eAlignMinText = "none" then some none else eAlignMinText.toInt? |>.map some
    let ns ← words.mapM String.toNat?
    bf16Json K E eAlignMin ns
  | "tf32" :: k :: neab :: eAlignMinText :: words =>
    let K ← k.toNat?
    let E ← neab.toNat?
    let eAlignMin ← if eAlignMinText = "none" then some none else eAlignMinText.toInt? |>.map some
    let ns ← words.mapM String.toNat?
    if ns.dropLast.length % 2 != 0 then none else tf32Json K E eAlignMin ns
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
