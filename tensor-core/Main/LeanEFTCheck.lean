import TensorCore.Kernels.EFT.Native
import Lean

/-! Compare bounded scalar summation with native FP32 summation. -/

open Lean TensorCore

private def word (n : ℕ) : Except String F32 :=
  if n < 2 ^ 32 then pure (BitVec.ofNat 32 n) else throw "FP32 word is out of range"

private def variant : String → Except String EFMachine.Variant
  | "v100-fp16" => pure .v100F16
  | "a100-fp16" => pure .ampereF16
  | "h100-fp16" => pure .hopperF16
  | "a100-bf16" => pure .ampereBF16
  | "h100-bf16" => pure .hopperBF16
  | "a100-tf32" => pure .ampereTF32
  | "h100-tf32-k4" | "h100-tf32-wmma" => pure .hopperTF32Wmma
  | "h100-tf32" | "h100-tf32-mma" => pure .hopperTF32Mma
  | "ada-e4m3" => pure .adaE4M3
  | "ada-e5m2" => pure .adaE5M2
  | "h100-e4m3" => pure .hopperE4M3
  | "h100-e5m2" => pure .hopperE5M2
  | "b200-e4m3" => pure .blackwellE4M3
  | "b200-e5m2" => pure .blackwellE5M2
  | _ => throw "Unknown EFT path"

private def resultJson : Except EFMachine.Error EFMachine.Result → Json
  | .error e => Json.mkObj [("error", toJson (reprStr e))]
  | .ok r => Json.mkObj [("bits", toJson (r.bits.map BitVec.toNat)),
      ("branch", toJson (match r with
        | .allZero => "allZero" | .scalar _ => "scalar"
        | .boundedExact _ => "boundedExact" | .outOfRange => "outOfRange"))]

private def block (j : Json) : Except String Json := do
  let p ← j.getObjValAs? String "profile" >>= variant
  let as ← j.getObjValAs? (List ℕ) "a"
  let bs ← j.getObjValAs? (List ℕ) "b"
  if as.length != bs.length then throw "Operand lists have different lengths"
  let ps ← (as.zip bs).mapM fun (a, b) => do
    if a ≥ 2 ^ p.model.input.width || b ≥ 2 ^ p.model.input.width then
      throw "Product word is out of range"
    pure ((BitVec.ofNat _ a, BitVec.ofNat _ b) : p.model.Word × p.model.Word)
  let c ← j.getObjValAs? ℕ "c" >>= word
  let d ← j.getObjValAs? ℕ "D" >>= word
  let x : BlockInput p.model := ⟨ps, c⟩
  pure <| Json.mkObj [("reference", resultJson (EFMachine.tcEft p x d)),
    ("native", resultJson (EFMachine.tcEftWithLean p x d))]

private def evaluate (j : Json) : Except String Json := do
  if (j.getObjVal? "profile").isOk then return ← block j
  let acc ← j.getObjValAs? ℕ "acc" >>= word
  let xs ← j.getObjValAs? (List ℕ) "terms" >>= List.mapM word
  let original := xs.foldlM EFMachine.add32 acc
  let native := EFMachine.naiveSum32WithLeanFrom acc xs
  pure <| Json.mkObj [("reference", toJson (original.map BitVec.toNat)),
    ("native", toJson (native.map BitVec.toNat))]

def main : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then return 0
    unless line.trimAscii.toString.isEmpty do
      match Json.parse line >>= evaluate with
      | .ok result => output.putStrLn result.compress
      | .error message =>
        (← IO.getStderr).putStrLn message
        return 2
  return 0
