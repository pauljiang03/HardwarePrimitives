import TensorCore.Kernels.EFT.Native
import Lean

/-! Batch adapter for the bounded EFT. -/

open TensorCore Lean

private def getVariant : String → Option EFMachine.Variant
  | "v100-fp16" => some .v100F16
  | "a100-fp16" => some .ampereF16
  | "h100-fp16" => some .hopperF16
  | "a100-bf16" => some .ampereBF16
  | "h100-bf16" => some .hopperBF16
  | "a100-tf32" => some .ampereTF32
  | "h100-tf32-k4" | "h100-tf32-wmma" => some .hopperTF32Wmma
  | "h100-tf32" | "h100-tf32-mma" => some .hopperTF32Mma
  | "ada-e4m3" => some .adaE4M3
  | "ada-e5m2" => some .adaE5M2
  | "h100-e4m3" => some .hopperE4M3
  | "h100-e5m2" => some .hopperE5M2
  | "b200-e4m3" => some .blackwellE4M3
  | "b200-e5m2" => some .blackwellE5M2
  | _ => none

private def pairs (variant : EFMachine.Variant) : List ℕ → Option (List (variant.model.Word × variant.model.Word))
  | [] => some []
  | a :: b :: xs => do
    if a ≥ 2 ^ variant.model.input.width || b ≥ 2 ^ variant.model.input.width then none
    else return (BitVec.ofNat _ a, BitVec.ofNat _ b) :: (← pairs variant xs)
  | _ => none

private def command (args : List String) : Option Json := do
  match args with
  | "block" :: name :: words =>
    let variant ← getVariant name
    let ns ← words.mapM String.toNat?
    if ns.length != variant.model.nfma * 2 + 2 then none else do
      let c := ns[variant.model.nfma * 2]!
      let D := ns[variant.model.nfma * 2 + 1]!
      if c ≥ 2 ^ 32 || D ≥ 2 ^ 32 then none else do
        let ps ← pairs variant (ns.take (variant.model.nfma * 2))
        let x : BlockInput variant.model := ⟨ps, BitVec.ofNat _ c⟩
        let d : F32 := BitVec.ofNat _ D
        let result := EFMachine.tcEftWithLean variant x d
        let components := (EFMachine.prepare variant x d).toOption.bind EFMachine.extract
        return match result with
        | .error e => Json.mkObj [("error", toJson (reprStr e))]
        | .ok r => Json.mkObj [
            ("bits", toJson (r.bits.map BitVec.toNat)),
            ("branch", toJson (match r with
              | .allZero => "allZero" | .scalar _ => "scalar"
              | .boundedExact _ => "boundedExact" | .outOfRange => "outOfRange")),
            ("grid", toJson (components.map fun z => z.prepared.grid.toNat)),
            ("recovered", toJson (components.map fun z => toString z.recovered.coefficient)),
            ("overlap", toJson (components.map fun z => toString z.overlap.coefficient)),
            ("coarse", toJson (components.map fun z => z.coarse.map fun w => toString w.coefficient)),
            ("low", toJson (components.map fun z => z.low.map fun w => toString w.coefficient)),
            ("guard", toJson (components.map EFMachine.Components.scalarGuard))]
  | ["round", signed] =>
    let n ← signed.toInt?
    if n.natAbs ≥ 2 ^ 576 then none else do
      let x : EFMachine.Word := ⟨decide (n < 0), BitVec.ofNat 576 n.natAbs⟩
      return Json.mkObj [("bits", toJson (x.round32.map BitVec.toNat))]
  | _ => none

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "Expected a batch input file")
  let contents ← IO.FS.readFile path
  for line in contents.splitOn "\n" do
    let words := (line.splitOn " ").filter (· != "")
    unless words.isEmpty do
      let some result := command words | throw (IO.userError "Invalid row or encoded width")
      IO.println result.compress
