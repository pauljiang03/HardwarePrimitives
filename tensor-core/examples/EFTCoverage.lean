import TensorCore.EFT.Extraction
import TensorCore.TC.CanonicalDefs
import Lean

/-! Exact-reference coverage runner. -/

open TensorCore Lean

private def parseHex (s : String) : Option ℕ :=
  if s.isEmpty then none else s.toList.foldlM (fun n c => do
    let v ← if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
      else none
    return 16 * n + v) 0

private def pairs : List ℕ → List (F16 × F16)
  | a :: b :: xs => (BitVec.ofNat 16 a, BitVec.ofNat 16 b) :: pairs xs
  | _ => []

private def runRow (row : List String) : IO Json := do
  let k :: padding :: words := row | throw (IO.userError "Expected K extra words")
  let some k := k.toNat? | throw (IO.userError "Invalid K")
  let some padding := padding.toNat? | throw (IO.userError "Invalid extra")
  let some words := words.mapM parseHex | throw (IO.userError "Invalid hex")
  unless words.length = 2 * k + 1 && (words.take (2 * k)).all (· < 65536) &&
      words.getLast! < 4294967296 do throw (IO.userError "Wrong word count or width")
  let x : BlockInput (fp16Fp32Model k padding none) :=
    ⟨pairs (words.take (2 * k)), BitVec.ofNat 32 words.getLast!⟩
  match evalBlock x with
  | .error e => return Json.mkObj [("error", toJson (reprStr e))]
  | .ok t =>
    let failed := (t.scalarChecks.filter fun c => !c.2).map Prod.fst
    return Json.mkObj [
      ("bits", toJson t.output.bits.toNat),
      ("accepted", toJson t.scalarPredicate),
      ("failed", toJson failed),
      ("corrected", toJson (t.scalarCorrected.map BitVec.toNat)),
      ("tceft", toJson (t.scalarTcEft.map BitVec.toNat)),
      ("unchecked", toJson (t.scalarCorrectedUnchecked.map BitVec.toNat)),
      ("support", toJson t.lowestLowBitExp),
      ("coefficient_sum", toJson (toString (magnitudeSum t.lowBits))),
      ("low_parts", toJson (t.lowParts.map fun q => s!"{q.num}/{q.den}"))]

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "Expected input file")
  let input ← IO.FS.readFile path
  for line in input.splitOn "\n" do
    let words := (line.splitOn " ").filter (· != "")
    unless words.isEmpty do IO.println (← runRow words).compress
