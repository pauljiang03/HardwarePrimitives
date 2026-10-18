import TensorCoreTests.TC.Cases
import Lean

open TensorCore TensorCore.Regression Lean

def ratText (q : ℚ) : String := s!"{q.num}/{q.den}"

def snapshotJson (x : BlockInput v100F16F32) : Json :=
  match snapshot x with
  | .error e => Json.mkObj [("error", toJson (reprStr e))]
  | .ok s => Json.mkObj [
      ("bits", toJson s.bits), ("alignExp", toJson s.alignExp),
      ("alignGridExponent", toJson s.qExponent), ("exponents", toJson s.exponents),
      ("coefficients", toJson s.alignedBits), ("ideal", toJson (ratText s.ideal)),
      ("accumulator", toJson (ratText s.accumulator)),
      ("alignmentResiduals", toJson (s.alignmentResiduals.map ratText)),
      ("outputResidual", toJson (ratText s.outputResidual)),
      ("residual", toJson (ratText s.residual)), ("correctedBits", toJson s.correctedBits)]

def parseHex (s : String) : Option ℕ :=
  if s.isEmpty then none else s.toList.foldlM (fun n c => do
    let v ← if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
      else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
      else none
    return 16 * n + v) 0

def parseInput (args : List String) : Option (BlockInput v100F16F32) := do
  let ns ← args.mapM parseHex
  match ns with
  | [a0,b0,a1,b1,a2,b2,a3,b3,c] =>
    if [a0,b0,a1,b1,a2,b2,a3,b3].all (· < 65536) && c < 4294967296 then
      return ⟨[(BitVec.ofNat 16 a0, BitVec.ofNat 16 b0),
        (BitVec.ofNat 16 a1, BitVec.ofNat 16 b1),
        (BitVec.ofNat 16 a2, BitVec.ofNat 16 b2),
        (BitVec.ofNat 16 a3, BitVec.ofNat 16 b3)], BitVec.ofNat 32 c⟩
    else none
  | _ => none

def printInput (args : List String) : IO Unit := do
  match parseInput args with
  | none => throw (IO.userError "Expected eight FP16 hex words (a0 b0 ... a3 b3) and one FP32 c word, without 0x prefixes.")
  | some x => IO.println (snapshotJson x).compress

def printRound (args : List String) : IO Unit := do
  match args with
  | [n, d] =>
    match n.toInt?, d.toNat? with
    | some num, some den =>
      if den = 0 then throw (IO.userError "Rational denominator must be positive.")
      let x : ℚ := num / (den : ℚ)
      IO.println (Json.mkObj [
        ("trunc", toJson ((round32 .truncate x).map BitVec.toNat)),
        ("rne", toJson ((round32 .nearestEven x).map BitVec.toNat))]).compress
    | _, _ => throw (IO.userError "Expected an integer numerator and positive denominator.")
  | _ => throw (IO.userError "Expected numerator denominator.")

def main (args : List String) : IO Unit := do
  match args with
  | [] =>
    for (name, x) in [("R1a", r1a), ("R1b", r1b), ("R2", r2), ("R3", r3)] do
      IO.println (Json.mkObj [("name", toJson name), ("trace", snapshotJson x)]).compress
  | ["--file", path] =>
    let data ← IO.FS.readFile path
    for line in data.splitOn "\n" do
      let words := (line.splitOn " ").filter (· != "")
      unless words.isEmpty do printInput words
  | ["--round-file", path] =>
    let data ← IO.FS.readFile path
    for line in data.splitOn "\n" do
      let words := (line.splitOn " ").filter (· != "")
      unless words.isEmpty do printRound words
  | _ => printInput args
