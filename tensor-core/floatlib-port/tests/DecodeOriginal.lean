import TensorCore.TC.CanonicalFormatDefs
import Lean
open TensorCore Lean

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "Expected input file")
  for line in (← IO.FS.readFile path).splitOn "\n" do
    unless line.isEmpty do
      let [fmt,word] := line.splitOn " " | throw (IO.userError "Invalid row")
      let some n := word.toNat? | throw (IO.userError "Invalid word")
      let f := match fmt with
        | "fp16" => fp16 | "bf16" => bf16 | "tf32" => tf19 | _ => fp32
      match (classifyNat f n).finite with
      | none => IO.println "null"
      | some d => IO.println (Json.mkObj [
          ("significand", toJson d.significand), ("scale", toJson d.exponent),
          ("mantissaBits", toJson d.mantissaBits),
          ("value", toJson s!"{d.value.num}/{d.value.den}")]).compress
