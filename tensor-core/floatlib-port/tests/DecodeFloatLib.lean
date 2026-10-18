import TCFloat.Model
import Lean
open TCFloat Lean
open FloatLib.Floats.Formats.BinaryInterchange

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "Expected input file")
  for line in (← IO.FS.readFile path).splitOn "\n" do
    unless line.isEmpty do
      let [fmt,word] := line.splitOn " " | throw (IO.userError "Invalid row")
      let some n := word.toNat? | throw (IO.userError "Invalid word")
      let f := match fmt with
        | "fp16" => FloatFormat.binary16 | "bf16" => .bfloat16 | "tf32" => .tf32 | _ => .binary32
      match decode f n with
      | none => IO.println "null"
      | some d => IO.println (Json.mkObj [
          ("significand", toJson d.dyadic.signedSignificand), ("scale", toJson d.exponent),
          ("mantissaBits", toJson d.mantissaBits),
          ("value", toJson s!"{d.value.num}/{d.value.den}")]).compress
