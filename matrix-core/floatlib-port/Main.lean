import MCFloat.Model

/-! # `mc_floatlib`: evaluate inner products with the FloatLib implementation

Same protocol as `mc_eval`: lines `<model> <a> <b> <c>` of comma-separated hexadecimal words,
answered by `F <hex>`, `I+`/`I-`, `N` (NaN) or `X` (malformed line). -/

open MCFloat
open FloatLib.Floats.Formats.BinaryInterchange

def modelOf : String → Option MCModel
  | "cdna1F16" => some cdna1F16
  | "cdna1BF16" => some cdna1BF16
  | "cdna2F16" => some cdna2F16
  | "cdna2BF16" => some cdna2BF16
  | "cdna2BF16_1k" => some cdna2BF16_1k
  | "cdna3F16" => some cdna3F16
  | "cdna3BF16" => some cdna3BF16
  | "cdna3XF32" => some cdna3XF32
  | "cdna3E4M3" => some (cdna3FP8 .e4m3fnuz .e4m3fnuz)
  | "cdna3E5M2" => some (cdna3FP8 .e5m2fnuz .e5m2fnuz)
  | "cdna3E4M3E5M2" => some (cdna3FP8 .e4m3fnuz .e5m2fnuz)
  | "sfma" => some sfma
  | _ => none

def parseHex (s : String) : Option ℕ :=
  s.toList.foldlM (fun acc c =>
    if '0' ≤ c ∧ c ≤ '9' then some (acc * 16 + (c.toNat - '0'.toNat))
    else if 'a' ≤ c ∧ c ≤ 'f' then some (acc * 16 + (c.toNat - 'a'.toNat + 10))
    else if 'A' ≤ c ∧ c ≤ 'F' then some (acc * 16 + (c.toNat - 'A'.toNat + 10))
    else none) 0

def hex8 (n : ℕ) : String :=
  let digits := Nat.toDigits 16 n
  String.ofList (List.replicate (8 - digits.length) '0' ++ digits)

def show32 (w : F32) : String :=
  if Model.isNaN w then "N"
  else if Model.isInf w then (if Model.signBit w then "I-" else "I+")
  else s!"F {hex8 (bits w)}"

def evalLine (line : String) : String :=
  let clean := String.ofList (line.toList.filter fun c => c ≠ '\n' ∧ c ≠ '\r')
  match clean.splitOn " " with
  | [p, a, b, c] =>
    match modelOf p, (a.splitOn ",").mapM parseHex, (b.splitOn ",").mapM parseHex, parseHex c with
    | some P, some as, some bs, some cw =>
      match dot P as bs cw with
      | some w => show32 w
      | none => "X"
    | _, _, _, _ => "X"
  | _ => "X"

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn (evalLine line)
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
