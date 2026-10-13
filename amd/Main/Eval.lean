import MatrixCore

/-! # `mc_eval`: evaluate inner products from words

Reads lines `<model> <a> <b> <c>`, where `model` names a model of the library (for example
`cdna3F16`), `a` and `b` are comma-separated hexadecimal words and
`c` is a hexadecimal binary32 word, and prints the observed result of `dotOutcome`:
`F <hex>` for a finite word, `I+`/`I-` for an infinity, `N` for NaN, `X` for a malformed line. -/

open MatrixCore

def modelOf : String → Option Model
  | "cdna1F16" => some cdna1F16
  | "cdna1BF16" => some cdna1BF16
  | "cdna2F16" => some cdna2F16
  | "cdna2BF16" => some cdna2BF16
  | "cdna2BF16_1k" => some cdna2BF16_1k
  | "cdna3F16" => some cdna3F16
  | "cdna3BF16" => some cdna3BF16
  | "cdna3XF32" => some cdna3XF32
  | "cdna3E4M3" => some (cdna3FP8 e4m3fnuz e4m3fnuz)
  | "cdna3E5M2" => some (cdna3FP8 e5m2fnuz e5m2fnuz)
  | "cdna3E4M3E5M2" => some (cdna3FP8 e4m3fnuz e5m2fnuz)
  | "sfma" => some sfmaF32
  | _ => none

def hexDigit (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def parseHex (s : String) : Option ℕ :=
  s.toList.foldlM (fun acc c => (hexDigit c).map (acc * 16 + ·)) 0

def hex8 (n : ℕ) : String :=
  let digits := (Nat.toDigits 16 n)
  String.ofList (List.replicate (8 - digits.length) '0' ++ digits)

def evalLine (line : String) : String := Id.run do
  let clean := String.ofList (line.toList.filter fun c => c ≠ '\n' ∧ c ≠ '\r')
  match clean.splitOn " " with
  | [p, a, b, c] =>
    match modelOf p, (a.splitOn ",").mapM parseHex, (b.splitOn ",").mapM parseHex, parseHex c with
    | some P, some as, some bs, some cw =>
      match dotOutcome P (as.map (BitVec.ofNat _)) (bs.map (BitVec.ofNat _)) (BitVec.ofNat 32 cw) with
      | some (.finite d) => return s!"F {hex8 d.toNat}"
      | some (.infinity s) => return if s then "I-" else "I+"
      | some .nan => return "N"
      | none => return "X"
    | _, _, _, _ => return "X"
  | _ => return "X"

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn (evalLine line)
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
