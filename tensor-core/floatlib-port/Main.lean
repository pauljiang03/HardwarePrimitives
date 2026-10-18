import TCFloat.Model
import Lean
open TCFloat Lean
open FloatLib.Floats.Formats.BinaryInterchange

private def qText (q : ℚ) : String := s!"{q.num}/{q.den}"
private def failure (s : String) : Json := Json.mkObj [("error", toJson ("TensorCore.ModelError." ++ s))]
private def traceJson (t : Trace) : Json := Json.mkObj [
  ("bits", toJson t.bits), ("alignExp", toJson t.block.alignExp),
  ("alignGridStep", toJson (qText (pow2 t.block.q))),
  ("accumulator", toJson (qText t.block.accumulator)),
  ("terms", toJson (t.block.terms.map (qText ∘ Term.value))),
  ("aligned", toJson (t.block.aligned.map qText)),
  ("alignment_residuals", toJson (t.block.residuals.map qText)),
  ("output_residual", toJson (qText (t.block.accumulator-t.output))),
  ("overlap", toJson (qText t.overlap)), ("low_parts", toJson (t.lowParts.map qText)),
  ("scalar_predicate", toJson t.scalarPredicate), ("scalar_bits", toJson t.scalar),
  ("algorithm_bits", toJson t.algorithm.1)]
private def pairs : List Nat → Option (List (Nat × Nat))
  | [] => some []
  | a :: b :: rest => return (a,b) :: (← pairs rest)
  | _ => none
private def format (s : String) : Option FloatFormat := match s with
  | "fp16" => some .binary16 | "bf16" => some .bfloat16 | "tf32" => some .tf32 | _ => none
private def fp8Model (s : String) : Option TCModel := match s with
  | "ada-e4m3" => some adaE4M3 | "ada-e5m2" => some adaE5M2
  | "h100-e4m3" => some hopperE4M3 | "h100-e5m2" => some hopperE5M2
  | "b200-e4m3" => some blackwellE4M3 | "b200-e5m2" => some blackwellE5M2 | _ => none
private def blockJson (p : TCModel) (ns : List Nat) : Option Json := do
  if ns.length != 2*p.nfma+2 then none else do
    let c := ns[2*p.nfma]!
    let d := ns[2*p.nfma+1]!
    let ps ← pairs (ns.take (2*p.nfma))
    if c ≥ 2^32 || d ≥ 2^32 || ps.any (fun (a,b) => a ≥ 2^p.format.bitWidth || b ≥ 2^p.format.bitWidth)
      then none else do
    match prepare p ps c with
    | none => return Json.mkObj [("ideal", Json.null), ("model", failure "nonfiniteInput"),
        ("correction", failure "nonfiniteInput")]
    | some b =>
      let model := match b.evaluate with
        | none => failure "accumulatorOutOfRange"
        | some n => match trace b n with
          | none => failure "nonfiniteOutput"
          | some t => traceJson t
      let correction := match trace b d with
        | none => failure "nonfiniteOutput"
        | some t => Json.mkObj [("bits", toJson t.encodedAlgorithm.1), ("branch", toJson t.encodedAlgorithm.2)]
      return Json.mkObj [("ideal", toJson (qText b.ideal)), ("model", model), ("correction", correction)]

private def featureJson (p : TCModel) (words : List Nat) (registerTF32 : Bool) : Json := Id.run do
  if words.length != 2*p.nfma+1 then return failure "wrongProductCount"
  let c := words[2*p.nfma]!
  let mut ws := words.take (2*p.nfma)
  if registerTF32 then
    if ws.any (fun x => x ≥ 2^32 || x % 2^13 != 0) then return failure "nonfiniteInput"
    ws := ws.map (· / 2^13)
  let some ps := pairs ws | return failure "wrongProductCount"
  let some b := prepare p ps c | return failure "nonfiniteInput"
  let some bits := b.evaluate | return failure "accumulatorOutOfRange"
  let some t := trace b bits | return failure "nonfiniteOutput"
  return Json.mkObj [("bits", toJson bits), ("ideal", toJson (qText b.ideal)),
    ("accumulated", toJson (qText b.accumulator)), ("value", toJson (qText t.output)),
    ("residual", toJson (qText t.residual))]

private def command (args : List String) : Option Json := do
  match args with
  | "block" :: fmt :: k :: padding :: fl :: words =>
    let f ← format fmt
    let k ← k.toNat?
    let padding ← padding.toNat?
    let eAlignMin ← if fl = "none" then some none else fl.toInt? |>.map some
    blockJson ⟨f,k,padding,eAlignMin,23⟩ (← words.mapM String.toNat?)
  | "fp8" :: m :: words => blockJson (← fp8Model m) (← words.mapM String.toNat?)
  | ["family", p, k, j] =>
    let p ← p.toNat?
    let k ← k.toNat?
    let j ← j.toNat?
    if p > 4 || k = 0 || k ≥ 2^(24+p) || j = 0 || j > 2^23 then none else do
      let v := [0x0c00,0x0800,0x0400,0x0200,0x0100][p]!
      let b ← prepare (fp16 k p) (List.replicate k (0x0c00,v)) (0x3f800000-j)
      return match b.evaluate with
        | none => failure "accumulatorOutOfRange"
        | some bits => Json.mkObj [("bits", toJson bits), ("accumulator", toJson (qText b.accumulator))]
  | ["round", n, d] =>
    let n ← n.toInt?
    let d ← d.toNat?
    if d = 0 then none else do
      let x : ℚ := n / (d : ℚ)
      return Json.mkObj [("rne", toJson (round32 .nearestEven x)), ("trunc", toJson (round32 .towardZero x))]
  | fmt :: k :: padding :: fl :: words =>
    let f ← format (if fmt = "canonical" then "fp16" else fmt)
    let k ← k.toNat?
    let padding ← padding.toNat?
    let eAlignMin ← if fl = "none" then some none else fl.toInt? |>.map some
    return featureJson ⟨f,k,padding,eAlignMin,23⟩ (← words.mapM String.toNat?) (fmt == "tf32")
  | _ => none

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "Expected an input file")
  let contents ← IO.FS.readFile path
  for line in contents.splitOn "\n" do
    let words := (line.splitOn " ").filter (· != "")
    unless words.isEmpty do
      let some result := command words | throw (IO.userError "Invalid row, shape, or word width")
      IO.println result.compress
