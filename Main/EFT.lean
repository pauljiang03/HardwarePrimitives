import TensorCore.EFT.Encoded
import TensorCore.TC.CanonicalFormatDefs
import Lean

/-! Compiled adapter for the pinned TC-EFT paper validation corpus. -/

open TensorCore Lean

private def qText (q : ℚ) : String := s!"{q.num}/{q.den}"

private def failure (e : ModelError) : Json := Json.mkObj [("error", toJson (reprStr e))]

private def correctionJson : Except ModelError EncodedEFTResult → Json
  | .error e => failure e
  | .ok r => Json.mkObj [("bits", toJson (r.bits.map BitVec.toNat)),
      ("branch", toJson (match r with
        | .allZero => "allZero"
        | .consolidated (.scalar _) => "scalar"
        | .consolidated (.exactReference _) => "exactReference"
        | .consolidated .outOfRange => "outOfRange"))]

private def traceJson (t : BlockTrace) : Json := Json.mkObj [
  ("bits", toJson t.output.bits.toNat), ("alignExp", toJson t.block.alignExp),
  ("alignGridStep", toJson (qText (pow2 t.block.alignGridExponent))),
  ("accumulator", toJson (qText t.block.accumulator)),
  ("terms", toJson (t.block.terms.map (qText ∘ DenormalizedProduct.value))),
  ("aligned", toJson (t.block.terms.map fun x => qText (truncGrid x.value t.block.alignGridExponent))),
  ("alignment_residuals", toJson (t.block.alignmentResiduals.map qText)),
  ("output_residual", toJson (qText t.outputResidual)),
  ("overlap", toJson (qText t.overlap)), ("low_parts", toJson (t.lowParts.map qText)),
  ("scalar_predicate", toJson t.scalarPredicate),
  ("scalar_bits", toJson (t.scalarCorrected.map BitVec.toNat)),
  ("algorithm_bits", toJson (t.tcEft.bits.map BitVec.toNat))]

private def parsePairs (p : Model) : List ℕ → Option (List (p.Word × p.Word))
  | [] => some []
  | a :: b :: rest => do
    if a ≥ 2 ^ p.input.width || b ≥ 2 ^ p.input.width then none
    else return (BitVec.ofNat _ a, BitVec.ofNat _ b) :: (← parsePairs p rest)
  | _ => none

private def blockJson (f : TensorCore.Format) (k neab : ℕ) (eAlignMin : Option ℤ) (ns : List ℕ) : Option Json := do
  if ns.length != 2 * k + 2 then none else do
    let c := ns[k * 2]!
    let D := ns[k * 2 + 1]!
    if c ≥ 2 ^ 32 || D ≥ 2 ^ 32 then none else do
      let p : Model := ⟨f, k, 23 + neab, eAlignMin⟩
      let ps ← parsePairs p (ns.take (2 * k))
      let x : BlockInput p := ⟨ps, BitVec.ofNat 32 c⟩
      return Json.mkObj [
        ("ideal", toJson ((exactDot x).map qText)),
        ("model", match evalBlock x with | .error e => failure e | .ok t => traceJson t),
        ("correction", correctionJson (tcEftEncoded x (BitVec.ofNat 32 D)))]

private def familyJson (p k j : ℕ) : Option Json := do
  if p > 4 || k = 0 || k ≥ 2 ^ (24 + p) || j = 0 || j > 2 ^ 23 then none else do
    let b : ℕ := match p with | 0 => 0x0c00 | 1 => 0x0800 | 2 => 0x0400 | 3 => 0x0200 | _ => 0x0100
    let x : BlockInput (fp16Fp32Model k p none) :=
      ⟨List.replicate k (0x0c00, BitVec.ofNat 16 b), BitVec.ofNat 32 (0x3f800000 - j)⟩
    return match evalBlock x with
    | .error e => failure e
    | .ok t => Json.mkObj [("bits", toJson t.output.bits.toNat),
        ("accumulator", toJson (qText t.block.accumulator))]

private def command (args : List String) : Option Json := do
  match args with
  | "block" :: fmt :: k :: neab :: fl :: words =>
    let f ← match fmt with | "fp16" => some fp16 | "bf16" => some bf16 | "tf32" => some tf19 | _ => none
    let k ← k.toNat?
    let neab ← neab.toNat?
    let eAlignMin ← if fl = "none" then some none else fl.toInt? |>.map some
    blockJson f k neab eAlignMin (← words.mapM String.toNat?)
  | ["family", p, k, j] => familyJson (← p.toNat?) (← k.toNat?) (← j.toNat?)
  | ["round", n, d] =>
    let n ← n.toInt?
    let d ← d.toNat?
    if d = 0 then none else do
      let x : ℚ := n / (d : ℚ)
      return Json.mkObj [("rne", toJson ((round32 .nearestEven x).map BitVec.toNat)),
        ("trunc", toJson ((round32 .truncate x).map BitVec.toNat))]
  | _ => none

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "Expected an input file")
  let contents ← IO.FS.readFile path
  for line in contents.splitOn "\n" do
    let words := (line.splitOn " ").filter (· != "")
    unless words.isEmpty do
      let some result := command words | throw (IO.userError "Invalid paper-suite row, shape, or word width")
      IO.println result.compress
