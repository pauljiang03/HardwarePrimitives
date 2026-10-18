import MatrixCore

/-! Targeted hardware-validation cases on the AMD Matrix Core model.

Run from `matrix-core/`: `lake env lean ../wip/ozaki/scripts/targeted/MatrixCoreCases.lean`.
Each `#eval` prints one line per inner product, `MC|id|model|c|a|b|output|value|exact`, where the
words are decimal naturals (converted to hex by `targeted_validation.py`), `output` is the model's
output word (or `ERR <error>`), `value` its value and `exact` the exact `c + Σ aᵢbᵢ`. Every
prediction comes from `MatrixCore.dotBits` (one block when the length is `N_FMA`). -/

open MatrixCore

namespace TargetedMC

def ratStr (q : ℚ) : String := if q.den = 1 then toString q.num else s!"{q.num}/{q.den}"

def wordsStr {w : ℕ} (xs : List (BitVec w)) : String :=
  "[" ++ ", ".intercalate (xs.map fun x => toString x.toNat) ++ "]"

/-- Evaluate an inner product (chained blocks) and print its line; returns the output word. -/
def run (id mname : String) (P : Model) (a : List P.a.Word) (b : List P.b.Word) (c : F32) :
    IO (Option F32) := do
  match dotBits P a b c with
  | .ok d =>
    IO.println s!"MC|{id}|{mname}|{c.toNat}|{wordsStr a}|{wordsStr b}|{d.toNat}|{ratStr (wordValue d)}|{ratStr (exactDot P a b c)}"
    return some d
  | .error e =>
    IO.println s!"MC|{id}|{mname}|{c.toNat}|{wordsStr a}|{wordsStr b}|ERR {repr e}|none|{ratStr (exactDot P a b c)}"
    return none

/-- Pass 1 from `c = +0`, then pass 2 from `c = −D1` (RNE), as `Ozaki.MC.mcTwoPass`. -/
def twoPass (id mname : String) (P : Model) (a : List P.a.Word) (b : List P.b.Word) :
    IO Unit := do
  match ← run (id ++ "/pass1") mname P a b 0 with
  | some d1 => let _ ← run (id ++ "/pass2") mname P a b ((rne32 (-wordValue d1)).getD 0)
  | none => pure ()

def z16 (n : ℕ) : List (BitVec 16) := List.replicate n 0

def wideA16 : List (BitVec 16) := List.replicate 5 0x67FF ++ [0x3C00] ++ List.replicate 2 0xE7FF
def wideB16 : List (BitVec 16) := List.replicate 5 0x67FF ++ [0x3C00] ++ List.replicate 2 0x67FF
def wideA32 : List (BitVec 32) :=
  List.replicate 5 0x44FFE000 ++ [0x3F800000] ++ List.replicate 2 0xC4FFE000
def wideB32 : List (BitVec 32) :=
  List.replicate 5 0x44FFE000 ++ [0x3F800000] ++ List.replicate 2 0x44FFE000

#eval show IO Unit from do
  -- Full block on CDNA 3: RNE of the exact sum after global alignment.
  let _ ← run "amd-cdna3-f16-full-block" "cdna3F16" cdna3F16
    (List.replicate 7 0x67FF ++ [0]) (List.replicate 8 0x67FF) 0
  twoPass "amd-cdna3-f16-two-pass" "cdna3F16" cdna3F16
    (List.replicate 7 0x67FF ++ [0]) (List.replicate 8 0x67FF)
  -- The fp16 variants are exact where the binary32 SFMA is not.
  let _ ← run "amd-cdna1-f16-exact-not-sfma" "cdna1F16" cdna1F16 wideA16 wideB16 0
  let _ ← run "amd-cdna2-f16-exact-not-sfma" "cdna2F16" cdna2F16 wideA16 wideB16 0
  let _ ← run "amd-cdna3-f16-exact-not-sfma" "cdna3F16" cdna3F16 wideA16 wideB16 0
  let _ ← run "amd-sfma-f32-not-exact" "sfmaF32" sfmaF32 wideA32 wideB32 0
  -- Cancellation beyond the old exactness bound.
  let _ ← run "amd-cdna3-f16-cancel-zero" "cdna3F16" cdna3F16
    (List.replicate 4 0x6800 ++ List.replicate 4 0xE800) (List.replicate 8 0x6800) 0
  let _ ← run "amd-cdna1-f16-cancel-c" "cdna1F16" cdna1F16
    [0x6800, 0xE800, 0x6800, 0xE800] (List.replicate 4 0x6800) 0x4B000000
  let _ ← run "amd-cdna2-f16-cancel-c" "cdna2F16" cdna2F16
    [0x6800, 0xE800, 0x6800, 0xE800] (List.replicate 4 0x6800) 0x4B000000
  -- Two passes: TwoProdFMA on the SFMA; CDNA 2's pairwise sums defeat the second pass.
  twoPass "amd-sfma-f32-two-prod" "sfmaF32" sfmaF32 [0x4B7FFFFF] [0x4B7FFFFF]
  twoPass "amd-cdna2-f16-two-pass-fails" "cdna2F16" cdna2F16
    [0x6800, 0x0400, 0, 0] [0x6800, 0x3C00, 0, 0]
  twoPass "amd-cdna1-f16-two-pass-recovers" "cdna1F16" cdna1F16
    [0x6800, 0x0400, 0, 0] [0x6800, 0x3C00, 0, 0]
  -- Product non-monotonicity (each pair: x, then x' with every product ≥ and a smaller output).
  let _ ← run "amd-cdna2-f16-nonmonotone/x" "cdna2F16" cdna2F16 [0x0200, 0, 0, 0] [0xD200, 0, 0, 0] 0
  let _ ← run "amd-cdna2-f16-nonmonotone/x'" "cdna2F16" cdna2F16 [0x0400, 0, 0, 0] [0xC800, 0, 0, 0] 0
  let _ ← run "amd-cdna2-bf16-nonmonotone/x" "cdna2BF16" cdna2BF16 [0x0040, 0] [0xF180, 0] 0
  let _ ← run "amd-cdna2-bf16-nonmonotone/x'" "cdna2BF16" cdna2BF16 [0x0080, 0] [0xF080, 0] 0
  let _ ← run "amd-cdna2-bf16_1k-nonmonotone/x" "cdna2BF16_1k" cdna2BF16_1k
    [0x0040, 0, 0, 0] [0xF180, 0, 0, 0] 0
  let _ ← run "amd-cdna2-bf16_1k-nonmonotone/x'" "cdna2BF16_1k" cdna2BF16_1k
    [0x0080, 0, 0, 0] [0xF080, 0, 0, 0] 0
  let _ ← run "amd-cdna3-f16-nonmonotone/x" "cdna3F16" cdna3F16
    (0x3C01 :: List.replicate 7 0x0C00) (0x17FE :: List.replicate 7 0x0C00) 0
  let _ ← run "amd-cdna3-f16-nonmonotone/x'" "cdna3F16" cdna3F16
    (0x0001 :: List.replicate 7 0x0C00) (0x7800 :: List.replicate 7 0x0C00) 0
  let _ ← run "amd-cdna3-bf16-nonmonotone/x" "cdna3BF16" cdna3BF16
    (0x3FD9 :: List.replicate 7 0x3980) (0x3C17 :: List.replicate 7 0x39FE) 0
  let _ ← run "amd-cdna3-bf16-nonmonotone/x'" "cdna3BF16" cdna3BF16
    (0x0001 :: List.replicate 7 0x3980) (0x7F00 :: List.replicate 7 0x39FE) 0
  let _ ← run "amd-cdna3-xf32-nonmonotone/x" "cdna3XF32" cdna3XF32
    (0x3F802000 :: List.replicate 3 0x39800000) (0x3AFFC000 :: List.replicate 3 0x39800000) 0
  let _ ← run "amd-cdna3-xf32-nonmonotone/x'" "cdna3XF32" cdna3XF32
    (0x00002000 :: List.replicate 3 0x39800000) (0x7F000000 :: List.replicate 3 0x39800000) 0
  let _ ← run "amd-cdna3-fp8-e4m3-nonmonotone/x" "cdna3FP8 e4m3fnuz e4m3fnuz"
    (cdna3FP8 e4m3fnuz e4m3fnuz) (0x2F :: List.replicate 15 0) (0x40 :: List.replicate 15 0)
    0x33000000
  let _ ← run "amd-cdna3-fp8-e4m3-nonmonotone/x'" "cdna3FP8 e4m3fnuz e4m3fnuz"
    (cdna3FP8 e4m3fnuz e4m3fnuz) (0x01 :: List.replicate 15 0) (0x7F :: List.replicate 15 0)
    0x33000000
  let _ ← run "amd-cdna3-fp8-e5m2-nonmonotone/x" "cdna3FP8 e5m2fnuz e5m2fnuz"
    (cdna3FP8 e5m2fnuz e5m2fnuz) (0x3B :: List.replicate 15 0) (0x40 :: List.replicate 15 0)
    0x33000000
  let _ ← run "amd-cdna3-fp8-e5m2-nonmonotone/x'" "cdna3FP8 e5m2fnuz e5m2fnuz"
    (cdna3FP8 e5m2fnuz e5m2fnuz) (0x01 :: List.replicate 15 0) (0x7F :: List.replicate 15 0)
    0x33000000
  -- Equal products, different outputs (normal operands only).
  let _ ← run "amd-cdna3-f16-products-not-determined/1.5x1.5" "cdna3F16" cdna3F16
    (0x3E00 :: List.replicate 7 0x0C00) (0x3E00 :: List.replicate 7 0x0C00) 0
  let _ ← run "amd-cdna3-f16-products-not-determined/2.25x1" "cdna3F16" cdna3F16
    (0x4080 :: List.replicate 7 0x0C00) (0x3C00 :: List.replicate 7 0x0C00) 0
  -- Signed zeros and subnormals (one block per model).
  for (pid, P, k) in [("cdna1F16", cdna1F16, 4), ("cdna2F16", cdna2F16, 4),
      ("cdna3F16", cdna3F16, 8)] do
    let w (x : BitVec 16) : P.a.Word := BitVec.ofNat _ x.toNat
    let v (x : BitVec 16) : P.b.Word := BitVec.ofNat _ x.toNat
    let za (n : ℕ) : List P.a.Word := List.replicate n 0
    let zb (n : ℕ) : List P.b.Word := List.replicate n 0
    let _ ← run s!"amd-{pid}-negzero-products-negzero-c" pid P
      (List.replicate k (w 0x8000)) (List.replicate k (v 0x3C00)) 0x80000000
    let _ ← run s!"amd-{pid}-cancel-to-zero-negzero-c" pid P
      ([w 0x3C00, w 0xBC00] ++ za (k - 2)) ([v 0x3C00, v 0x3C00] ++ zb (k - 2)) 0x80000000
    let _ ← run s!"amd-{pid}-subnormal-operand" pid P
      (w 0x0001 :: za (k - 1)) (v 0x3C00 :: zb (k - 1)) 0
    let _ ← run s!"amd-{pid}-subnormal-operand-beside-normal" pid P
      ([w 0x0001, w 0x0400] ++ za (k - 2)) ([v 0x7BFF, v 0x3C00] ++ zb (k - 2)) 0
    let _ ← run s!"amd-{pid}-subnormal-c-passthrough" pid P (za k) (zb k) 3
  for (pid, P, k) in [("cdna1BF16", cdna1BF16, 2), ("cdna2BF16", cdna2BF16, 2),
      ("cdna3BF16", cdna3BF16, 8)] do
    let w (x : BitVec 16) : P.a.Word := BitVec.ofNat _ x.toNat
    let v (x : BitVec 16) : P.b.Word := BitVec.ofNat _ x.toNat
    let za (n : ℕ) : List P.a.Word := List.replicate n 0
    let zb (n : ℕ) : List P.b.Word := List.replicate n 0
    let _ ← run s!"amd-{pid}-subnormal-output" pid P
      (w 0x0080 :: za (k - 1)) (v 0x3E80 :: zb (k - 1)) 0
    let _ ← run s!"amd-{pid}-subnormal-operand" pid P
      (w 0x0001 :: za (k - 1)) (v 0x4B00 :: zb (k - 1)) 0

end TargetedMC
