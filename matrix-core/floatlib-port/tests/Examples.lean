import MCFloat

/-! # Worked examples

The FloatLib implementation evaluated on a few of the paper's inputs. -/

open MCFloat
open FloatLib.Floats.Formats.BinaryInterchange

def observed (w : Option F32) : String :=
  match w with
  | none => "X"
  | some w =>
    if Model.isNaN w then "N"
    else if Model.isInf w then (if Model.signBit w then "I-" else "I+")
    else s!"F {bits w}"

-- CDNA 1 FP16: four products `1 · 1` with `c = 0` give `4`.
#guard observed (block cdna1F16 (List.replicate 4 0x3C00) (List.replicate 4 0x3C00) 0) =
  s!"F {0x40800000}"

-- CDNA 3 BF16: `c = −∞` with the overflowing product `2^127 · 2^2` is NaN.
#guard observed (block cdna3BF16 (0x7F00 :: List.replicate 7 0) (0x4080 :: List.replicate 7 0)
  0xFF800000) = "N"

-- CDNA 3 BF16: the same product alone overflows to `+∞`.
#guard observed (block cdna3BF16 (0x7F00 :: List.replicate 7 0) (0x4080 :: List.replicate 7 0) 0) =
  "I+"

-- CDNA 1 BF16: the exact sum `2^129` overflows at the final rounding.
#guard observed (block cdna1BF16 [0x7F00, 0] [0x4080, 0] 0) = "I+"

-- E4M3 FNUZ: `0x80` is NaN.
#guard observed (block (cdna3FP8 .e4m3fnuz .e4m3fnuz) (0x80 :: List.replicate 15 0)
  (List.replicate 16 0) 0) = "N"

-- An empty inner product returns `c`.
#guard observed (dot cdna3F16 [] [] 0x7F800000) = "I+"
