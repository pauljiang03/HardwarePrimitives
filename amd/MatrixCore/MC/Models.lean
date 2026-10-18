import MatrixCore.MC.Defs

/-! # CDNA 1, CDNA 2 and CDNA 3 matrix cores

Models for every input format characterized in the paper (Section 4); `c` and `d` are FP32. -/

namespace MatrixCore

/-- FP32 on CDNA 1, 2 and 3: a sequential FMA `(…((c + p₁) + p₂) + …)` with RNE at each step. -/
def sfmaF32 : Model :=
  { a := .packed fp32, b := .packed fp32, nfma := 1, accumulation := .correctRounding }

/-! ## CDNA 1 (MI100) -/

/-- CDNA 1 FP16 MFMA: exact sum of `c` and the products, one RNE (Fig. 1a). -/
def cdna1F16 : Model :=
  { a := .packed fp16, b := .packed fp16, nfma := 4, accumulation := .correctRounding }

/-- CDNA 1 BF16 MFMA; products may exceed `2^128` inside a block (Fig. 1b). -/
def cdna1BF16 : Model :=
  { a := .packed bf16, b := .packed bf16, nfma := 2, accumulation := .correctRounding }

/-! ## CDNA 2 (MI210, MI250) -/

/-- CDNA 2 FP16 MFMA: `fl{c + fl{fl{p₁ + p₂} + fl{p₃ + p₄}}}`, no subnormals (Fig. 2a). -/
def cdna2F16 : Model :=
  { a := .packed fp16, b := .packed fp16, nfma := 4, accumulation := .pairWiseSum,
    subnormals := false }

/-- CDNA 2 BF16 MFMA without the `_1k` suffix: `fl{c + fl{p₁ + p₂}}` (Fig. 2b). -/
def cdna2BF16 : Model :=
  { a := .packed bf16, b := .packed bf16, nfma := 2, accumulation := .pairWiseSum,
    subnormals := false }

/-- CDNA 2 BF16 `_1k` MFMA: as FP16 (Fig. 2a). -/
def cdna2BF16_1k : Model :=
  { a := .packed bf16, b := .packed bf16, nfma := 4, accumulation := .pairWiseSum,
    subnormals := false }

/-! ## CDNA 3 (MI300A, MI300X) -/

/-- CDNA 3 FP16 MFMA (Algorithm 1): global alignment of the products, then late `c`. -/
def cdna3F16 : Model :=
  { a := .packed fp16, b := .packed fp16, nfma := 8, accumulation := .globalAlignment,
    productOverflow := true }

/-- CDNA 3 BF16 MFMA: as FP16. -/
def cdna3BF16 : Model :=
  { a := .packed bf16, b := .packed bf16, nfma := 8, accumulation := .globalAlignment,
    productOverflow := true }

/-- CDNA 3 XF32 MFMA: FP32 words truncated to `tf19`, otherwise as FP16. -/
def cdna3XF32 : Model :=
  { a := .xf32, b := .xf32, nfma := 4, accumulation := .globalAlignment, productOverflow := true }

/-- CDNA 3 FP8 MFMA (Algorithm 2), any mix of E4M3 and E5M2 FNUZ operands: odd/even grouping. -/
def cdna3FP8 (fa fb : Format) : Model :=
  { a := .packed fa, b := .packed fb, nfma := 16, accumulation := .oddEvenGrouping,
    late := { cCutoff := some 25 }, productOverflow := true }

/-! ## Devices and input formats -/

inductive Architecture where
  | cdna1
  | cdna2
  | cdna3
  deriving Repr, DecidableEq

/-- MFMA input formats; `fp8 a b` takes any mix of E4M3 and E5M2 FNUZ operands. -/
inductive InputKind where
  | fp32
  | fp16
  | bf16
  | bf16_1k
  | xf32
  | fp8 (a b : Format)
  deriving Repr, DecidableEq

def Architecture.ofDevice : String → Option Architecture
  | "MI100" => some .cdna1
  | "MI210" | "MI250" | "MI250X" => some .cdna2
  | "MI300" | "MI300A" | "MI300X" => some .cdna3
  | _ => none

def Architecture.model : Architecture → InputKind → Option Model
  | _, .fp32 => some sfmaF32
  | .cdna1, .fp16 => some cdna1F16
  | .cdna1, .bf16 => some cdna1BF16
  | .cdna2, .fp16 => some cdna2F16
  | .cdna2, .bf16 => some cdna2BF16
  | .cdna2, .bf16_1k => some cdna2BF16_1k
  | .cdna3, .fp16 => some cdna3F16
  | .cdna3, .bf16 => some cdna3BF16
  | .cdna3, .xf32 => some cdna3XF32
  | .cdna3, .fp8 a b =>
    if (a = e4m3fnuz ∨ a = e5m2fnuz) ∧ (b = e4m3fnuz ∨ b = e5m2fnuz) then some (cdna3FP8 a b)
    else none
  | _, _ => none

/-! ## Instruction shapes -/

structure Instruction where
  name : String
  architectures : List Architecture
  input : InputKind
  m : ℕ
  n : ℕ
  k : ℕ
  deriving Repr

private def shapes (pre suf : String) (archs : List Architecture) (input : InputKind)
    (mnk : List (ℕ × ℕ × ℕ)) : List Instruction :=
  mnk.map fun (m, n, k) => ⟨s!"{pre}{m}x{n}x{k}{suf}", archs, input, m, n, k⟩

/-- Instructions whose shapes the paper lists. -/
def instructions : List Instruction :=
  shapes "mfma_f32_" "f32" [.cdna1, .cdna2, .cdna3] .fp32
      [(32, 32, 1), (16, 16, 1), (4, 4, 1), (32, 32, 2), (16, 16, 4)] ++
  shapes "mfma_f32_" "f16" [.cdna1, .cdna2, .cdna3] .fp16
      [(32, 32, 4), (16, 16, 4), (4, 4, 4), (32, 32, 8), (16, 16, 16)] ++
  shapes "mfma_f32_" "bf16" [.cdna1, .cdna2] .bf16
      [(32, 32, 2), (16, 16, 2), (4, 4, 2), (32, 32, 4), (16, 16, 8)] ++
  shapes "mfma_f32_" "bf16_1k" [.cdna2] .bf16_1k
      [(32, 32, 4), (16, 16, 4), (4, 4, 4), (32, 32, 8), (16, 16, 16)] ++
  shapes "mfma_f32_" "_xf32" [.cdna3] .xf32 [(16, 16, 8)] ++
  shapes "mfma_f32_" "_fp8_fp8" [.cdna3] (.fp8 e4m3fnuz e4m3fnuz) [(32, 32, 16), (16, 16, 32)] ++
  shapes "mfma_f32_" "_fp8_bf8" [.cdna3] (.fp8 e4m3fnuz e5m2fnuz) [(32, 32, 16), (16, 16, 32)] ++
  shapes "mfma_f32_" "_bf8_fp8" [.cdna3] (.fp8 e5m2fnuz e4m3fnuz) [(32, 32, 16), (16, 16, 32)] ++
  shapes "mfma_f32_" "_bf8_bf8" [.cdna3] (.fp8 e5m2fnuz e5m2fnuz) [(32, 32, 16), (16, 16, 32)]

end MatrixCore
