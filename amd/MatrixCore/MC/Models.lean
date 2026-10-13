import MatrixCore.MC.Defs

/-! # CDNA 1, CDNA 2 and CDNA 3 matrix cores

Profiles for every input format characterised in the paper (Section 4). The architectures are
CDNA 1 (MI100), CDNA 2 (MI210, MI250) and CDNA 3 (MI300A, MI300X). `c` and `d` are binary32
throughout. -/

namespace MatrixCore

/-- binary32 inputs on CDNA 1, 2 and 3 form a sequential FMA (SFMA),
`(…((c + p₁) + p₂) + …)`, keeping each product exact and rounding each step with RNE: blocks of
one product with correct rounding. Subnormals are supported in input and output. -/
def sfmaF32 : Model :=
  { a := .packed binary32, b := .packed binary32, nfma := 1, accumulation := .correctRounding }

/-! ## CDNA 1 (MI100): full-precision products, exact accumulation, final RNE -/

/-- CDNA 1 fp16: `N_FMA = 4`, `c` accumulated with the products, exact sum, RNE (Fig. 1a). -/
def cdna1F16 : Model :=
  { a := .packed binary16, b := .packed binary16, nfma := 4, accumulation := .correctRounding }

/-- CDNA 1 bf16: `N_FMA = 2`; products may exceed `2^128` inside a block (Fig. 1b). -/
def cdna1BF16 : Model :=
  { a := .packed bfloat16, b := .packed bfloat16, nfma := 2, accumulation := .correctRounding }

/-! ## CDNA 2 (MI210, MI250): pairwise sums of binary32 values, subnormals flushed -/

/-- CDNA 2 fp16: `fl{c + fl{fl{p₁ + p₂} + fl{p₃ + p₄}}}`, no subnormals (Fig. 2a). -/
def cdna2F16 : Model :=
  { a := .packed binary16, b := .packed binary16, nfma := 4, accumulation := .pairWiseSum,
    subnormals := false }

/-- CDNA 2 bf16 without the `_1k` suffix: group size `2`, `fl{c + fl{p₁ + p₂}}` (Fig. 2b). -/
def cdna2BF16 : Model :=
  { a := .packed bfloat16, b := .packed bfloat16, nfma := 2, accumulation := .pairWiseSum,
    subnormals := false }

/-- CDNA 2 bf16 `_1k` instructions: group size `4`, as fp16 (Fig. 2a). -/
def cdna2BF16_1k : Model :=
  { a := .packed bfloat16, b := .packed bfloat16, nfma := 4, accumulation := .pairWiseSum,
    subnormals := false }

/-! ## CDNA 3 (MI300A, MI300X): global alignment with late `c` -/

/-- CDNA 3 fp16 (Algorithm 1): `N_FMA = 8`, products denormalised and aligned with `(2, 24)`,
`c` added late with `(24, 32, RD)` alignment, `e_{c=0} = −126`, `|p_ℓ| ≥ 2^128` overflows. -/
def cdna3F16 : Model :=
  { a := .packed binary16, b := .packed binary16, nfma := 8, accumulation := .globalAlignment,
    productOverflow := true }

/-- CDNA 3 bf16: every feature as fp16. -/
def cdna3BF16 : Model :=
  { a := .packed bfloat16, b := .packed bfloat16, nfma := 8, accumulation := .globalAlignment,
    productOverflow := true }

/-- CDNA 3 XF32: binary32 words truncated to tf19, `N_FMA = 4`, otherwise as fp16. -/
def cdna3XF32 : Model :=
  { a := .xf32, b := .xf32, nfma := 4, accumulation := .globalAlignment, productOverflow := true }

/-- CDNA 3 binary8 (Algorithm 2) for any combination of fp8-E4M3 and fp8-E5M2 (FNUZ) operands:
`N_FMA = 16` in odd/even groups of eight, `s'_c = 0` once `e_max − e_c > 25`. -/
def cdna3FP8 (fa fb : Format) : Model :=
  { a := .packed fa, b := .packed fb, nfma := 16, accumulation := .oddEvenGrouping,
    late := { cCutoff := some 25 }, productOverflow := true }

/-! ## Devices and input formats -/

inductive Architecture where
  | cdna1
  | cdna2
  | cdna3
  deriving Repr, DecidableEq

/-- Input formats of the MFMA instructions in the paper. `bf16_1k` is CDNA 2's `_1k` variant;
`fp8 a b` combines fp8-E4M3 (`fp8`) and fp8-E5M2 (`bf8`) FNUZ operands. -/
inductive InputKind where
  | fp32
  | fp16
  | bf16
  | bf16_1k
  | xf32
  | fp8 (a b : Format)
  deriving Repr, DecidableEq

/-- Device to architecture. -/
def Architecture.ofDevice : String → Option Architecture
  | "MI100" => some .cdna1
  | "MI210" | "MI250" | "MI250X" => some .cdna2
  | "MI300" | "MI300A" | "MI300X" => some .cdna3
  | _ => none

/-- The profile of an architecture and input format, where the architecture supports it. -/
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

/-! ## Instruction shapes

Shapes `m×n×k` listed in the paper. Every output element is one inner product of length `k`,
evaluated in `⌈k / N_FMA⌉` chained blocks; `m` and `n` do not change the arithmetic. -/

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
