import TensorCore.Scalar.LeanFiniteAddition
import TensorCore.Kernels.EFT.Correctness

/-! EFT scalar consolidation using Lean's native FP32 addition. -/

namespace TensorCore.EFMachine

open TensorCore.IEEE.LeanBridge

set_option maxRecDepth 4096
set_option exponentiation.threshold 1024

theorem value32_finite_exponent {a : F32} {x : ℚ} (h : TensorCore.value32 a = some x) :
    a.toNat / 8388608 % 256 < 255 := by
  have he : a.toNat / 8388608 % 256 < 256 := Nat.mod_lt _ (by decide)
  by_cases hf : a.toNat / 8388608 % 256 < 255
  · exact hf
  have hz : a.toNat / 8388608 % 256 = 255 := by omega
  by_cases hm : a.toNat % 8388608 = 0 <;>
    simp [TensorCore.value32, TensorCore.decode32, classify, classifyNat, fp32, hz, hm,
      Classification.finite] at h

/-- Native nearest-even FP32 addition with finite-input and exact-sum range checks. -/
def add32WithLean (a b : F32) : Option F32 := do
  if ha : a.toNat / 8388608 % 256 < 255 then
    if hb : b.toNat / 8388608 % 256 < 255 then
      let x ← decode32Word a
      let y ← decode32Word b
      let s ← x.add y
      if s.magnitude ≤ maxMagnitude32 then
        some (nativeFiniteAdd32 a b ha hb)
      else none
    else none
  else none

/-- Native addition agrees with `add32` on every input, including rejections and signed zeros. -/
theorem add32WithLean_eq (a b : F32) : add32WithLean a b = add32 a b := by
  cases hx : decode32Word a with
  | none =>
    simp only [add32WithLean, add32, hx]
    split <;> (try rfl)
    split <;> rfl
  | some x =>
    have hxa : TensorCore.value32 a = some x.value := by rw [← decode32Word_value, hx]; rfl
    have ha := value32_finite_exponent hxa
    cases hy : decode32Word b with
    | none => simp [add32WithLean, add32, ha, hx, hy]
    | some y =>
      have hyb : TensorCore.value32 b = some y.value := by rw [← decode32Word_value, hy]; rfl
      have hb := value32_finite_exponent hyb
      simp only [add32WithLean, add32, ha, hb, ↓reduceDIte, hx, hy, Bind.bind, Option.bind]
      cases hs : x.add y with
      | none => rfl
      | some s =>
        simp only
        by_cases hr : s.magnitude ≤ maxMagnitude32
        · rw [if_pos hr, Word.round32_eq, Word.add_value hs]
          exact (nativeFiniteAdd32_round a b ha hb x.value y.value hxa hyb (by
            have h := s.range_iff.mpr hr
            rwa [Word.add_value hs] at h)).symm
        · have hgt : s.magnitude > maxMagnitude32 := by
            change ¬ s.magnitude.toNat ≤ maxMagnitude32.toNat at hr
            exact Nat.lt_of_not_ge hr
          simp [hr, Word.round32, hgt]

/-- Encoded, left-to-right naive accumulation with rounding at every addition. -/
def naiveSum32WithLeanFrom (acc : F32) (xs : List F32) : Option F32 :=
  xs.foldlM add32WithLean acc

theorem naiveSum32WithLeanFrom_eq (acc : F32) (xs : List F32) :
    naiveSum32WithLeanFrom acc xs = xs.foldlM add32 acc := by
  simp only [naiveSum32WithLeanFrom, show add32WithLean = add32 from by funext a b; exact add32WithLean_eq a b]

def scalarSumWithLean (xs : List Word) : Option F32 := do
  let bs ← xs.mapM Word.round32
  naiveSum32WithLeanFrom 0 bs

theorem scalarSumWithLean_eq (xs : List Word) : scalarSumWithLean xs = scalarSum xs := by
  simp only [scalarSumWithLean, scalarSum, naiveSum32WithLeanFrom_eq]

def Components.scalarWithLean (c : Components) : Option F32 := do
  if !c.scalarGuard then none else do
    let eBits ← scalarSumWithLean c.low
    let dBits ← c.prepared.output.round32
    let oBits ← c.overlap.neg.round32
    let hBits ← add32WithLean dBits oBits
    add32WithLean hBits eBits

theorem Components.scalarWithLean_eq (c : Components) : c.scalarWithLean = c.scalar := by
  simp only [Components.scalarWithLean, Components.scalar, scalarSumWithLean_eq, add32WithLean_eq]

/-- Algorithm 1 with native FP32 scalar additions. -/
def tcEftWithLean (variant : Variant) (x : BlockInput variant.model) (D : F32) : Except Error Result := do
  let p ← prepare variant x D
  if p.terms.all (fun t => t.word.magnitude == 0) then return .allZero
  let some c := extract p | throw .arithmeticOverflow
  match c.scalarWithLean with
  | some b => return .scalar b
  | none =>
    match c.recovered.round32 with
    | some b => return .boundedExact b
    | none => return .outOfRange

/-- The same result as `tcEft` on every input, including branch tags and errors. -/
theorem tcEftWithLean_eq (variant : Variant) (x : BlockInput variant.model) (D : F32) :
    tcEftWithLean variant x D = tcEft variant x D := by
  simp only [tcEftWithLean, tcEft, Components.scalarWithLean_eq]
  rfl

theorem tcEftWithLean_correct {variant : Variant} {x : BlockInput variant.model}
    {D : F32} {s d : ℚ} (hlen : x.products.length = variant.model.nfma)
    (hx : TensorCore.exactDot x = some s) (hD : TensorCore.value32 D = some d) :
    ∃ r, tcEftWithLean variant x D = .ok r ∧ r.bits = TensorCore.round32 .nearestEven s := by
  rw [tcEftWithLean_eq]
  exact tcEft_correct hlen hx hD

theorem tcEftWithLean_success {variant : Variant} {x : BlockInput variant.model}
    {D : F32} {s d : ℚ} (hlen : x.products.length = variant.model.nfma)
    (hx : TensorCore.exactDot x = some s) (hD : TensorCore.value32 D = some d)
    (hrange : absQ s ≤ maxFinite32) :
    ∃ r b, tcEftWithLean variant x D = .ok r ∧ r.bits = some b ∧ NearestEven32 s b := by
  rw [tcEftWithLean_eq]
  exact tcEft_success hlen hx hD hrange

theorem tcEftWithLean_range_iff {variant : Variant} {x : BlockInput variant.model}
    {D : F32} {s d : ℚ} (hlen : x.products.length = variant.model.nfma)
    (hx : TensorCore.exactDot x = some s) (hD : TensorCore.value32 D = some d) :
    (∃ r b, tcEftWithLean variant x D = .ok r ∧ r.bits = some b) ↔ absQ s ≤ maxFinite32 := by
  rw [tcEftWithLean_eq]
  exact tcEft_range_iff hlen hx hD

end TensorCore.EFMachine
