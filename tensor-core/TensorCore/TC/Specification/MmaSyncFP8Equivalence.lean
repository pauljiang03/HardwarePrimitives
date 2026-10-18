import TensorCore.TC.MmaSyncFP8
import TensorCore.TC.Specification.MmaSyncFP8
import TensorCore.TC.Specification.OutputWidth
import TensorCore.TC.Specification.Rounding

/-! The FP8 `mma.sync` model equals its independent specification on every input. -/

namespace TensorCore.IndependentSpec

theorem zipIdx_firstPairs : ∀ (xs : List α) (n : ℕ), n % 4 = 0 →
    ((xs.zipIdx n).filter fun x => decide (x.2 % 4 < 2)).map Prod.fst = firstPairs xs
  | [], _, _ => rfl
  | [a], n, h => by
    have h0 : n % 4 < 2 := by omega
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.filter_cons, List.filter_nil, decide_eq_true_eq, ↓reduceIte, List.map_cons, List.map_nil, h0]; rfl
  | [a, b], n, h => by
    have h0 : n % 4 < 2 := by omega
    have h1 : (n + 1) % 4 < 2 := by omega
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.filter_cons, List.filter_nil, decide_eq_true_eq, ↓reduceIte, List.map_cons, List.map_nil, h0, h1]; rfl
  | [a, b, c], n, h => by
    have h0 : n % 4 < 2 := by omega
    have h1 : (n + 1) % 4 < 2 := by omega
    have h2 : ¬ (n + 1 + 1) % 4 < 2 := by omega
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.filter_cons, List.filter_nil, decide_eq_true_eq, ↓reduceIte, List.map_cons, List.map_nil, h0, h1, h2]; rfl
  | a :: b :: c :: d :: rest, n, h => by
    have h0 : n % 4 < 2 := by omega
    have h1 : (n + 1) % 4 < 2 := by omega
    have h2 : ¬ (n + 1 + 1) % 4 < 2 := by omega
    have h3 : ¬ (n + 1 + 1 + 1) % 4 < 2 := by omega
    simp only [List.zipIdx_cons, List.filter_cons, decide_eq_true_eq, h0, h1, h2, h3, ↓reduceIte,
      List.map_cons, firstPairs]
    rw [show n + 1 + 1 + 1 + 1 = n + 4 by omega, zipIdx_firstPairs rest (n + 4) (by omega)]

theorem zipIdx_secondPairs : ∀ (xs : List α) (n : ℕ), n % 4 = 0 →
    ((xs.zipIdx n).filter fun x => decide (2 ≤ x.2 % 4)).map Prod.fst = secondPairs xs
  | [], _, _ => rfl
  | [a], n, h => by
    have h0 : ¬ 2 ≤ n % 4 := by omega
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.filter_cons, List.filter_nil, decide_eq_true_eq, ↓reduceIte, List.map_nil, h0]; rfl
  | [a, b], n, h => by
    have h0 : ¬ 2 ≤ n % 4 := by omega
    have h1 : ¬ 2 ≤ (n + 1) % 4 := by omega
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.filter_cons, List.filter_nil, decide_eq_true_eq, ↓reduceIte, List.map_nil, h0, h1]; rfl
  | [a, b, c], n, h => by
    have h0 : ¬ 2 ≤ n % 4 := by omega
    have h1 : ¬ 2 ≤ (n + 1) % 4 := by omega
    have h2 : 2 ≤ (n + 1 + 1) % 4 := by omega
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.filter_cons, List.filter_nil, decide_eq_true_eq, ↓reduceIte, List.map_cons, List.map_nil, h0, h1, h2]; rfl
  | a :: b :: c :: d :: rest, n, h => by
    have h0 : ¬ 2 ≤ n % 4 := by omega
    have h1 : ¬ 2 ≤ (n + 1) % 4 := by omega
    have h2 : 2 ≤ (n + 1 + 1) % 4 := by omega
    have h3 : 2 ≤ (n + 1 + 1 + 1) % 4 := by omega
    simp only [List.zipIdx_cons, List.filter_cons, decide_eq_true_eq, h0, h1, h2, h3, ↓reduceIte,
      List.map_cons, secondPairs]
    rw [show n + 1 + 1 + 1 + 1 = n + 4 by omega, zipIdx_secondPairs rest (n + 4) (by omega)]

theorem groupA_eq (xs : List α) : groupA xs = firstPairs xs := zipIdx_firstPairs xs 0 rfl

theorem groupB_eq (xs : List α) : groupB xs = secondPairs xs := zipIdx_secondPairs xs 0 rfl

theorem hopperFP16_eq : parametersOf hopperF16F32 = hopperFP16 := rfl

/-- One FP16 block FMA of the Hopper model is the block specification. -/
theorem hmma_iff (c0 : F32) (g : List (F16 × F16)) (d : F32) :
    hmma c0 g = some d ↔ ResultM hopperFP16 23 ⟨padPairs 16 g, c0⟩ d := by
  have h := resultM_iff_eval (p := hopperF16F32) ⟨padTo 16 g, c0⟩ d
  unfold hmma
  change _ ↔ ResultM (parametersOf hopperF16F32) hopperF16F32.outputMantissaBits
    (inputOf (⟨padTo 16 g, c0⟩ : BlockInput hopperF16F32)) d
  rw [h]
  cases he : evalBlock (p := hopperF16F32) ⟨padTo 16 g, c0⟩ with
  | error e => simp [Except.toOption]
  | ok t => simp [Except.toOption]

/-- The final FP32 addition is the round-to-nearest-even specification. -/
theorem addFp32_iff (d c bits : F32) :
    addFp32 d c = some bits ↔ ∃ v₂ vc, value32 d = some v₂ ∧ value32 c = some vc ∧
      magnitude (v₂ + vc) ≤ maxFinite ∧ RoundsNearestEven (v₂ + vc) bits := by
  simp only [value32_eq]
  unfold addFp32
  cases hd : TensorCore.value32 d with
  | none => simp
  | some v₂ =>
    cases hc : TensorCore.value32 c with
    | none => simp
    | some vc =>
      simp only [Option.bind_eq_bind, Option.bind_some, Option.some.injEq, exists_and_left,
        exists_eq_left']
      constructor
      · intro h
        exact ⟨round32_range h, round32_nearestEven_rounds _ _ h⟩
      · rintro ⟨hr, hs⟩
        exact (roundsNearestEven_iff _ _ hr).mp hs

/-- The FP8 `mma.sync` model returns a word exactly when the specification does, and the same
word. -/
theorem mmaSyncFP8_eq_spec (conv : BitVec 8 → F16) (c : F32) (ps : List (BitVec 8 × BitVec 8))
    (bits : F32) : mmaSyncFP8 conv c ps = some bits ↔ MmaSyncFP8Result conv c ps bits := by
  unfold mmaSyncFP8 MmaSyncFP8Result
  simp only [groupA_eq, groupB_eq, Option.bind_eq_bind, Option.bind_eq_some_iff, hmma_iff,
    addFp32_iff]
  constructor
  · rintro ⟨d₁, h₁, d₂, h₂, v₂, vc, hv₂, hvc, hr, hs⟩
    exact ⟨d₁, d₂, v₂, vc, h₁, h₂, hv₂, hvc, hr, hs⟩
  · rintro ⟨d₁, d₂, v₂, vc, h₁, h₂, hv₂, hvc, hr, hs⟩
    exact ⟨d₁, h₁, d₂, h₂, v₂, vc, hv₂, hvc, hr, hs⟩

end TensorCore.IndependentSpec
