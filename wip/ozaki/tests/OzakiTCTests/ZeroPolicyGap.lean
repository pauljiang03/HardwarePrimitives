import OzakiTC.ADPZeroPolicyGap

/-! # The gap between the zero-policy conditions, on explicit words

`OzakiTC/ADPZeroPolicyGap.lean`'s results on one family of exponent patterns, checked by kernel
evaluation with the default configuration (block size `2`, speed ratio `100`) and zeros skipped:
the row `x = (2^ep, x₁, 0, 0)` with `x₁ ∈ [1, 2)` against the column `y = (0, 1, 0, 0)`. Skipping
zeros gives the matrix ESC `0`, so `W = 54`, and `x₁` loses `D = ep − 1` bits; the entry's exact ESC
is `ep`, so `adpPolicy_entry_gradeA` never applies.

* **`ep = 5` (`D = 4`), inside the original gap.** `adpPolicy_unmasked_fails_left`'s condition fails
  (`36 u < 16 u`), yet the pattern admits both outcomes: `x₁ = 1` meets Grade A and
  `x₁ = 1 + 15 · 2^-52` (every dropped bit set) breaks it. The worst-case condition of
  `adpPolicy_unmasked_fails_full_left` holds (`18 (1 + 2^-48) u < 30 u`), and
  `adpPolicy_pattern_undecided_left` applies to the original words.
* **`ep = 3` (`D = 2`).** The loss-aware sufficient condition holds (`Dx = 2`, `Dy = −1`:
  `Λ + u (1 + Λ) ≈ 10 u ≤ 17 u`), so every input with the pattern meets Grade A; checked on the
  worst-case input `x₁ = 1 + 3 · 2^-52` through `adpPolicy_entry_gradeA_loss`.
* **`ep = 4` (`D = 3`), the band both theorems leave.** Neither condition holds (`≈ 18 u ≤ 17 u`
  fails, `18 u < 14 u` fails); the worst-case input `x₁ = 1 + 7 · 2^-52` still meets Grade A
  (its error `14 u` is below `17 u`). -/

open TensorCore Ozaki Ozaki.TC Ozaki.ADP

namespace OzakiTCTests.ZeroPolicyGap

def w1 : BitVec 64 := 0x3FF0000000000000
def w8 : BitVec 64 := 0x4020000000000000
def w16 : BitVec 64 := 0x4030000000000000
def w32 : BitVec 64 := 0x4040000000000000
/-- `1 + 3 · 2^-52`, `1 + 7 · 2^-52`, `1 + 15 · 2^-52`: the low `2`, `3`, `4` bits set. -/
def w1p2 : BitVec 64 := 0x3FF0000000000003
def w1p3 : BitVec 64 := 0x3FF0000000000007
def w1p4 : BitVec 64 := 0x3FF000000000000F

/-- The column `y = (0, 1, 0, 0)`. -/
def B : List (List (BitVec 64)) := [[0], [w1], [0], [0]]
def yq : List ℚ := [0, 1, 0, 0]
def Bq : List (List ℚ) := yq.map fun v => [v]

def emulatedGradeA (r : ADPPath × Option (List (List ℚ))) (Aq Bq : List (List ℚ)) : Bool :=
  match r with
  | (.emulated, some C) => gradeA Aq Bq C
  | _ => false

example : decodeMatrix64 B = some Bq := by decide +kernel
example : adpWidth 0 = 54 := by decide

theorem keeps_y : KeepsLead ((adpWidth 0 : ℕ) : ℤ) yq := by
  intro ep hep v hv h0
  have hm : maxE (expsOf yq) = some 0 := by decide +kernel
  rw [hm] at hep; cases hep
  simp only [yq, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact absurd rfl h0
  · decide +kernel
  · exact absurd rfl h0
  · exact absurd rfl h0

/-! ## `ep = 5`: both outcomes in the original gap -/

def x5 : List ℚ := [2 ^ (5 : ℤ), 1, 0, 0]
def A5 : List (List (BitVec 64)) := [[w32, w1, 0, 0]]
def A5' : List (List (BitVec 64)) := [[w32, w1p4, 0, 0]]
def x5' : List ℚ := [2 ^ (5 : ℤ), 1 + 15 * 2 ^ (-52 : ℤ), 0, 0]

example : decodeMatrix64 A5 = some [x5] := by decide +kernel
example : decodeMatrix64 A5' = some [x5'] := by decide +kernel
/-- Same exponent pattern, same matrix ESC `0`. -/
example : [x5].map expsOf = [x5'].map expsOf := by decide +kernel
example : matrixEscPolicy .skip 2 [x5] (transpose Bq) = some 0 := by decide +kernel
example : matrixEscPolicy .skip 2 [x5'] (transpose Bq) = some 0 := by decide +kernel
/-- The entry's exact ESC is `5 > 0`: the sufficient condition does not apply. -/
example : escExact x5 yq = 5 := by decide +kernel
/-- The original necessary condition fails: `36 u` is not below `16 u`. -/
example : ¬ ((8 * ((4 : ℕ) : ℚ) + 4) * 2 ^ (-53 : ℤ) * patSum (expsOf x5) (expsOf yq) +
    2 ^ (-1074 : ℤ) < 2 ^ ((0 : ℤ) + 0 - 53 + min 4 53)) := by decide +kernel
/-- The worst-case condition holds: `18 (1 + 2^-48) u < 30 u`. -/
example : (4 * ((4 : ℕ) : ℚ) + 2) * fullBeta 4 * 2 ^ (-53 : ℤ) * patSum (expsOf x5) (expsOf yq) +
    2 ^ (-1074 : ℤ) < fullLossAmt 0 4 * 2 ^ exp64 (1 : ℚ) := by decide +kernel
/-- `x₁ = 1` meets Grade A … -/
example : emulatedGradeA (adpPolicy {} .skip A5 B) [x5] Bq = true := by decide +kernel
/-- … `x₁ = 1 + 15 · 2^-52`, with the same pattern, breaks it. -/
example : adpPolicy {} .skip A5' B = (.emulated, some [[1]]) := by decide +kernel
example : gradeAEntry x5' yq 1 = false := by decide +kernel
/-- The paper's policy meets Grade A on both. -/
example : emulatedGradeA (adp {} A5 B) [x5] Bq = true := by decide +kernel
example : emulatedGradeA (adp {} A5' B) [x5'] Bq = true := by decide +kernel

theorem keeps_x5 : KeepsLead ((adpWidth 0 : ℕ) : ℤ) x5 := by
  intro ep hep v hv h0
  have hm : maxE (expsOf x5) = some 5 := by decide +kernel
  rw [hm] at hep; cases hep
  simp only [x5, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · exact absurd rfl h0
  · exact absurd rfl h0

/-- **`adpPolicy_pattern_undecided_left` on the original words**: the powers of two meet Grade A,
the worst-case input breaks it, with the same matrix ESC and path. -/
example := adpPolicy_pattern_undecided_left (cfg := {}) (pol := .skip) (A := A5) (B := B)
    (Aq := [x5]) (Bq := Bq)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (i := 0) (j := 0) (t := 1) (x := x5) (y := yq) (by decide +kernel) (by decide +kernel)
    (a := 1) (b := 1) (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (ep := 5) (e := 0) (D := 4) (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (by decide +kernel) keeps_x5 keeps_y

/-! ## `ep = 3`: every input meets Grade A, by the loss-aware condition -/

def x3' : List ℚ := [2 ^ (3 : ℤ), 1 + 3 * 2 ^ (-52 : ℤ), 0, 0]
def A3' : List (List (BitVec 64)) := [[w8, w1p2, 0, 0]]

example : decodeMatrix64 A3' = some [x3'] := by decide +kernel
example : matrixEscPolicy .skip 2 [x3'] (transpose Bq) = some 0 := by decide +kernel
example : escExact x3' yq = 3 := by decide +kernel
example : adpPolicy {} .skip A3' B = (.emulated, some [[1]]) := by decide +kernel
/-- `Λ + u (1 + Λ) ≤ 17 u` for `Dx = 2`, `Dy = −1`. -/
example : lossFactor 2 (-1) + 2 ^ (-53 : ℤ) * (1 + lossFactor 2 (-1)) ≤
    (4 * ((4 : ℕ) : ℚ) + 1) * 2 ^ (-53 : ℤ) := by decide +kernel

theorem loss_x3 : ∀ ep, maxE (expsOf x3') = some ep → ∀ a ∈ x3', a ≠ 0 →
    ep - exp64 a + 53 - ((adpWidth 0 : ℕ) : ℤ) ≤ 2 := by
  intro ep hep v hv h0
  have hm : maxE (expsOf x3') = some 3 := by decide +kernel
  rw [hm] at hep; cases hep
  simp only [x3', List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · exact absurd rfl h0
  · exact absurd rfl h0

theorem loss_y : ∀ eq, maxE (expsOf yq) = some eq → ∀ b ∈ yq, b ≠ 0 →
    eq - exp64 b + 53 - ((adpWidth 0 : ℕ) : ℤ) ≤ -1 := by
  intro eq heq v hv h0
  have hm : maxE (expsOf yq) = some 0 := by decide +kernel
  rw [hm] at heq; cases heq
  simp only [yq, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact absurd rfl h0
  · decide +kernel
  · exact absurd rfl h0
  · exact absurd rfl h0

theorem normal_x3 : ∀ a ∈ [x3'][0], Normal64 a := by
  intro a ha
  simp only [x3', List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at ha
  unfold Normal64
  rcases ha with rfl | rfl | rfl | rfl
  · right; decide +kernel
  · right; decide +kernel
  · left; rfl
  · left; rfl

theorem normal_y : ∀ b ∈ (transpose Bq)[0], Normal64 b := by
  have ht : (transpose Bq)[0] = yq := by decide +kernel
  rw [ht]
  intro b hb
  simp only [yq, List.mem_cons, List.not_mem_nil, or_false] at hb
  unfold Normal64
  rcases hb with rfl | rfl | rfl | rfl
  · left; rfl
  · right; decide +kernel
  · left; rfl
  · left; rfl

/-- **`adpPolicy_entry_gradeA_loss` on the worst-case input of the pattern.** -/
example : gradeAEntry x3' yq 1 = true := by
  obtain ⟨_, _, h⟩ := adpPolicy_entry_gradeA_loss (cfg := {}) (pol := .skip) (A := A3') (B := B)
    (C := [[1]]) (Aq := [x3']) (Bq := Bq) (by decide +kernel) (by decide +kernel) (by decide +kernel) (e := 0)
    (by decide +kernel) (i := 0) (j := 0) (by decide) (by decide +kernel)
    normal_x3 normal_y (by decide +kernel) (Dx := 2) (Dy := -1)
    loss_x3 loss_y (by decide +kernel)
  exact h

/-! ## `ep = 4`: the band neither theorem decides -/

def x4' : List ℚ := [2 ^ (4 : ℤ), 1 + 7 * 2 ^ (-52 : ℤ), 0, 0]
def A4' : List (List (BitVec 64)) := [[w16, w1p3, 0, 0]]

example : decodeMatrix64 A4' = some [x4'] := by decide +kernel
example : matrixEscPolicy .skip 2 [x4'] (transpose Bq) = some 0 := by decide +kernel
/-- The loss-aware sufficient condition fails for `Dx = 3`, `Dy = −1` … -/
example : ¬ (lossFactor 3 (-1) + 2 ^ (-53 : ℤ) * (1 + lossFactor 3 (-1)) ≤
    (4 * ((4 : ℕ) : ℚ) + 1) * 2 ^ (-53 : ℤ)) := by decide +kernel
/-- … and so does the worst-case necessary condition (`18 u < 14 u`) … -/
example : ¬ ((4 * ((4 : ℕ) : ℚ) + 2) * fullBeta 3 * 2 ^ (-53 : ℤ) *
    patSum (expsOf x4') (expsOf yq) + 2 ^ (-1074 : ℤ) < fullLossAmt 0 3 * 2 ^ exp64 (1 : ℚ)) := by
  decide +kernel
/-- … while the worst-case input still meets Grade A. -/
example : adpPolicy {} .skip A4' B = (.emulated, some [[1]]) := by decide +kernel
example : gradeAEntry x4' yq 1 = true := by decide +kernel

end OzakiTCTests.ZeroPolicyGap
