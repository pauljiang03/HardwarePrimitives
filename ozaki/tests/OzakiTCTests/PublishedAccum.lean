import Ozaki.UchinoCRT

/-! # Accumulation by levels and the floating-point CRT reconstruction, on numbers

**Accumulation by levels** (`Ozaki.AbdelfattahAcc`). Ozaki-I with six `11`-bit slices on a
binary64 vector pair: the `21` exact slice products are grouped into three levels of two
diagonals each, every level passes the run-time check `levelOKB` for binary64 on the grid of its
finer diagonal, and the level accumulation (`levelAcc`, two rounded additions) is within the bound
of `ozaki1Levels_error` of `x · y`.

**Uchino, Ozaki and Imamura's reconstruction** (`Ozaki.UchinoCRT`). The first twelve moduli of
their table (`P ≈ 2^95`), the standard CRT weights, high parts on the grid `2^53` (their
`⌈log₂ ρ⌉ + ⌊log₂ max w⌋ + 1 − 53` here), low parts, `P1`, `P2` and `P_inv` all rounded to
binary64. For an `88`-bit product `c` of scaled integers the residues' weighted sum is `q P + c`,
the margin of `uchinoRecon_error` holds, and the binary64 reconstruction is within its bound,
about `3 u |c|`; a product below `2^53` comes back within the absolute accumulation error, not
exactly. -/

local notation "ℕ" => Nat
local notation "ℤ" => Int
local notation "ℚ" => Rat

open Ozaki

namespace OzakiTCTests.PublishedAccum

/-! ## Accumulation by levels -/

def x : List ℚ := [3 / 7, -5 / 11, 1 / 3, 7 / 13]
def y : List ℚ := [2 / 9, 4 / 17, -6 / 19, 1 / 23]

/-- The grid of slice pair `(t, u)`. -/
def pairGrid (t u : ℕ) : ℤ :=
  ((split 11 6 x).1.getD t default).grid + ((split 11 6 y).1.getD u default).grid

/-- The products of the diagonals `d` in a list, as a left-to-right tree. -/
def diagTerms (ds : List ℕ) : List ℚ :=
  ds.flatMap fun d => (List.range (d + 1)).map fun t =>
    exactTerm (split 11 6 x).1 (split 11 6 y).1 (t, d - t)

def comb : List ℚ → SumTree
  | [] => .leaf 0
  | [t] => .leaf t
  | t :: ts => .node (.leaf t) (comb ts)

theorem comb_leaves : ∀ ts : List ℚ, ts ≠ [] → (comb ts).leaves = ts
  | [], h => absurd rfl h
  | [t], _ => rfl
  | t :: u :: ts, _ => by
    simp only [comb, SumTree.leaves, List.singleton_append]
    rw [comb_leaves (u :: ts) (by simp)]

def levels : List SumTree := [comb (diagTerms [5, 4]), comb (diagTerms [3, 2]), comb (diagTerms [1, 0])]

/-- The finest grid of the slice pairs of the diagonals `ds`. -/
def levelGrid (ds : List ℕ) : ℤ :=
  (ds.flatMap fun d => (List.range (d + 1)).map fun t => pairGrid t (d - t)).foldl min 1000

/-- Every level passes the check on its finest grid. -/
example : levelOKB 53 (-1022) 1023 (levelGrid [5, 4]) (diagTerms [5, 4]) = true ∧
    levelOKB 53 (-1022) 1023 (levelGrid [3, 2]) (diagTerms [3, 2]) = true ∧
    levelOKB 53 (-1022) 1023 (levelGrid [1, 0]) (diagTerms [1, 0]) = true := by decide +kernel

/-- The levels hold exactly the slice products of Ozaki-I. -/
example : (levels.flatMap SumTree.leaves).Perm (exactTerms 11 6 x y) := by
  rw [show levels.flatMap SumTree.leaves = diagTerms [5, 4] ++ diagTerms [3, 2] ++ diagTerms [1, 0] by
    simp only [levels, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
    rw [comb_leaves _ (by decide +kernel), comb_leaves _ (by decide +kernel),
      comb_leaves _ (by decide +kernel)]]
  exact List.Perm.of_eq (by decide +kernel)

/-- The accumulation by levels returns a value within the bound of `ozaki1Levels_error`. -/
example : ∃ v, levelAcc (roundRNE 53 (-1022) 1023) levels = some v ∧
    Rat.abs (v - dot x y) ≤
      ((levels.length - 1 : ℕ) : ℚ) * 2 ^ (-(53 : ℤ)) *
          (levels.map fun T => Rat.abs T.leaves.sum).sum +
        ((6 + 1 : ℕ) : ℚ) * x.length * 2 ^ (splitExp 11 x + splitExp 11 y - 6 * (11 + 1)) := by
  decide +kernel

/-! ## The floating-point CRT reconstruction -/

def moduli12 : List ℕ := [256, 255, 253, 251, 247, 241, 239, 233, 229, 227, 223, 217]
def B : CRTBasis := crtBasis moduli12
def P : ℕ := B.modulus
def G1 : ℤ := 53

/-- The scaled integers and their product, near `2^90`. -/
def a : List ℤ := [2 ^ 44 + 12345, -(2 ^ 43) + 678, 2 ^ 42 - 91]
def c : List ℤ := [2 ^ 45 - 7, 2 ^ 44 + 13, -(2 ^ 45) + 999]
def cprod : ℤ := dotZ a c

def W : List ℤ := moduli12.map fun m => symMod cprod m
def P1 : ℚ := (roundRNE 53 (-1022) 1023 (P : ℚ)).getD 0
def P2 : ℚ := (roundRNE 53 (-1022) 1023 ((P : ℚ) - P1)).getD 0
def Pinv : ℚ := (roundRNE 53 (-1022) 1023 (1 / (P : ℚ))).getD 0
def s2 : List ℚ :=
  (B.weights.mapM fun w : ℤ => roundRNE 53 (-1022) 1023 ((w : ℚ) - weightHi G1 w)).getD []
def q : ℤ := (dotZ B.weights W - cprod) / P

/-- The weighted sum is `q P + c`. -/
example : dotZ B.weights W = q * P + cprod := by decide +kernel

/-- The high parts' products fit binary64 on the grid `2^53`. -/
example : (List.zipWith (fun a r : ℤ => (((a * r).natAbs : ℕ) : ℚ)) B.weights W).sum <
    2 ^ ((53 : ℤ) + G1) := by decide +kernel

/-- The margin of `uchinoRecon_error` holds. -/
example : 2 * (Rat.abs (cprod : ℚ) +
    uchinoDelta (2 ^ (-(53 : ℤ))) (2 ^ (-1075 : ℤ)) P Pinv G1 B.weights W) < P := by
  decide +kernel

/-- The binary64 reconstruction returns a value within the bound of `uchinoRecon_error`, which
is about `3 u |c|` here: an `88`-bit product does not fit binary64, so the reconstructed value is
rounded. -/
example : ∃ v, uchinoRecon (roundRNE 53 (-1022) 1023) P1 P2 Pinv (B.weights.map (weightHi G1)) s2 W =
    some v ∧ Rat.abs (v - cprod) ≤
      uchinoBound (2 ^ (-(53 : ℤ))) (2 ^ (-1075 : ℤ)) P P1 P2 q cprod G1 B.weights W s2 ∧
    uchinoBound (2 ^ (-(53 : ℤ))) (2 ^ (-1075 : ℤ)) P P1 P2 q cprod G1 B.weights W s2 ≤
      4 * 2 ^ (-(53 : ℤ)) * Rat.abs (cprod : ℚ) := by
  decide +kernel

/-- A product below `2^53` is not reconstructed exactly either: the accumulation error is of the
order of `u² ρ P` in absolute terms (their Lemma 3), `57` here, within the bound. -/
def cs : ℤ := 2 ^ 52 - 12345
def Ws : List ℤ := moduli12.map fun m => symMod cs m
def qs : ℤ := (dotZ B.weights Ws - cs) / P

example : dotZ B.weights Ws = qs * P + cs ∧
    2 * (Rat.abs (cs : ℚ) + uchinoDelta (2 ^ (-(53 : ℤ))) (2 ^ (-1075 : ℤ)) P Pinv G1 B.weights Ws) < P ∧
    ∃ v, uchinoRecon (roundRNE 53 (-1022) 1023) P1 P2 Pinv (B.weights.map (weightHi G1)) s2 Ws =
      some v ∧ v ≠ cs ∧ Rat.abs (v - cs) ≤
        uchinoBound (2 ^ (-(53 : ℤ))) (2 ^ (-1075 : ℤ)) P P1 P2 qs cs G1 B.weights Ws s2 := by
  decide +kernel

end OzakiTCTests.PublishedAccum
