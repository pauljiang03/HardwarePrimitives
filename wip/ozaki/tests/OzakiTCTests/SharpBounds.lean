import OzakiTCTests.Accuracy
import OzakiTCTests.Correct
import OzakiTC.SharpBounds

/-! # The sharper bounds on the test matrices

For every entry of the Z3 models' two binary32 cases (`4 × 4`, `k = 4`), of the two binary64
oracle cases (`k = 8`), and of two constructed inputs, kernel evaluation checks that the actual
error is within each sharper bound and each sharper bound within the bound it replaces:

* Ozaki-I with `4` slices of `11` bits (`5` for binary64): the slicing error
  `|x · y − Σ terms| ≤ (s + 1) Σᵢ min(2|xᵢyᵢ|, 2^(E+F−s(b+1)))` (`exactTerms_error_sharp`)
  `≤ (s + 1) k 2^(E+F−s(b+1))` (`exactTerms_error`);
* Ozaki-II's truncation with `P = 22` (`P = 69` for binary64): the actual error, the componentwise
  bound of `truncProduct_error`, the mixed bound `2^(−sₓ) Σ|yᵢ| + 2^(−s_y) Σ|xᵢ|`
  (`truncProduct_error_mixed`), `4 k max|x| max|y| 2^(−P)` (`truncProduct_error_normwise4`) and
  `8 k max|x| max|y| 2^(−P)` (`truncProduct_error_normwise`), in increasing order;
* native binary32 (binary64) dot products: the actual error, `k u Σ|xᵢyᵢ|` (Jeannerod and Rump,
  `nativeDot_error_jr_rne32`, every product normal) and `γₖ Σ|xᵢyᵢ| + 2k (1 + u)^k η`
  (`nativeDot_error_gamma`), in increasing order.

The ratios printed by `#eval` (largest and smallest, over all entries) show how much tighter each
sharper bound is. -/

open TensorCore Ozaki Ozaki.TC OzakiTCTests.Z3Matrices

namespace OzakiTCTests.SharpBounds

/-- Every (row, column) pair of `A` and `B` (`B` by rows). -/
def pairs (A B : List (List ℚ)) : List (List ℚ × List ℚ) :=
  A.flatMap fun x => (transpose B).map fun y => (x, y)

/-- Ozaki-I with `s` slices of `b` bits: actual slicing error, entrywise bound, normwise bound. -/
def ozaki1Bounds (b s : ℕ) (x y : List ℚ) : ℚ × ℚ × ℚ :=
  let M : ℚ := 2 ^ (splitExp b x + splitExp b y - s * (b + 1))
  (Rat.abs (dot x y - (exactTerms b s x y).sum), ((s + 1 : ℕ) : ℚ) * capSum M x y,
    ((s + 1 : ℕ) : ℚ) * x.length * M)

/-- Ozaki-II's truncation with `P` bits: actual error, componentwise, mixed, `4k`, `8k`. -/
def ozaki2Bounds (P : ℕ) (x y : List ℚ) : ℚ × ℚ × ℚ × ℚ × ℚ :=
  let sx := scaleShift P x
  let sy := scaleShift P y
  (Rat.abs (dot x y - 2 ^ (-(sx + sy)) * (dotZ (scaleTrunc sx x) (scaleTrunc sy y) : ℚ)),
   (List.zipWith (fun a b => 2 ^ (-sx) * Rat.abs b +
      2 ^ (-(sx + sy)) * Rat.abs (truncInt (a * 2 ^ sx) : ℚ)) x y).sum,
   2 ^ (-sx) * absSum y + 2 ^ (-sy) * absSum x,
   4 * x.length * maxAbs x * maxAbs y * 2 ^ (-(P : ℤ)),
   8 * x.length * maxAbs x * maxAbs y * 2 ^ (-(P : ℤ)))

/-- A native dot product with rounding `rnd` of unit roundoff `u` and underflow term `η`: actual
error, Jeannerod and Rump's `k u Σ|xᵢyᵢ|`, and the `γₖ` bound. -/
def nativeBounds (u η : ℚ) (rnd : ℚ → Option ℚ) (x y : List ℚ) : Option (ℚ × ℚ × ℚ) := do
  let v ← nativeDot rnd x y
  let k : ℚ := x.length
  let S := ((List.zipWith (· * ·) x y).map Rat.abs).sum
  pure (Rat.abs (v - dot x y), k * u * S,
    k * u / (1 - k * u) * S + 2 * k * (1 + u) ^ x.length * η)

/-- Every product is zero or at least `2^emin` (no underflow, the hypothesis of
`nativeDot_error_jr_rne32`). -/
def normalProducts (emin : ℤ) (x y : List ℚ) : Bool :=
  (List.zipWith (· * ·) x y).all fun z => z == 0 || decide ((2 : ℚ) ^ emin ≤ Rat.abs z)

def ok1 (b s : ℕ) (A B : List (List ℚ)) : Bool :=
  (pairs A B).all fun (x, y) =>
    let (e, sh, n) := ozaki1Bounds b s x y
    decide (e ≤ sh) && decide (sh ≤ n)

def ok2 (P : ℕ) (A B : List (List ℚ)) : Bool :=
  (pairs A B).all fun (x, y) =>
    let (e, c, m, n4, n8) := ozaki2Bounds P x y
    decide (e ≤ c) && decide (c ≤ m) && decide (m ≤ n4) && decide (n4 ≤ n8)

def okN (emin : ℤ) (u η : ℚ) (rnd : ℚ → Option ℚ) (A B : List (List ℚ)) : Bool :=
  (pairs A B).all fun (x, y) =>
    normalProducts emin x y &&
    match nativeBounds u η rnd x y with
    | some (e, jr, g) => decide (e ≤ jr) && decide (jr ≤ g)
    | none => false

/-! ## The Z3 models' binary32 cases -/

example : (do
    let A ← decodeMatrix A_narrow; let B ← decodeMatrix B_narrow
    pure (ok1 11 4 A B && ok2 22 A B && okN (-126) (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) rne32Q A B)) =
    some true := by decide +kernel

example : (do
    let A ← decodeMatrix A_wide; let B ← decodeMatrix B_wide
    pure (ok1 11 4 A B && ok2 22 A B && okN (-126) (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) rne32Q A B)) =
    some true := by decide +kernel

/-! ## The binary64 oracle cases -/

example : (do
    let A ← OzakiTCTests.Correct.decode64 OzakiTCTests.Correct.A_narrow64
    let B ← OzakiTCTests.Correct.decode64 OzakiTCTests.Correct.B_narrow64
    pure (ok1 11 5 A B && ok2 69 A B &&
      okN (-1022) (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) rne64 A B)) = some true := by decide +kernel

example : (do
    let A ← OzakiTCTests.Correct.decode64 OzakiTCTests.Correct.A_wide64
    let B ← OzakiTCTests.Correct.decode64 OzakiTCTests.Correct.B_wide64
    pure (ok1 11 5 A B && ok2 69 A B &&
      okN (-1022) (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) rne64 A B)) = some true := by decide +kernel

/-! ## Constructed inputs

A badly scaled row against a column with one large entry: the entrywise Ozaki-I bound counts only
the large product. Rows and columns with disjoint supports: every product is zero, the entrywise
bound is `0`, and the exact terms add up to `x · y = 0` (`exactTerms_eq_of_products_zero`). -/

def badX : List ℚ := [1, 2 ^ (-30 : ℤ), 2 ^ (-40 : ℤ), 2 ^ (-50 : ℤ)]
def badY : List ℚ := [1, 2 ^ (-20 : ℤ), 2 ^ (-20 : ℤ), 2 ^ (-20 : ℤ)]
def disjX : List ℚ := [3, 0, 5, 0]
def disjY : List ℚ := [0, 7, 0, 1 / 3]

example : ok1 11 2 [badX] (transpose [badY]) = true := by decide +kernel
example : ((ozaki1Bounds 11 2 disjX disjY).2.1 = 0) ∧
    (exactTerms 11 2 disjX disjY).sum = dot disjX disjY := by decide +kernel

/-! ## How much tighter -/

/-- `q` to `30` binary places, as a float (the rationals here have huge denominators). -/
def toF (q : ℚ) : Float := Float.ofInt (q * 2 ^ (30 : ℤ)).floor / 1073741824

/-- Largest and smallest ratio `old / new` over all entries (entries where `new = 0` skipped). -/
def ratios (l : List (ℚ × ℚ)) : Float × Float :=
  let rs := (l.filter fun p => p.2 ≠ 0).map fun p => toF (p.1 / p.2)
  (rs.foldl max 0, rs.foldl min 1e300)

def report (b s P : ℕ) (u η : ℚ) (rnd : ℚ → Option ℚ) (A B : List (List ℚ)) :
    (Float × Float) × (Float × Float) × (Float × Float) :=
  (ratios ((pairs A B).map fun (x, y) => let (_, sh, n) := ozaki1Bounds b s x y; (n, sh)),
   ratios ((pairs A B).map fun (x, y) => let (_, _, m, _, n8) := ozaki2Bounds P x y; (n8, m)),
   ratios ((pairs A B).filterMap fun (x, y) =>
     (nativeBounds u η rnd x y).map fun (_, jr, g) => (g - jr, jr * u)))

-- Ozaki-I normwise / entrywise, Ozaki-II `8k` / mixed, and native (`γₖ` − Jeannerod–Rump) / (JR · u):
-- the native gain is second order, `≈ k u` relative (plus the underflow term).
#eval do
  let A ← decodeMatrix A_narrow; let B ← decodeMatrix B_narrow
  pure (report 11 4 22 (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) rne32Q A B)
#eval do
  let A ← decodeMatrix A_wide; let B ← decodeMatrix B_wide
  pure (report 11 4 22 (2 ^ (-24 : ℤ)) (2 ^ (-150 : ℤ)) rne32Q A B)
#eval do
  let A ← OzakiTCTests.Correct.decode64 OzakiTCTests.Correct.A_narrow64
  let B ← OzakiTCTests.Correct.decode64 OzakiTCTests.Correct.B_narrow64
  pure (report 11 5 69 (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) rne64 A B)
#eval do
  let A ← OzakiTCTests.Correct.decode64 OzakiTCTests.Correct.A_wide64
  let B ← OzakiTCTests.Correct.decode64 OzakiTCTests.Correct.B_wide64
  pure (report 11 5 69 (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) rne64 A B)
#eval (let (_, sh, n) := ozaki1Bounds 11 2 badX badY; (toF sh, toF n, toF (n / sh)))

end OzakiTCTests.SharpBounds
