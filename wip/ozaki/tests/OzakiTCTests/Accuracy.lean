import OzakiTCTests.Z3Matrices

/-! # The Z3 models' accuracy checks on the V100 Tensor Core

The Z3 models measure the error of each method on their test matrices, in units of
`u32 = 2^-24`, componentwise (`|C − AB|ᵢⱼ / (|A||B|)ᵢⱼ`) and normwise
(`|C − AB|ᵢⱼ / (k max|aᵢ:| max|b:ⱼ|)`), print them (`ozaki1/output.txt`, `ozaki2/output.txt`), and
check:

* Ozaki-I `[M.2]`: four slices are at least as accurate as one (componentwise);
* Ozaki-I `[M.3]`: four slices meet the binary32 GEMM bound `k u |A||B|` (componentwise);
* Ozaki-II `[M.2]`: with `n` moduli and the largest `P` for them, the normwise error is at most
  `4 · 2^(24−P) + 1`, for `n = 1, 2, 3, 4`;
* Ozaki-II `[M.3]`: four moduli are at least as accurate as one (normwise).

Here the methods are the Lean pipelines on the V100 model, and every check is a kernel evaluation
in exact rational arithmetic. The errors also agree with every value the Z3 models print, to the
printed three decimals. -/

open TensorCore Ozaki Ozaki.TC OzakiTCTests.Z3Matrices

namespace OzakiTCTests.Accuracy

/-- The exact product `AB`. -/
def exactGemm (A B : List (List ℚ)) : List (List ℚ) :=
  A.map fun row => (transpose B).map fun col => dot row col

/-- Componentwise scale `(|A||B|)ᵢⱼ`. -/
def compScale (A B : List (List ℚ)) : List (List ℚ) :=
  A.map fun row => (transpose B).map fun col =>
    (List.zipWith (fun a b => Rat.abs a * Rat.abs b) row col).sum

/-- Normwise scale `k max|aᵢ:| max|b:ⱼ|`. -/
def normScale (A B : List (List ℚ)) : List (List ℚ) :=
  A.map fun row => (transpose B).map fun col => (row.length : ℚ) * maxAbs row * maxAbs col

/-- `maxᵢⱼ |C − Cₓ|ᵢⱼ / scaleᵢⱼ` in units of `2^-24`, skipping zero scales (the Z3 models'
`err_in_u32`). -/
def errU32 (C Cx S : List (List ℚ)) : ℚ :=
  (List.zipWith (fun r q => List.zipWith (fun c p => if p.2 = 0 then 0 else
      Rat.abs (c - p.1) / p.2) r q) C (List.zipWith List.zip Cx S)).flatten.foldl max 0 *
    2 ^ (24 : ℤ)

/-- Componentwise and normwise error of a computed product. -/
def errs (A B C : List (List ℚ)) : ℚ × ℚ :=
  (errU32 C (exactGemm A B) (compScale A B), errU32 C (exactGemm A B) (normScale A B))

/-- The errors of Ozaki-I with `s` slices of `11` bits on V100. -/
def errI (s : ℕ) (A B : List (List F32)) : Option (ℚ × ℚ) := do
  let A ← decodeMatrix A; let B ← decodeMatrix B
  let C ← tcOzaki1Gemm v100F16F32 11 s A B
  pure (errs A B C)

/-- The first `n` Z3 moduli and the largest `P` for them (`k = 4`). -/
def basisOf (n : ℕ) : CRTBasis := crtBasis (z3Moduli.take n)

def bitsOf (n : ℕ) : ℕ := ozaki2Bits 4 (basisOf n).modulus 64

/-- The errors of Ozaki-II with the first `n` Z3 moduli on V100. -/
def errII (n : ℕ) (A B : List (List F32)) : Option (ℚ × ℚ) := do
  let A ← decodeMatrix A; let B ← decodeMatrix B
  let C ← tcOzaki2Gemm v100F16F32 (basisOf n) (bitsOf n) A B
  pure (errs A B C)

/-- `a ≤ b` for two computed errors; `false` if either is missing. -/
def leOpt : Option ℚ → Option ℚ → Bool
  | some a, some b => decide (a ≤ b)
  | _, _ => false

/-- An error agrees with a value printed to three decimals. -/
def printed (e : Option ℚ) (v : ℚ) : Bool :=
  match e with
  | some e => decide (Rat.abs (e - v) ≤ 1 / 2000)
  | none => false

example : (List.range' 1 4).map bitsOf = [4, 10, 16, 22] := by decide +kernel
example : ∀ n ∈ List.range' 1 4, (basisOf n).Valid := by decide +kernel

/-! ## Ozaki-I -/

/-- `[M.2]`: four slices are at least as accurate as one, componentwise, both cases. -/
example : leOpt ((errI 4 A_narrow B_narrow).map (·.1)) ((errI 1 A_narrow B_narrow).map (·.1)) &&
    leOpt ((errI 4 A_wide B_wide).map (·.1)) ((errI 1 A_wide B_wide).map (·.1)) := by
  decide +kernel

/-- `[M.3]`: four slices are within `k u |A||B|`, componentwise, both cases. -/
example : leOpt ((errI 4 A_narrow B_narrow).map (·.1)) (some 4) &&
    leOpt ((errI 4 A_wide B_wide).map (·.1)) (some 4) := by decide +kernel

/-- The errors printed by the Z3 Ozaki-I model (`ozaki1/output.txt`), componentwise and normwise,
for one to four slices, narrow case. -/
example : [(1, 10867112, 2735486), (2, 4028, 1057), (3, 767, 246), (4, 767, 246)].all
    (fun (s, c, n) => printed ((errI s A_narrow B_narrow).map (·.1)) (c / 1000) &&
      printed ((errI s A_narrow B_narrow).map (·.2)) (n / 1000)) := by decide +kernel

/-- The same, wide case. -/
example : [(1, 28573011, 2154034), (2, 9782, 850), (3, 646, 139), (4, 646, 139)].all
    (fun (s, c, n) => printed ((errI s A_wide B_wide).map (·.1)) (c / 1000) &&
      printed ((errI s A_wide B_wide).map (·.2)) (n / 1000)) := by decide +kernel

/-! ## Ozaki-II -/

/-- `[M.2]`: with `n` moduli the normwise error is at most `4 · 2^(24−P) + 1`, both cases. -/
example : (List.range' 1 4).all (fun n =>
    leOpt ((errII n A_narrow B_narrow).map (·.2)) (some (4 * 2 ^ ((24 : ℤ) - bitsOf n) + 1)) &&
    leOpt ((errII n A_wide B_wide).map (·.2)) (some (4 * 2 ^ ((24 : ℤ) - bitsOf n) + 1))) := by
  decide +kernel

/-- `[M.3]`: four moduli are at least as accurate as one, normwise, both cases. -/
example : leOpt ((errII 4 A_narrow B_narrow).map (·.2)) ((errII 1 A_narrow B_narrow).map (·.2)) &&
    leOpt ((errII 4 A_wide B_wide).map (·.2)) ((errII 1 A_wide B_wide).map (·.2)) := by
  decide +kernel

/-- The errors printed by the Z3 Ozaki-II model (`ozaki2/output.txt`), componentwise and
normwise, for one to four moduli, narrow case. -/
example : [(1, 2422764634, 775373493), (2, 57895018, 17909900), (3, 728585, 252025),
    (4, 10112, 3036)].all
    (fun (n, c, w) => printed ((errII n A_narrow B_narrow).map (·.1)) (c / 1000) &&
      printed ((errII n A_narrow B_narrow).map (·.2)) (w / 1000)) := by decide +kernel

/-- The same, wide case. -/
example : [(1, 16777216000, 627678195), (2, 207973078, 18800136), (3, 3134025, 230808),
    (4, 61716, 3193)].all
    (fun (n, c, w) => printed ((errII n A_wide B_wide).map (·.1)) (c / 1000) &&
      printed ((errII n A_wide B_wide).map (·.2)) (w / 1000)) := by decide +kernel

end OzakiTCTests.Accuracy
