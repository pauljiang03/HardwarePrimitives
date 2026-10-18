import MatrixCore.MC.Eval

/-! # Infinities, NaN and overflow

The observed output of one block for every input word. NaN payloads are not modeled. -/

namespace MatrixCore

/-- Observed output of one block. -/
inductive Outcome where
  | finite (d : F32)
  | infinity (negative : Bool)
  | nan
  deriving Repr, DecidableEq

/-- Extended values of the special-value semantics. -/
inductive XVal where
  | fin (q : ℚ)
  | inf (negative : Bool)
  | nan
  deriving Repr, DecidableEq

namespace XVal

def ofDatum : Datum → XVal
  | .finite x => .fin x.value
  | .infinity s => .inf s
  | .nan => .nan

/-- IEEE multiplication: `∞ · 0` is NaN. -/
def mul : XVal → XVal → XVal
  | .nan, _ | _, .nan => .nan
  | .inf s, .inf t => .inf (s != t)
  | .inf s, .fin q | .fin q, .inf s => if q = 0 then .nan else .inf (s != decide (q < 0))
  | .fin p, .fin q => .fin (p * q)

/-- IEEE addition: `+∞ + −∞` is NaN. -/
def add : XVal → XVal → XVal
  | .nan, _ | _, .nan => .nan
  | .inf s, .inf t => if s = t then .inf s else .nan
  | .inf s, .fin _ | .fin _, .inf s => .inf s
  | .fin p, .fin q => .fin (p + q)

def toFin : XVal → Option ℚ
  | .fin q => some q
  | _ => none

/-- `fl{·}` on extended values: overflow gives an infinity of the input's sign. -/
def fl (ftz : Bool) : XVal → XVal
  | .fin q => match flValue ftz q with
    | some v => .fin v
    | none => .inf (decide (q < 0))
  | v => v

end XVal

/-- Input-level special values: NaN dominates, `+∞` with `−∞` is NaN; `none` if all are finite. -/
def combineSpecial (xs : List XVal) : Option Outcome :=
  if xs.any (· == .nan) then some .nan
  else if xs.any (· == .inf false) && xs.any (· == .inf true) then some .nan
  else if xs.any (· == .inf false) then some (.infinity false)
  else if xs.any (· == .inf true) then some (.infinity true)
  else none

/-- `fl{S_acc}` as an observation. -/
def roundOutcome (ftz : Bool) (s : ℚ) : Outcome :=
  match fl32 ftz s with
  | some d => .finite d
  | none => .infinity (decide (s < 0))

/-- `pairwiseGroupSum` over extended values. -/
def pairwiseGroupSumX (ftz : Bool) : ℕ → List XVal → XVal
  | _, [] => .fin 0
  | _, [x] => x
  | 0, _ => .nan
  | depth + 1, xs =>
    let h := xs.length / 2
    XVal.fl ftz (XVal.add (pairwiseGroupSumX ftz depth (xs.take h)) (pairwiseGroupSumX ftz depth (xs.drop h)))

/-- Final `fl{·}` of an extended value. -/
def finishOutcome (ftz : Bool) : XVal → Outcome
  | .fin s => roundOutcome ftz s
  | .inf s => .infinity s
  | .nan => .nan

/-- CDNA 2 with FP32 special-value arithmetic, for finite inputs. -/
def pairwiseOutcome (P : Model) (x : Prepared) : Outcome :=
  let x' := if P.subnormals then x else x.flushed
  let ps := x'.p.map fun p => XVal.fl (!P.subnormals) (.fin p.value)
  finishOutcome (!P.subnormals) (XVal.add (.fin x'.c.value) (pairwiseGroupSumX (!P.subnormals) ps.length ps))

def finiteOutcome (P : Model) (x : Prepared) : Outcome :=
  if P.productOverflow && x.productOverflows then
    (combineSpecial (x.p.map fun p =>
      if pow2 128 ≤ absQ p.value then .inf (decide (p.value < 0)) else .fin p.value)).getD .nan
  else
    match P.accumulation with
    | .correctRounding => roundOutcome (!P.subnormals) x.exact
    | .pairWiseSum => pairwiseOutcome P x
    | .globalAlignment | .oddEvenGrouping => roundOutcome (!P.subnormals) (alignedAccumulation P x)

/-- A product with special values; CDNA 3 overflows at `|p_ℓ| ≥ 2^128`, CDNA 2 in `fl{p_ℓ}`. -/
def productX (P : Model) : Datum → Datum → XVal
  | .finite u, .finite v =>
    let q := (u.mul v).value
    if P.productOverflow && decide (pow2 128 ≤ absQ q) then .inf (decide (q < 0))
    else if P.accumulation = .pairWiseSum ∧ flValue (!P.subnormals) q = none then
      .inf (decide (q < 0))
    else .fin q
  | x, y => XVal.mul (.ofDatum x) (.ofDatum y)

/-- Products `a_ℓ · b_ℓ` of the decoded words, with special values. -/
def blockProducts {P : Model} (x : BlockInput P) : List XVal :=
  List.zipWith (fun a b => productX P (P.a.read a) (P.b.read b)) x.a x.b

/-- Observed output of one block; `none` only when the length of `a` or `b` is not `N_FMA`. -/
def blockOutcome {P : Model} (x : BlockInput P) : Option Outcome :=
  if x.a.length ≠ P.nfma ∨ x.b.length ≠ P.nfma then none
  else
    match prepare x with
    | some px => some (finiteOutcome P px)
    | none => some ((combineSpecial (.ofDatum (fp32.decode x.c) :: blockProducts x)).getD .nan)

/-- FP32 encodings of the infinities. -/
def infinity32 (negative : Bool) : F32 := if negative then 0xFF800000 else 0x7F800000

end MatrixCore
