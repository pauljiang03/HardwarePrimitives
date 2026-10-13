import MatrixCore.MC.Eval
import MatrixCore.Numerics.Sum

/-! # A fixed-width register model of the CDNA 3 accumulation

Algorithms 1 and 2 accumulate the products in fixed point: each product is shifted to `e_max`
and keeps `23 + n_eab` fractional bits, so it is an integer number of steps of
`2^(e_max − 23 − n_eab)` (`alignedBits`). The model adds these integers exactly (`alignedSum`).
Here they are added by modular `w`-bit additions, and odd/even grouping moves the group with the
smaller exponent to the common `e_max` by an arithmetic right shift, which is the RD of
Algorithm 2. The late addition of `c` and the final `fl{·}` are unchanged. -/

namespace MatrixCore

/-- `23 + n_eab`: fractional bits kept by product alignment. -/
abbrev Model.alignFracBits (P : Model) : ℕ := 23 + P.neab

/-- The aligned significands of the products as integers: steps of `2^(e − 23 − n_eab)`. -/
def alignedBits (neab : ℕ) (e : ℤ) (ps : List Unpacked) : List ℤ :=
  ps.map fun p => truncBits p.value (e - (23 + neab : ℕ))

/-- Actual modular signed-word additions, starting from a supplied register. -/
def machineAccumulate (w : ℕ) (acc : BitVec w) : List ℤ → BitVec w
  | [] => acc
  | z :: zs => machineAccumulate w (acc + BitVec.ofInt w z) zs

/-- `e_max` of a group and its aligned sum in a `w`-bit register, counting steps of
`2^(e_max − 23 − n_eab)`. -/
def machineAlignedSum (w neab : ℕ) (ps : List Unpacked) : Option ℤ × BitVec w :=
  match maxExp ps with
  | none => (none, 0)
  | some e => (some e, machineAccumulate w 0 (alignedBits neab e ps))

/-- A group's register moved from its own `e_max` to the common exponent `e`: an arithmetic right
shift, which rounds toward −∞ (RD). -/
def shiftRegister (e : ℤ) (s : Option ℤ × BitVec w) : BitVec w :=
  s.2.sshiftRight (e - s.1.getD e).toNat

/-- `(e_max, S_{p_i,sum})` of the configuration, computed in `w`-bit registers. -/
def machineProductSum (w : ℕ) (P : Model) (ps : List Unpacked) : Option ℤ × ℚ :=
  match P.accumulation with
  | .oddEvenGrouping =>
    let odd := machineAlignedSum w P.neab (oddIndexed ps)
    let even := machineAlignedSum w P.neab (evenIndexed ps)
    match joinExp odd.1 even.1 with
    | none => (none, 0)
    | some e =>
      (some e, ((shiftRegister e odd + shiftRegister e even).toInt : ℚ) *
        pow2 (e - (23 + P.neab : ℕ)))
  | _ =>
    let s := machineAlignedSum w P.neab ps
    (s.1, (s.2.toInt : ℚ) * pow2 (s.1.getD 0 - (23 + P.neab : ℕ)))

/-- `S_acc` of Algorithms 1 and 2 with `w`-bit product accumulation. -/
def machineAlignedAccumulation (w : ℕ) (P : Model) (x : Prepared) : ℚ :=
  let s := machineProductSum w P x.p
  lateSum P s.1 s.2 x.c

/-- `accumulate` with the CDNA 3 product sums in `w`-bit registers. -/
def accumulateMachine (w : ℕ) (P : Model) (x : Prepared) : Except ModelError ℚ :=
  if P.productOverflow && x.productOverflows then .error .productOverflow
  else
    match P.accumulation with
    | .correctRounding => .ok x.exact
    | .pairWiseSum =>
      match pairwiseSum P x with
      | none => .error .intermediateOverflow
      | some s => .ok s
    | .globalAlignment | .oddEvenGrouping => .ok (machineAlignedAccumulation w P x)

/-- `evalBlock` with `w`-bit product accumulation, then the ordinary final `fl{·}`. -/
def evalBlockMachine (w : ℕ) {P : Model} (x : BlockInput P) : Except ModelError (BlockTrace P) :=
  if x.a.length ≠ P.nfma ∨ x.b.length ≠ P.nfma then .error .wrongLength
  else
    match prepare x with
    | none => .error .nonfiniteInput
    | some px =>
      match accumulateMachine w P px with
      | .error e => .error e
      | .ok s =>
        match fl32 (!P.subnormals) s with
        | none => .error .outputOverflow
        | some d => .ok ⟨px, s, d⟩

end MatrixCore
