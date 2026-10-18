import TensorCore.TC.AlignmentExponent
import TensorCore.TC.CanonicalDefs

/-! Fixed-width and exact accumulation give the same output. -/

namespace TensorCore

theorem evalPreparedMachine_eq (b : PreparedBlock) (w : ℕ) (hw : 0 < w)
    (h : magnitudeSum b.alignedBits < 2 ^ (w - 1)) :
    evalPreparedMachine w b = evalPrepared b := by
  simp only [evalPreparedMachine, evalPrepared, machineAccumulator_eq b w hw h]
  rfl

/-- All encoded inputs have identical reference and machine results at any adequate width. -/
theorem evalBlockMachine_eq {p : Model} (x : BlockInput p) (w F carryBits : ℕ)
    (hF : p.alignMantissaBits = F) (hcount : p.nfma + 1 ≤ 2 ^ carryBits)
    (hw : F + 2 + carryBits + 1 ≤ w) : evalBlockMachine w x = evalBlock x := by
  unfold evalBlockMachine evalBlock
  split
  · rfl
  · rename_i hshape
    have hs : x.products.length = p.nfma := by simpa using hshape
    cases hp : prepare x with
    | none => rfl
    | some b =>
      apply evalPreparedMachine_eq b w (by omega)
      have hc := prepare_coefficient_capacity hp hs F carryBits hF hcount
      have hm : 2 ^ ((F + 2 + carryBits + 1) - 1) ≤ 2 ^ (w - 1) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      omega

theorem fp16Fp32_machine_eq (K padding carryBits w : ℕ) (eAlignMin : Option ℤ)
    (x : BlockInput (fp16Fp32Model K padding eAlignMin))
    (hc : K + 1 ≤ 2 ^ carryBits) (hw : 26 + padding + carryBits ≤ w) :
    evalBlockMachine w x = evalBlock x :=
  evalBlockMachine_eq x w (23 + padding) carryBits rfl hc (by omega)

theorem v100_machine_eq (x : BlockInput v100F16F32) :
    evalBlockMachine 29 x = evalBlock x :=
  evalBlockMachine_eq x 29 23 3 rfl (by decide) (by decide)

theorem ampere_machine_eq (x : BlockInput ampereF16F32) :
    evalBlockMachine 31 x = evalBlock x :=
  fp16Fp32_machine_eq 8 1 4 31 (some (-132)) x (by decide) (by decide)

theorem hopper_machine_eq (x : BlockInput hopperF16F32) :
    evalBlockMachine 33 x = evalBlock x :=
  fp16Fp32_machine_eq 16 2 5 33 (some (-133)) x (by decide) (by decide)

end TensorCore
