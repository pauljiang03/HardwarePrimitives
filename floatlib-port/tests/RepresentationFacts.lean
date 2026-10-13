import TCFloat

/-! Representation checks for zero signs, metadata consistency, trace invariants, and model scope. -/
namespace TCFloat.Comparison
open FloatLib.Floats.Formats.BinaryInterchange

def project (t : Term) : Int × Int × Int :=
  (t.dyadic.signedSignificand,t.exponent,t.mantissaBits)

def zeroPositive : Term := ⟨⟨false,0,0⟩,0,0⟩
def zeroNegative : Term := ⟨⟨true,0,0⟩,0,0⟩

/-- Numerical projection erases the zero sign retained by FloatLib's dyadic representation. -/
theorem projection_not_injective :
    project zeroPositive = project zeroNegative ∧ zeroPositive ≠ zeroNegative := by
  constructor
  · decide +kernel
  · intro h
    have : false = true := congrArg (fun t : Term => t.dyadic.negative) h
    contradiction

theorem both_zero_forms_reachable :
    decode .binary16 0 = some zeroPositive ∧ decode .binary16 32768 = some zeroNegative := by
  constructor <;> rfl

/-- The extra dyadic exponent is unconstrained in the public unchecked Term structure. -/
def inconsistentTerm : Term := ⟨⟨false,1,0⟩,0,23⟩

theorem unrestricted_projection_changes_value :
    inconsistentTerm.value = 1 ∧
    (inconsistentTerm.dyadic.signedSignificand : ℚ) *
      pow2 (inconsistentTerm.exponent-inconsistentTerm.mantissaBits) ≠ inconsistentTerm.value := by
  decide +kernel

/-- `TensorCore.Finite32` requires bits/value consistency by a proof field; unchecked `Trace` permits inconsistent fields. -/
def inconsistentTrace : Trace :=
  ⟨⟨fp16 0 0,zeroPositive,[]⟩,0,1⟩

theorem unrestricted_trace_inconsistent :
    value32 inconsistentTrace.bits = some 0 ∧ inconsistentTrace.output = 1 := by
  decide +kernel

/-- The checked constructor does not construct the inconsistent trace. -/
theorem checked_trace_consistent :
    (trace inconsistentTrace.block 0).map Trace.output = some 0 := by
  decide +kernel

/-- The `23 + neab` family of models cannot keep F = 22 fractional bits after alignment. -/
theorem model_subset (neab : Nat) : (23 + neab : Int) ≠ 22 := by omega

end TCFloat.Comparison
