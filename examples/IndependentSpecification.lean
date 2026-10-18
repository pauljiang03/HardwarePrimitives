import TensorCore.TC.Specification.Composition

open TensorCore

/-- Every encoded input of every named supported variant, with rejection preserved. -/
example (variant : IndependentSpec.Variant) (x : BlockInput (IndependentSpec.implementationModel variant)) :
    (evalBlock x).toOption.map (fun t => t.output.bits) =
      IndependentSpec.bits (IndependentSpec.parameters variant) (IndependentSpec.supportedInput variant x) :=
  IndependentSpec.supported_eq_spec variant x

/-- The specification-side validity condition entails success, rather than assuming it. -/
example (x : BlockInput a100BF16F32)
    (h : IndependentSpec.Valid (IndependentSpec.parametersOf a100BF16F32) (IndependentSpec.inputOf x)) :
    ∃ t, evalBlock x = .ok t ∧
      IndependentSpec.bits (IndependentSpec.parametersOf a100BF16F32) (IndependentSpec.inputOf x) = some t.output.bits :=
  IndependentSpec.valid_success x h (by decide)

/-- Every intermediate encoding of an explicitly ordered schedule, for an FP32 block output. -/
example (p : Model) (c : F32) (blocks : List (List (p.Word × p.Word))) (hw : 23 ≤ p.outputMantissaBits) :
    (runBlocks p c blocks).toOption.map (fun ts => ts.map fun t => t.output.bits) =
      IndependentSpec.runChain (IndependentSpec.parametersOf p) c blocks :=
  IndependentSpec.runBlocks_eq_spec p c blocks hw
