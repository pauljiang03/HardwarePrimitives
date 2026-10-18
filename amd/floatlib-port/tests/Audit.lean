import Lean
import MCFloat

/-! # Trust audit

Every `MCFloat` theorem uses only Lean's standard axioms, and the executable implementation reaches
no `MatrixCore` declaration. -/

open Lean Elab Command

namespace MCFloatTests.Audit

def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

partial def reach (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  match env.find? n with
  | none => pure ()
  | some info =>
    info.type.getUsedConstants.forM (reach env)
    match info with
    | .defnInfo d => d.value.getUsedConstants.forM (reach env)
    | .opaqueInfo d => d.value.getUsedConstants.forM (reach env)
    | _ => pure ()

def fromMatrixCore (env : Environment) (root : Name) : Array Name := Id.run do
  let deps := ((reach env root).run {}).2
  let mut bad := #[]
  for n in deps do
    if (moduleOf env n).any fun m => m.getRoot == `MatrixCore then bad := bad.push n
  return bad

def executableRoots : List Name :=
  [``MCFloat.dot, ``MCFloat.block, ``MCFloat.finiteBlock, ``MCFloat.pairwiseBlock,
    ``MCFloat.classify, ``MCFloat.Operand.read, ``MCFloat.round32, ``MCFloat.fl,
    ``MCFloat.add32, ``MCFloat.special, ``MCFloat.product, ``MCFloat.lateC]

elab "independence_audit" : command => do
  let env ← getEnv
  for root in executableRoots do
    let bad := fromMatrixCore env root
    unless bad.isEmpty do throwError "{root} depends on Matrix-Core declarations {bad}"
  let deps := ((reach env ``MCFloat.dot).run {}).2
  for used in [``FloatLib.Floats.Formats.BinaryInterchange.Model.toDyadic?,
      ``FloatLib.Floats.Formats.BinaryInterchange.Model.roundRatWithRounding,
      ``FloatLib.Floats.Formats.BinaryInterchange.Model.isNaN,
      ``FloatLib.Floats.Formats.BinaryInterchange.Model.isInf,
      ``FloatLib.Numerics.Dyadic.mul] do
    unless deps.contains used do throwError "MCFloat.dot does not use {used}"
  logInfo m!"independence_audit: {executableRoots.length} executable roots reach no Matrix-Core \
    declaration ({deps.size} constants reachable from MCFloat.dot); FloatLib decoding, \
    classification, products and rounding are used"

elab "axiom_audit" : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let roots := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    if ci.isTheorem && (`MCFloat).isPrefixOf n && !n.isInternal then acc.push n else acc
  for n in roots do
    let deps ← liftCoreM (collectAxioms n)
    unless deps.all allowed.contains do throwError "nonstandard axioms in {n}: {deps}"
  logInfo m!"axiom_audit: {roots.size} theorems, standard axioms only"

/-- Negative control: a definition that uses `MatrixCore` must be reported. -/
def badImplementation : ℚ := MatrixCore.pow2 3 + MCFloat.pow2 3

elab "negative_control" : command => do
  let bad := fromMatrixCore (← getEnv) ``badImplementation
  if bad.isEmpty then throwError "negative control: the audit missed a Matrix-Core dependency"
  logInfo m!"negative_control: detected {bad.size} Matrix-Core dependencies"

end MCFloatTests.Audit

independence_audit
axiom_audit
negative_control
