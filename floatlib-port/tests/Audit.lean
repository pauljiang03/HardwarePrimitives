import Lean
import TCFloat

/-! Axiom audit of every `TCFloat` theorem, and dependency checks on the executable. -/

open Lean Elab Command

elab "floatlib_port_audit" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let representationDefs : List Name := [``TCFloat.Equivalence.termEquiv,
    ``TCFloat.Equivalence.wordEquiv, ``TCFloat.Equivalence.inputEquiv,
    ``TCFloat.Equivalence.errorEquiv, ``TCFloat.Equivalence.eftResultEquiv]
  let names := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    if (ci.isTheorem || representationDefs.contains n) && n.getRoot == `TCFloat && !n.isInternal then acc.push n else acc
  let names := names.qsort fun a b => a.toString < b.toString
  let mut bad : Array Name := #[]
  let mut written : Nat := 0
  for n in names do
    let axioms ← liftCoreM (collectAxioms n)
    let axioms := axioms.qsort fun a b => a.toString < b.toString
    let axiomText := String.intercalate ", " (axioms.toList.map Name.toString)
    logInfo m!"'{n}' depends on axioms: [{axiomText}]"
    if axioms.any fun a => !allowed.contains a then
      bad := bad.push n
    if (← liftCoreM (findDeclarationRanges? n)).isSome then
      written := written + 1
  logInfo m!"floatlib_port_audit: {names.size} proof roots ({written} written in source, the rest generated)"
  unless bad.isEmpty do
    throwError m!"floatlib_port_audit: theorems with nonstandard axioms: {bad.toList}"

floatlib_port_audit

partial def visitDefinitions (env : Environment) (n : Name) : StateM NameSet Unit := do
  if (← get).contains n then return
  modify (·.insert n)
  match env.find? n with
  | some (.defnInfo info) => info.value.getUsedConstants.forM (visitDefinitions env)
  | some (.opaqueInfo info) => info.value.getUsedConstants.forM (visitDefinitions env)
  | _ => pure ()

def checkDependencies (root : Name) : CommandElabM Unit := do
  let deps := ((visitDefinitions (← getEnv) root).run {}).2
  let forbidden := [``TCFloat.Block.evaluate, ``TCFloat.Block.ideal, ``TCFloat.evalWords]
  let bad := forbidden.filter deps.contains
  unless bad.isEmpty do throwError "Forbidden executable dependencies: {bad}"
  logInfo m!"checked executable dependencies: {root}"

run_cmd do
  checkDependencies ``TCFloat.Trace.scalar
  checkDependencies ``TCFloat.Trace.encodedAlgorithm

/-- The executable implementation must remain independent of the source model. -/
def checkSourceIndependence (root : Name) : CommandElabM Unit := do
  let env ← getEnv
  let deps := ((visitDefinitions env root).run {}).2
  let bad := env.constants.fold (init := ([] : List Name)) fun acc n _ =>
    if n.getRoot == `TensorCore && deps.contains n then n :: acc else acc
  unless bad.isEmpty do throwError "Original implementation in executable dependencies: {bad}"
  logInfo m!"checked source independence: {root}"

run_cmd do
  checkDependencies ``TCFloat.Interface.eft
  checkDependencies ``TCFloat.Interface.eftChecked
  for root in [``TCFloat.decode, ``TCFloat.Term.mul, ``TCFloat.round32,
    ``TCFloat.Block.evaluate, ``TCFloat.Trace.scalar, ``TCFloat.Trace.encodedAlgorithm,
    ``TCFloat.Interface.tc, ``TCFloat.Interface.eft, ``TCFloat.Interface.tcChecked, ``TCFloat.Interface.eftChecked] do
    checkSourceIndependence root
