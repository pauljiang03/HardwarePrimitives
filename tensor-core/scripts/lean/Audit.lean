import Lean
import TensorCoreTests

/-! Axiom audit: every theorem in the `TensorCore` namespace, with the axioms its proof uses. -/

open Lean Elab Command

elab "tc_audit" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let names := env.constants.fold (init := (#[] : Array Name)) fun acc n ci =>
    if ci.isTheorem && n.getRoot == `TensorCore && !n.isInternal then acc.push n else acc
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
  logInfo m!"tc_audit: {names.size} theorem roots ({written} written in source, the rest generated)"
  unless bad.isEmpty do
    throwError m!"tc_audit: theorems with nonstandard axioms: {bad.toList}"

tc_audit
